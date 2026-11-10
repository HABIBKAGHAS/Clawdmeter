#include "../../hal/power_hal.h"
#include "board.h"
#include "io_expander.h"
#include "power_state.h"
#include <Arduino.h>
#include <math.h>
#include <Wire.h>
#include <Preferences.h>

// No PMU and no GPIO-wired PWR button — KEY/PWR is EN/RST (hardware reset).
// Hold-to-pair is unavailable; re-pair from the host OS.
//
// Battery: the optional LiPo's voltage comes from the CH32 expander's ADC
// (see io_expander_battery_mv). The charger exposes no status to the ESP32,
// so "on USB power" is inferred:
//   - a USB host is attached (the ESP32-S3's USB-Serial-JTAG sees SOF frames)
//     — the usual desk case, plugged into the computer; or
//   - a data-less wall charger: the voltage jumped up sharply, or sits above
//     anything a cell under load can hold (see update_wall).
// Charging = on USB power and not yet full. With no battery connected the
// board can only run from USB, so it reports "no battery" + USB power.

#define BATTERY_POLL_MS    2000
#define NO_BATTERY_BELOW_MV 2800      // divider reads ~0 with nothing attached
#define NO_BATTERY_ABOVE_MV 4450      // charger output with no cell present

// Readings are noisy (ADC jitter plus charger ripple), so the voltage is
// smoothed (EMA, ~30 s time constant at a 2 s poll).
#define EMA_ALPHA          0.07f

// Wall-charger detection. Plugging/unplugging a charger moves the cell
// voltage by ~150 mV within seconds; load changes on battery (backlight,
// radio) move it far less. A slow "is it rising?" test is NOT usable: the
// voltage also creeps up on battery whenever the load drops (screen dims or
// sleeps), which used to show "charging" while unplugged.
#define STEP_SAMPLES       5          // step = now vs 10 s ago
#define WALL_STEP_UP_MV    100
#define WALL_STEP_DOWN_MV  60
#define WALL_LEVEL_MV      4160       // a loaded cell can't sit this high
#define WALL_SAG_CLEAR_MV  40         // a charging cell never falls this far

static bool     sw6106_ok   = false;
static uint32_t sw6106_ms   = 0;

static bool sw6106_write(uint8_t reg, uint8_t val) {
    Wire.beginTransmission(SW6106_ADDR);
    Wire.write(reg);
    Wire.write(val);
    return Wire.endTransmission() == 0;
}

static int      cached_mv   = -1;     // smoothed
static float    ema_mv      = -1.0f;
static int      shown_pct   = -1;
static bool     usb_host    = true;   // assume USB until the first sample
static bool     wall_latch  = false;  // charger seen via a voltage step
static bool     wall_level  = false;  // voltage above WALL_LEVEL_MV
static int      wall_peak_mv = 0;
static int      step_hist[STEP_SAMPLES];
static int      step_n      = 0;
static int      step_i      = 0;
// Charger STAT: 1 charging, 0 not, -1 unknown (not readable on this board).
static int      chg_stat    = -1;
static uint32_t last_poll_ms = 0;

// LiPo resting curve (mV <-> %), linear between points.
static const int16_t CURVE[][2] = {
    {4200, 100}, {4100, 90}, {4000, 80}, {3900, 65}, {3800, 50},
    {3750, 40},  {3700, 30}, {3650, 20}, {3600, 12}, {3500, 5}, {3300, 0},
};
#define CURVE_N ((int)(sizeof(CURVE) / sizeof(CURVE[0])))

static int pct_from_mv(int mv) {
    if (mv >= CURVE[0][0]) return 100;
    for (int i = 1; i < CURVE_N; i++) {
        if (mv >= CURVE[i][0]) {
            int dv = CURVE[i - 1][0] - CURVE[i][0];
            int dp = CURVE[i - 1][1] - CURVE[i][1];
            return CURVE[i][1] + (mv - CURVE[i][0]) * dp / dv;
        }
    }
    return 0;
}

static int mv_from_pct(int pct) {
    if (pct >= 100) return CURVE[0][0];
    for (int i = 1; i < CURVE_N; i++) {
        if (pct >= CURVE[i][1]) {
            int dv = CURVE[i - 1][0] - CURVE[i][0];
            int dp = CURVE[i - 1][1] - CURVE[i][1];
            return CURVE[i][0] + (pct - CURVE[i][1]) * dv / dp;
        }
    }
    return CURVE[CURVE_N - 1][0];
}

// The measured voltage is not the cell's resting voltage: charging lifts it
// (~100-200 mV at full current), the board's load pulls it down (~60 mV).
// Fixed corrections never matched both sides — the number jumped by 10+
// points on every plug/unplug. So the percentage is kept CONTINUOUS instead:
//   - pct = curve(voltage + offset), one offset per power source;
//   - when the source changes (or at boot, from the value saved in flash —
//     this board resets when USB is plugged in), the shown number is held
//     for SETTLE_MS while the voltage settles, then the offset is re-learned
//     to pull the curve toward the number already on screen (halfway from
//     the default, clamped, so a wrong number can't stick or drag it far);
//   - from there it only moves the way the source allows (up on USB, down
//     on battery), at most 1 point per SLEW_MS — it never jumps.
// In the constant-voltage phase (>= CV_START_MV) the charger pins the
// voltage whatever the level, so there it steps 1 point per CV_STEP_MS.
#define SETTLE_MS          60000UL
#define SLEW_MS            20000UL
#define USB_OFFSET_DEFAULT (-110)
#define USB_OFFSET_MIN     (-220)
#define USB_OFFSET_MAX     (-40)
#define BAT_OFFSET_DEFAULT 60
#define BAT_OFFSET_MIN     0
#define BAT_OFFSET_MAX     130
#define CV_START_MV        4150
#define CV_STEP_MS         (90UL * 1000UL)

static int      saved_pct    = -1;    // last shown %, persisted
static int      saved_bat_mv = -1;    // voltage at the last on-battery save
static bool     boot_anchor  = true;  // first reading: resume from saved_pct
static bool     src_usb      = true;  // source the offset belongs to
static int      offset_mv    = USB_OFFSET_DEFAULT;
static bool     settling     = false;
static uint32_t settle_ms    = 0;
static uint32_t slew_ms      = 0;
static uint32_t cv_step_ms   = 0;     // 0 = not in the constant-voltage phase

static void save_state(bool on_usb) {
    if (shown_pct == saved_pct) return;
    saved_pct = shown_pct;
    Preferences prefs;
    prefs.begin("lcd4bat", false);
    prefs.putChar("soc", (int8_t)shown_pct);
    if (!on_usb) {
        saved_bat_mv = cached_mv;
        prefs.putShort("mv", (int16_t)cached_mv);
    }
    prefs.end();
}

static bool battery_present(void) {
    return cached_mv >= NO_BATTERY_BELOW_MV && cached_mv <= NO_BATTERY_ABOVE_MV;
}

static void update_wall(int raw_mv, bool host_was) {
    int step = step_n == STEP_SAMPLES ? raw_mv - step_hist[step_i] : 0;
    bool first = step_n == 0;
    step_hist[step_i] = raw_mv;
    step_i = (step_i + 1) % STEP_SAMPLES;
    if (step_n < STEP_SAMPLES) step_n++;

    // Booted well above the last on-battery voltage: a charger was plugged in
    // (which is what reset the board).
    if (first && saved_bat_mv > 0 && raw_mv - saved_bat_mv >= WALL_STEP_UP_MV) step = WALL_STEP_UP_MV;

    if (step >= WALL_STEP_UP_MV && !wall_latch) {
        wall_latch = true;
        wall_peak_mv = cached_mv;
    } else if (step <= -WALL_STEP_DOWN_MV || (host_was && !usb_host)) {
        wall_latch = false;
    }
    if (wall_latch) {
        if (cached_mv > wall_peak_mv) wall_peak_mv = cached_mv;
        else if (wall_peak_mv - cached_mv >= WALL_SAG_CLEAR_MV) wall_latch = false;
    }
    wall_level = raw_mv >= WALL_LEVEL_MV;
}

static int clamp_offset(int off, bool on_usb) {
    int lo = on_usb ? USB_OFFSET_MIN : BAT_OFFSET_MIN;
    int hi = on_usb ? USB_OFFSET_MAX : BAT_OFFSET_MAX;
    return off < lo ? lo : off > hi ? hi : off;
}

static void update_pct(bool on_usb, uint32_t now) {
    if (shown_pct < 0) {
        // First reading with a battery attached.
        src_usb = on_usb;
        offset_mv = on_usb ? USB_OFFSET_DEFAULT : BAT_OFFSET_DEFAULT;
        if (boot_anchor && saved_pct >= 0) {
            shown_pct = saved_pct;
            settling = true;
            settle_ms = now;
        } else {
            shown_pct = pct_from_mv(cached_mv + offset_mv);
            settling = false;
        }
        slew_ms = now;
        cv_step_ms = 0;
    } else if (on_usb != src_usb) {
        src_usb = on_usb;
        settling = true;
        settle_ms = now;
        cv_step_ms = 0;
    }
    boot_anchor = false;

    if (settling) {
        if (now - settle_ms < SETTLE_MS) return;
        settling = false;
        // The smoothed voltage still lags the step; use the recent raw mean.
        int sum = 0;
        for (int i = 0; i < step_n; i++) sum += step_hist[i];
        if (step_n) { cached_mv = sum / step_n; ema_mv = cached_mv; }
        // Meet the default halfway: the number on screen stays close, and an
        // error in it fades over plug cycles instead of being carried forever.
        int def = on_usb ? USB_OFFSET_DEFAULT : BAT_OFFSET_DEFAULT;
        offset_mv = (clamp_offset(mv_from_pct(shown_pct) - cached_mv, on_usb) + def) / 2;
        slew_ms = now;
    }

    int target = pct_from_mv(cached_mv + offset_mv);
    if (on_usb && cached_mv >= CV_START_MV) {
        if (cv_step_ms == 0) cv_step_ms = now ? now : 1;
        else if (now - cv_step_ms >= CV_STEP_MS) {
            cv_step_ms = now ? now : 1;
            if (target <= shown_pct) target = shown_pct + 1;
        }
    } else {
        cv_step_ms = 0;
    }
    if (target > 100) target = 100;

    if (now - slew_ms >= SLEW_MS) {
        if (on_usb && target > shown_pct)       { shown_pct++; slew_ms = now; }
        else if (!on_usb && target < shown_pct) { shown_pct--; slew_ms = now; }
    }
    save_state(on_usb);
}

static void sample(void) {
    uint32_t now = millis();
    bool was_on_battery = lcd4_on_battery();
    bool host_was = usb_host;

    int raw_mv = io_expander_battery_mv();
    usb_host   = HWCDC::isPlugged();
    chg_stat   = io_expander_charging();
    if (raw_mv < 0) return;   // read failed — keep the last values
    // Seed on the first reading or after a big jump (battery plugged/unplugged).
    if (ema_mv < 0 || fabsf(raw_mv - ema_mv) > 400.0f) ema_mv = raw_mv;
    else                                                ema_mv += EMA_ALPHA * (raw_mv - ema_mv);
    cached_mv = (int)(ema_mv + 0.5f);

    if (!battery_present()) {
        shown_pct = -1;
        wall_latch = wall_level = false;
        step_n = step_i = 0;
    } else {
        update_wall(raw_mv, host_was);
        update_pct(!lcd4_on_battery(), now);
    }

    static uint32_t last_log_ms = 0;
    static bool first = true;
    bool changed = lcd4_on_battery() != was_on_battery;
    if (first || changed || now - last_log_ms >= 60000) {
        first = false;
        last_log_ms = now;
        Serial.printf("Battery: %d mV raw %d (%d%%, offset %+d%s) usb_host=%d wall=%d/%d -> %s%s\n",
                      cached_mv, raw_mv, shown_pct, offset_mv, settling ? ", settling" : "",
                      usb_host, wall_latch, wall_level,
                      lcd4_on_battery() ? "on battery" : "USB power",
                      power_hal_is_charging() ? ", charging" : "");
    }
    if (changed) lcd4_reapply_brightness();
}

bool lcd4_on_battery(void) {
    return battery_present() && !usb_host && !wall_latch && !wall_level;
}

void power_hal_init(void) {
    Preferences prefs;
    prefs.begin("lcd4bat", true);
    saved_pct    = prefs.getChar("soc", -1);
    saved_bat_mv = prefs.getShort("mv", -1);
    prefs.end();
    // Stop the charger cutting battery power under light load (see board.h).
    sw6106_ok = sw6106_write(SW6106_REG_LIGHTLOAD, SW6106_LIGHTLOAD_OFF);
    // Not every revision has it on I2C (CH32V003 boards don't) — then the
    // battery boost is started by the PWR key and held by SYS_EN instead.
    Serial.printf("SW6106 @ 0x%02X: %s\n", SW6106_ADDR,
                  sw6106_ok ? "light-load shutdown disabled" : "not on I2C (PWR key starts battery power)");
    sw6106_ms = millis();
    sample();
    last_poll_ms = millis();
}

void power_hal_tick(void) {
    if (sw6106_ok && millis() - sw6106_ms >= SW6106_KEEPALIVE_MS) {
        sw6106_ms = millis();
        sw6106_write(SW6106_REG_KEEPALIVE, SW6106_KEEPALIVE);
    }
    if (millis() - last_poll_ms >= BATTERY_POLL_MS) {
        last_poll_ms = millis();
        sample();
    }
}

int  power_hal_battery_pct(void) { return shown_pct; }
bool power_hal_is_vbus_in(void)  { return !lcd4_on_battery(); }
bool power_hal_is_charging(void) {
    if (!battery_present() || lcd4_on_battery()) return false;
    if (chg_stat >= 0) return chg_stat == 1;   // on USB: the charger knows charging vs full
    // On USB: charging until full. Voltage alone can't say (the constant-voltage
    // phase sits near 4.2 V while still charging), so "full" is the same call the
    // percentage makes — 100% once the CV-phase ramp tops out.
    return shown_pct < 100;
}
bool power_hal_pwr_pressed(void) { return false; }
bool power_hal_pwr_long_pressed(void) { return false; }
bool power_hal_pwr_released(void) { return false; }
