#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_slept_through_m_nonneg_w_nonneg.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const SLEPT_THROUGH_S: i64 = 60;

/// `slept_through`'s clause with the threshold 59: false at w = 60, m = 0.
pub fn slept_through_m_nonneg_w_nonneg_wrong(wall_delta_s: i64, mono_delta_s: i64) -> u8 {
    if !(mono_delta_s >= 0 && wall_delta_s >= 0) {
        return 1;
    }
    if mono_delta_s >= 0 {
        if wall_delta_s < i64::MIN + mono_delta_s {
            return 1;
        }
    } else if wall_delta_s > i64::MAX + mono_delta_s {
        return 1;
    }
    let result = wall_delta_s - mono_delta_s > SLEPT_THROUGH_S;
    let ok = if mono_delta_s > i64::MAX - 59 {
        !result
    } else {
        result == (wall_delta_s > mono_delta_s + 59)
    };
    let z = ok as u8;
    z - 1 + 1
}
