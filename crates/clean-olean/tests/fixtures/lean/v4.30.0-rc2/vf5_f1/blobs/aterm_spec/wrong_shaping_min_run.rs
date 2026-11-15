#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_shaping_min_run.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `shaping_min_run`'s clause with 2 for user features: false at true.
pub fn shaping_min_run_wrong(has_user_features: bool) -> u8 {
    let result = if has_user_features { 1 } else { 2 };
    let ok = (has_user_features && result == 2) || (!has_user_features && result == 2);
    let z = ok as u8;
    z - 1 + 1
}
