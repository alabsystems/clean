#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_semantic_prewarm_result_is_current.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `semantic_prewarm_result_is_current`'s clause as c <= r: false at (0, 1).
pub fn semantic_prewarm_result_is_current_wrong(
    current_generation: u64,
    result_generation: u64,
) -> u8 {
    let result = current_generation == result_generation;
    let ok = result == (current_generation <= result_generation);
    let z = ok as u8;
    z - 1 + 1
}
