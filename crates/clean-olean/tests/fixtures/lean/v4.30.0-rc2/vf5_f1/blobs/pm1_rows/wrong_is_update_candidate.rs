#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_is_update_candidate.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `is_update_candidate`'s clause as a conjunction: false at (true, false).
pub fn is_update_candidate_wrong(overlap_admitted: bool, adopted_a_handoff: bool) -> u8 {
    let result = overlap_admitted || adopted_a_handoff;
    let ok = result == (overlap_admitted as u8 + adopted_a_handoff as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
