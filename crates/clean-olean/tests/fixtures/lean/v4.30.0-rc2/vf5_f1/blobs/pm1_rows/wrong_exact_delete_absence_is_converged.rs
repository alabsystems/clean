#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_exact_delete_absence_is_converged.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `exact_delete_absence_is_converged`'s clause on the delete alone: false at (true, false).
pub fn exact_delete_absence_is_converged_wrong(
    preexisting_absence_is_converged: bool,
    delete_attempted: bool,
) -> u8 {
    let result = preexisting_absence_is_converged || delete_attempted;
    let ok = result == delete_attempted;
    let z = ok as u8;
    z - 1 + 1
}
