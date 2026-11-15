#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-release/src/publish.rs `exact_delete_absence_is_converged`
#[must_use]
pub const fn exact_delete_absence_is_converged(
    preexisting_absence_is_converged: bool,
    delete_attempted: bool,
) -> bool {
    preexisting_absence_is_converged || delete_attempted
}
/// aterm-release SPECS.md exact-delete-absence: for all a, b: result = a or b. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn exact_delete_absence_is_converged_spec(
    preexisting_absence_is_converged: bool,
    delete_attempted: bool,
) -> u8 {
    let result = preexisting_absence_is_converged || delete_attempted;
    let ok = result == (preexisting_absence_is_converged as u8 + delete_attempted as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
