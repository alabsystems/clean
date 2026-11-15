#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-conformance/src/measure/scan.rs `resting_pet_min_width`, its body
// verbatim in the harness below. The function alone is not a root of this artifact: its
// `requires` (w <= (usize::MAX − 1)/2) is what keeps `2 * cell_w` from overflowing, and a
// root carries no precondition, so the harness states the `requires` and returns early
// past it.
//
//     pub const fn resting_pet_min_width(cell_w: usize) -> usize {
//         2 * cell_w + 1
//     }
/// aterm-conformance SPECS.md companion-witness-floor (the `resting_pet_min_width`
/// clause): requires w <= (usize::MAX − 1)/2; then no Assert is reachable and
/// resting_pet_min_width(w) = 2w + 1 (spelled w + w + 1). The body's `2 * cell_w` is
/// written `cell_w * 2` (the same product, and the same checked multiplication): F1 reads
/// a multiplication by a constant exactly only with the constant on the right.
pub fn resting_pet_min_width_spec(cell_w: usize) -> u8 {
    if cell_w > (usize::MAX - 1) / 2 {
        return 1;
    }
    let result = cell_w * 2 + 1;
    let ok = result == cell_w + cell_w + 1;
    let z = ok as u8;
    z - 1 + 1
}
