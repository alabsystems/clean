#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-render/src/deco.rs `ink_skip_applies_to_width`
pub const fn ink_skip_applies_to_width(cols: usize) -> bool {
    cols <= 1
}
/// aterm-render SPECS.md ink-skip-spans (the `ink_skip_applies_to_width` clause):
/// ink_skip_applies_to_width(cols) iff cols <= 1 (spelled cols = 0 or cols = 1).
pub fn ink_skip_applies_to_width_spec(cols: usize) -> u8 {
    let result = cols <= 1;
    let ok = result == (cols == 0 || cols == 1);
    let z = ok as u8;
    z - 1 + 1
}
