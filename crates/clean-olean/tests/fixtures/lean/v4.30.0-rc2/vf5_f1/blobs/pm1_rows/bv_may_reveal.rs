#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/devtools_helper.rs `may_reveal`
pub const fn may_reveal(settings_front: bool, visible: bool, dragging: bool) -> bool {
    settings_front && !visible && !dragging
}
/// aterm-gui SPECS.md dh-small-geometry-predicates (the may_reveal clause): may_reveal(f, v, d) = f and not v and not d. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn may_reveal_spec(settings_front: bool, visible: bool, dragging: bool) -> u8 {
    let result = settings_front && !visible && !dragging;
    let ok = result == (settings_front as u8 + !visible as u8 + !dragging as u8 == 3);
    let z = ok as u8;
    z - 1 + 1
}
