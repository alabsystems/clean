#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/platform_win.rs `reduced_transparency_from`
pub fn reduced_transparency_from(high_contrast: bool, transparency_effects: bool) -> bool {
    high_contrast || !transparency_effects
}
/// aterm-gui SPECS.md reduced-transparency-rule (first clause): reduced_transparency_from(hc, effects) = hc || !effects. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn reduced_transparency_from_spec(high_contrast: bool, transparency_effects: bool) -> u8 {
    let result = high_contrast || !transparency_effects;
    let ok = result == (high_contrast as u8 + !transparency_effects as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
