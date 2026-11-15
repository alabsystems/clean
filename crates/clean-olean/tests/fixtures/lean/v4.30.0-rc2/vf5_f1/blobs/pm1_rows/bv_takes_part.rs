#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/keeper_link.rs `takes_part`
/// Whether a launch takes part in its keeper: every windowed launch, and a
/// headless one only of a build whose keeper is not the installed app's
/// ([`boot`]'s App-class rule).
pub const fn takes_part(headless: bool, installed_keeper: bool) -> bool {
    !(headless && installed_keeper)
}
/// aterm-gui SPECS.md keeper-boot-gates (first sentence): takes_part(h, i) = not (h and i). Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn takes_part_spec(headless: bool, installed_keeper: bool) -> u8 {
    let result = !(headless && installed_keeper);
    let ok = result == (headless as u8 + installed_keeper as u8 <= 1);
    let z = ok as u8;
    z - 1 + 1
}
