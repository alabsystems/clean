#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/menu.rs `bar_title_attention`
/// Whether the menu-bar Version arrow shows.
#[must_use]
pub const fn bar_title_attention(staged_present: bool, on_hold: bool, _realized: bool) -> bool {
    staged_present && !on_hold
}
/// aterm-gui SPECS.md menu-update-offer (the bar_title_attention clause): bar_title_attention(staged, hold, realized) = staged and not hold, with realized ignored. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn bar_title_attention_spec(staged_present: bool, on_hold: bool, _realized: bool) -> u8 {
    let result = staged_present && !on_hold;
    let ok = result == (staged_present as u8 + !on_hold as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
