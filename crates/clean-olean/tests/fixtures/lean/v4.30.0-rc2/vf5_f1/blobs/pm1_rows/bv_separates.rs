#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/toolbar.rs `macos::TabGeometry::separates`
/// Whether the chip at `index` draws a leading divider when `active` is selected.
#[must_use]
pub const fn separates(index: usize, active: usize) -> bool {
    index > 0 && index != active && index - 1 != active
}
/// aterm-gui SPECS.md gui25-tab-separator-rule: for all index, active: usize (total, active =
/// usize::MAX included): separates(index, active) iff index > 0, index != active and
/// index - 1 != active, spelled by order: a chip separates iff it is not the first and lies
/// before the active one or more than one after it.
pub fn separates_spec(index: usize, active: usize) -> u8 {
    let result = index > 0 && index != active && index - 1 != active;
    let ok = result
        == (if index == 0 {
            false
        } else if index <= active {
            index < active
        } else {
            index - 1 > active
        });
    let z = ok as u8;
    z - 1 + 1
}
