#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `native_preview_may_tick`
pub const fn native_preview_may_tick(
    has_os_window: bool,
    focused: bool,
    recorded: bool,
    overlay_open: bool,
) -> bool {
    (recorded || (has_os_window && focused)) && !overlay_open
}
/// aterm-gui SPECS.md native-preview-deadline (the may_tick clause): native_preview_may_tick(os, focused, recorded, overlay) = (recorded or (os and focused)) and not overlay. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn native_preview_may_tick_spec(
    has_os_window: bool,
    focused: bool,
    recorded: bool,
    overlay_open: bool,
) -> u8 {
    let result = (recorded || (has_os_window && focused)) && !overlay_open;
    let ok = result
        == (((has_os_window as u8 + focused as u8 == 2) as u8 + recorded as u8 >= 1) as u8
            + !overlay_open as u8
            == 2);
    let z = ok as u8;
    z - 1 + 1
}
