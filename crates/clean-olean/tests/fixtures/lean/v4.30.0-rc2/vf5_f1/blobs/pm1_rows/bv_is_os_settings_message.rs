#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/platform_win.rs `WM_*`, `is_os_settings_message`
const WM_SYSCOLORCHANGE: u32 = 0x0015;
const WM_SETTINGCHANGE: u32 = 0x001A;
const WM_THEMECHANGED: u32 = 0x031A;
const WM_DWMCOLORIZATIONCOLORCHANGED: u32 = 0x0320;

pub fn is_os_settings_message(msg: u32) -> bool {
    matches!(
        msg,
        WM_SETTINGCHANGE | WM_SYSCOLORCHANGE | WM_THEMECHANGED | WM_DWMCOLORIZATIONCOLORCHANGED
    )
}
/// aterm-gui SPECS.md os-settings-watch (the first clause): is_os_settings_message(m) iff m
/// is one of 0x1A, 0x15, 0x31A, 0x320, spelled as exactly one of four equalities holding. The
/// harness's copy writes the `matches!` as the `||` chain it is (the same function on every
/// `u32`): F1's `switch` keeps no `m != c` on its default arm.
pub fn is_os_settings_message_spec(msg: u32) -> u8 {
    let result = msg == WM_SETTINGCHANGE
        || msg == WM_SYSCOLORCHANGE
        || msg == WM_THEMECHANGED
        || msg == WM_DWMCOLORIZATIONCOLORCHANGED;
    let ok = result
        == ((msg == 0x15) as u8
            + (msg == 0x1A) as u8
            + (msg == 0x31A) as u8
            + (msg == 0x320) as u8
            == 1);
    let z = ok as u8;
    z - 1 + 1
}
