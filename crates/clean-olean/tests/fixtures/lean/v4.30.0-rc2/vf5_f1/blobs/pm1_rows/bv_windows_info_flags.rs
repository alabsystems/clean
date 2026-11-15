#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/notify.rs `windows_info_flags`
pub const fn windows_info_flags(silent: bool, own_icon: bool) -> u32 {
    const NIIF_INFO: u32 = 0x1;
    const NIIF_USER: u32 = 0x4;
    const NIIF_NOSOUND: u32 = 0x10;
    const NIIF_LARGE_ICON: u32 = 0x20;
    const NIIF_RESPECT_QUIET_TIME: u32 = 0x80;
    let icon = if own_icon {
        NIIF_USER | NIIF_LARGE_ICON
    } else {
        NIIF_INFO
    };
    icon | NIIF_RESPECT_QUIET_TIME | if silent { NIIF_NOSOUND } else { 0 }
}
/// aterm-gui SPECS.md windows-info-flags: the flags are the SUM of the disjoint bits
/// (own ? 0x4 + 0x20 : 0x1) + 0x80 + (s ? 0x10 : 0), and the corollaries: NIIF_NOSOUND is set
/// iff s, flags & 0xF = (own ? NIIF_USER : NIIF_INFO), NIIF_LARGE_ICON is set iff own.
pub fn windows_info_flags_spec(silent: bool, own_icon: bool) -> u8 {
    const NIIF_INFO: u32 = 0x1;
    const NIIF_USER: u32 = 0x4;
    const NIIF_NOSOUND: u32 = 0x10;
    const NIIF_LARGE_ICON: u32 = 0x20;
    const NIIF_RESPECT_QUIET_TIME: u32 = 0x80;
    let icon = if own_icon {
        NIIF_USER | NIIF_LARGE_ICON
    } else {
        NIIF_INFO
    };
    let result = icon | NIIF_RESPECT_QUIET_TIME | if silent { NIIF_NOSOUND } else { 0 };
    let sum = (if own_icon { 0x24 } else { 0x1 }) + 0x80 + (if silent { 0x10 } else { 0 });
    let ok = result == sum
        && (result & 0x10 != 0) == silent
        && result & 0xF == (if own_icon { 0x4 } else { 0x1 })
        && (result & 0x20 != 0) == own_icon;
    let z = ok as u8;
    z - 1 + 1
}
