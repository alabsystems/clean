#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_windows_info_flags.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `windows_info_flags`'s clause with NIIF_INFO kept beside NIIF_USER: false at (false, true).
pub fn windows_info_flags_wrong(silent: bool, own_icon: bool) -> u8 {
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
    let ok = (result & 0x10 != 0) == silent
        && result & 0xF == (if own_icon { 0x5 } else { 0x1 })
        && (result & 0x20 != 0) == own_icon;
    let z = ok as u8;
    z - 1 + 1
}
