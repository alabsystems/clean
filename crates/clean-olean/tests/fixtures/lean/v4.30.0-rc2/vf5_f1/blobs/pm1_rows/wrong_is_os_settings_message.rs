#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_is_os_settings_message.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const WM_SYSCOLORCHANGE: u32 = 0x0015;
const WM_SETTINGCHANGE: u32 = 0x001A;
const WM_THEMECHANGED: u32 = 0x031A;
const WM_DWMCOLORIZATIONCOLORCHANGED: u32 = 0x0320;

/// `is_os_settings_message`'s clause without WM_DWMCOLORIZATIONCOLORCHANGED: false at 0x320.
pub fn is_os_settings_message_wrong(msg: u32) -> u8 {
    let result = msg == WM_SETTINGCHANGE
        || msg == WM_SYSCOLORCHANGE
        || msg == WM_THEMECHANGED
        || msg == WM_DWMCOLORIZATIONCOLORCHANGED;
    let ok = result == ((msg == 0x15) as u8 + (msg == 0x1A) as u8 + (msg == 0x31A) as u8 == 1);
    let z = ok as u8;
    z - 1 + 1
}
