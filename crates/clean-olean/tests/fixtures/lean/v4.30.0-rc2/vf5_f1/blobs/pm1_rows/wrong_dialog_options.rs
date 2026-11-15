#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_dialog_options.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const FOS_PICKFOLDERS: u32 = 0x0000_0020;
const FOS_FORCEFILESYSTEM: u32 = 0x0000_0040;
const FOS_ALLOWMULTISELECT: u32 = 0x0000_0200;
const FOS_PATHMUSTEXIST: u32 = 0x0000_0800;
const FOS_FILEMUSTEXIST: u32 = 0x0000_1000;
const FOS_NODEREFERENCELINKS: u32 = 0x0010_0000;

/// `dialog_options`'s clause passing FOS_PICKFOLDERS through: false at defaults 0x20.
pub fn dialog_options_wrong(defaults: u32) -> u8 {
    let result = (defaults | FOS_FORCEFILESYSTEM | FOS_FILEMUSTEXIST | FOS_PATHMUSTEXIST)
        & !(FOS_PICKFOLDERS | FOS_ALLOWMULTISELECT | FOS_NODEREFERENCELINKS);
    let ok = result & 0x1840 == 0x1840
        && result & 0x10_0200 == 0
        && result & !0x10_1A40 == defaults & !0x10_1A40;
    let z = ok as u8;
    z - 1 + 1
}
