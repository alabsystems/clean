#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/file_picker_win.rs `FOS_*`, `dialog_options`
const FOS_PICKFOLDERS: u32 = 0x0000_0020;
const FOS_FORCEFILESYSTEM: u32 = 0x0000_0040;
const FOS_ALLOWMULTISELECT: u32 = 0x0000_0200;
const FOS_PATHMUSTEXIST: u32 = 0x0000_0800;
const FOS_FILEMUSTEXIST: u32 = 0x0000_1000;
const FOS_NODEREFERENCELINKS: u32 = 0x0010_0000;

/// The `FILEOPENDIALOGOPTIONS` this picker runs with, folded over the dialog's own defaults
/// (`GetOptions`) so the ones we have no opinion about survive.
pub fn dialog_options(defaults: u32) -> u32 {
    (defaults | FOS_FORCEFILESYSTEM | FOS_FILEMUSTEXIST | FOS_PATHMUSTEXIST)
        & !(FOS_PICKFOLDERS | FOS_ALLOWMULTISELECT | FOS_NODEREFERENCELINKS)
}
/// aterm-gui SPECS.md fpw-dialog-options: the three forced bits (0x1840) are set, the three
/// refused bits (0x10_0220) are clear, and every other bit is the default's: three masks by
/// value, not the body's expression.
pub fn dialog_options_spec(defaults: u32) -> u8 {
    let result = (defaults | FOS_FORCEFILESYSTEM | FOS_FILEMUSTEXIST | FOS_PATHMUSTEXIST)
        & !(FOS_PICKFOLDERS | FOS_ALLOWMULTISELECT | FOS_NODEREFERENCELINKS);
    let ok = result & 0x1840 == 0x1840
        && result & 0x10_0220 == 0
        && result & !0x10_1A60 == defaults & !0x10_1A60;
    let z = ok as u8;
    z - 1 + 1
}
