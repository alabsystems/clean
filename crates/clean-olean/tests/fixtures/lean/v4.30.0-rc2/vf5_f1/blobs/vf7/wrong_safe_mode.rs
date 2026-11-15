#![allow(dead_code)]
// A VF7 negative control (Clean docs/DECISIONS.md R206): the harness of `bv_safe_mode.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

/// `safe_mode`'s clause with the owner execute bit (`0o100`) dropped: false at mode 64.
pub fn safe_mode_wrong(entry_mode: u32, is_dir: bool) -> u8 {
    let result = if is_dir || entry_mode & 0o111 != 0 {
        0o755
    } else {
        0o644
    };
    let x = entry_mode % 2 == 1 || (entry_mode / 8) % 2 == 1;
    let ok = result == (if is_dir || x { 0o755 } else { 0o644 }) && result & 0o7022 == 0;
    let z = ok as u8;
    z - 1 + 1
}
