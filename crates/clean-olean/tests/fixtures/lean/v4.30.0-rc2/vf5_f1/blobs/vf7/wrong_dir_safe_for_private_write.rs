#![allow(dead_code)]
// A VF7 negative control (Clean docs/DECISIONS.md R206): the harness of `bv_dir_safe_for_private_write.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

/// `dir_safe_for_private_write`'s clause with the other-write bit read as `/ 4` for `/ 2`
/// (`0o004`, other-read, for `0o002`): false at mode 2.
pub fn dir_safe_for_private_write_wrong(uid: u32, owner_uid: u32, mode: u32) -> u8 {
    let result = owner_uid == uid && mode & 0o022 == 0;
    let ok = result == (owner_uid == uid && (mode / 4) % 2 == 0 && (mode / 16) % 2 == 0);
    let z = ok as u8;
    z - 1 + 1
}
