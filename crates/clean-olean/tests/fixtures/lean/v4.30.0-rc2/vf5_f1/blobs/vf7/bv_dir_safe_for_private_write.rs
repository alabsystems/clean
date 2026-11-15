#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/aterm-types/src/fs_restricted.rs `dir_safe_for_private_write`
pub const fn dir_safe_for_private_write(uid: u32, owner_uid: u32, mode: u32) -> bool {
    owner_uid == uid && mode & 0o022 == 0
}
/// aterm-types SPECS.md fs-dir-safe-predicate: result ⇔ owner = uid ∧ mode & 0o022 = 0,
/// the two write bits (group 0o020, other 0o002) read arithmetically.
pub fn dir_safe_for_private_write_spec(uid: u32, owner_uid: u32, mode: u32) -> u8 {
    let result = owner_uid == uid && mode & 0o022 == 0;
    let ok = result == (owner_uid == uid && (mode / 2) % 2 == 0 && (mode / 16) % 2 == 0);
    let z = ok as u8;
    z - 1 + 1
}
