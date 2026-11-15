#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/atpkg/src/extract.rs `safe_mode`
pub const fn safe_mode(entry_mode: u32, is_dir: bool) -> u32 {
    if is_dir || entry_mode & 0o111 != 0 {
        0o755
    } else {
        0o644
    }
}
/// atpkg SPECS.md extract-safe-mode: safe_mode(m, d) = 0o755 if d ∨ (m & 0o111 ≠ 0), else
/// 0o644, the three execute bits read arithmetically; and never setuid/setgid/sticky or
/// group/other-writable (`r & 0o7022 == 0`).
pub fn safe_mode_spec(entry_mode: u32, is_dir: bool) -> u8 {
    let result = if is_dir || entry_mode & 0o111 != 0 {
        0o755
    } else {
        0o644
    };
    let x = entry_mode % 2 == 1 || (entry_mode / 8) % 2 == 1 || (entry_mode / 64) % 2 == 1;
    let ok = result == (if is_dir || x { 0o755 } else { 0o644 }) && result & 0o7022 == 0;
    let z = ok as u8;
    z - 1 + 1
}
