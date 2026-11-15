#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/aterm-uds/src/spawn.rs `DETACHED_PROCESS`, `CREATE_NEW_CONSOLE`,
// `CREATE_NO_WINDOW`, `CONSOLE_BITS`, `Console` (its derives dropped: a derived `Clone`
// reads through a pointer, outside F1), `creation_flags`
pub const DETACHED_PROCESS: u32 = 0x0000_0008;
pub const CREATE_NEW_CONSOLE: u32 = 0x0000_0010;
pub const CREATE_NO_WINDOW: u32 = 0x0800_0000;
pub const CONSOLE_BITS: u32 = DETACHED_PROCESS | CREATE_NEW_CONSOLE | CREATE_NO_WINDOW;
pub enum Console {
    Quiet,
    Detached,
}
pub const fn creation_flags(console: Console, extra: u32, have_console: bool) -> u32 {
    let extra = extra & !CONSOLE_BITS;
    match console {
        Console::Quiet if have_console => extra,
        Console::Quiet => extra | CREATE_NO_WINDOW,
        Console::Detached => extra | DETACHED_PROCESS,
    }
}
/// aterm-uds SPECS.md creation-flags-rule: the non-console bits are `extra`'s, and the
/// console bits are k(c, have) (k(Quiet, true) = 0, k(Quiet, false) = CREATE_NO_WINDOW,
/// k(Detached, _) = DETACHED_PROCESS); corollary: at most one console bit is set.
pub fn creation_flags_spec(console: Console, extra: u32, have_console: bool) -> u8 {
    let quiet = match console {
        Console::Quiet => true,
        Console::Detached => false,
    };
    let e = extra & !CONSOLE_BITS;
    let result = match console {
        Console::Quiet if have_console => e,
        Console::Quiet => e | CREATE_NO_WINDOW,
        Console::Detached => e | DETACHED_PROCESS,
    };
    let k = if quiet {
        if have_console {
            0
        } else {
            CREATE_NO_WINDOW
        }
    } else {
        DETACHED_PROCESS
    };
    let c = result & CONSOLE_BITS;
    let ok = result & !CONSOLE_BITS == extra & !CONSOLE_BITS
        && c == k
        && (c == 0 || c == DETACHED_PROCESS || c == CREATE_NEW_CONSOLE || c == CREATE_NO_WINDOW);
    let z = ok as u8;
    z - 1 + 1
}
