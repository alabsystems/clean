#![allow(dead_code)]
// A VF7 negative control (Clean docs/DECISIONS.md R206): the harness of `bv_creation_flags.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub const DETACHED_PROCESS: u32 = 0x0000_0008;
pub const CREATE_NEW_CONSOLE: u32 = 0x0000_0010;
pub const CREATE_NO_WINDOW: u32 = 0x0800_0000;
pub const CONSOLE_BITS: u32 = DETACHED_PROCESS | CREATE_NEW_CONSOLE | CREATE_NO_WINDOW;
pub enum Console {
    Quiet,
    Detached,
}
/// `creation_flags`'s clause with k(Quiet, false) = DETACHED_PROCESS for CREATE_NO_WINDOW:
/// false at `(Quiet, 0, false)`. (`creation_flags` has no obligation to certify, so its
/// certificate control says nothing about the program; this one does.)
pub fn creation_flags_wrong(console: Console, extra: u32, have_console: bool) -> u8 {
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
            DETACHED_PROCESS
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
