#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_nests_inside_aterm.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `nests_inside_aterm`'s clause without the tty: false at (true, false, true, false).
pub fn nests_inside_aterm_wrong(
    bare: bool,
    force_session: bool,
    aterm_child: bool,
    stdin_tty: bool,
) -> u8 {
    let result = bare && !force_session && aterm_child && stdin_tty;
    let ok = result == (bare as u8 + !force_session as u8 + aterm_child as u8 == 3);
    let z = ok as u8;
    z - 1 + 1
}
