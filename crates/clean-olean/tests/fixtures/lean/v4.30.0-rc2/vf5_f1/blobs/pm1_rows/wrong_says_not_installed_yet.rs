#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_says_not_installed_yet.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `says_not_installed_yet`'s clause ignoring the window pass: false at (true, true).
pub fn says_not_installed_yet_wrong(store_empty: bool, window_pass: bool) -> u8 {
    let result = store_empty && !window_pass;
    let ok = result == store_empty;
    let z = ok as u8;
    z - 1 + 1
}
