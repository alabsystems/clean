#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_bar_title_attention.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `bar_title_attention`'s clause asking for realized too: false at (true, false, false).
pub fn bar_title_attention_wrong(staged_present: bool, on_hold: bool, _realized: bool) -> u8 {
    let result = staged_present && !on_hold;
    let ok = result == (staged_present as u8 + !on_hold as u8 + _realized as u8 == 3);
    let z = ok as u8;
    z - 1 + 1
}
