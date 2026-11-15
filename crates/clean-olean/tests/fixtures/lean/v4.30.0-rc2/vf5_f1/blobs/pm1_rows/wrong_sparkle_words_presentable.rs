#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_sparkle_words_presentable.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `sparkle_words_presentable`'s clause ignoring suspension: false at (true, true).
pub fn sparkle_words_presentable_wrong(word_focus: bool, suspended: bool) -> u8 {
    let result = word_focus && !suspended;
    let ok = result == (word_focus as u8 == 1);
    let z = ok as u8;
    z - 1 + 1
}
