#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_class_rank.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum Class {
    Profanity,
    Feline,
    Canine,
    Animal,
    Emphasis,
}
/// The table with Animal ranked 2: false at Animal.
pub fn class_rank_wrong(class: Class) -> u8 {
    let result = match class {
        Class::Profanity => 5,
        Class::Feline => 4,
        Class::Canine => 3,
        Class::Animal => 1,
        Class::Emphasis => 0,
    };
    let want: u8 = match class {
        Class::Profanity => 5,
        Class::Feline => 4,
        Class::Canine => 3,
        Class::Animal => 2,
        Class::Emphasis => 0,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
/// The precedence reversed: false at (Profanity, Feline).
pub fn class_rank_precedence_wrong(a: Class, b: Class) -> u8 {
    let ia: u8 = match a {
        Class::Profanity => 0,
        Class::Feline => 1,
        Class::Canine => 2,
        Class::Animal => 3,
        Class::Emphasis => 4,
    };
    let ib: u8 = match b {
        Class::Profanity => 0,
        Class::Feline => 1,
        Class::Canine => 2,
        Class::Animal => 3,
        Class::Emphasis => 4,
    };
    let ra = match a {
        Class::Profanity => 5,
        Class::Feline => 4,
        Class::Canine => 3,
        Class::Animal => 1,
        Class::Emphasis => 0,
    };
    let rb = match b {
        Class::Profanity => 5,
        Class::Feline => 4,
        Class::Canine => 3,
        Class::Animal => 1,
        Class::Emphasis => 0,
    };
    let ok = ia >= ib || ra < rb;
    let z = ok as u8;
    z - 1 + 1
}
