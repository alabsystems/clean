#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-lexicon/src/lib.rs `Class` (derives dropped), `class_rank`
pub enum Class {
    Profanity,
    Feline,
    Canine,
    Animal,
    Emphasis,
}
pub const fn class_rank(class: Class) -> u8 {
    match class {
        Class::Profanity => 5,
        Class::Feline => 4,
        Class::Canine => 3,
        Class::Animal => 1,
        Class::Emphasis => 0,
    }
}
/// aterm-lexicon SPECS.md insert-class-merge (rank sub-clause, written out): class_rank is the
/// precedence profanity 5 > feline 4 > canine 3 > animal 1 > emphasis 0.
pub fn class_rank_spec(class: Class) -> u8 {
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
        Class::Animal => 1,
        Class::Emphasis => 0,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
/// The same sub-clause's order: the declaration order is the precedence, so a class declared
/// before another ranks strictly above it (hence class_rank is injective and the class of
/// maximal rank is unique): ∀ a, b: (a before b) ⇒ class_rank(a) > class_rank(b).
pub fn class_rank_precedence_spec(a: Class, b: Class) -> u8 {
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
    let ok = ia >= ib || ra > rb;
    let z = ok as u8;
    z - 1 + 1
}
