#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `waiter.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Waiter {
    Person,
    Nobody,
}
impl Waiter {
    /// `takes_row`'s clause without the `∨ h`: false at `(Nobody, true)`.
    pub fn takes_row_wrong(self, very_heavy: bool) -> u8 {
        let result = matches!(self, Self::Person) || very_heavy;
        let person = match self {
            Self::Person => true,
            Self::Nobody => false,
        };
        let ok = result == person;
        let z = ok as u8;
        z - 1 + 1
    }
    /// `of`'s clause negated (of(b) = Person ⇔ ¬b): false at `true`.
    pub fn of_wrong(person: bool) -> u8 {
        let result = if person { Self::Person } else { Self::Nobody };
        let is_person = match result {
            Self::Person => true,
            Self::Nobody => false,
        };
        let ok = is_person == !person;
        let z = ok as u8;
        z - 1 + 1
    }
}
