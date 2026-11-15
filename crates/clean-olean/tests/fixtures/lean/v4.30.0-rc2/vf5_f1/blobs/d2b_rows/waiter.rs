#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-messages/src/progress.rs `Waiter` (derives dropped), `Waiter::takes_row`,
// `Waiter::of`
pub enum Waiter {
    Person,
    Nobody,
}
impl Waiter {
    pub const fn takes_row(self, very_heavy: bool) -> bool {
        matches!(self, Self::Person) || very_heavy
    }
    pub const fn of(person: bool) -> Self {
        if person {
            Self::Person
        } else {
            Self::Nobody
        }
    }
    /// aterm-messages SPECS.md waiter-takes-row: ∀ w ∈ {Person, Nobody}, h: takes_row(w, h) ⇔
    /// (w = Person ∨ h).
    pub fn takes_row_spec(self, very_heavy: bool) -> u8 {
        let result = matches!(self, Self::Person) || very_heavy;
        let person = match self {
            Self::Person => true,
            Self::Nobody => false,
        };
        let ok = result == (person || very_heavy);
        let z = ok as u8;
        z - 1 + 1
    }
    /// aterm-messages SPECS.md waiter-takes-row: ∀ b: Waiter::of(b) = Person ⇔ b.
    pub fn of_spec(person: bool) -> u8 {
        let result = if person { Self::Person } else { Self::Nobody };
        let is_person = match result {
            Self::Person => true,
            Self::Nobody => false,
        };
        let ok = is_person == person;
        let z = ok as u8;
        z - 1 + 1
    }
}
