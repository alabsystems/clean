#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `reset_kind_takeable.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum ResetKind {
    Session,
    Weekly,
    Fable,
    Full,
}
impl ResetKind {
    /// `takeable`'s clause with `Fable`'s entry flipped: false at `Fable`.
    pub fn takeable_wrong(self) -> u8 {
        let result = !matches!(self, ResetKind::Fable);
        let want = match self {
            Self::Session => true,
            Self::Weekly => true,
            Self::Fable => true,
            Self::Full => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
