#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `dr_class_grant_stable.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum DrClass {
    Identity,
    Cdhash,
    Unsigned,
    Unknown,
}
impl DrClass {
    /// `grant_stable`'s clause with `Cdhash`'s entry flipped: false at `Cdhash`.
    pub fn grant_stable_wrong(self) -> u8 {
        let result = matches!(self, Self::Identity);
        let want = match self {
            Self::Identity => true,
            Self::Cdhash => true,
            Self::Unsigned => false,
            Self::Unknown => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
