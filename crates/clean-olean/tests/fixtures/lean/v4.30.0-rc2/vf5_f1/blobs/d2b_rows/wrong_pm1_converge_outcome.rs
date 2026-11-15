#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of
// `pm1_converge_outcome.rs`, its body the same verbatim aterm body (`f306a395db`), with its
// SPECS.md clause made FALSE for some input, so the harness panics there and no sound calculus
// certifies it: the row's harness form is not vacuous.

pub enum Outcome {
    Ok,
    Planned,
    Changed,
    Person,
    Blocked,
    NotApplicable,
    Deferred,
    Unknown,
    Failed,
}
impl Outcome {
    /// `is_failure`'s clause with `Deferred`'s entry flipped: false at `Deferred`.
    pub fn is_failure_wrong(self) -> u8 {
        let result = matches!(self, Self::Failed | Self::Unknown);
        let want = match self {
            Self::Ok => false,
            Self::Planned => false,
            Self::Changed => false,
            Self::Person => false,
            Self::Blocked => false,
            Self::NotApplicable => false,
            Self::Deferred => true,
            Self::Unknown => true,
            Self::Failed => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
