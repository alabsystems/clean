#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `presence_due_now.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Due {
    First,
    Changed,
    Unchanged,
    Capped,
}
impl Due {
    /// `now`'s clause with `Capped`'s entry flipped: false at `Capped`.
    pub fn now_wrong(self) -> u8 {
        let result = matches!(self, Due::First | Due::Changed);
        let want = match self {
            Self::First => true,
            Self::Changed => true,
            Self::Unchanged => false,
            Self::Capped => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
