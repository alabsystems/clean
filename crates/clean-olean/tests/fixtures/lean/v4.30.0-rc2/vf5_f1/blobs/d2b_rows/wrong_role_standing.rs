#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `role_standing.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Role {
    Once,
    Session,
    Persist,
    ModeSwitch,
    Deny,
    Exit,
    Trust,
    AutoResume,
    Answer,
    Other,
}
impl Role {
    /// `standing`'s clause with `Once`'s entry flipped: false at `Once`.
    pub fn standing_wrong(self) -> u8 {
        let result = matches!(self, Role::Session | Role::Persist | Role::ModeSwitch);
        let want = match self {
            Self::Once => true,
            Self::Session => true,
            Self::Persist => true,
            Self::ModeSwitch => true,
            Self::Deny => false,
            Self::Exit => false,
            Self::Trust => false,
            Self::AutoResume => false,
            Self::Answer => false,
            Self::Other => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
