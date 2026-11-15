#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-phase/src/prompt.rs `Role` (derives dropped), `Role::standing`
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
    pub const fn standing(self) -> bool {
        matches!(self, Role::Session | Role::Persist | Role::ModeSwitch)
    }
    /// aterm-phase SPECS.md option-role-soundness (the `Role::standing` sub-clause):
    /// standing(r) ⇔ r ∈ {Session, Persist, ModeSwitch}.
    pub fn standing_spec(self) -> u8 {
        let result = matches!(self, Role::Session | Role::Persist | Role::ModeSwitch);
        let want = match self {
            Self::Once => false,
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
