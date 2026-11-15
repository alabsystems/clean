#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-link/src/presence.rs `Due` (derives dropped), `Due::now`
pub enum Due {
    First,
    Changed,
    Unchanged,
    Capped,
}
impl Due {
    pub const fn now(self) -> bool {
        matches!(self, Due::First | Due::Changed)
    }
    /// aterm-link SPECS.md presence-slot-due (clause): Due::now() ⇔ due ∈ {First, Changed}.
    pub fn now_spec(self) -> u8 {
        let result = matches!(self, Due::First | Due::Changed);
        let want = match self {
            Self::First => true,
            Self::Changed => true,
            Self::Unchanged => false,
            Self::Capped => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
