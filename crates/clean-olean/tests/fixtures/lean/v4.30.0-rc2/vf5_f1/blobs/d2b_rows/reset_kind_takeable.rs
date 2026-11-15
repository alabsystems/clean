#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-phase/src/reset.rs `ResetKind` (derives dropped), `ResetKind::takeable`
pub enum ResetKind {
    Session,
    Weekly,
    Fable,
    Full,
}
impl ResetKind {
    pub const fn takeable(self) -> bool {
        !matches!(self, ResetKind::Fable)
    }
    /// aterm-phase SPECS.md reset-row-grammar (clause): takeable(K) ⇔ K ≠ Fable.
    pub fn takeable_spec(self) -> u8 {
        let result = !matches!(self, ResetKind::Fable);
        let want = match self {
            Self::Session => true,
            Self::Weekly => true,
            Self::Fable => false,
            Self::Full => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
