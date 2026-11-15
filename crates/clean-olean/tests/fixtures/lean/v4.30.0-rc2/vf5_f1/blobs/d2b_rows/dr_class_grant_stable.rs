#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-containment/src/consent.rs `DrClass` (derives dropped, and its `#[default]` with them), `DrClass::grant_stable`
pub enum DrClass {
    Identity,
    Cdhash,
    Unsigned,
    Unknown,
}
impl DrClass {
    pub const fn grant_stable(self) -> bool {
        matches!(self, Self::Identity)
    }
    /// aterm-containment SPECS.md classify-dr (clause): grant_stable(c) ⇔ c = Identity.
    pub fn grant_stable_spec(self) -> u8 {
        let result = matches!(self, Self::Identity);
        let want = match self {
            Self::Identity => true,
            Self::Cdhash => false,
            Self::Unsigned => false,
            Self::Unknown => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
