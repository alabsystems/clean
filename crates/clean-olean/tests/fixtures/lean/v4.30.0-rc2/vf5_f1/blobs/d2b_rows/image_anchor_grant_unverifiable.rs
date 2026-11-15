#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-containment/src/consent.rs `ImageAnchor` (derives dropped), `ImageAnchor::grant_unverifiable`
pub enum ImageAnchor {
    Live,
    Displaced,
    Deleted,
    NotBundled,
    Unknown,
}
impl ImageAnchor {
    pub const fn grant_unverifiable(self) -> bool {
        matches!(self, Self::Displaced | Self::Deleted)
    }
    /// aterm-containment SPECS.md image-anchor (clause): grant_unverifiable(a) ⇔
    /// a ∈ {Displaced, Deleted}.
    pub fn grant_unverifiable_spec(self) -> u8 {
        let result = matches!(self, Self::Displaced | Self::Deleted);
        let want = match self {
            Self::Live => false,
            Self::Displaced => true,
            Self::Deleted => true,
            Self::NotBundled => false,
            Self::Unknown => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
