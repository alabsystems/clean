#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `image_anchor_grant_unverifiable.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum ImageAnchor {
    Live,
    Displaced,
    Deleted,
    NotBundled,
    Unknown,
}
impl ImageAnchor {
    /// `grant_unverifiable`'s clause with `Deleted`'s entry flipped: false at `Deleted`.
    pub fn grant_unverifiable_wrong(self) -> u8 {
        let result = matches!(self, Self::Displaced | Self::Deleted);
        let want = match self {
            Self::Live => false,
            Self::Displaced => true,
            Self::Deleted => false,
            Self::NotBundled => false,
            Self::Unknown => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
