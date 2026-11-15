#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-containment/src/consent.rs `ResetOffer` (derives dropped), `ResetOffer::shows_button`
pub enum ResetOffer {
    Offer,
    ExplainRebuild,
    HideNoTool,
    HideNoBundleId,
}
impl ResetOffer {
    pub const fn shows_button(self) -> bool {
        matches!(self, Self::Offer)
    }
    /// aterm-containment SPECS.md reset-offer (clause): shows_button(o) ⇔ o = Offer.
    pub fn shows_button_spec(self) -> u8 {
        let result = matches!(self, Self::Offer);
        let want = match self {
            Self::Offer => true,
            Self::ExplainRebuild => false,
            Self::HideNoTool => false,
            Self::HideNoBundleId => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
