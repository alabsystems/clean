#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `reset_offer_shows_button.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum ResetOffer {
    Offer,
    ExplainRebuild,
    HideNoTool,
    HideNoBundleId,
}
impl ResetOffer {
    /// `shows_button`'s clause with `Offer`'s entry flipped: false at `Offer`.
    pub fn shows_button_wrong(self) -> u8 {
        let result = matches!(self, Self::Offer);
        let want = match self {
            Self::Offer => false,
            Self::ExplainRebuild => false,
            Self::HideNoTool => false,
            Self::HideNoBundleId => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
