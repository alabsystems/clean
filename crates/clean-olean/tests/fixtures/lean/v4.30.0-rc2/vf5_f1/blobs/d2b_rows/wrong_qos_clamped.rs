#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `qos_clamped.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Qos {
    UserInteractive,
    UserInitiated,
    Default,
    Utility,
    Background,
    Unspecified,
}
impl Qos {
    /// `clamped`'s clause with `Background`'s entry flipped: false at `Background`.
    pub fn clamped_wrong(self) -> u8 {
        let result = matches!(self, Self::Utility | Self::Background);
        let want = match self {
            Self::UserInteractive => false,
            Self::UserInitiated => false,
            Self::Default => false,
            Self::Utility => true,
            Self::Background => false,
            Self::Unspecified => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
