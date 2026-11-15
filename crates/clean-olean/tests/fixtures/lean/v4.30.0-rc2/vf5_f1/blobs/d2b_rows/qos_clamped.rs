#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-conformance/src/measure/starvation.rs `Qos` (derives dropped), `Qos::clamped`
pub enum Qos {
    UserInteractive,
    UserInitiated,
    Default,
    Utility,
    Background,
    Unspecified,
}
impl Qos {
    pub const fn clamped(self) -> bool {
        matches!(self, Self::Utility | Self::Background)
    }
    /// aterm-conformance SPECS.md qos-table (clause): clamped(q) ⇔ q ∈ {Utility, Background}.
    pub fn clamped_spec(self) -> u8 {
        let result = matches!(self, Self::Utility | Self::Background);
        let want = match self {
            Self::UserInteractive => false,
            Self::UserInitiated => false,
            Self::Default => false,
            Self::Utility => true,
            Self::Background => true,
            Self::Unspecified => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
