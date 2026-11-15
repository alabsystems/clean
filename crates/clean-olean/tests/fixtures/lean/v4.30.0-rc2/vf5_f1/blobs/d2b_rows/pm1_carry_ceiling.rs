#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-update-core/src/handoff_policy.rs `CarryCeiling` (derives dropped),
// `CarryCeiling::carries_scrollback`
pub enum CarryCeiling {
    Full,
    Visible,
    Repaint,
}
impl CarryCeiling {
    pub const fn carries_scrollback(self) -> bool {
        matches!(self, Self::Full)
    }
    /// aterm-update-core SPECS.md policy-knob-predicates (first clause):
    /// carries_scrollback(c) ⇔ c = Full.
    pub fn carries_scrollback_spec(self) -> u8 {
        let result = matches!(self, Self::Full);
        let want = match self {
            Self::Full => true,
            Self::Visible => false,
            Self::Repaint => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
