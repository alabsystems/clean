#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-agent/src/harness/lights.rs `Mode` (derives dropped), `Mode::is_expected`
pub enum Mode {
    Bypass,
    Auto,
    AcceptEdits,
    DontAsk,
    Plan,
    Manual,
}
impl Mode {
    pub const fn is_expected(self) -> bool {
        matches!(self, Mode::Bypass | Mode::Auto)
    }
    /// aterm-agent SPECS.md lights-mode-pill-table (clause): is_expected(m) ⇔ m ∈ {Bypass, Auto}.
    pub fn is_expected_spec(self) -> u8 {
        let result = matches!(self, Mode::Bypass | Mode::Auto);
        let want = match self {
            Self::Bypass => true,
            Self::Auto => true,
            Self::AcceptEdits => false,
            Self::DontAsk => false,
            Self::Plan => false,
            Self::Manual => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
