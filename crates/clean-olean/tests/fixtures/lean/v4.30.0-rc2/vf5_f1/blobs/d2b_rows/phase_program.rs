#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-phase/src/reader.rs `Program` (derives dropped), `Program::supervisable`,
// `Program::harness_table`
pub enum Program {
    Claude,
    Codex,
    Agy,
    Muse,
    Grok,
    Kimi,
    Generic,
}
impl Program {
    pub const fn supervisable(self) -> bool {
        match self {
            Program::Claude | Program::Agy | Program::Muse => true,
            Program::Codex | Program::Grok | Program::Kimi | Program::Generic => false,
        }
    }
    pub const fn harness_table(self) -> bool {
        match self {
            Program::Claude | Program::Codex | Program::Agy | Program::Muse => true,
            Program::Grok | Program::Kimi | Program::Generic => false,
        }
    }
    /// aterm-phase SPECS.md identify-dispatch (clause): supervisable(p) ⇔ p ∈ {Claude, Agy, Muse}.
    pub fn supervisable_spec(self) -> u8 {
        let result = match self {
            Program::Claude | Program::Agy | Program::Muse => true,
            Program::Codex | Program::Grok | Program::Kimi | Program::Generic => false,
        };
        let want = match self {
            Program::Claude => true,
            Program::Codex => false,
            Program::Agy => true,
            Program::Muse => true,
            Program::Grok => false,
            Program::Kimi => false,
            Program::Generic => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
    /// aterm-phase SPECS.md identify-dispatch (clause): harness_table(p) ⇔ supervisable(p) ∨
    /// p = Codex, both bodies verbatim (the clause cites supervisable; no call is made).
    pub fn harness_table_spec(self) -> u8 {
        let result = match self {
            Program::Claude | Program::Codex | Program::Agy | Program::Muse => true,
            Program::Grok | Program::Kimi | Program::Generic => false,
        };
        let supervisable = match self {
            Program::Claude | Program::Agy | Program::Muse => true,
            Program::Codex | Program::Grok | Program::Kimi | Program::Generic => false,
        };
        let ok = result == (supervisable || matches!(self, Program::Codex));
        let z = ok as u8;
        z - 1 + 1
    }
}
