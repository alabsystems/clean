#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `phase_program.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

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
    /// `supervisable`'s clause with Codex in the set: false at `Codex`.
    pub fn supervisable_wrong(self) -> u8 {
        let result = match self {
            Program::Claude | Program::Agy | Program::Muse => true,
            Program::Codex | Program::Grok | Program::Kimi | Program::Generic => false,
        };
        let want = match self {
            Program::Claude => true,
            Program::Codex => true,
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
    /// `harness_table`'s clause with Codex left out (harness_table ⇔ supervisable): false at
    /// `Codex`.
    pub fn harness_table_wrong(self) -> u8 {
        let result = match self {
            Program::Claude | Program::Codex | Program::Agy | Program::Muse => true,
            Program::Grok | Program::Kimi | Program::Generic => false,
        };
        let supervisable = match self {
            Program::Claude | Program::Agy | Program::Muse => true,
            Program::Codex | Program::Grok | Program::Kimi | Program::Generic => false,
        };
        let ok = result == supervisable;
        let z = ok as u8;
        z - 1 + 1
    }
}
