#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-types/src/keyboard/key_types.rs `KeyEventType` (derives dropped, and its `#[default]` with them), `KeyEventType::kitty_value`
#[non_exhaustive]
pub enum KeyEventType {
    Press,
    Repeat,
    Release,
}
impl KeyEventType {
    pub const fn kitty_value(self) -> u8 {
        match self {
            KeyEventType::Press => 1,
            KeyEventType::Repeat => 2,
            KeyEventType::Release => 3,
        }
    }
    /// aterm-types SPECS.md kb-wire-values (kitty_value part): Press 1, Repeat 2, Release 3.
    pub fn kitty_value_spec(self) -> u8 {
        let result: u8 = match self {
            KeyEventType::Press => 1,
            KeyEventType::Repeat => 2,
            KeyEventType::Release => 3,
        };
        let want: u8 = match self {
            Self::Press => 1,
            Self::Repeat => 2,
            Self::Release => 3,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
