#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `key_event_kitty_value.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

#[non_exhaustive]
pub enum KeyEventType {
    Press,
    Repeat,
    Release,
}
impl KeyEventType {
    /// `kitty_value`'s clause with `Release`'s value off by one: false at `Release`.
    pub fn kitty_value_wrong(self) -> u8 {
        let result: u8 = match self {
            KeyEventType::Press => 1,
            KeyEventType::Repeat => 2,
            KeyEventType::Release => 3,
        };
        let want: u8 = match self {
            Self::Press => 1,
            Self::Repeat => 2,
            Self::Release => 4,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
