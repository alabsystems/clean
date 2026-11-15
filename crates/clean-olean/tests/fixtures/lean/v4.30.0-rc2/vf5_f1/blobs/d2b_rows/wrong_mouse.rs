#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `mouse.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

#[non_exhaustive]
pub enum MouseButton {
    Left,
    Middle,
    Right,
    Back,
    Forward,
}
impl MouseButton {
    /// `code`'s clause with Forward's button number 10: false at `Forward`.
    pub fn code_wrong(self) -> u8 {
        let result = match self {
            MouseButton::Left => 0,
            MouseButton::Middle => 1,
            MouseButton::Right => 2,
            MouseButton::Back => 128,
            MouseButton::Forward => 129,
        };
        let n: u8 = match self {
            MouseButton::Left => 1,
            MouseButton::Middle => 2,
            MouseButton::Right => 3,
            MouseButton::Back => 8,
            MouseButton::Forward => 10,
        };
        let want = if n <= 3 { n - 1 } else { 128 + (n - 8) };
        let ok = result == want && result != 3;
        let z = ok as u8;
        z - 1 + 1
    }
    /// `slot`'s clause with the image bound `≤ 3`: false at `Forward`.
    pub fn slot_wrong(self) -> u8 {
        let result = match self {
            MouseButton::Left => 0,
            MouseButton::Middle => 1,
            MouseButton::Right => 2,
            MouseButton::Back => 3,
            MouseButton::Forward => 4,
        };
        let ok = result == self as u8 && result <= 3;
        let z = ok as u8;
        z - 1 + 1
    }
}
pub enum WheelDir {
    Up,
    Down,
    Left,
    Right,
}
impl WheelDir {
    /// `WheelDir::code`'s clause with 64 + (n − 4) read as 63 + (n − 4): false at `Up`.
    pub fn code_wrong(self) -> u8 {
        let result = match self {
            WheelDir::Up => 64,
            WheelDir::Down => 65,
            WheelDir::Left => 66,
            WheelDir::Right => 67,
        };
        let n: u8 = match self {
            WheelDir::Up => 4,
            WheelDir::Down => 5,
            WheelDir::Left => 6,
            WheelDir::Right => 7,
        };
        let ok = result == 63 + (n - 4);
        let z = ok as u8;
        z - 1 + 1
    }
}
