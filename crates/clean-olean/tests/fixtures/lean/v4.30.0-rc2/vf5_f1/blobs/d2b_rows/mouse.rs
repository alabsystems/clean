#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-types/src/mouse/types.rs `MouseButton`, `WheelDir` (derives dropped),
// `MouseButton::code`, `MouseButton::slot`, `WheelDir::code`
#[non_exhaustive]
pub enum MouseButton {
    Left,
    Middle,
    Right,
    Back,
    Forward,
}
impl MouseButton {
    pub const fn code(self) -> u8 {
        match self {
            MouseButton::Left => 0,
            MouseButton::Middle => 1,
            MouseButton::Right => 2,
            MouseButton::Back => 128,
            MouseButton::Forward => 129,
        }
    }
    pub const fn slot(self) -> u8 {
        match self {
            MouseButton::Left => 0,
            MouseButton::Middle => 1,
            MouseButton::Right => 2,
            MouseButton::Back => 3,
            MouseButton::Forward => 4,
        }
    }
    /// aterm-types SPECS.md mouse-button-codes: code is xterm's Cb base for button n: n − 1
    /// for n ∈ 1..=3 (Left 0, Middle 1, Right 2) and 128 + (n − 8) for n ∈ {8, 9} (Back 128,
    /// Forward 129); no button code is 3 (the legacy release code).
    pub fn code_spec(self) -> u8 {
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
            MouseButton::Forward => 9,
        };
        let want = if n <= 3 { n - 1 } else { 128 + (n - 8) };
        let ok = result == want && result != 3;
        let z = ok as u8;
        z - 1 + 1
    }
    /// aterm-types SPECS.md mouse-button-slot-injective: slot is a bijection from the five
    /// variants onto 0..=4 (Left 0, Middle 1, Right 2, Back 3, Forward 4): slot(b) is b's
    /// declaration index `b as u8` (B3 binds it to rustc's), so it is injective, and ≤ 4.
    pub fn slot_spec(self) -> u8 {
        let result = match self {
            MouseButton::Left => 0,
            MouseButton::Middle => 1,
            MouseButton::Right => 2,
            MouseButton::Back => 3,
            MouseButton::Forward => 4,
        };
        let ok = result == self as u8 && result <= 4;
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
    pub const fn code(self) -> u8 {
        match self {
            WheelDir::Up => 64,
            WheelDir::Down => 65,
            WheelDir::Left => 66,
            WheelDir::Right => 67,
        }
    }
    /// aterm-types SPECS.md mouse-button-codes: wheel n ∈ 4..=7 gives 64 + (n − 4): Up 64,
    /// Down 65, Left 66, Right 67.
    pub fn code_spec(self) -> u8 {
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
        let ok = result == 64 + (n - 4);
        let z = ok as u8;
        z - 1 + 1
    }
}
