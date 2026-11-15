#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of
// `pm1_blink_clock_armed.rs`, its body the same verbatim aterm body (`f306a395db`), with its
// SPECS.md clause made FALSE for some input, so the harness panics there and no sound calculus
// certifies it: the row's harness form is not vacuous.

#[non_exhaustive]
#[repr(u8)]
pub enum CursorStyle {
    BlinkingBlock = 1,
    SteadyBlock = 2,
    BlinkingUnderline = 3,
    SteadyUnderline = 4,
    BlinkingBar = 5,
    SteadyBar = 6,
    Hidden = 7,
    HollowBlock = 8,
    Bolt = 9,
}
/// The clause without `¬(r ∧ s = BlinkingBlock)`: false at (true, BlinkingBlock, true).
pub fn blink_clock_armed_wrong(
    cursor_visible: bool,
    style: CursorStyle,
    rainbow_caret_policy: bool,
) -> u8 {
    let result = {
        let rainbow_owns_caret =
            rainbow_caret_policy && matches!(style, CursorStyle::BlinkingBlock);
        cursor_visible
            && matches!(
                style,
                CursorStyle::BlinkingBlock
                    | CursorStyle::BlinkingUnderline
                    | CursorStyle::BlinkingBar
            )
            && !rainbow_owns_caret
    };
    let ok = {
        let blinking = match style {
            CursorStyle::BlinkingBlock => true,
            CursorStyle::SteadyBlock => false,
            CursorStyle::BlinkingUnderline => true,
            CursorStyle::SteadyUnderline => false,
            CursorStyle::BlinkingBar => true,
            CursorStyle::SteadyBar => false,
            CursorStyle::Hidden => false,
            CursorStyle::HollowBlock => false,
            CursorStyle::Bolt => false,
        };
        result == (cursor_visible && blinking)
    };
    let z = ok as u8;
    z - 1 + 1
}
