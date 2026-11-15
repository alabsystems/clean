#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `cursor_shown.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

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
/// `cursor_shown`'s gate with HollowBlock read as blinking: false at `(HollowBlock, false)`.
pub fn cursor_shown_wrong(style: CursorStyle, blink_phase: bool) -> u8 {
    let result = match style {
        CursorStyle::Hidden => false,
        CursorStyle::BlinkingBlock | CursorStyle::BlinkingUnderline | CursorStyle::BlinkingBar => {
            blink_phase
        }
        _ => true,
    };
    let want = match style {
        CursorStyle::BlinkingBlock => blink_phase,
        CursorStyle::SteadyBlock => true,
        CursorStyle::BlinkingUnderline => blink_phase,
        CursorStyle::SteadyUnderline => true,
        CursorStyle::BlinkingBar => blink_phase,
        CursorStyle::SteadyBar => true,
        CursorStyle::Hidden => false,
        CursorStyle::HollowBlock => blink_phase,
        CursorStyle::Bolt => true,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
