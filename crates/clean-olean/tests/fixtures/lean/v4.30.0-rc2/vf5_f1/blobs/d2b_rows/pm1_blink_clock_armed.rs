#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-types/src/cursor.rs `CursorStyle` (derives, the serde `cfg_attr` and
// `#[default]` dropped), crates/aterm-gui/src/lib.rs `blink_clock_armed`
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
pub const fn blink_clock_armed(
    cursor_visible: bool,
    style: CursorStyle,
    rainbow_caret_policy: bool,
) -> bool {
    let rainbow_owns_caret = rainbow_caret_policy && matches!(style, CursorStyle::BlinkingBlock);
    cursor_visible
        && matches!(
            style,
            CursorStyle::BlinkingBlock | CursorStyle::BlinkingUnderline | CursorStyle::BlinkingBar
        )
        && !rainbow_owns_caret
}
/// aterm-gui SPECS.md blink-clock-armed: blink_clock_armed(v, s, r) = v ∧ s ∈ {BlinkingBlock,
/// BlinkingUnderline, BlinkingBar} ∧ ¬(r ∧ s = BlinkingBlock).
pub fn blink_clock_armed_spec(
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
        let block = match style {
            CursorStyle::BlinkingBlock => true,
            CursorStyle::SteadyBlock => false,
            CursorStyle::BlinkingUnderline => false,
            CursorStyle::SteadyUnderline => false,
            CursorStyle::BlinkingBar => false,
            CursorStyle::SteadyBar => false,
            CursorStyle::Hidden => false,
            CursorStyle::HollowBlock => false,
            CursorStyle::Bolt => false,
        };
        result == (cursor_visible && blinking && !(rainbow_caret_policy && block))
    };
    let z = ok as u8;
    z - 1 + 1
}
