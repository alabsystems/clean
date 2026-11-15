#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-types/src/cursor.rs `CursorStyle` (derives, the serde `cfg_attr` and
// its `#[default]` dropped), crates/aterm-render/src/lib.rs `cursor_shown`
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
pub const fn cursor_shown(style: CursorStyle, blink_phase: bool) -> bool {
    match style {
        CursorStyle::Hidden => false,
        CursorStyle::BlinkingBlock | CursorStyle::BlinkingUnderline | CursorStyle::BlinkingBar => {
            blink_phase
        }
        _ => true,
    }
}
/// aterm-render SPECS.md cursor-paint-denotation, the blink-gate conjunct: cursor_shown(s, b)
/// = false if s = Hidden, b if s is blinking (BlinkingBlock, BlinkingUnderline,
/// BlinkingBar), else true (the style is steady).
pub fn cursor_shown_spec(style: CursorStyle, blink_phase: bool) -> u8 {
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
        CursorStyle::HollowBlock => true,
        CursorStyle::Bolt => true,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
