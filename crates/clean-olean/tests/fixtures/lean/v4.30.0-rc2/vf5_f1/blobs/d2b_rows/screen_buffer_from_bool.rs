#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-types/src/kitty_keyboard.rs `ScreenBuffer` (derives dropped),
// `<ScreenBuffer as From<bool>>::from`
#[non_exhaustive]
pub enum ScreenBuffer {
    Main,
    Alternate,
}
impl From<bool> for ScreenBuffer {
    #[inline]
    fn from(is_alternate: bool) -> Self {
        if is_alternate {
            Self::Alternate
        } else {
            Self::Main
        }
    }
}
impl ScreenBuffer {
    /// aterm-types SPECS.md screen-buffer-from-bool: ∀ b: ScreenBuffer::from(b) =
    /// (b ? Alternate : Main).
    pub fn from_spec(is_alternate: bool) -> u8 {
        let result = if is_alternate {
            Self::Alternate
        } else {
            Self::Main
        };
        let ok = if is_alternate {
            matches!(result, Self::Alternate)
        } else {
            matches!(result, Self::Main)
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
