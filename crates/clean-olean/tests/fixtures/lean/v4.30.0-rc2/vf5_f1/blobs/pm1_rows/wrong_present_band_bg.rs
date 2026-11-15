#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_present_band_bg.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

mod aterm_core {
    pub mod render {
        pub const COLOR_UNSET: u32 = 0xFF00_0000;
    }
}

/// `present_band_bg`'s clause reading every 0xFF-alpha colour as unset: false at (0xFF00_0001, 0).
pub fn present_band_bg_wrong(default_bg: u32, theme_bg: u32) -> u8 {
    let result = if default_bg == aterm_core::render::COLOR_UNSET {
        theme_bg
    } else {
        default_bg
    };
    let ok = (default_bg >= 0xFF00_0000 && result == theme_bg)
        || (default_bg < 0xFF00_0000 && result == default_bg);
    let z = ok as u8;
    z - 1 + 1
}
