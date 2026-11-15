#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-core/src/render.rs `COLOR_UNSET`, crates/aterm-gui/src/app_render.rs `present_band_bg`
mod aterm_core {
    pub mod render {
        pub const COLOR_UNSET: u32 = 0xFF00_0000;
    }
}

// `present_band_bg` (app_render.rs; the header above names it)
#[inline]
pub const fn present_band_bg(default_bg: u32, theme_bg: u32) -> u32 {
    if default_bg == aterm_core::render::COLOR_UNSET {
        theme_bg
    } else {
        default_bg
    }
}
/// aterm-gui SPECS.md render-live-bg-fallback (the first clause): for all d, t:
/// present_band_bg(d, t) = if d = COLOR_UNSET (0xFF00_0000) then t else d, spelled as the
/// two cases' disjunction.
pub fn present_band_bg_spec(default_bg: u32, theme_bg: u32) -> u8 {
    let result = if default_bg == aterm_core::render::COLOR_UNSET {
        theme_bg
    } else {
        default_bg
    };
    let ok = (default_bg == 0xFF00_0000 && result == theme_bg)
        || (default_bg != 0xFF00_0000 && result == default_bg);
    let z = ok as u8;
    z - 1 + 1
}
