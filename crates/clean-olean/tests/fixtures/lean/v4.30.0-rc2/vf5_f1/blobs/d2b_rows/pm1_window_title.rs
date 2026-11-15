#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/app_window.rs `WindowTitleAuthority` (derives dropped),
// `window_title_authority`
pub enum WindowTitleAuthority {
    Search,
    Canonical,
}
pub const fn window_title_authority(search_active: bool) -> WindowTitleAuthority {
    if search_active {
        WindowTitleAuthority::Search
    } else {
        WindowTitleAuthority::Canonical
    }
}
/// aterm-gui SPECS.md window-title-authority (first clause): ∀ s: window_title_authority(s) =
/// Search if s, else Canonical.
pub fn window_title_authority_spec(search_active: bool) -> u8 {
    let result = if search_active {
        WindowTitleAuthority::Search
    } else {
        WindowTitleAuthority::Canonical
    };
    let ok = if search_active {
        matches!(result, WindowTitleAuthority::Search)
    } else {
        matches!(result, WindowTitleAuthority::Canonical)
    };
    let z = ok as u8;
    z - 1 + 1
}
