#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_window_title.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum WindowTitleAuthority {
    Search,
    Canonical,
}
/// The clause flipped: false at `true`.
pub fn window_title_authority_wrong(search_active: bool) -> u8 {
    let result = if search_active {
        WindowTitleAuthority::Search
    } else {
        WindowTitleAuthority::Canonical
    };
    let ok = if search_active {
        matches!(result, WindowTitleAuthority::Canonical)
    } else {
        matches!(result, WindowTitleAuthority::Search)
    };
    let z = ok as u8;
    z - 1 + 1
}
