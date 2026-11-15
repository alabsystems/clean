#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `panel_column.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum PanelRenderer {
    Fullscreen,
    Inline,
}
impl PanelRenderer {
    /// `column`'s clause with `Inline`'s value off by one: false at `Inline`.
    pub fn column_wrong(self) -> u8 {
        let result: usize = match self {
            PanelRenderer::Fullscreen => 3,
            PanelRenderer::Inline => 2,
        };
        let want: usize = match self {
            Self::Fullscreen => 3,
            Self::Inline => 3,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
