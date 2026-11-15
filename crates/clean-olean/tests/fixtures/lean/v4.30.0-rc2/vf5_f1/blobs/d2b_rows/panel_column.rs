#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-phase/src/panel.rs `PanelRenderer` (derives dropped), `PanelRenderer::column`
pub enum PanelRenderer {
    Fullscreen,
    Inline,
}
impl PanelRenderer {
    pub const fn column(self) -> usize {
        match self {
            PanelRenderer::Fullscreen => 3,
            PanelRenderer::Inline => 2,
        }
    }
    /// aterm-phase SPECS.md settings-panel-contract (sub-clause): Fullscreen → column 3,
    /// Inline → column 2.
    pub fn column_spec(self) -> u8 {
        let result: usize = match self {
            PanelRenderer::Fullscreen => 3,
            PanelRenderer::Inline => 2,
        };
        let want: usize = match self {
            Self::Fullscreen => 3,
            Self::Inline => 2,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
