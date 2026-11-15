#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `folder_absent_means_allowed.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Folder {
    Documents,
    Desktop,
    Downloads,
    AppData,
}
impl Folder {
    /// `absent_means_allowed`'s clause with `Downloads`'s entry flipped: false at `Downloads`.
    pub fn absent_means_allowed_wrong(self) -> u8 {
        let result = match self {
            Self::Documents | Self::Desktop | Self::Downloads => false,
            Self::AppData => true,
        };
        let want = match self {
            Self::Documents => false,
            Self::Desktop => false,
            Self::Downloads => true,
            Self::AppData => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
