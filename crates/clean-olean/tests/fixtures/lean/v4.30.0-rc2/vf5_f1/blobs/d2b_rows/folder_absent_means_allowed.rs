#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-containment/src/consent.rs `Folder` (derives dropped), `Folder::absent_means_allowed`
pub enum Folder {
    Documents,
    Desktop,
    Downloads,
    AppData,
}
impl Folder {
    pub const fn absent_means_allowed(self) -> bool {
        match self {
            Self::Documents | Self::Desktop | Self::Downloads => false,
            Self::AppData => true,
        }
    }
    /// aterm-containment SPECS.md folder-table (clause): absent_means_allowed(f) ⇔ f = AppData.
    pub fn absent_means_allowed_spec(self) -> u8 {
        let result = match self {
            Self::Documents | Self::Desktop | Self::Downloads => false,
            Self::AppData => true,
        };
        let want = match self {
            Self::Documents => false,
            Self::Desktop => false,
            Self::Downloads => false,
            Self::AppData => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
