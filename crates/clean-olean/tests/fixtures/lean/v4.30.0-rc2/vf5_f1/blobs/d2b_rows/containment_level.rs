#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): an aterm function copied VERBATIM from
// aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC HARNESS: the
// same body, then the crate's SPECS.md clause written apart from the body; `ok as u8 - 1`
// underflows (an overflow `Assert`) exactly when the clause is false, so "the harness
// never panics" is "the clause holds for every valid input".

// aterm: crates/aterm-containment/src/mode.rs `ContainmentMode` (its derives dropped: a
// derived `Clone` reads through a pointer, outside F1), `ContainmentMode::level`
#[repr(u8)]
#[non_exhaustive]
pub enum ContainmentMode {
    Containment = 0,
    Safety = 1,
    User = 2,
}
impl ContainmentMode {
    pub const fn level(self) -> u8 {
        self as u8
    }
    /// aterm-containment SPECS.md mode-order (level clause): level(a) = LV(a), with
    /// Containment = 0, Safety = 1, User = 2 (so level ∈ 0..=2).
    pub fn level_spec(self) -> u8 {
        let lv: u8 = match self {
            Self::Containment => 0,
            Self::Safety => 1,
            Self::User => 2,
        };
        let result = self as u8;
        let ok = result == lv && result <= 2;
        let z = ok as u8;
        z - 1 + 1
    }
}
