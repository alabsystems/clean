#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `containment_level.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

#[repr(u8)]
#[non_exhaustive]
pub enum ContainmentMode {
    Containment = 0,
    Safety = 1,
    User = 2,
}
impl ContainmentMode {
    /// `level`'s clause with Safety and User swapped (Safety = 2, User = 1): false at `Safety`.
    pub fn level_wrong(self) -> u8 {
        let lv: u8 = match self {
            Self::Containment => 0,
            Self::Safety => 2,
            Self::User => 1,
        };
        let result = self as u8;
        let ok = result == lv && result <= 2;
        let z = ok as u8;
        z - 1 + 1
    }
}
