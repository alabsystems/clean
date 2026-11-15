#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_carry_ceiling.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum CarryCeiling {
    Full,
    Visible,
    Repaint,
}
impl CarryCeiling {
    /// `carries_scrollback`'s clause with `Visible`'s entry flipped: false at `Visible`.
    pub fn carries_scrollback_wrong(self) -> u8 {
        let result = matches!(self, Self::Full);
        let want = match self {
            Self::Full => true,
            Self::Visible => true,
            Self::Repaint => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
