#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_lights_mode.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum Mode {
    Bypass,
    Auto,
    AcceptEdits,
    DontAsk,
    Plan,
    Manual,
}
impl Mode {
    /// `is_expected`'s clause with `Plan`'s entry flipped: false at `Plan`.
    pub fn is_expected_wrong(self) -> u8 {
        let result = matches!(self, Mode::Bypass | Mode::Auto);
        let want = match self {
            Self::Bypass => true,
            Self::Auto => true,
            Self::AcceptEdits => false,
            Self::DontAsk => false,
            Self::Plan => true,
            Self::Manual => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
