#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_held_loss.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum HeldLoss {
    ScreenOnly,
    Withheld,
    Failed,
}
impl HeldLoss {
    /// The clause read as withheld ⇒ Withheld: false at (true, true).
    pub fn from_wire_wrong(withheld: bool, failed: bool) -> u8 {
        let result = if failed {
            Self::Failed
        } else if withheld {
            Self::Withheld
        } else {
            Self::ScreenOnly
        };
        let ok = !withheld || matches!(result, Self::Withheld);
        let z = ok as u8;
        z - 1 + 1
    }
}
