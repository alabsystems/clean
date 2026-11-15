#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_cli_mark.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum Mark {
    Ok,
    Note,
    Warn,
    Fail,
}
impl Mark {
    /// `is_fail`'s clause with `Warn`'s entry flipped: false at `Warn`.
    pub fn is_fail_wrong(self) -> u8 {
        let result = matches!(self, Self::Fail);
        let want = match self {
            Self::Ok => false,
            Self::Note => false,
            Self::Warn => true,
            Self::Fail => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
    /// `from_ok`'s clause read as (b ? Fail : Ok): false at `true`.
    pub fn from_ok_wrong(ok: bool) -> u8 {
        let result = if ok { Self::Ok } else { Self::Fail };
        let is_ok = matches!(result, Self::Ok);
        let is_fail = matches!(result, Self::Fail);
        let good = if ok { is_fail } else { is_ok };
        let z = good as u8;
        z - 1 + 1
    }
}
