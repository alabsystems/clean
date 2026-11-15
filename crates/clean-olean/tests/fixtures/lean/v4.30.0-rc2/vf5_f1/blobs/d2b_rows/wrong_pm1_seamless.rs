#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_seamless.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

/// The clause without `off`: false at (true, 0, true).
pub fn overlap_intake_exits_wrong(overlap_degraded: bool, adopted: usize, offered: bool) -> u8 {
    let result = overlap_degraded && (adopted > 0 || offered);
    let ok = result == (overlap_degraded && adopted >= 1);
    let z = ok as u8;
    z - 1 + 1
}
#[cfg(unix)]
pub enum RefusedIntakeLeave {
    Ordinary,
    Passing,
    ParentEndsIt,
}
#[cfg(unix)]
impl RefusedIntakeLeave {
    /// The clause with Ordinary and Passing flipped: false at `Ordinary`.
    pub fn gives_back_trial_launch_wrong(self) -> u8 {
        let result = matches!(self, Self::Passing | Self::ParentEndsIt);
        let ok = {
            let want = match self {
                Self::Ordinary => true,
                Self::Passing => false,
                Self::ParentEndsIt => true,
            };
            result == want
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
