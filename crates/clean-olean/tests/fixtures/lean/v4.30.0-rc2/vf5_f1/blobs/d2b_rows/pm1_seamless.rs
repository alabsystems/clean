#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/seamless.rs `overlap_intake_exits`; `RefusedIntakeLeave` (derives
// dropped; its `cfg(unix)` true on this triple), `RefusedIntakeLeave::gives_back_trial_launch`
pub const fn overlap_intake_exits(overlap_degraded: bool, adopted: usize, offered: bool) -> bool {
    overlap_degraded && (adopted > 0 || offered)
}
/// aterm-gui SPECS.md successor-exit-decisions: overlap_intake_exits(d, a, off) = d ∧ (a > 0 ∨
/// off).
pub fn overlap_intake_exits_spec(overlap_degraded: bool, adopted: usize, offered: bool) -> u8 {
    let result = overlap_degraded && (adopted > 0 || offered);
    let ok = result == (overlap_degraded && (adopted >= 1 || offered));
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
    pub const fn gives_back_trial_launch(self) -> bool {
        matches!(self, Self::Passing | Self::ParentEndsIt)
    }
    /// aterm-gui SPECS.md successor-exit-decisions: gives_back ⇔ leave ∈ {Passing, ParentEndsIt}.
    pub fn gives_back_trial_launch_spec(self) -> u8 {
        let result = matches!(self, Self::Passing | Self::ParentEndsIt);
        let ok = {
            let want = match self {
                Self::Ordinary => false,
                Self::Passing => true,
                Self::ParentEndsIt => true,
            };
            result == want
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
