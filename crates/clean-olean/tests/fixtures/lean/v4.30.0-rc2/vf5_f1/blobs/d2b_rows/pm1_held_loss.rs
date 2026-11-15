#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/handoff_history.rs `HeldLoss` (derives dropped),
// `HeldLoss::from_wire`
pub enum HeldLoss {
    ScreenOnly,
    Withheld,
    Failed,
}
impl HeldLoss {
    pub const fn from_wire(withheld: bool, failed: bool) -> Self {
        if failed {
            Self::Failed
        } else if withheld {
            Self::Withheld
        } else {
            Self::ScreenOnly
        }
    }
    /// aterm-gui SPECS.md held-pane-loss-reason (the from_wire clause): from_wire(withheld,
    /// failed) reads Failed whenever the failed key is set, both keys included: failed ⇒
    /// Failed.
    pub fn from_wire_spec(withheld: bool, failed: bool) -> u8 {
        let result = if failed {
            Self::Failed
        } else if withheld {
            Self::Withheld
        } else {
            Self::ScreenOnly
        };
        let ok = !failed || matches!(result, Self::Failed);
        let z = ok as u8;
        z - 1 + 1
    }
}
