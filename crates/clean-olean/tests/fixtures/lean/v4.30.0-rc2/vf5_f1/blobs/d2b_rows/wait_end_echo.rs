#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-messages/src/waits.rs `WaitEnd`, crates/aterm-messages/src/center.rs
// `EchoKind` (derives dropped), `WaitEnd::echo`
pub enum WaitEnd {
    Done,
    Stopped,
    Gone,
    Failed,
}
pub enum EchoKind {
    Complete,
    Fault,
    Vanish,
}
impl WaitEnd {
    pub const fn echo(self) -> EchoKind {
        match self {
            Self::Done => EchoKind::Complete,
            Self::Stopped | Self::Gone => EchoKind::Vanish,
            Self::Failed => EchoKind::Fault,
        }
    }
    /// aterm-messages SPECS.md retirement-outcome-echo-and-record-words (the WaitEnd::echo
    /// clause): Done → Complete, Stopped | Gone → Vanish, Failed → Fault.
    pub fn echo_spec(self) -> u8 {
        let result = match self {
            Self::Done => EchoKind::Complete,
            Self::Stopped | Self::Gone => EchoKind::Vanish,
            Self::Failed => EchoKind::Fault,
        };
        let ok = match self {
            Self::Done => matches!(result, EchoKind::Complete),
            Self::Stopped => matches!(result, EchoKind::Vanish),
            Self::Gone => matches!(result, EchoKind::Vanish),
            Self::Failed => matches!(result, EchoKind::Fault),
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
