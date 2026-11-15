#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `wait_end_echo.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

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
    /// `echo`'s clause with Gone → Fault: false at `Gone`.
    pub fn echo_wrong(self) -> u8 {
        let result = match self {
            Self::Done => EchoKind::Complete,
            Self::Stopped | Self::Gone => EchoKind::Vanish,
            Self::Failed => EchoKind::Fault,
        };
        let ok = match self {
            Self::Done => matches!(result, EchoKind::Complete),
            Self::Stopped => matches!(result, EchoKind::Vanish),
            Self::Gone => matches!(result, EchoKind::Fault),
            Self::Failed => matches!(result, EchoKind::Fault),
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
