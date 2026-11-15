#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of
// `pm1_capture_after_present.rs`, its body the same verbatim aterm body (`f306a395db`), with its
// SPECS.md clause made FALSE for some input, so the harness panics there and no sound calculus
// certifies it: the row's harness form is not vacuous.

pub enum CaptureAfterPresentDecision {
    Capture,
    Retry,
    FailClosed,
}
/// The clause retrying at attempts = limit: false at (false, 3, 3).
pub fn capture_after_present_decision_wrong(
    present_succeeded: bool,
    attempts: u8,
    attempt_limit: u8,
) -> u8 {
    let result = if present_succeeded {
        CaptureAfterPresentDecision::Capture
    } else if attempts < attempt_limit {
        CaptureAfterPresentDecision::Retry
    } else {
        CaptureAfterPresentDecision::FailClosed
    };
    let ok = if present_succeeded {
        matches!(result, CaptureAfterPresentDecision::Capture)
    } else if attempts <= attempt_limit {
        matches!(result, CaptureAfterPresentDecision::Retry)
    } else {
        matches!(result, CaptureAfterPresentDecision::FailClosed)
    };
    let z = ok as u8;
    z - 1 + 1
}
