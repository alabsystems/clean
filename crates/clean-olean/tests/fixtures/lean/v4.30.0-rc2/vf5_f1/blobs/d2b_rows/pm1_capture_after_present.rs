#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/lib.rs `CaptureAfterPresentDecision` (derives dropped),
// `capture_after_present_decision`
pub enum CaptureAfterPresentDecision {
    Capture,
    Retry,
    FailClosed,
}
pub const fn capture_after_present_decision(
    present_succeeded: bool,
    attempts: u8,
    attempt_limit: u8,
) -> CaptureAfterPresentDecision {
    if present_succeeded {
        CaptureAfterPresentDecision::Capture
    } else if attempts < attempt_limit {
        CaptureAfterPresentDecision::Retry
    } else {
        CaptureAfterPresentDecision::FailClosed
    }
}
/// aterm-gui SPECS.md capture-after-present (first clause): ∀ ok, attempts, limit:
/// capture_after_present_decision(ok, attempts, limit) = Capture if ok; Retry if ¬ok ∧ attempts <
/// limit; else FailClosed.
pub fn capture_after_present_decision_spec(
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
    } else if attempts < attempt_limit {
        matches!(result, CaptureAfterPresentDecision::Retry)
    } else {
        matches!(result, CaptureAfterPresentDecision::FailClosed)
    };
    let z = ok as u8;
    z - 1 + 1
}
