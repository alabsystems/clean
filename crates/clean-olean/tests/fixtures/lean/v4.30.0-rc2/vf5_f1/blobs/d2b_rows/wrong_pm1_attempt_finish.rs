#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_attempt_finish.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum AttemptResult {
    Accepted,
    #[cfg(any(unix, test))]
    InstalledNeedsRelaunch,
    Blocked,
    Failed,
}
pub enum AttemptDisposition {
    Complete,
    Retry,
    ManualOnly,
}
/// The clause with finish(Blocked) = ManualOnly: false at Blocked.
pub fn finish_wrong(result: AttemptResult) -> u8 {
    let out = match result {
        AttemptResult::Accepted => AttemptDisposition::Complete,
        #[cfg(any(unix, test))]
        AttemptResult::InstalledNeedsRelaunch => AttemptDisposition::Complete,
        AttemptResult::Blocked => AttemptDisposition::Retry,
        AttemptResult::Failed => AttemptDisposition::ManualOnly,
    };
    let ok = match result {
        AttemptResult::Accepted => matches!(out, AttemptDisposition::Complete),
        #[cfg(any(unix, test))]
        AttemptResult::InstalledNeedsRelaunch => matches!(out, AttemptDisposition::Complete),
        AttemptResult::Blocked => matches!(out, AttemptDisposition::ManualOnly),
        AttemptResult::Failed => matches!(out, AttemptDisposition::ManualOnly),
    };
    let z = ok as u8;
    z - 1 + 1
}
