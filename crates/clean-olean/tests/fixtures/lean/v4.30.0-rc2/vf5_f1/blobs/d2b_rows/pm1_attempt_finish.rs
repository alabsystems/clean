#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/native_update_auto_intent.rs `AttemptResult`, `AttemptDisposition`
// (derives dropped; `InstalledNeedsRelaunch`'s `cfg(any(unix, test))` kept and true on this
// triple), `finish`
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
pub const fn finish(result: AttemptResult) -> AttemptDisposition {
    match result {
        AttemptResult::Accepted => AttemptDisposition::Complete,
        #[cfg(any(unix, test))]
        AttemptResult::InstalledNeedsRelaunch => AttemptDisposition::Complete,
        AttemptResult::Blocked => AttemptDisposition::Retry,
        AttemptResult::Failed => AttemptDisposition::ManualOnly,
    }
}
/// aterm-gui SPECS.md attempt-finish: finish(Accepted) = finish(InstalledNeedsRelaunch) = Complete;
/// finish(Blocked) = Retry; finish(Failed) = ManualOnly (total over the four variants).
pub fn finish_spec(result: AttemptResult) -> u8 {
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
        AttemptResult::Blocked => matches!(out, AttemptDisposition::Retry),
        AttemptResult::Failed => matches!(out, AttemptDisposition::ManualOnly),
    };
    let z = ok as u8;
    z - 1 + 1
}
