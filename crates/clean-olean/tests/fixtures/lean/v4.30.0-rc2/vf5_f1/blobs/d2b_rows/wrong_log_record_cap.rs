#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `log_record_cap.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub const MAX_RECORD_BYTES: usize = 512;
pub const MAX_ALERT_RECORD_BYTES: usize = 1024;
#[repr(usize)]
pub enum Level {
    Error = 1,
    Warn = 2,
    Info = 3,
    Debug = 4,
    Trace = 5,
}
/// `record_cap`'s clause with `l < Warn` for `l ≤ Warn`: false at `Warn`.
pub fn record_cap_wrong(level: Level) -> u8 {
    let result = match level {
        Level::Error | Level::Warn => MAX_ALERT_RECORD_BYTES,
        Level::Info | Level::Debug | Level::Trace => MAX_RECORD_BYTES,
    };
    let want = if (level as usize) < 2 { 1024 } else { 512 };
    let ok = result == want && result <= MAX_ALERT_RECORD_BYTES;
    let z = ok as u8;
    z - 1 + 1
}
