#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-log/src/lib.rs `MAX_RECORD_BYTES`, `MAX_ALERT_RECORD_BYTES`, `Level`
// (derives dropped), `record_cap`
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
pub const fn record_cap(level: Level) -> usize {
    match level {
        Level::Error | Level::Warn => MAX_ALERT_RECORD_BYTES,
        Level::Info | Level::Debug | Level::Trace => MAX_RECORD_BYTES,
    }
}
/// aterm-log SPECS.md record-cap-by-level: ∀ l: record_cap(l) = if l ≤ Warn then 1024 else 512,
/// `l ≤ Warn` read as `(l as usize) ≤ 2` (the derived order is the discriminants', and B3
/// binds them to rustc's); hence record_cap(l) ≤ MAX_ALERT_RECORD_BYTES.
pub fn record_cap_spec(level: Level) -> u8 {
    let result = match level {
        Level::Error | Level::Warn => MAX_ALERT_RECORD_BYTES,
        Level::Info | Level::Debug | Level::Trace => MAX_RECORD_BYTES,
    };
    let want = if level as usize <= 2 { 1024 } else { 512 };
    let ok = result == want && result <= MAX_ALERT_RECORD_BYTES;
    let z = ok as u8;
    z - 1 + 1
}
