#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/file_picker_win.rs `HRESULT_CANCELLED`, `is_cancelled`
const HRESULT_CANCELLED: i32 = 0x8007_04C7u32 as i32;

/// Whether an `IModalWindow::Show` HRESULT is the user cancelling (Cancel, Esc, ✕) rather
/// than a fault.
pub fn is_cancelled(hr: i32) -> bool {
    hr == HRESULT_CANCELLED
}
/// aterm-gui SPECS.md fpw-is-cancelled: is_cancelled(hr) iff hr = HRESULT_FROM_WIN32(
/// ERROR_CANCELLED), 0x800704C7 as i32; spelled on hr's 32-bit pattern.
pub fn is_cancelled_spec(hr: i32) -> u8 {
    let result = hr == HRESULT_CANCELLED;
    let ok = result == (hr as u32 == 0x8007_04C7);
    let z = ok as u8;
    z - 1 + 1
}
