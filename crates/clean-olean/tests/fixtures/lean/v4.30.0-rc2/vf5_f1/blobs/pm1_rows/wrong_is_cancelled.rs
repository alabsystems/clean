#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_is_cancelled.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const HRESULT_CANCELLED: i32 = 0x8007_04C7u32 as i32;

/// `is_cancelled`'s clause at 0x800704C6: false at hr = 0x800704C7 as i32.
pub fn is_cancelled_wrong(hr: i32) -> u8 {
    let result = hr == HRESULT_CANCELLED;
    let ok = result == (hr as u32 == 0x8007_04C6);
    let z = ok as u8;
    z - 1 + 1
}
