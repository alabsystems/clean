#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_is_vendor_build.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const VENDOR_BUILD_BASE: u64 = 1_000_000_000_000_000_000;

/// `is_vendor_build`'s clause as b > 10^18: false at 10^18.
pub fn is_vendor_build_wrong(build: u64) -> u8 {
    let result = build >= VENDOR_BUILD_BASE;
    let ok = result == (build > 1_000_000_000_000_000_000);
    let z = ok as u8;
    z - 1 + 1
}
