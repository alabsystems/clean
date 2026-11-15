#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_defer_gpu_build.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `defer_gpu_build`'s clause as g or h: false at (true, false).
pub fn defer_gpu_build_wrong(want_gpu: bool, headless: bool) -> u8 {
    let result = want_gpu && headless;
    let ok = result == (want_gpu as u8 + headless as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
