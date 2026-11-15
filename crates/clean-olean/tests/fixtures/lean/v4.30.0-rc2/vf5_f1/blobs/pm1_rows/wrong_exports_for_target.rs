#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_exports_for_target.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const IMPORTS_HISTORY_FROM_BUILD: u64 = 1_790_526_323;

/// `exports_for_target`'s clause handing no rollback the export: false at r = 1_790_526_324, t = 1_790_526_323.
pub fn exports_for_target_wrong(running_build: u64, target_build: u64) -> u8 {
    let result = target_build >= running_build || target_build >= IMPORTS_HISTORY_FROM_BUILD;
    let ok = if target_build >= running_build {
        result
    } else {
        !result
    };
    let z = ok as u8;
    z - 1 + 1
}
