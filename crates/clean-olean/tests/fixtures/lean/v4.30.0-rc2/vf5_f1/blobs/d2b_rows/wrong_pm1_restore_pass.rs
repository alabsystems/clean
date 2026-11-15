#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_restore_pass.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum RestorePassSite {
    FirstAttach,
    Park,
}
/// The Park guard reading the lane: false at (Park, false, true, true).
pub fn restore_pass_due_wrong(
    site: RestorePassSite,
    handoff_lane: bool,
    first_present_done: bool,
    queued: bool,
) -> u8 {
    let result = queued
        && match site {
            RestorePassSite::FirstAttach => handoff_lane,
            RestorePassSite::Park => first_present_done,
        };
    let ok = {
        let attach = match site {
            RestorePassSite::FirstAttach => true,
            RestorePassSite::Park => false,
        };
        if attach {
            result == (queued && handoff_lane)
        } else {
            result == (queued && handoff_lane)
        }
    };
    let z = ok as u8;
    z - 1 + 1
}
