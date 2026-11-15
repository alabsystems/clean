#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_pending_wait.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum WaitStep {
    Run,
    Fail,
    Wait,
}
/// The clause without `¬running`: false at (false, false, false).
pub fn pending_wait_step_wrong(running: bool, installed: bool, failed: bool) -> u8 {
    let result = if installed {
        WaitStep::Run
    } else if failed || !running {
        WaitStep::Fail
    } else {
        WaitStep::Wait
    };
    let ok = if installed {
        matches!(result, WaitStep::Run)
    } else if failed {
        matches!(result, WaitStep::Fail)
    } else {
        matches!(result, WaitStep::Wait)
    };
    let z = ok as u8;
    z - 1 + 1
}
