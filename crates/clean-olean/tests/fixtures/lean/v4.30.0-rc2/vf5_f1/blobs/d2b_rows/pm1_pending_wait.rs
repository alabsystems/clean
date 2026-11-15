#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/atpkg/src/cli.rs `WaitStep` (derives dropped), `pending_wait_step`
pub enum WaitStep {
    Run,
    Fail,
    Wait,
}
pub const fn pending_wait_step(running: bool, installed: bool, failed: bool) -> WaitStep {
    if installed {
        WaitStep::Run
    } else if failed || !running {
        WaitStep::Fail
    } else {
        WaitStep::Wait
    }
}
/// atpkg SPECS.md pending-wait-step (pure half): pending_wait_step(running, installed, failed)
/// = Run if installed; else Fail if failed ∨ ¬running; else Wait.
pub fn pending_wait_step_spec(running: bool, installed: bool, failed: bool) -> u8 {
    let result = if installed {
        WaitStep::Run
    } else if failed || !running {
        WaitStep::Fail
    } else {
        WaitStep::Wait
    };
    let ok = if installed {
        matches!(result, WaitStep::Run)
    } else if failed || !running {
        matches!(result, WaitStep::Fail)
    } else {
        matches!(result, WaitStep::Wait)
    };
    let z = ok as u8;
    z - 1 + 1
}
