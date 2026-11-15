#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_roster_duty.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum RosterDuty {
    Sign,
    Finish,
}
/// The clause with Sign for a finished build: false at `true`.
pub fn roster_duty_wrong(build_done: bool) -> u8 {
    let result = if build_done {
        RosterDuty::Finish
    } else {
        RosterDuty::Sign
    };
    let ok = if build_done {
        matches!(result, RosterDuty::Sign)
    } else {
        matches!(result, RosterDuty::Sign)
    };
    let z = ok as u8;
    z - 1 + 1
}
