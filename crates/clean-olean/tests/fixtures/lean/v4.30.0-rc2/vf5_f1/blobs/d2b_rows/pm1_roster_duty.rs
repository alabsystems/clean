#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-release/src/publish.rs `RosterDuty` (derives dropped), `roster_duty`
pub enum RosterDuty {
    Sign,
    Finish,
}
pub const fn roster_duty(build_done: bool) -> RosterDuty {
    if build_done {
        RosterDuty::Finish
    } else {
        RosterDuty::Sign
    }
}
/// aterm-release SPECS.md rel-roster-duty: ∀ b: roster_duty(b) = (b ? Finish : Sign).
pub fn roster_duty_spec(build_done: bool) -> u8 {
    let result = if build_done {
        RosterDuty::Finish
    } else {
        RosterDuty::Sign
    };
    let ok = if build_done {
        matches!(result, RosterDuty::Finish)
    } else {
        matches!(result, RosterDuty::Sign)
    };
    let z = ok as u8;
    z - 1 + 1
}
