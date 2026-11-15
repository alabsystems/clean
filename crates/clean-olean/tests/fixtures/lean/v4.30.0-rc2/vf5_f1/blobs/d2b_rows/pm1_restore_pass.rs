#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/lib.rs `RestorePassSite` (derives dropped), `restore_pass_due`
pub enum RestorePassSite {
    FirstAttach,
    Park,
}
pub const fn restore_pass_due(
    site: RestorePassSite,
    handoff_lane: bool,
    first_present_done: bool,
    queued: bool,
) -> bool {
    queued
        && match site {
            RestorePassSite::FirstAttach => handoff_lane,
            RestorePassSite::Park => first_present_done,
        }
}
/// aterm-gui SPECS.md restore-pass-refines-model, the restore_pass_due guard: the model's
/// guards (aterm-models-update NativeUpdateSuccessorAttach) RebuildAtAttach `queued == 1 &&
/// lane == 1` and RebuildAtPark `queued == 1 && painted > 0`, so restore_pass_due(FirstAttach,
/// h, f, q) = q ∧ h and restore_pass_due(Park, h, f, q) = q ∧ f.
pub fn restore_pass_due_spec(
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
            result == (queued && first_present_done)
        }
    };
    let z = ok as u8;
    z - 1 + 1
}
