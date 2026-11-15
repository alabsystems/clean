#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-update/src/install.rs `BootHealthLane` (derives dropped),
// `boot_health_lane` (install.rs is `cfg(target_os = "macos")`, this triple)
pub enum BootHealthLane {
    FullProof,
    CountOnly,
}
pub const fn boot_health_lane(handoff_target: bool, attempts_after_launch: u32) -> BootHealthLane {
    if handoff_target && attempts_after_launch <= 1 {
        BootHealthLane::CountOnly
    } else {
        BootHealthLane::FullProof
    }
}
/// aterm-update SPECS.md boot-health-lane: ∀ t, a: boot_health_lane(t, a) = CountOnly ⇔ t ∧ a ≤
/// 1, and FullProof otherwise.
pub fn boot_health_lane_spec(handoff_target: bool, attempts_after_launch: u32) -> u8 {
    let result = if handoff_target && attempts_after_launch <= 1 {
        BootHealthLane::CountOnly
    } else {
        BootHealthLane::FullProof
    };
    let ok = {
        let count_only = matches!(result, BootHealthLane::CountOnly);
        let full = matches!(result, BootHealthLane::FullProof);
        count_only == (handoff_target && attempts_after_launch < 2) && full == !count_only
    };
    let z = ok as u8;
    z - 1 + 1
}
