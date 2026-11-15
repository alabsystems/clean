#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/metrics.rs `PresentDropReason` (the `label_enum!` expansion's
// enum), `drop_taints_present_latency`
pub enum PresentDropReason {
    None,
    GpuReconfigured,
    GpuTimeout,
    GpuUnavailable,
    GpuOccluded,
    GpuValidation,
    CpuResize,
    CpuAcquire,
    CpuCommit,
    TargetMismatch,
    Virtual,
    CpuRaster,
}
pub const fn drop_taints_present_latency(reason: PresentDropReason, parked: bool) -> bool {
    parked || matches!(reason, PresentDropReason::GpuOccluded)
}
/// aterm-gui SPECS.md m-drop-taint: ∀ r, parked: drop_taints_present_latency(r, parked) = parked ∨
/// r = GpuOccluded.
pub fn drop_taints_present_latency_spec(reason: PresentDropReason, parked: bool) -> u8 {
    let result = parked || matches!(reason, PresentDropReason::GpuOccluded);
    let ok = {
        let occluded = match reason {
            PresentDropReason::None => false,
            PresentDropReason::GpuReconfigured => false,
            PresentDropReason::GpuTimeout => false,
            PresentDropReason::GpuUnavailable => false,
            PresentDropReason::GpuOccluded => true,
            PresentDropReason::GpuValidation => false,
            PresentDropReason::CpuResize => false,
            PresentDropReason::CpuAcquire => false,
            PresentDropReason::CpuCommit => false,
            PresentDropReason::TargetMismatch => false,
            PresentDropReason::Virtual => false,
            PresentDropReason::CpuRaster => false,
        };
        result == (parked || occluded)
    };
    let z = ok as u8;
    z - 1 + 1
}
