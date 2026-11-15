#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_drop_taint.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

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
/// The clause with `∧` for `∨`: false at (GpuOccluded, false).
pub fn drop_taints_present_latency_wrong(reason: PresentDropReason, parked: bool) -> u8 {
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
        result == (parked && occluded)
    };
    let z = ok as u8;
    z - 1 + 1
}
