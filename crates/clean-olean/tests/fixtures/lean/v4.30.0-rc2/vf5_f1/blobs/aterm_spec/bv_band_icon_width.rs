#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-render/src/procedural/icons.rs `band_icon_width`, its body verbatim
// in the harness below. The function alone is not a root of this artifact: its
// `requires` (spill ⇒ cw <= usize::MAX/3) is what keeps `cell_w * 3` from overflowing,
// and a root carries no precondition, so the harness states the `requires` and returns
// early past it.
//
//     pub const fn band_icon_width(cell_w: usize, spill: bool) -> usize {
//         if spill { cell_w * 3 } else { cell_w }
//     }
/// aterm-render SPECS.md band-icon-coverage (the `band_icon_width` sub-clause): requires
/// spill ⇒ cw <= usize::MAX/3; then no Assert is reachable and band_icon_width(cw, spill)
/// = 3cw if spill else cw (spelled cw + cw + cw). The bound is written as its value,
/// 6148914691236517205 = usize::MAX / 3 on the 64-bit target: trust-ir keeps a constant's
/// division by 3 as a `udiv` the calculus reads as a fresh value.
pub fn band_icon_width_spec(cell_w: usize, spill: bool) -> u8 {
    if spill && cell_w > 6_148_914_691_236_517_205 {
        return 1;
    }
    let result = if spill { cell_w * 3 } else { cell_w };
    let ok = if spill {
        result == cell_w + cell_w + cell_w
    } else {
        result == cell_w
    };
    let z = ok as u8;
    z - 1 + 1
}
