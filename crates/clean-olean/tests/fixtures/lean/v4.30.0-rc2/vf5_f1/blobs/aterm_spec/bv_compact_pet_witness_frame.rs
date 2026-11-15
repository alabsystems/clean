#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-conformance/src/measure/scan.rs `compact_pet_witness_frame`,
// REWRITTEN for F1 (aterm's body calls `saturating_sub`, which trust-ir lowers to a
// call), the plan's select: `frame_count.saturating_sub(3)` is 0 when
// `frame_count < 3` (and `frame_no >= 0` holds), else `frame_count - 3`: the same function
// on every input.
//
//     pub const fn compact_pet_witness_frame(frame_no: usize, frame_count: usize) -> bool {
//         frame_no == 0 || frame_no >= frame_count.saturating_sub(3)
//     }
pub const fn compact_pet_witness_frame(frame_no: usize, frame_count: usize) -> bool {
    frame_no == 0 || frame_count < 3 || frame_no >= frame_count - 3
}
/// aterm-conformance SPECS.md companion-witness-floor (the isolating clause):
/// isolating(n, c) iff n = 0 or n >= c.saturating_sub(3), spelled as n = 0, or n >= c,
/// or c − n <= 3 (for n < c, n >= c − 3 is c − n <= 3).
pub fn compact_pet_witness_frame_spec(frame_no: usize, frame_count: usize) -> u8 {
    let result = frame_no == 0 || frame_count < 3 || frame_no >= frame_count - 3;
    let ok = result == (frame_no == 0 || frame_no >= frame_count || frame_count - frame_no <= 3);
    let z = ok as u8;
    z - 1 + 1
}
