#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_compact_pet_witness_frame.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `compact_pet_witness_frame`'s clause with `c - n <= 2`: false at n = 1, c = 4.
pub fn compact_pet_witness_frame_wrong(frame_no: usize, frame_count: usize) -> u8 {
    let result = frame_no == 0 || frame_count < 3 || frame_no >= frame_count - 3;
    let ok = result == (frame_no == 0 || frame_no >= frame_count || frame_count - frame_no <= 2);
    let z = ok as u8;
    z - 1 + 1
}
