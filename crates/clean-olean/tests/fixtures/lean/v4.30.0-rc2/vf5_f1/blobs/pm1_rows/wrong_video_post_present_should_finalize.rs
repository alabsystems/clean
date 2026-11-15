#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_video_post_present_should_finalize.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `video_post_present_should_finalize`'s clause on the deadline alone: false at (false, true).
pub fn video_post_present_should_finalize_wrong(
    deadline_reached: bool,
    resized_or_format_stopped: bool,
) -> u8 {
    let result = deadline_reached || resized_or_format_stopped;
    let ok = result == deadline_reached;
    let z = ok as u8;
    z - 1 + 1
}
