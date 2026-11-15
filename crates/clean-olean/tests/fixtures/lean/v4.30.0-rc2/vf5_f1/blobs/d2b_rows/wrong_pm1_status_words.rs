#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_status_words.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

#[cfg(any(unix, test))]
pub enum StatusWords {
    Current,
    PreHangup,
}
#[cfg(any(unix, test))]
pub const READS_HANGUP_FROM_BUILD: u64 = 1_790_807_622;
#[cfg(any(unix, test))]
impl StatusWords {
    /// The clause with `≤`: false at t = READS_HANGUP_FROM_BUILD.
    pub fn for_target_wrong(target_build: u64) -> u8 {
        let result = if target_build < READS_HANGUP_FROM_BUILD {
            Self::PreHangup
        } else {
            Self::Current
        };
        let ok = if target_build <= 1_790_807_622 {
            matches!(result, Self::PreHangup)
        } else {
            matches!(result, Self::Current)
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
