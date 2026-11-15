#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/handoff_carry.rs `StatusWords` (derives dropped),
// `READS_HANGUP_FROM_BUILD`, `StatusWords::for_target` (their `cfg(any(unix, test))` true on
// this triple)
#[cfg(any(unix, test))]
pub enum StatusWords {
    Current,
    PreHangup,
}
#[cfg(any(unix, test))]
pub const READS_HANGUP_FROM_BUILD: u64 = 1_790_807_622;
#[cfg(any(unix, test))]
impl StatusWords {
    pub const fn for_target(target_build: u64) -> Self {
        if target_build < READS_HANGUP_FROM_BUILD {
            Self::PreHangup
        } else {
            Self::Current
        }
    }
    /// aterm-gui SPECS.md status-words-for-target (the for_target clause): for_target(t) =
    /// PreHangup ⇔ t < READS_HANGUP_FROM_BUILD (1_790_807_622), else Current.
    pub fn for_target_spec(target_build: u64) -> u8 {
        let result = if target_build < READS_HANGUP_FROM_BUILD {
            Self::PreHangup
        } else {
            Self::Current
        };
        let ok = if target_build < 1_790_807_622 {
            matches!(result, Self::PreHangup)
        } else {
            matches!(result, Self::Current)
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
