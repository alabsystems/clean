#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/handoff_carry.rs `MAX_TURN_ID`, crates/aterm-gui/src/control_session.rs `past_ceiling`
mod handoff_carry {
    pub(crate) const MAX_TURN_ID: u64 = i64::MAX as u64;
}

// `past_ceiling` (control_session.rs; the header above names it)
pub const fn past_ceiling(minted: u64, ceiling: u64) -> bool {
    ceiling > 0 && ceiling < crate::handoff_carry::MAX_TURN_ID && minted > ceiling
}
/// aterm-gui SPECS.md turn-id-ceiling (the `past_ceiling` clause): past_ceiling(m, c) iff
/// 0 < c && c < MAX_TURN_ID && m > c (MAX_TURN_ID = 2^63 - 1): no ceiling at c = 0, none at
/// the manifest's top or above it, whatever m is; otherwise past it iff m > c.
pub fn past_ceiling_spec(minted: u64, ceiling: u64) -> u8 {
    let result = ceiling > 0 && ceiling < crate::handoff_carry::MAX_TURN_ID && minted > ceiling;
    let ok = if ceiling == 0 {
        !result
    } else if ceiling >= 0x7FFF_FFFF_FFFF_FFFF {
        !result
    } else {
        result == (minted > ceiling)
    };
    let z = ok as u8;
    z - 1 + 1
}
