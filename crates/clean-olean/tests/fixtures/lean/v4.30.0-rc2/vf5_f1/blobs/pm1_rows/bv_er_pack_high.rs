#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/echo_rtt.rs `US_MASK`, `pack`
const US_MASK: u64 = (1 << 48) - 1;

pub const fn pack(session: u64, now_us: u64) -> u64 {
    ((session & 0xFFFF) << 48) | (now_us & US_MASK)
}
/// aterm-gui SPECS.md er-pack: for all session and us, pack(session, us) >> 48 =
/// session & 0xFFFF and pack(session, us) & US_MASK = us & US_MASK, US_MASK = 2^48 - 1.
/// Spelled with division and remainder by 2^48 and 2^16.
///
/// This harness is one of 2 parts of the row (the whole one is past the reference
/// entry's heartbeat budget): the high conjunct, pack >> 48 = session & 0xFFFF; together the parts are the clause.
pub fn er_pack_high_spec(session: u64, now_us: u64) -> u8 {
    let result = ((session & 0xFFFF) << 48) | (now_us & US_MASK);
    let ok = result / 281_474_976_710_656 == session % 65_536;
    let z = ok as u8;
    z - 1 + 1
}
