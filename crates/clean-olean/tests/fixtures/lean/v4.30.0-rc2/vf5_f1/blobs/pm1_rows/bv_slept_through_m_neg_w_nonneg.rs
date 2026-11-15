#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-agent/src/supervise/run.rs `SLEPT_THROUGH_S`, `slept_through`, the body verbatim in the
// harness below. The function alone is not a root of this artifact: its `requires`
// (i64::MIN + m <= w <= i64::MAX + m) is what keeps `w - m` from overflowing, and a root
// carries no precondition, so the harness states the `requires` and returns early past it.
//
//     const SLEPT_THROUGH_S: i64 = 60;
//
//     pub(super) const fn slept_through(wall_delta_s: i64, mono_delta_s: i64) -> bool {
//         wall_delta_s - mono_delta_s > SLEPT_THROUGH_S
//     }
const SLEPT_THROUGH_S: i64 = 60;
/// aterm-agent SPECS.md sleep-wake-settle (the `slept_through` clause): requires
/// i64::MIN + m <= w <= i64::MAX + m (each bound written on the side where it cannot
/// overflow); then slept_through(w, m) iff w - m > 60, spelled w > m + 60 where m + 60 fits,
/// and false where it does not (then w - m <= i64::MAX - m < 60).
///
/// This harness is one of 4 parts of the row (the whole one is past the reference
/// entry's heartbeat budget): m < 0 and w >= 0; together the parts are the clause.
pub fn slept_through_m_neg_w_nonneg_spec(wall_delta_s: i64, mono_delta_s: i64) -> u8 {
    if !(mono_delta_s < 0 && wall_delta_s >= 0) {
        return 1;
    }
    if mono_delta_s >= 0 {
        if wall_delta_s < i64::MIN + mono_delta_s {
            return 1;
        }
    } else if wall_delta_s > i64::MAX + mono_delta_s {
        return 1;
    }
    let result = wall_delta_s - mono_delta_s > SLEPT_THROUGH_S;
    let ok = if mono_delta_s > i64::MAX - 60 {
        !result
    } else {
        result == (wall_delta_s > mono_delta_s + 60)
    };
    let z = ok as u8;
    z - 1 + 1
}
