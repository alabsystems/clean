#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-containment/src/consent.rs `devtool_answer_age_ms`, REWRITTEN for F1
// (aterm's body calls `saturating_sub` and `unsigned_abs`, which trust-ir lowers to
// calls), the plan's select: `now - a` saturates only upward when `a < 0` and
// `now > i64::MAX + a` (then `i64::MAX`, and `unsigned_abs` of it is `i64::MAX as u64`),
// and only downward to `i64::MIN` when it is negative; a negative age is 0, and a
// nonnegative one is its own `unsigned_abs`. `i64::MAX + a` cannot overflow for `a < 0`,
// nor `now - a` past the guards: the same function on every input.
//
//     pub const fn devtool_answer_age_ms(answered_at_ms: i64, now_ms: i64) -> u64 {
//         let age = now_ms.saturating_sub(answered_at_ms);
//         if age < 0 { 0 } else { age.unsigned_abs() }
//     }
pub const fn devtool_answer_age_ms(answered_at_ms: i64, now_ms: i64) -> u64 {
    if now_ms <= answered_at_ms {
        0
    } else if answered_at_ms < 0 && now_ms > i64::MAX + answered_at_ms {
        i64::MAX as u64
    } else {
        (now_ms - answered_at_ms) as u64
    }
}
/// aterm-containment SPECS.md devtool-timestamp (the `devtool_answer_age_ms` clause):
/// devtool_answer_age_ms(a, n) = max(0, n.saturating_sub(a)) as u64. Spelled on the two
/// stamps' 64-bit patterns: for n > a the true difference n − a is in 1 ..= 2^64 − 1, so it
/// is `un − ua` when `un ≥ ua`, else `un + (u64::MAX − ua) + 1`; saturating, it is that
/// difference capped at `i64::MAX`; for n ≤ a it is 0.
pub fn devtool_answer_age_ms_spec(answered_at_ms: i64, now_ms: i64) -> u8 {
    let result = if now_ms <= answered_at_ms {
        0
    } else if answered_at_ms < 0 && now_ms > i64::MAX + answered_at_ms {
        i64::MAX as u64
    } else {
        (now_ms - answered_at_ms) as u64
    };
    let ok = if now_ms <= answered_at_ms {
        result == 0
    } else {
        let un = now_ms as u64;
        let ua = answered_at_ms as u64;
        let diff = if un >= ua {
            un - ua
        } else {
            un + (u64::MAX - ua) + 1
        };
        let cap = 0x7FFF_FFFF_FFFF_FFFF;
        result == (if diff > cap { cap } else { diff })
    };
    let z = ok as u8;
    z - 1 + 1
}
