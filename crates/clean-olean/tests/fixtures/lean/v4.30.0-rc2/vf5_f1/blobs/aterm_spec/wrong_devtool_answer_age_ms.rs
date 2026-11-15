#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_devtool_answer_age_ms.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `devtool_answer_age_ms`'s clause without the saturation: false at a = -1, n = i64::MAX (the difference is 2^63).
pub fn devtool_answer_age_ms_wrong(answered_at_ms: i64, now_ms: i64) -> u8 {
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
        result == diff
    };
    let z = ok as u8;
    z - 1 + 1
}
