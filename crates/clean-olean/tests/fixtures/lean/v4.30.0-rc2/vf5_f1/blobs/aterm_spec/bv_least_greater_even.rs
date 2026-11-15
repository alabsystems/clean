#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-bidi/src/lib.rs `least_greater_even`, REWRITTEN for F1 (aterm's
// body calls `is_multiple_of` and `saturating_add`, which trust-ir lowers to calls):
// `level.is_multiple_of(2)` is `level % 2 == 0` (a `u8` remainder by 2, never by zero),
// and `level.saturating_add(k)` is `if level > 255 - k { 255 } else { level + k }`
// (`u8::MAX` when the sum would pass it, else the sum): the same function on every `u8`.
//
//     const fn least_greater_even(level: u8) -> u8 {
//         if level.is_multiple_of(2) {
//             level.saturating_add(2)
//         } else {
//             level.saturating_add(1)
//         }
//     }
pub const fn least_greater_even(level: u8) -> u8 {
    if level % 2 == 0 {
        if level > 253 {
            255
        } else {
            level + 2
        }
    } else {
        if level > 254 {
            255
        } else {
            level + 1
        }
    }
}
/// aterm-bidi SPECS.md levels-shape (the `least_greater_even` clause): the least even
/// level greater than `level`, saturating at `u8::MAX`: below 254 the result is even,
/// greater than `level` and at most `level + 2` (so it is the least such); from 254 on
/// it is 255.
pub fn least_greater_even_spec(level: u8) -> u8 {
    let result = if level % 2 == 0 {
        if level > 253 {
            255
        } else {
            level + 2
        }
    } else {
        if level > 254 {
            255
        } else {
            level + 1
        }
    };
    let ok = if level >= 254 {
        result == 255
    } else {
        result & 1 == 0 && result > level && result - level <= 2
    };
    let z = ok as u8;
    z - 1 + 1
}
