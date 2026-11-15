#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_least_greater_odd.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `least_greater_odd`'s clause with the least bound `result - level <= 1`: false at 1 (the result is 3).
pub fn least_greater_odd_wrong(level: u8) -> u8 {
    let result = if level % 2 == 0 {
        if level > 254 {
            255
        } else {
            level + 1
        }
    } else {
        if level > 253 {
            255
        } else {
            level + 2
        }
    };
    let ok = if level >= 254 {
        result == 255
    } else {
        result & 1 == 1 && result > level && result - level <= 1
    };
    let z = ok as u8;
    z - 1 + 1
}
