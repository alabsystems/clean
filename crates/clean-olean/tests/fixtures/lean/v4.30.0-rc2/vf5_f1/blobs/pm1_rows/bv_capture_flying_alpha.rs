#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/app_introspect.rs `capture_flying_alpha`
pub const fn capture_flying_alpha(pet_mode: bool, kitty_enabled: bool, cat_alpha: u8) -> u8 {
    if kitty_enabled && !pet_mode {
        cat_alpha
    } else {
        0
    }
}
/// aterm-gui SPECS.md capture-flying-gate (the `capture_flying_alpha` clause): for all
/// pet_mode, kitty, a: the alpha is a if kitty and not pet_mode, else 0; the guard spelled
/// as a count.
pub fn capture_flying_alpha_spec(pet_mode: bool, kitty_enabled: bool, cat_alpha: u8) -> u8 {
    let result = if kitty_enabled && !pet_mode {
        cat_alpha
    } else {
        0
    };
    let ok = result
        == (if kitty_enabled as u8 + !pet_mode as u8 == 2 {
            cat_alpha
        } else {
            0
        });
    let z = ok as u8;
    z - 1 + 1
}
