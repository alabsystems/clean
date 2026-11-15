#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/amacs-term/src/render.rs `tab_cells`
pub const fn tab_cells(column: usize) -> u16 {
    match column % 4 {
        0 => 4,
        1 => 3,
        2 => 2,
        _ => 1,
    }
}
/// amacs-term SPECS.md tab-stop: for all column, result = 4 - column mod 4 (spelled
/// result + column mod 4 = 4). The harness's copy writes the `match` with a wildcard default
/// as the `if` chain it is (the same function on every `usize`): F1's `switch` keeps no
/// `r != c` on its default arm.
pub fn tab_cells_spec(column: usize) -> u8 {
    let r = column % 4;
    let result: u16 = if r == 0 {
        4
    } else if r == 1 {
        3
    } else if r == 2 {
        2
    } else {
        1
    };
    let ok = result as usize + column % 4 == 4;
    let z = ok as u8;
    z - 1 + 1
}
