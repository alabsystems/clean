#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-types/src/selection.rs `selection_contains_linear`. Its harness is split
// in seven, one artifact each (`bv_selection_contains_linear_<part>.rs`), by the case of the
// `requires` and the row: a one-row selection (r1 = r2 and c1 <= c2) with `row` above, on or
// below it, or one over several rows (r1 < r2) with `row` outside them, strictly inside, on the
// first or on the last. The seven guards partition the `requires`, so the seven rows together are
// the clause on every input it admits; whole, the harness's check took 9.2 s of Lean's kernel and
// exceeded the reference entry's 2,000,000-heartbeat budget for one declaration (measured), each
// part takes at most 2.7 s. This part: a one-row selection, `row` above its row (`row < start_row`).
// The function as it stands, verbatim (no arithmetic: a root with no precondition).
pub const fn selection_contains_linear(
    row: i32,
    col: usize,
    start_row: i32,
    start_col: usize,
    end_row: i32,
    end_col: usize,
) -> bool {
    if row < start_row || row > end_row {
        return false;
    }
    if row == start_row && row == end_row {
        col >= start_col && col <= end_col
    } else if row == start_row {
        col >= start_col
    } else if row == end_row {
        col <= end_col
    } else {
        true
    }
}
/// aterm-types SPECS.md sel-linear, on a one-row selection, `row` above its row (`row < start_row`):
/// requires (r1,c1) <=Lex (r2,c2); then
/// selection_contains_linear(row,col,r1,c1,r2,c2) iff (r1,c1) <=Lex (row,col) <=Lex
/// (r2,c2). The body is aterm's with its early `return false` as `break 'body false` out
/// of a labelled block (the same acyclic control); (a, b) <=Lex (c, d) is spelled
/// a < c or (a = c and b <= d).
pub fn selection_contains_linear_one_row_below_spec(
    row: i32,
    col: usize,
    start_row: i32,
    start_col: usize,
    end_row: i32,
    end_col: usize,
) -> u8 {
    if !(start_row == end_row && start_col <= end_col && row < start_row) {
        return 1;
    }
    let result = 'body: {
        if row < start_row || row > end_row {
            break 'body false;
        }
        if row == start_row && row == end_row {
            col >= start_col && col <= end_col
        } else if row == start_row {
            col >= start_col
        } else if row == end_row {
            col <= end_col
        } else {
            true
        }
    };
    let after_start = start_row < row || (start_row == row && start_col <= col);
    let before_end = row < end_row || (row == end_row && col <= end_col);
    let ok = result == (after_start && before_end);
    let z = ok as u8;
    z - 1 + 1
}
