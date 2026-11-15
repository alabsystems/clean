#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_selection_contains_linear_many_end.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `selection_contains_linear` on a selection over several rows, `row` on its last, the clause with a strict end column: false at (1, 0) of the selection (0, 0) to (1, 0).
pub fn selection_contains_linear_many_end_wrong(
    row: i32,
    col: usize,
    start_row: i32,
    start_col: usize,
    end_row: i32,
    end_col: usize,
) -> u8 {
    if !(start_row < end_row && row == end_row) {
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
    let before_end = row < end_row || (row == end_row && col < end_col);
    let ok = result == (after_start && before_end);
    let z = ok as u8;
    z - 1 + 1
}
