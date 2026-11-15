#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_tab_cells.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `tab_cells`'s clause with no cells at a stop: false at column 0.
pub fn tab_cells_wrong(column: usize) -> u8 {
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
    let ok = if column % 4 == 0 {
        result == 0
    } else {
        result as usize + column % 4 == 4
    };
    let z = ok as u8;
    z - 1 + 1
}
