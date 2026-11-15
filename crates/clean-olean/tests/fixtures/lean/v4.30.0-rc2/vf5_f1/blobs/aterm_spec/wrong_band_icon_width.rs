#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_band_icon_width.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `band_icon_width`'s clause as 2cw when spilled: false at (1, true).
pub fn band_icon_width_wrong(cell_w: usize, spill: bool) -> u8 {
    if spill && cell_w > 6_148_914_691_236_517_205 {
        return 1;
    }
    let result = if spill { cell_w * 3 } else { cell_w };
    let ok = if spill {
        result == cell_w + cell_w
    } else {
        result == cell_w
    };
    let z = ok as u8;
    z - 1 + 1
}
