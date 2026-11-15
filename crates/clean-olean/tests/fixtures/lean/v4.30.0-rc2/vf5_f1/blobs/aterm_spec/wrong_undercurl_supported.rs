#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_undercurl_supported.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub const DECO_ATLAS_MAX_DIM: usize = 2048;
pub const DECO_ATLAS_SPRITES: usize = 8;
/// `undercurl_supported`'s clause with the width cap 255: false at (256, 1).
pub fn undercurl_supported_wrong(cell_w: usize, cell_h: usize) -> u8 {
    let result = cell_w > 0
        && cell_h > 0
        && cell_w <= DECO_ATLAS_MAX_DIM / DECO_ATLAS_SPRITES
        && cell_h <= DECO_ATLAS_MAX_DIM;
    let ok = result == (1 <= cell_w && cell_w <= 255 && 1 <= cell_h && cell_h <= 2048);
    let z = ok as u8;
    z - 1 + 1
}
