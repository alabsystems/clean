#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-render/src/deco.rs `DECO_ATLAS_MAX_DIM`, `DECO_ATLAS_SPRITES`,
// `undercurl_supported`
pub const DECO_ATLAS_MAX_DIM: usize = 2048;
pub const DECO_ATLAS_SPRITES: usize = 8;
pub const fn undercurl_supported(cell_w: usize, cell_h: usize) -> bool {
    cell_w > 0
        && cell_h > 0
        && cell_w <= DECO_ATLAS_MAX_DIM / DECO_ATLAS_SPRITES
        && cell_h <= DECO_ATLAS_MAX_DIM
}
/// aterm-render SPECS.md undercurl-tile (the `undercurl_supported` clause):
/// undercurl_supported(cw, ch) iff 1 <= cw <= 2048/8 = 256 and 1 <= ch <= 2048.
pub fn undercurl_supported_spec(cell_w: usize, cell_h: usize) -> u8 {
    let result = cell_w > 0
        && cell_h > 0
        && cell_w <= DECO_ATLAS_MAX_DIM / DECO_ATLAS_SPRITES
        && cell_h <= DECO_ATLAS_MAX_DIM;
    let ok = result == (1 <= cell_w && cell_w <= 256 && 1 <= cell_h && cell_h <= 2048);
    let z = ok as u8;
    z - 1 + 1
}
