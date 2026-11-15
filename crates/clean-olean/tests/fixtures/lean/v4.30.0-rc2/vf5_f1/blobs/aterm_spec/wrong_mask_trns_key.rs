#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_mask_trns_key.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `mask_trns_key`'s clause masking at depth 16 too: false at key 256, depth 16.
pub fn mask_trns_key_wrong(key: u16, depth: u32) -> u8 {
    let result = if depth < 16 { key & 0x00FF } else { key };
    let ok = if depth < 17 {
        result == key % 256
    } else {
        result == key
    };
    let z = ok as u8;
    z - 1 + 1
}
