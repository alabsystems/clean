// The corrected twins of VF7's mutant witnesses, each safe only by the exact bit-level
// reading: `x >> 31` is 0 or -1 (so `+ 2` is 1 or 2), `(a ^ 0xFF) + a` is 255, and
// `x as u8` is `x % 256`; and CAST-SIGNED-CLAMP-UB-1's twin, the clamp closed below at 0.
pub fn ashr_div_twin(x: i32) -> i32 {
    100 / ((x >> 31) + 2)
}
pub fn xor_div_twin(a: u8) -> u8 {
    100 / ((a ^ 0xFF) + a - 254)
}
pub fn trunc_div_twin(x: u32) -> u8 {
    if x % 256 > 0 {
        100 / (x as u8)
    } else {
        0
    }
}
pub fn c2_add_twin(v: i32) -> u32 {
    let l = if v > 10 {
        10
    } else if v < 0 {
        0
    } else {
        v
    };
    (l as u32) + 4294967200
}
