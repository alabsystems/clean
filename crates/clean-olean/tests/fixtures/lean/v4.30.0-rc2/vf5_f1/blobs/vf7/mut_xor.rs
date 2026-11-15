// VF7's `mutXor` witness: `^` read as `|` makes `a ^ 1` at least 1, so the divisor
// never 0; SemR's run of `xor_div(1)` divides by 0.
pub fn xor_div(a: u8) -> u8 {
    100 / (a ^ 1)
}
