// VF7's `mutTrunc` witness: a narrowing cast read without its wrap makes `x as u8`
// positive whenever `x` is; SemR's run of `trunc_div(256)` divides by 0.
pub fn trunc_div(x: u32) -> u8 {
    if x > 0 {
        100 / (x as u8)
    } else {
        0
    }
}
