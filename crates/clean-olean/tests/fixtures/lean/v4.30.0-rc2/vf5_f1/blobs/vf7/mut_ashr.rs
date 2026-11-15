// VF7's `mutAshr` witness: an arithmetic shift right read as a logical one makes
// `x >> 31` 0 or 1, so the divisor never 0; SemR's run of `ashr_div(-1)` divides by 0.
pub fn ashr_div(x: i32) -> i32 {
    100 / ((x >> 31) + 1)
}
