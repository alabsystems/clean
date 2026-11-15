// Trust's CAST-SIGNED-CLAMP-UB-1 (`crates/trust-vcgen/tests/data/signed_clamp_cast.rs`),
// its one F1 shape verbatim: a SIGNED min-clamp, so `l` can be negative and `l as u32`
// wraps it to a huge value; `c2_add(-1)` overflows the add.
pub fn c2_add(v: i32) -> u32 {
    let l = if v > 10 { 10 } else { v };
    (l as u32) + 4294967200
}
