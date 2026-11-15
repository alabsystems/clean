#![allow(dead_code)]
// Controls for VF7's spec harnesses (`aterm_bv.rs`): each clause here is FALSE for some
// input (the body is the same verbatim aterm body), so its harness panics there and no
// sound calculus certifies it; the harness form is not vacuous.

/// `exited_zero` with the low field read as 8 bits (`% 256` for `% 128`): false at 128.
pub fn exited_zero_wrong(status: i32) -> u8 {
    let result = status & 0x7f == 0 && (status >> 8) & 0xff == 0;
    let u = status as u32;
    let ok = result == (u % 256 == 0 && (u / 256) % 256 == 0);
    let z = ok as u8;
    z - 1 + 1
}

const FIT_TOKEN_MASK_LITERAL: u8 = 0b00001111;
const FIT_TOKEN_MASK_MATCH: u8 = 0b11110000;
/// `does_token_fit` with `< 16` for the match nibble's `< 15`: false at 0xF0.
pub fn does_token_fit_wrong(token: u8) -> u8 {
    let result = !((token & FIT_TOKEN_MASK_LITERAL) == FIT_TOKEN_MASK_LITERAL
        || (token & FIT_TOKEN_MASK_MATCH) == FIT_TOKEN_MASK_MATCH);
    let ok = result == ((token >> 4) < 16 && (token & 0x0F) < 15);
    let z = ok as u8;
    z - 1 + 1
}
