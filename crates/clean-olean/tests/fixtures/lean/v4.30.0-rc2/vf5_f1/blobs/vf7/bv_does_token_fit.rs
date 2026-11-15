#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/aterm-lz4/src/block/decompress_safe.rs `FIT_TOKEN_MASK_*`, `does_token_fit`
const FIT_TOKEN_MASK_LITERAL: u8 = 0b00001111;
const FIT_TOKEN_MASK_MATCH: u8 = 0b11110000;
pub const fn does_token_fit(token: u8) -> bool {
    !((token & FIT_TOKEN_MASK_LITERAL) == FIT_TOKEN_MASK_LITERAL
        || (token & FIT_TOKEN_MASK_MATCH) == FIT_TOKEN_MASK_MATCH)
}
/// aterm-lz4 SPECS.md token-fit-table: ∀ t:u8: does_token_fit(t) ⇔ (t >> 4) < 15 ∧ (t & 0x0F) < 15.
pub fn does_token_fit_spec(token: u8) -> u8 {
    let result = !((token & FIT_TOKEN_MASK_LITERAL) == FIT_TOKEN_MASK_LITERAL
        || (token & FIT_TOKEN_MASK_MATCH) == FIT_TOKEN_MASK_MATCH);
    let ok = result == ((token >> 4) < 15 && (token & 0x0F) < 15);
    let z = ok as u8;
    z - 1 + 1
}
