// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M4, reader C: the ELABORATED KERNEL TERM decodes back to the committed
//! core — and the frozen `ir_lz` term still does too.**
//!
//! Reader C never sees the minter's output. `ir_mint::decode` walks the term
//! the elaborator actually registered in the specification environment and
//! rebuilds a core module from it; comparing that against the committed
//! `IR_LZC_CORE` — which reader A projected from the artifact BINARY — is what
//! keeps `mint` out of the trusted base. On this chain reader C is also the
//! only reader that sees both minted bodies AND the global as one term.
//!
//! The second test is the reason this lane could not wait for Phase B.
//! `ir_lzc` RE-MINTS function 0 under new names, so for the first time two
//! elaborated terms in one environment claim to be the same emitted body. The
//! kernel-checked `ir_lzc_func0_is_the_lz_mint` says they are equal; this says
//! the frozen one is still equal to the ARTIFACT, which is the half an
//! `Eq.refl` between the two cannot establish on its own — a re-mint that
//! dragged `ir_lz_func` with it would satisfy the equation and break the
//! projection.
//!
//! Both pay one full `Specification` build, which is why this is the last lane
//! in the file.

use clean_verify::ir_mint;

use super::{canon, tags};

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), "ir_lzc_module", &tags())
        .unwrap_or_else(|e| panic!("decode ir_lzc_module: {e}"));
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_LZC_CORE,
        "the ELABORATED term registered under `ir_lzc_module` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is the only reader that sees \
         both bodies AND the global as one term."
    );
}

#[test]
fn the_lz_module_is_untouched() {
    let spec = clean_verify::test_utils::shared_spec();
    let lz_tags =
        ir_mint::tags::parse(ir_mint::IR_LZ_TAGS).expect("the ir_lz tag table must parse");
    let decoded = ir_mint::decode(spec.env(), "ir_lz_module", &lz_tags)
        .unwrap_or_else(|e| panic!("decode ir_lz_module: {e}"));
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_LZ_CORE,
        "registering the ir_lzc chain moved the FROZEN ir_lz term. ir_lzc re-mints function 0 \
         under its own names precisely so that ir_lz stays byte-frozen; if this fails, the \
         re-mint edited the original instead of standing beside it, and every gate over ir_lz \
         is measuring something else than it was."
    );
}
