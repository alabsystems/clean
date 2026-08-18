// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the NINTH complete chain — the first over a CAST:
//! `env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}`.**
//!
//! ```text
//! bb0(%0: (), %1: u64):
//!     %2 = trunc u64 %1 to u32
//!     ret %2
//! ```
//!
//! One block, two instructions — and before this file gained a cast lane, that
//! body parsed to an **entirely empty `Cfg`** on both sides. Every assertion the
//! gate had would have passed against a transcription with no cast in it at all,
//! against one that cast a different SSA id, against one at a different width,
//! and against one that zero-extended instead of truncating. Two empty CFGs
//! compare equal; that is the coverage-denominator failure this whole file is
//! built to refuse, and a cast walked straight into it.
//!
//! So this chain adds two lanes, for the same reason the eighth chain added
//! three:
//!
//! * **`casts`** — `(op, result, operand)`. `zext` and `trunc` are the same
//!   shape and opposite operations.
//! * **`cast_tys`** — `(op, result, SOURCE, DESTINATION)`. A cast has **two**
//!   types and both are semantic input, which is one more than the eighth
//!   chain's `binop_tys` has to carry:
//!   - the DESTINATION is the modulus (`ir_trunc_int` returns `ir_wrap dw x`);
//!   - the SOURCE decides FAULT versus VALUE (the guard is `ir_nat_leb dw sw`),
//!     so it is not "the operand's type, already implied".
//!
//! Measured on `clean-kernel` itself at this HEAD, with the sealed lane-8
//! stage1 trustc (`seal_driver.sh verify` OK and `guard` PASS before every run),
//! three clean non-incremental builds plus a negative control, all four with a
//! byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("5 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 2 REAL marker lines
//! interpreter differential   agreed  on 5 sampled inputs
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:607c1d96…
//! flip event                 FIRED, codegen seam, same lineage, flipped_so_far=195
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! ```
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst.cast`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_gc_module` is hand-transcribed: this makes an incorrect
//! transcription FAIL, it does not make a correct one automatic. And nothing
//! here says `ir_wrap ir_d32` is Rust's `as u32` — see the module doc of
//! `spec/core_spec/eval_ir_trunc.rs`.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn get_char_val_trunc_proved_module_matches_the_emitted_artifact() {
    let text = fixture("get_char_val_trunc.trust-ir.txt");
    assert!(
        text.starts_with(
            "rustcc fn @env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}("
        ),
        "the fixture must be the get_char_val closure itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_trunc.rs", "const SRC_IR_GC_B"),
        "def ir_gc_b",
    );

    // COVERAGE DENOMINATOR. On this body it is not a formality: without the
    // cast lanes BOTH sides of every comparison below are empty maps.
    assert_eq!(
        emitted.blocks,
        vec![0u32],
        "ONE block, bb0; parser found {:?}",
        emitted.blocks
    );
    assert_eq!(
        emitted.casts,
        BTreeMap::from([(0, vec![("trunc".to_string(), 2, 1)])]),
        "exactly one cast, `trunc` of %1 into %2: {:?}",
        emitted.casts
    );
    assert_eq!(
        emitted.cast_tys,
        BTreeMap::from([(
            0,
            vec![(
                "trunc".to_string(),
                2,
                "uint64".to_string(),
                "uint32".to_string()
            )]
        )]),
        "…from u64 DOWN to u32. Both widths are semantic input and this is the lane the cast \
         forced: {:?}",
        emitted.cast_tys
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![2u32])]),
        "the body returns %2 — the TRUNCATED value, not %1 the argument: {:?}",
        emitted.rets
    );
    assert!(
        emitted.icmps.is_empty()
            && emitted.binops.is_empty()
            && emitted.binop_tys.is_empty()
            && emitted.icmp_tys.is_empty()
            && emitted.condbrs.is_empty()
            && emitted.cases.is_empty()
            && emitted.branches.is_empty()
            && emitted.consts.is_empty()
            && emitted.int_consts.is_empty()
            && emitted.agg_consts.is_empty()
            && emitted.loads.is_empty()
            && emitted.extracts.is_empty()
            && emitted.param_blocks.is_empty()
            && emitted.const_tys.is_empty()
            && emitted.edge_args.is_empty()
            && emitted.block_params.is_empty(),
        "this body compares nothing, computes nothing, branches nowhere, materializes no \
         constant, reads no field and loads nothing: it is one cast and a return"
    );
    assert_eq!(emitted.default, u32::MAX, "no switch");
    assert_eq!(
        emitted.switch_on,
        u32::MAX,
        "…and therefore no scrutinee: {}",
        emitted.switch_on
    );

    // The two parameters, read off the emitted entry-block signature. They are
    // not in `Cfg` — `parse_emitted` treats the entry block's parameter list as
    // the function signature — so they are asserted here against the text and
    // against the registered `IRFunc`, in both directions.
    assert!(
        text.contains("bb0(%0: (), %1: u64):"),
        "TWO parameters: the closure environment — whose emitted type is the UNIT type, because \
         this closure captures nothing — and the u64 operand"
    );
    let func = clean_block_sources("eval_ir_trunc.rs", "const SRC_IR_GC_FUNC");
    assert!(
        func.contains("IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0"),
        "the registered IRFunc must bind the same two parameter ids in the same order: {func}"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block BOOL constants differ: emitted {:?} vs Clean {:?}",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}",
        emitted.int_consts, clean.int_consts
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE constants differ: emitted {:?} vs Clean {:?}",
        emitted.agg_consts, clean.agg_consts
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted {} vs Clean {}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.param_blocks, clean.param_blocks,
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_trunc.rs", "const SRC_IR_GC_FUNC"),
        "get_char_val_trunc",
    );
    assert_lanes(&emitted, &clean, "get_char_val_trunc");
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
    assert!(
        !text.contains("call @func."),
        "the body must make no calls — that is what makes its reachable closure bodyful, and it \
         is the A0 criterion Level::is_zero fails"
    );
}

/// **The two new lanes are not decoration: without them the perturbations are
/// invisible.** This test is the negative half — it constructs four drifted
/// transcriptions and checks that every PRE-EXISTING lane still compares equal
/// on them, so the lanes are load-bearing by measurement rather than by
/// argument.
#[test]
fn get_char_val_trunc_the_new_lanes_catch_what_every_old_lane_misses() {
    let emitted = parse_emitted(&fixture("get_char_val_trunc.trust-ir.txt"));
    let head = "rustcc fn @x(functy.540) {\nbb0(%0: (), %1: u64):\n";

    // Drift 0: the cast DELETED. Before the cast lanes existed, this was the
    // whole body and the whole gate saw nothing.
    let no_cast = parse_emitted(&format!("{head}    ret %2\n}}\n"));
    assert_eq!(emitted.blocks, no_cast.blocks);
    assert_eq!(
        emitted.rets, no_cast.rets,
        "even the RET lane cannot see it"
    );
    assert_eq!(emitted.binops, no_cast.binops);
    assert_eq!(emitted.icmps, no_cast.icmps);
    assert_eq!(emitted.loads, no_cast.loads);
    assert_eq!(emitted.extracts, no_cast.extracts);
    assert_ne!(
        emitted.casts, no_cast.casts,
        "…and the CAST lane must: the body's only computation is gone"
    );

    // Drift 1: zext instead of trunc — an embedding instead of a discard.
    let as_zext = parse_emitted(&format!(
        "{head}    %2 = zext u64 %1 to u32\n    ret %2\n}}\n"
    ));
    assert_eq!(emitted.rets, as_zext.rets, "the RET lane cannot see it");
    assert_eq!(emitted.blocks, as_zext.blocks);
    assert_ne!(emitted.casts, as_zext.casts, "…and the CAST lane must");

    // Drift 2: the DESTINATION width. `trunc u64 -> u16` is a different modulus
    // and is invisible to the operand lane.
    let narrow_dst = parse_emitted(&format!(
        "{head}    %2 = trunc u64 %1 to u16\n    ret %2\n}}\n"
    ));
    assert_eq!(
        emitted.casts, narrow_dst.casts,
        "the CAST OPERAND lane cannot see a width change"
    );
    assert_eq!(emitted.rets, narrow_dst.rets);
    assert_ne!(
        emitted.cast_tys, narrow_dst.cast_tys,
        "…and the CAST TYPE lane must: uint32 vs uint16 destination"
    );

    // Drift 3: the SOURCE width, changed independently of the destination.
    // `trunc u16 -> u32` is `ir_width_fault` where the artifact is a value.
    let narrow_src = parse_emitted(&format!(
        "{head}    %2 = trunc u16 %1 to u32\n    ret %2\n}}\n"
    ));
    assert_eq!(
        emitted.casts, narrow_src.casts,
        "the CAST OPERAND lane cannot see it either"
    );
    assert_ne!(
        emitted.cast_tys, narrow_src.cast_tys,
        "…and the CAST TYPE lane must, on the SOURCE side, independently of the destination"
    );
    assert_ne!(
        narrow_src.cast_tys, narrow_dst.cast_tys,
        "the two width drifts are distinguishable from EACH OTHER, so the lane carries both \
         widths rather than one conflated token"
    );

    // Drift 4: the OPERAND. Casting %0 — the closure environment — instead of
    // %1 is a different function and changes no type.
    let wrong_operand = parse_emitted(&format!(
        "{head}    %2 = trunc u64 %0 to u32\n    ret %2\n}}\n"
    ));
    assert_eq!(
        emitted.cast_tys, wrong_operand.cast_tys,
        "the TYPE lane cannot see an operand swap, which is why it is a SEPARATE lane and not a \
         replacement for the operand"
    );
    assert_eq!(emitted.rets, wrong_operand.rets);
    assert_ne!(
        emitted.casts, wrong_operand.casts,
        "…and the CAST lane must"
    );

    // Drift 5: the RESULT id the cast binds. The eighth chain's `rets` lane
    // catches the return side of this; the cast lane catches the binding side.
    let wrong_result = parse_emitted(&format!(
        "{head}    %3 = trunc u64 %1 to u32\n    ret %2\n}}\n"
    ));
    assert_eq!(emitted.rets, wrong_result.rets);
    assert_ne!(emitted.casts, wrong_result.casts);
    assert_ne!(emitted.cast_tys, wrong_result.cast_tys);
}

/// **`usize` is left UNRESOLVED on purpose, and the gate refuses it loudly.**
///
/// The two unchained `zext` bodies emit `zext u32 %1 to usize`. Resolving
/// `usize` to a width is a target assumption, so `norm_emitted_ty` returns the
/// `?`-prefixed token and `assert_lanes` refuses it on BOTH sides. Without that,
/// a later zext chain would compare an unresolved token against a resolved one
/// and get a lane difference nobody can read — or, worse, two unresolved tokens
/// against each other and a silent pass.
#[test]
fn get_char_val_trunc_usize_is_unresolved_rather_than_assumed() {
    let with_usize = parse_emitted(
        "rustcc fn @x(functy.108) {\nbb0(%0: struct.317):\n    %1 = extractfield u32 %0, 0\n    \
         %2 = zext u32 %1 to usize\n    ret %2\n}\n",
    );
    let tys = with_usize
        .cast_tys
        .get(&0)
        .expect("the zext must be in the cast type lane");
    assert_eq!(tys.len(), 1);
    assert_eq!(tys[0].0, "zext");
    assert_eq!(tys[0].2, "uint32", "the SOURCE resolves");
    assert_eq!(
        tys[0].3, "?usize",
        "the DESTINATION does NOT — and it is the loud `?` token, not a dropped field and not a \
         guessed 64"
    );
}

// The A0/A6 EVIDENCE gates — the measured row, the re-derived census, the two
// unchained `zext` siblings, and the recorded cast-semantics answer.
#[path = "get_char_val_trunc_evidence.rs"]
mod evidence;
