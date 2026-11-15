// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_lzd` — the FIVE-BODY module, registered. No authored function in it.**
//!
//! Link 4 for the designated target holds today over `ir_lzb_module`, whose
//! function 1 is an AUTHORED model of `<level::LevelArc as Deref>::deref`.
//! That model is the chain's residual. This stage registers the module that
//! retires it: `level::Level::is_zero` together with the REAL bodies of every
//! function it can reach.
//!
//! Five functions, from TWO compiler artifacts joined by the callee sidecar's
//! own manifest:
//!
//! | canonical | body | source |
//! |---|---|---|
//! | 0 | `level::Level::is_zero` | crate module |
//! | 1 | `<level::LevelArc as std::ops::Deref>::deref` | crate module |
//! | 2 | `Option::<Arc<Level>>::as_deref` | sidecar bundle |
//! | 3 | `Option::<&Level>::expect` | sidecar bundle |
//! | 4 | `<Arc<Level> as Deref>::deref` | sidecar bundle |
//!
//! NINE calls, every one naming a canonical index this module defines.
//! `ir_lz_module` was stuck at the deref it did not define; `ir_lzc_module`
//! one call deeper at `as_deref`; this module is stuck nowhere, and the five
//! `ir_func_find` equations below are where that stops being a sentence.
//!
//! # What is registered and what is NOT
//!
//! Registered: the 34 minted declarations, the equation that keeps `ir_lz`
//! byte-frozen, and the five resolution facts.
//!
//! NOT registered, and not claimed anywhere in this file: A4 or A5 over
//! `ir_lzd_module`. A module being closed is not a module being correct. The
//! authored `ir_lzb_deref` stays the chain's residual until those two are
//! proved here, and `docs/CRYSTAL_STATUS.md` says so.
//!
//! # What A4 needs, traced out of the emitted code rather than guessed
//!
//! A4 is universally quantified over a heap, so it needs a witness heap for
//! the DERIVED path, and the derived bodies say exactly what shape that heap
//! has. `as_deref` loads `enum.1` — `Option<Arc<Level>>` — from its receiver.
//! Then, in the Some arm, it geps that SAME receiver by ZERO, borrows it,
//! round-trips the borrow through an `insertfield`/`extractfield` pair, copies
//! it, and calls `<Arc<Level>>::deref` with it:
//!
//! ```text
//!     %6  = const i64 0
//!     %7  = gep inbounds i8, ptr %0, %6      <- the same address
//!     %8  = borrow %7
//!     %9  = const enum.0 { 1, 0 }
//!     %10 = insertfield enum.0 %9, 1, %8
//!     %11 = extractfield ptr %10, 1
//!     %12 = copy ptr %11
//!     %13 = call @func.2(%12)
//! ```
//!
//! and `<Arc<Level>>::deref`'s first instruction is `load struct.3, ptr %0` —
//! it reads an `Arc` out of it.
//!
//! So ONE heap address is read as an `Option<Arc<Level>>` by one body and as
//! an `Arc` by the next. That is the null-pointer NICHE, and it is shown here
//! by the emitted code rather than inferred from the Rust type. A witness heap
//! that stores a plain aggregate at that address satisfies one reader and not
//! the other.
//!
//! This module mints `IRModule.mkv` and carries a FOUR-row encodings table:
//! two niche rows for the two `Option`s, two wrapper rows for `Arc` and
//! `NonNull`. The sentence that stood here saying it mints `IRModule.mk` and
//! that the `mkv` arm was "still not taken" is superseded — the arm is taken,
//! and the rows are derived rather than typed. What the table does NOT settle
//! is A4: an encodings table makes the machine read the emitted program the way
//! the compiler laid it out, which is a precondition for the theorem, not the
//! theorem.
//!
//! # The row that arm needs IS derivable — a RETRACTION, with its cause
//!
//! This file said, and the status page said with it, that A4 was "blocked on a
//! layout fact the artifact does not carry" and that the next brick was on the
//! TRUST side. **That was FALSE, and it was pushed.** The retraction matters
//! less than the cause, so the cause is recorded first: it was read out of the
//! sibling checkout `$HOME/trust-ir`, which is at a DIFFERENT revision
//! from the one this workspace pinned at the time
//! (`4803c40dd3b71fcdf102827d9b66b9e59f4483af`; moved to
//! `6a7fe3525a93467542a10dfd4bf336499fa121dc`, trust-ir binary v41, on
//! 2026-09-14 — the trap is unchanged).
//! `CLAUDE.md` documents that exact trap three times for the `../trust` clone —
//! fetching does not move HEAD, and a sibling checkout is not the pinned
//! revision — and it binds `trust-ir` the same way. Read the vendored source
//! under `~/.cargo/git/checkouts`, not the sibling.
//!
//! At the PINNED revision `trust_ir::ty::EnumDef` carries
//! `layout: Option<EnumLayoutDescriptor>`, and `EnumTagEncoding::Niche` has
//! precisely the fields `IREnc.nicheptr` needs. The committed bundle carries
//! one, measured with `a2project --layouts`:
//!
//! ```text
//!   enum.0 core::option::Option  Niche { untagged_variant: 1,
//!       niche_variants_start: 0, niche_variants_end: 0, niche_start: 0,
//!       niche_offset: 0, niche_ty: U64 }, size: 8, align: 8,
//!       variant_field_offsets: [[], [0]]
//!   enum.1 core::option::Option  (the same)
//! ```
//!
//! Read: eight bytes, niche-encoded, the untagged variant is Some (1), the
//! niche variant is None (0), None is the ZERO word, and the Some payload sits
//! at offset 0. That is `IREnc.nicheptr k 0 1 <payload>` directly.
//!
//! The second half of the earlier claim is retracted too. It said the derived
//! body was "internally inconsistent" because it reads field 0 of the enum as
//! a tag AND address+0 as an `Arc`. Both readings are correct and the
//! descriptor is why: under the niche the Arc's pointer word IS the
//! discriminant, so one word is honestly both. The inconsistency was only with
//! trust-ir's CANONICAL tagged-union layout, which a producer-provided
//! descriptor overrides — which is exactly what "mapping a rustc-laid-out enum
//! onto this canonical shape is a producer-side concern" means, and the
//! producer did it and recorded it.
//!
//! The first of those steps is DONE and its output is in
//! `ir_lzd.core.prov.json`: reader A derives the rows from the descriptors and
//! refuses clause by clause.
//!
//! ```text
//!   {"canonical": 1, "crate_id": 0, "kind": "nicheptr",
//!    "none_variant": 0, "some_variant": 1, "payload": "(ptr)"}
//!   {"canonical": 2, "crate_id": 1, "kind": "nicheptr",
//!    "none_variant": 0, "some_variant": 1, "payload": "(struct 0)"}
//! ```
//!
//! Which is `IREnc.nicheptr 1 0 1 IRTy.ptr_` and
//! `IREnc.nicheptr 2 0 1 (IRTy.struct_ ir_d0)`. The core digest does not move:
//! the derivation is additive to the provenance and touches no term.
//!
//! # And the refusal beside them is the bigger finding
//!
//! `Level` ITSELF is niche-encoded, and `IREnc` cannot express it. Reader A
//! refuses its row with every failing clause named, and rustc's descriptor for
//! it reads:
//!
//! ```text
//!   enum.6 Level  Niche { untagged_variant: 4, niche_variants_start: 0,
//!       niche_variants_end: 3, niche_start: 3, niche_offset: 0,
//!       niche_ty: U64 }, size: 40, align: 8,
//!       variant_field_offsets: [[], [8], [8, 16], [8, 16], [0]]
//! ```
//!
//! Five variants, four of them niched from 3, `Param` untagged with its
//! payload at offset 0. `IREnc.nicheptr` is two-variant only, so no row can be
//! derived and none is invented.
//!
//! WHAT THAT DOES AND DOES NOT SAY. It does NOT say the existing chains are
//! wrong, and the descriptor is partly why: the field offsets `is_zero` geps
//! to — 8 and 16 for `Max` and `IMax` — are exactly this descriptor's
//! `variant_field_offsets`, so the payload addressing agrees. What is NOT
//! modelled is the DISCRIMINANT: the machine reads field 0 of a canonically
//! tagged value, every witness heap in this programme spells a `Level` as
//! `ir_var <tag> <payload>`, and rustc computes the discriminant from a niche
//! at offset 0 starting at 3. That gap is a LAYOUT OBLIGATION of the same
//! family as the Arc header offset already in the ledger, it is older than
//! this chain and is inherited by `ir_lz`, `ir_lzb` and `ir_lzc` alike, and it
//! is recorded here because this is where it was first measured rather than
//! assumed.
//!
//! So A4 still needs, in order: the minter taking the `IRModule.mkv` arm when
//! the table carries rows, a witness heap written against the niche, and the
//! activation. None of that is registered here.

use super::{SpecError, Specification};

/// Reader A's minted script for the five-body module.
const MINTED_IR_LZD: &str = include_str!("generated/ir_lzd.defs.txt");

/// One rationale per minted declaration, in the script's own order.
const MINTED_IR_LZD_DOCS: &[&str] = &[
    "ir_lzd_tlevel: the Level enum, crate enum id 6 in dump-sidecar-O3 -- the same type ir_lz_tlevel and ir_lzc_tlevel name, at a DIFFERENT crate id because this chain was projected from a different dump. That the aliases denote one type is not asserted here; it falls out of ir_lzd_func0_is_the_lz_mint, which unfolds both. DerivedProved, zero axiom_deps.",
    "ir_lzd_topt_ref: `Option<&Level>` -- the type `expect` takes and `as_deref` returns. NEW in this chain: no earlier module carried a second aggregate, because no earlier module carried a body from a second artifact. DerivedProved, zero axiom_deps.",
    "ir_lzd_topt_arc: `Option<Arc<Level>>` -- the type `as_deref` LOADS out of its receiver. Distinct from ir_lzd_topt_ref and the distinction is load-bearing: as_deref's whole job is to turn one into the other. DerivedProved, zero axiom_deps.",
    "ir_lzd_tarc: `alloc::sync::Arc` -- the three-field struct `<Arc<T>>::deref` loads. Its field 0 is the NonNull below; the ArcInner header offset the deref geps by is a CONSTANT in the body, not a field of this type. DerivedProved, zero axiom_deps.",
    "ir_lzd_tnonnull: `core::ptr::NonNull` -- field 0 of the Arc, a transparent pointer wrapper. The deref extractfields it, copies it, and extractfields the pointer out of it, which is why both this and ir_lzd_tarc are named. DerivedProved, zero axiom_deps.",
    "ir_lzd_g0: the `expect` message, promoted by the producer to a module-table global -- 34 int_ bytes that ARE `live LevelArc must contain a level`. Identical content to ir_lzc_g0 at a different crate id (1055 here, 4557 in the control dump), which is the numbering difference the two readers are checked across. Its canonical id 0 IS its address, which is why every heap over this module must start above it. DerivedProved, zero axiom_deps.",
    "ir_lzd_b0: entry of the root -- load the Level, extractfield the u8 discriminant, four-case switch with IMax on the default edge. Byte-identical to ir_lz_b0 under the prefix. DerivedProved, zero axiom_deps.",
    "ir_lzd_b1: Zero => true, br to the join b6. DerivedProved, zero axiom_deps.",
    "ir_lzd_b2: Succ => false, br b6. DerivedProved, zero axiom_deps.",
    "ir_lzd_b3: Param => false, br b6. DerivedProved, zero axiom_deps.",
    "ir_lzd_b4: Max -- gep to both children at 8 and 16, call the deref on the first, call the root recursively, and condbr on the answer. The first of the two blocks that make this body branching. DerivedProved, zero axiom_deps.",
    "ir_lzd_b5: the switch DEFAULT edge, which is IMax -- gep to the second child at 16 only, deref, recurse, br b6. IMax's first child is not consulted, which is the asymmetry ir_lz's cost equations are about. DerivedProved, zero axiom_deps.",
    "ir_lzd_b6: the outer join, one bool block parameter, ret. DerivedProved, zero axiom_deps.",
    "ir_lzd_b7: Max's true leg -- deref and recurse on the SECOND child, br the short-circuit join. DerivedProved, zero axiom_deps.",
    "ir_lzd_b8: Max's false leg -- the short circuit, const false, br b9 without touching the second child. DerivedProved, zero axiom_deps.",
    "ir_lzd_b9: the short-circuit join, one bool parameter, br b6. DerivedProved, zero axiom_deps.",
    "ir_lzd_func: function 0 of the module -- the designated target, ten blocks, entry b0. The equation below says it is ir_lz_func and not merely like it. DerivedProved, zero axiom_deps.",
    "ir_lzd_f1_b0: the deref's one block, six instructions: `call 2` into as_deref, globaladdr 0 for the message, const u64 34 for its length, ptrfromparts building the &str, `call 3` into expect, ret. In ir_lzc both calls went to DECLARATIONS and the module halted stuck at the first; here both resolve, and the two resolution equations below are the proof of it. DerivedProved, zero axiom_deps.",
    "ir_lzd_f1_func: function 1 -- the deref, ONE parameter, entry b0. This is the body the authored ir_lzb_deref stands in for, registered as the compiler emitted it. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_b0: as_deref's entry -- ALLOCA the return slot, load the `Option<Arc<Level>>` receiver, extractfield its u8 tag, widen it, and switch. The first alloca in any crystal chain: the return-slot family Phase-B's B0 lemmas were proved for. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_b1: the switch's unreachable default. The producer emits it for a two-variant enum whose tag it has just matched exhaustively. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_b2: None => store the none-constant into the return slot and br the exit. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_b3: Some => gep by zero, BORROW the payload, build the Some, extractfield the pointer, COPY it, and `call 4` into <Arc<T>>::deref. The borrow and the copy are the two IRInst constructors Phase-B added for this closure and that nothing the THIR lowerer emits uses. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_b4: the exit -- load the return slot and ret it. The other half of the alloca/store/load/ret shape. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_b5: the Some continuation -- wrap the deref's result as Some and store it into the slot. DerivedProved, zero axiom_deps.",
    "ir_lzd_f2_func: function 2 -- as_deref, six blocks, one parameter. A DECLARATION in ir_lzc and the place that module went stuck; a body here. DerivedProved, zero axiom_deps.",
    "ir_lzd_f3_b0: expect's entry -- extractfield the u8 tag, widen it, switch. Takes the Option by value and the message as a fat pointer, which is why its function has TWO parameters. DerivedProved, zero axiom_deps.",
    "ir_lzd_f3_b1: the unreachable default. DerivedProved, zero axiom_deps.",
    "ir_lzd_f3_b2: *** THE PANIC PATH, AND IT IS NOT A CALL. *** None => const false, ASSERT it, unreachable. The sidecar's walk stops at a diverging panic terminal and lowers it to this shape instead of a call to core::option::expect_failed, which is why this module has no callee outside itself. That the assert is unreachable is not claimed here -- it is the semantic no-escape obligation, and ir_lzb_panic_path_is_unreachable is its proof for the authored chain. DerivedProved, zero axiom_deps.",
    "ir_lzd_f3_b3: Some => extractfield the pointer, COPY it, ret. The whole of the success path. DerivedProved, zero axiom_deps.",
    "ir_lzd_f3_func: function 3 -- expect, four blocks, TWO parameters. A DECLARATION in ir_lzc, never reached there because the frame was already stuck one call earlier. DerivedProved, zero axiom_deps.",
    "ir_lzd_f4_b0: <Arc<Level>>::deref's one block -- load the Arc, extractfield the NonNull, copy it, extractfield the pointer, const 16, GEP by it, BORROW the result, ret. The 16 is the ArcInner header, and it is the compiler's own constant: the authored ir_lzb_deref geps by the same sixteen and scripts/crystal_lzd_readiness.py refuses unless the recomputed offset, this emitted constant and the model's constant all agree. DerivedProved, zero axiom_deps.",
    "ir_lzd_f4_func: function 4 -- <Arc<Level>>::deref, one block, one parameter. Reached only from as_deref, and present in NO crate-module closure: it is the one body the sidecar derives that the crate module's own call graph never names. DerivedProved, zero axiom_deps.",
    "ir_lzd_e0: *** THE FIRST ENCODINGS ROW IN THIS PROGRAMME. *** `Option<&Level>` is niche-encoded: eight bytes, no separate tag, the ZERO word is None and any other word is Some carrying a pointer. DERIVED by reader A from the artifact's own EnumLayoutDescriptor and refused clause by clause -- IREnc's rule is that a hand-typed row is never a pin. Without it the machine would read this type under trust-ir's CANONICAL tagged-union layout, which is a different program from the one the compiler emitted. DerivedProved, zero axiom_deps.",
    "ir_lzd_e1: the same for `Option<Arc<Level>>`, whose Some payload is the Arc itself -- which is why as_deref can gep its receiver by ZERO and hand that address to <Arc<Level>>::deref: under the niche the Arc's pointer word IS the discriminant, so one word is honestly both. This row is what makes those two readings of one address consistent instead of contradictory. DerivedProved, zero axiom_deps.",
    "ir_lzd_e2: *** THE ROW WITHOUT WHICH THE DERIVED PATH HAS NOTHING TO EXTRACT FROM. *** `alloc::sync::Arc` is three fields of which only slot 0 is non-ZST, so its byte image is ONE pointer word -- and `<Arc<Level>>::deref`'s first instruction is `extractfield struct.0 %1, 0`. Without this row the load hands that instruction a bare word, which is not an aggregate, and the derived chain is stuck for a reason that has nothing to do with the program. DERIVED by reader A from the artifact's own StructDefs: a field counts as a ZST only when its own StructDef.size is Some(0), measured, and a struct with two non-ZST fields is REFUSED rather than having one of them picked. `ir_enc_matches` keys on (KIND, id), which is why this row at canonical 0 and ir_lzd_e0's niche row at canonical 1 cannot be confused with each other or with the struct/enum of the other number. DerivedProved, zero axiom_deps.",
    "ir_lzd_e3: the same for `core::ptr::NonNull` -- one field, the pointer itself, repr(transparent). It is the payload type of ir_lzd_e2, so the view at an Arc word chains Arc -> NonNull -> ptr, three deep; `ir_view_ty`'s fuel is the row COUNT, which is four, so the chain terminates with fuel to spare and never falls back to the identity. DerivedProved, zero axiom_deps.",
    "ir_lzd_module: *** THE MODULE WITH NO AUTHORED FUNCTION IN IT, AND THE FIRST `IRModule.mkv`. *** IRModule.mkv over five functions, one global and FOUR derived encodings rows -- two niche rows for the two Options, two wrapper rows for Arc and NonNull -- the first module in this programme minted through the `mkv` arm rather than `mk`. That arm is ADDITIVE and that is the whole conservativity argument: `ir_mod_encs` sends every `mk` module to the EMPTY table, where the encoding-aware load iota-reduces to the identity, so no term any earlier chain minted can move. Every function is the compiler's own emitted body -- two from the crate module, three derived by the callee sidecar from their monomorphized upstream MIR. Nothing here is a model of anything. What this does NOT say is that the module computes what Level::is_zero computes: that is A4, it is not proved in this file, and until it is, link 4 for the designated target still rests on ir_lzb_module and its authored deref. DerivedProved, zero axiom_deps.",
];

/// A `Nat` term for `k`, built from atom-pool numerals only.
///
/// The EvalIr bundle declares `ir_d0`..`ir_d63` EXCEPT `ir_d32`, which is
/// chain-owned, and nothing above 63 at all — so a probe above the pool has to
/// be a sum. Thirty is the step: it is in the pool, and `k mod 30` never lands
/// on 32.
fn numeral(k: u32) -> String {
    let mut out = format!("ir_d{}", k % 30);
    for _ in 0..(k / 30) {
        out = format!("(Nat.add {out} ir_d30)");
    }
    out
}

/// The `Max(Zero, Zero)` run's initial configuration, spelled exactly as
/// `ir_lzd_max_zz_returns_true_at_107` spells it, so a witness can CITE that
/// run instead of recomputing it (`eval_ir_stack_axes.rs`).
pub(super) fn lzd_maxzz_init() -> String {
    format!("(ir_init ir_lzd_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d40)) {HEAP_MAXZZ} ir_d63)")
}

/// [`numeral`], for the same reason.
pub(super) fn lzd_numeral(k: u32) -> String {
    numeral(k)
}

impl Specification {
    /// Register the five-body module and the facts that make it closed.
    ///
    /// Ordering: this stage runs AFTER `add_eval_ir_lz_module`, because
    /// `ir_lzd_func0_is_the_lz_mint` names `ir_lz_func`.
    ///
    /// # Errors
    /// Returns `SpecError` if the minted script and the rationale table
    /// disagree in length, or if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_lzd_module(&mut self) -> Result<(), SpecError> {
        let minted: Vec<&str> = MINTED_IR_LZD
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect();
        if minted.len() != MINTED_IR_LZD_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_lzd script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_LZD_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_LZD_DOCS) {
            self.add_recursive_def(line, doc)?;
        }

        // *** NO `ir_lzd_func0_is_the_lz_mint` EQUATION, AND THE ABSENCE IS
        // *** A MEASUREMENT. ***
        //
        // `ir_lzc` registers `ir_lzc_func0_is_the_lz_mint : Eq IRFunc
        // ir_lzc_func ir_lz_func`, and the obvious move here was the same
        // equation one chain over. It was written, and the KERNEL REFUSED IT:
        //
        //     Type mismatch: expected ir_lzd_func = ir_lz_func,
        //     got ir_lz_func = ir_lz_func
        //
        // The kernel is right and the equation is FALSE. The two functions are
        // the same FUNCTION and not the same TERM, because a type alias
        // carries the artifact's crate aggregate id and the two chains were
        // projected from different dumps:
        //
        //     def ir_lz_tlevel  : IRTy := IRTy.enum_ ir_d3   (047ebd051 dump; ir_d2 on the control dump)
        //     def ir_lzc_tlevel : IRTy := IRTy.enum_ ir_d3   (047ebd051 dump; ir_d2 on the control dump)
        //     def ir_lzd_tlevel : IRTy := IRTy.enum_ ir_d6   (dump-sidecar-O3)
        //
        // Every block of this root is otherwise byte-identical to `ir_lz`'s
        // under the prefix — measured, all ten plus the function — so the
        // difference is exactly that numeral and nothing else.
        //
        // WHAT THIS TELLS YOU, and it is worth more than the equation would
        // have been: the CORE module is dump-independent (it is written in
        // canonical indices, which is why reader A on one dump and reader B on
        // another agree on it), and the MINTED module is NOT. `Tags::alias_defs`
        // writes the crate id into the spec, so a producer re-interning an
        // enum yields a different minted term for the same program. That is
        // the `aggregate-id` blind slot's consequence, stated by a kernel
        // refusal rather than by prose.
        //
        // `ir_lz` is untouched either way: nothing in this file names it.

        for (name, idx, tgt, doc) in [
            (
                "ir_lzd_find0_is_the_root",
                "ir_d0",
                "(IROption.some IRFunc ir_lzd_func)",
                "ir_lzd_find0_is_the_root: id 0 resolves to the designated target itself -- the recursive call ir_lz makes three times. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzd_find1_is_the_deref",
                "ir_d1",
                "(IROption.some IRFunc ir_lzd_f1_func)",
                "ir_lzd_find1_is_the_deref: id 1 resolves to the deref's own emitted body. Over ir_lz_module this returned none and ir_call_exec halted stuck. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzd_find2_is_as_deref",
                "ir_d2",
                "(IROption.some IRFunc ir_lzd_f2_func)",
                "ir_lzd_find2_is_as_deref: *** THE ONE ir_lzc COULD NOT SAY. *** Over ir_lzc_module id 2 is a DECLARATION and ir_func_find returns none, which is exactly where that chain halts stuck. Here it returns the body the callee sidecar derived from Option::<T>::as_deref's monomorphized MIR. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzd_find3_is_expect",
                "ir_d3",
                "(IROption.some IRFunc ir_lzd_f3_func)",
                "ir_lzd_find3_is_expect: id 3 resolves to expect's body. A declaration in ir_lzc, and never reached there because the frame was already stuck at id 2. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzd_find4_is_arc_deref",
                "ir_d4",
                "(IROption.some IRFunc ir_lzd_f4_func)",
                "ir_lzd_find4_is_arc_deref: id 4 resolves to <Arc<Level>>::deref. It appears in no crate-module closure at all -- the crate module carries as_deref as a bodyless declaration, so nothing there reaches this function; it is reachable only once as_deref HAS a body. DerivedProved, zero axiom_deps.",
            ),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} : Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs ir_lzd_module) {idx}) {tgt} := Eq.refl (IROption IRFunc) {tgt}"
                ),
                doc,
            )?;
        }
        Ok(())
    }

    /// The step counts that say this module RUNS where every earlier one
    /// halted.
    ///
    /// MUST follow `add_eval_ir_steps`: these are the only `ir_lzd`
    /// declarations naming `ir_steps` and `ir_config_outcome`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check. A wrong step count fails HERE, by computation.
    pub(super) fn add_eval_ir_lzd_steps(&mut self) -> Result<(), SpecError> {
        // `ir_d63`, not `ir_d64`, and the difference is a FAIL-OPEN that was
        // live here: this bundle declares `ir_d0`..`ir_d63` (except the
        // chain-owned `ir_d32`) and NOT `ir_d64`. The two running equations
        // below shipped naming `ir_d64` on 2026-09-10 and passed, because an
        // identifier the environment does not declare becomes a free variable
        // when it appears in a declaration's TYPE — in VALUE position the same
        // spelling is a hard `Unknown identifier`. They were therefore true of
        // an arbitrary counter rather than of 64, which is a weaker statement
        // than the one written, arrived at silently. Named here because the
        // general hole is not this chain's to close.
        let init = format!(
            "(ir_init ir_lzd_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d40)) {HEAP_MAXZZ} ir_d63)"
        );
        let running = "IROutcome.fuel_out";
        for (name, n, doc) in [
            (
                "ir_lzd_max_running_at_9",
                "ir_d9",
                "ir_lzd_max_running_at_9: *** THE DERIVED MODULE RUNS WHERE EVERY EARLIER ONE HALTED. *** `ir_config_outcome` reads fuel_out off a RUNNING configuration and the real outcome off a halted one, so this says the machine has NOT halted after nine steps on Max(Zero, Zero). Nine is exactly where ir_lzc dies: ir_lzc_max_stuck_at_9 computes `halted (stuck no_func)` there, because the deref frame's first instruction is `call 2` into a DECLARATION. Here that call resolves to the body the callee sidecar derived, the frame is pushed, and the machine keeps going. The number is computed by the kernel; an off-by-one is a build failure. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzd_max_running_at_10",
                "ir_d10",
                "ir_lzd_max_running_at_10: and one step further, which is the first instruction of a body no chain before this one could execute at all -- as_deref's ALLOCA, the return slot. Registered beside the one above because a halted configuration is a FIXED POINT of ir_steps: an `= halted` equation at any N is implied by halting earlier, so only the running direction pins depth. What is NOT claimed here is that the run ever returns: this module's Max arm reads an `Option<Arc<Level>>` out of the heap, and HEAP_MAXZZ holds a bare pointer at that address because it was written for a module whose deref was a seven-node MODEL. The witness heap for the DERIVED path is A4's work and is not in this file. DerivedProved, zero axiom_deps.",
            ),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} : Eq IROutcome (ir_config_outcome (ir_steps {n} ir_lzd_module {init})) {running} := Eq.refl IROutcome {running}"
                ),
                doc,
            )?;
        }
        // TEMPORARY MEASUREMENT PROBE — remove before commit.
        // ── WHAT THE ENCODINGS TABLE MAKES THE MACHINE SEE ───────────────
        //
        // Four `Eq.refl`s at an ABSTRACT base, one per row. They are the
        // negative witnesses the derivation cannot supply: the derivation says
        // a row is well formed, these say the row FIRES, at the type the
        // emitted code actually loads, and produces the aggregate the next
        // instruction extracts from.
        //
        // They also pin the thing that went wrong and was invisible for two
        // commits: `ir_enc_matches` compares a row's key against the number an
        // `IRTy.enum_`/`IRTy.struct_` carries, which is the CRATE id, and the
        // first cut of the derivation keyed on the CANONICAL index. Both
        // numbers exist here, so the mis-keyed table did not read as empty --
        // one row fired at the wrong type and another became self-referential.
        // A row that does not fire is indistinguishable from no row at all
        // unless something states the image, so these state it.
        self.add_recursive_def(
            "def ir_lzd_view_nonnull (b : Nat) : Eq IRStepResult (ir_load_view (ir_mod_encs ir_lzd_module) ir_lzd_tnonnull (IRStepResult.value (IRScalar.ptr_ (Nat.succ b)))) (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)))",
            "ir_lzd_view_nonnull: `core::ptr::NonNull` is ONE field and repr(transparent), so its byte image is the pointer word itself and its VIEW is that word at slot 0 of a one-field spine. Stated at an abstract SUCCESSOR base, because a represented Arc is never the zero word -- that is what NonNull means, and the derived chain's relation carries it structurally rather than as a side condition. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def ir_lzd_view_arc (b : Nat) : Eq IRStepResult (ir_load_view (ir_mod_encs ir_lzd_module) ir_lzd_tarc (IRStepResult.value (IRScalar.ptr_ (Nat.succ b)))) (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.aggv (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) IRScalar.vnil))))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.aggv (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) IRScalar.vnil)))))",
            "ir_lzd_view_arc: *** THE ROW THAT MADE THE DERIVED PATH EXECUTABLE. *** `alloc::sync::Arc` is three fields of which only slot 0 is non-ZST, so one stored pointer word images as a three-slot aggregate whose slot 0 is the NonNull view and whose other two slots are `aggv vnil`, the model's ZST. Without it `<Arc<Level>>::deref`'s first `extractfield` faults `not_agg` -- measured, at step 24 of the Max(Zero,Zero) run, before this row existed. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def ir_lzd_view_optref (b : Nat) : Eq IRStepResult (ir_load_view (ir_mod_encs ir_lzd_module) ir_lzd_topt_ref (IRStepResult.value (IRScalar.ptr_ (Nat.succ b)))) (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil))))",
            "ir_lzd_view_optref: `Option<&Level>` niche-encoded -- a non-zero word is Some at tag 1 carrying the pointer. This is the type `as_deref` RETURNS and `expect` consumes. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def ir_lzd_view_optarc (b : Nat) : Eq IRStepResult (ir_load_view (ir_mod_encs ir_lzd_module) ir_lzd_topt_arc (IRStepResult.value (IRScalar.ptr_ (Nat.succ b)))) (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.aggv (IRScalar.vcons (IRScalar.aggv (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) IRScalar.vnil)))) IRScalar.vnil)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.aggv (IRScalar.vcons (IRScalar.aggv (IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) IRScalar.vnil)))) IRScalar.vnil))))",
            "ir_lzd_view_optarc: *** THE THREE-DEEP CHAIN, IN ONE LOAD. *** `Option<Arc<Level>>` niche-encoded over an Arc payload: the same word is the discriminant AND the Arc, so its Some payload is that word imaged at the Arc's own row, which images it at NonNull's, which bottoms out at the pointer. Three rows deep against a table of four, so `ir_view_ty`'s fuel -- the row COUNT -- is spent to three and never falls back to the identity. A table with fewer rows than its own nesting depth would read as the identity here and the machine would then fault, which is why the fuel is the length and not a constant. DerivedProved, zero axiom_deps.",
        )?;
        // ── THE WHOLE PROGRAM, EXECUTED ──────────────────────────────────
        //
        // Everything above says the machine has not halted yet. This says what
        // it DOES.
        self.add_recursive_def(
            &format!(
                "def ir_lzd_max_zz_returns_true_at_107 : Eq IROutcome (ir_config_outcome (ir_steps {} ir_lzd_module {init})) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))",
                numeral(107)
            ),
            "ir_lzd_max_zz_returns_true_at_107: *** THE FIRST TIME `Level::is_zero` HAS BEEN EXECUTED END TO END WITH NO AUTHORED FUNCTION ANYWHERE IN THE MODULE. *** On Max(Zero, Zero) the derived five-body module returns `true` -- the answer `level_is_zero (Level.max Level.zero Level.zero)` computes -- in exactly 107 steps, through the compiler's own emitted bodies for the deref, `as_deref`, `expect` and `<Arc<Level>>::deref`, and through the module's derived encodings table, which is what makes the ONE pointer word at the child field readable first as an `Option<Arc<Level>>` and then as an `Arc`. ir_lz halted `stuck no_func` at the deref; ir_lzc one call deeper at `as_deref`; ir_lzb needed an AUTHORED deref to get here. This module needs none. The number is computed by the kernel, so an off-by-one is a build failure, and 106 is still running -- the two beside it pin the depth from below. WHAT THIS IS NOT: it is one witness, not A4. A4 quantifies over every represented Level and is not proved in this file. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!(
                "def ir_lzd_max_zz_running_at_106 : Eq IROutcome (ir_config_outcome (ir_steps {} ir_lzd_module {init})) IROutcome.fuel_out := Eq.refl IROutcome IROutcome.fuel_out",
                numeral(106)
            ),
            "ir_lzd_max_zz_running_at_106: and 107 is EXACT -- one step earlier the machine is still running. Registered beside the return because a halted configuration is a fixed point of `ir_steps`, so the `= ret` equation alone would hold at every larger count and pin nothing. Together they say the run takes 107 steps and not fewer. DerivedProved, zero axiom_deps.",
        )?;
        {
            let init = format!(
                "(ir_init ir_lzd_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d40)) {HEAP_IMAXZZ} ir_d63)"
            );
            self.add_recursive_def(
                &format!(
                    "def ir_lzd_imax_zz_at_55 : Eq IROutcome (ir_config_outcome (ir_steps {} ir_lzd_module {init})) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))",
                    numeral(55)
                ),
                "ir_lzd_imax_zz_returns_true_at_55: IMax(Zero, Zero) through the switch DEFAULT edge, which geps to offset 16 ONLY -- the first operand is bound in the cell and never read. One derived deref, 55 steps. Together with the Max witnesses this SOLVES the derived deref's cost: 55 = 7 + D + 6 and 107 = 11 + 2D + 6 + 6 both give D = 42, from two independent runs with different arm counts. The authored model cost 7. DerivedProved, zero axiom_deps.",
            )?;
            self.add_recursive_def(
                &format!(
                    "def ir_lzd_imax_zz_running_at_54 : Eq IROutcome (ir_config_outcome (ir_steps {} ir_lzd_module {init})) IROutcome.fuel_out := Eq.refl IROutcome IROutcome.fuel_out",
                    numeral(54)
                ),
                "ir_lzd_imax_zz_running_at_54: and the count above is EXACT -- one step earlier the machine is still running. DerivedProved, zero axiom_deps.",
            )?;
        }
        {
            let init = format!(
                "(ir_init ir_lzd_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d40)) {HEAP_MAXSZ} ir_d63)"
            );
            self.add_recursive_def(
                &format!(
                    "def ir_lzd_max_sz_at_60 : Eq IROutcome (ir_config_outcome (ir_steps {} ir_lzd_module {init})) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))",
                    numeral(60)
                ),
                "ir_lzd_max_sz_returns_false_at_60: *** THE DERIVED MODULE SHORT-CIRCUITS. *** Max(Succ(Zero), Zero): the first child is not zero, so the answer is false and the SECOND child is never read -- one derived deref, not two, and 60 = 12 + D + 6 with the same D = 42. A module that evaluated both operands would take 42 steps longer and would still answer false, so the count is the only thing that distinguishes them and it is the kernel that computes it. DerivedProved, zero axiom_deps.",
            )?;
            self.add_recursive_def(
                &format!(
                    "def ir_lzd_max_sz_running_at_59 : Eq IROutcome (ir_config_outcome (ir_steps {} ir_lzd_module {init})) IROutcome.fuel_out := Eq.refl IROutcome IROutcome.fuel_out",
                    numeral(59)
                ),
                "ir_lzd_max_sz_running_at_59: and the count above is EXACT -- one step earlier the machine is still running. DerivedProved, zero axiom_deps.",
            )?;
        }
        Ok(())
    }
}

/// `IMax(Zero, Zero)`, same shape as [`HEAP_MAXZZ`] with the tag at 3. IMax
/// reads its SECOND child only — the impredicative collapse — so this witness
/// exercises the `switch` DEFAULT edge and one derived deref.
const HEAP_IMAXZZ: &str = "(ir_cell ir_d40 (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))";

/// `Max(Succ(Zero), Zero)` — the SHORT-CIRCUIT witness. The first child is not
/// zero, so the answer is `false` and the second child is never read: one
/// derived deref, not two. Its `Succ` node at cell 17 carries its own child
/// pointer at 25 and that child at 19, which the run never touches — they are
/// there because the representation relation requires them, not because the
/// machine reads them.
const HEAP_MAXSZ: &str = "(ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d3))) (ir_cell ir_d25 (IRScalar.ptr_ ir_d3) (ir_cell ir_d19 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))))";

/// `Max(Zero, Zero)` with the receiver at cell 40, the same witness
/// `ir_lzc_max_running_at_8` and `ir_lzc_max_stuck_at_9` use. Reused
/// deliberately: the two chains are then compared at the SAME input, and the
/// only thing that differs is which module is stepping.
const HEAP_MAXZZ: &str = "(ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))";
