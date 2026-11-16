// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Option B, step one — the minted body with a deref MODEL beside it, and
//! the two arms that went `stuck no_func` now RUNNING.**
//!
//! `ir_lz_module` (`eval_ir_level_minted.rs`) is the designated target's
//! minted module: `level::Level::is_zero` exactly as the compiler emits it,
//! ten blocks, six call sites. It defines ONE function and calls a second —
//! `<LevelArc as Deref>::deref`, canonical index 1 — that the artifact carries
//! as a declaration only, because rustc has no cross-crate THIR. So its `Max`
//! and `IMax` arms halt `IROutcome.stuck IRFault.no_func`, and A4 over it is
//! FALSE, kernel-checked (`ir_lz_minted_refutes_a4_on_max`). Link 4 for the
//! designated target is OPEN; the memo
//! `designs/2026-08-22-is-zero-model-vs-minted-decision.md` scopes Option B as
//! the route that closes it.
//!
//! This module is Option B's first step: **`ir_lzb_module`**, whose function 0
//! IS the minted `ir_lz_func` — by name, not by transcription — and whose
//! function 1 is an authored model of the deref.
//!
//! ## Why a THIRD module, and not a second function inside `ir_lz_module`
//!
//! The memo says "a THIRD module" and gives the reason as re-derivation cost.
//! Measured at HEAD, there is a second and harder reason: **four independent
//! gates refuse an authored function inside the minted module**, and they are
//! right to.
//!
//! * `ir_mint::mint` (`src/ir_mint/mint.rs`) requires the module's function
//!   list to be exactly the bodies the tag table declares — *"A body the table
//!   does not declare has no pinned interface and no name prefix, so minting it
//!   would invent both"*.
//! * M3 (`tests/crystal_a2_mint_lz.rs`) byte-compares the committed script
//!   against what `mint` reproduces — *"a difference here means the minted
//!   module is hand-edited"*.
//! * M4, reader C, decodes the registered term against `ir_lz.core.txt`, which
//!   is reader A's projection of the artifact **binary**. That binary has no
//!   deref body, so no registered two-function module can decode to it.
//! * `tests/crystal_a2_mint/callee_identity.rs` asserts `funcs.len() == 1` and
//!   that three of the six sites call OUT of the module — the fail-closed wall
//!   `crystal_a1_lineage` relies on.
//!
//! **This corrects the memo's §2.2 item 4.** *"M4 decodes the two-function
//! module; the tag table's `funcs` lane pins both ids"* is not achievable as
//! written: `funcs` pins the callee NAMESPACE (it already carries both ids
//! today, while the module still defines one function), the lane that declares
//! a defined body is `extra_bodies`, and reader A cannot project a body the
//! artifact does not carry. So the authored half is **outside** the mint
//! lineage by construction, under the synthetic-module labelling convention
//! this tree already uses (`ir_frs_module`, `SRC_IR_HLB_HEADLESS`,
//! `ir_mt_oob_module`). `ir_lz_module` stays byte-frozen and artifact-equal;
//! nothing here touches it, and its refutation theorem stays true.
//!
//! ## What is assumed, stated once and not laundered
//!
//! `ir_lzb_deref` is an **ASSUMPTION**, and it is the residual of the whole
//! chain. It states that `<LevelArc as Deref>::deref` — that is,
//! `Option::as_deref` followed by `Option::expect` on a
//! `LevelArc(Option<Arc<Level>>)` — loads the pointer out of the field it is
//! given, traps if that pointer is null, and otherwise returns that pointer
//! offset by the `Arc` header. Seven nodes: `load ptr`, `const null`,
//! `icmp ne`, `assert`, `const i64 16`, `gep`, `ret`. No gate can promote
//! this to a derivation, because no artifact in this repository carries those
//! two `core` bodies — measured, not assumed: both appear by name in the
//! trust-ir text artifact, among 309 `std`/`core`/`alloc`-named entries, and
//! all 309 are **empty** (a name, a `; #producer` line, 0 instructions between
//! them). They are declarations.
//!
//! Why it cannot become a build item, stated exactly, because three walls were
//! long conflated here and only one is a floor. That rustc has no cross-crate
//! THIR (`thir_body` takes a `LocalDefId`) and that every body-producing path
//! keys on `is_local()` are both real and both BUILD ITEMS. The floor is that
//! `expect`'s closure ends at a declaration with no body **anywhere**:
//! `expect → expect_failed → panic_display → panic_fmt → panic_impl`, and
//! `panic_impl` is `unsafe extern "Rust"` in `core/src/panicking.rs:67-70`,
//! supplied at link time from `std/src/panicking.rs:611`. No lowering fixes
//! that, and it holds for any body that can panic.
//!
//! And note what this model deliberately is *not*. Transcribing the emitted
//! body structurally — two `call`s — would not shrink the assumption; it would
//! replace one clearly-stated semantic assumption with three (an `as_deref`
//! model, an `expect` model, and the niche layout), none of them derivable.
//! What is assumed here is exactly TWO things:
//!
//!   1. `Option<Arc<Level>>`'s `None` is the null niche.
//!   2. `as_deref().expect()` is load + null-check + assert, and the pointer it
//!      yields is the `Arc`'s DATA address.
//!
//! ## THE ARC DATA OFFSET — the third clause, and why it is gone
//!
//! Audit r16 M16-6 (2026-09-02) measured a THIRD assumption that four committed
//! artifacts had enumerated away: the model returned the loaded field word
//! UNCHANGED, so it computed `x` where the shipped function computes `&*x`.
//! `<Arc<T> as Deref>::deref` yields the address of the Arc's DATA, past the
//! strong and weak counts, which on this target is `stored_ptr + 16` — measured
//! on stable rustc 1.97.1 aarch64-apple-darwin against a stand-in with `Level`'s
//! recorded shape (size 40 / align 8): `stored=0x105459bf0`,
//! `deref_result=0x105459c00`, `delta=16`.
//!
//! That clause was not weak, it was FALSE, and it made the relation
//! unsatisfiable: `EncodesLevelArcF` was written to match the model, so under
//! the byte-offset reading this repo pins in
//! `tests/crystal_a1_lineage/level_is_zero.rs` no real `Level` heap satisfied it
//! at a `Succ`/`Max`/`IMax` node — exactly the nodes link 4's content is about.
//!
//! **The strengthening is TAKEN here.** The model carries the missing
//! `const i64 16` + `gep`, `EncodesLevelArcF` places each child at the Arc's
//! data address rather than at the stored word, and the two `Eq.refl` cost
//! equations it re-derives moved with it: `ir_lzb_cost_halts_max` 37 → **41**
//! and `ir_lzb_cost_halts_imax` 20 → **22**, two more steps per deref frame,
//! four frames in `Max` and one in `IMax`. Every one of those numbers is
//! computed by the kernel, not asserted: an off-by-one is a build failure.
//! `designs/2026-08-26-a0-semantic-no-escape.md` states the residual as the
//! identity `Option::Some(x).as_deref().expect(_) == &*x`; the model now
//! implements the right side.
//!
//! Two things keep the assumption honest rather than convenient:
//! `ir_lzb_deref_refuses_none` computes `ub assert_failed` on a null field, so
//! the model is not total and the `assert` is not decoration; and
//! `ir_lzb_func0_is_minted` is a kernel-checked equation that function 0 of
//! this module is the minted term itself, so the half that IS derived cannot
//! drift into the half that is assumed.
//!
//! ## The field-addressed heap
//!
//! The minted body `gep`s the receiver to byte offsets 8 and 16 and passes
//! those FIELD ADDRESSES to the deref; the hand model read the children out of
//! the loaded value with `extractfield`. `ir_gep_base` is cell-addressed, so a
//! represented `Level` at cell `a` now also needs its two `LevelArc` pointers
//! at cells `a+8` and `a+16`. The heaps here carry both — the enum value at
//! `a`, whose tag `b0` reads, and the two field cells the `gep`s address. That
//! redundancy is not a modelling choice; it is what the emitted body observes.
//!
//! **That adds a layout claim, and it is a NEW one.** `eval_ir_repr.rs` already
//! names one open obligation — the real Rust `Level` is niche-encoded, so the
//! declaration-index tags `ir_d0..ir_d4` are adequate for these modules only.
//! The field-addressed heap names a second: that a represented `Level` at cell
//! `a` has its two `LevelArc` fields reachable at cells `a+8` and `a+16`. Those
//! two offsets are not chosen here — they are the byte offsets the emitted body
//! `gep`s to, read off the committed artifact fixture
//! (`tests/fixtures/level_is_zero.trust-ir.txt:18-21`, `const i64 8` / `gep` and
//! `const i64 16` / `gep`, and again at `:26-27` for the `IMax` arm) — but
//! *that the representation places
//! anything there* is an assumption about `repr(Rust)` field placement, which
//! is unspecified and which `repr(Rust)` is free to reorder. It is stated here
//! rather than left implicit, and it belongs in the same layout-adequacy
//! theorem as the niche decode. Neither is discharged, and neither is claimed
//! to be.
//!
//! ## The five arms, computed by the kernel
//!
//! | witness | input | outcome | on `ir_lz_module` |
//! |---|---|---|---|
//! | `ir_lzb_on_zero` | `Zero` | `ret [true]` | `ret [true]` |
//! | `ir_lzb_on_succ` | `Succ 0` | `ret [false]` | `ret [false]` |
//! | `ir_lzb_on_param` | `Param n`, ∀ n | `ret [false]` | `ret [false]` |
//! | `ir_lzb_on_max` | `Max(0, 0)` | **`ret [true]`** | `stuck no_func` |
//! | `ir_lzb_on_imax` | `IMax(Param n, 0)`, ∀ n | **`ret [true]`** | `stuck no_func` |
//!
//! The two recursive arms are the ones the memo is about. They now run to the
//! answer `Level::is_zero` gives, through three deref frames and three self
//! frames, with the short-circuit `&&` taking its then-edge.
//!
//! The `ir_lzb_cost_halts_*` witnesses pin the EXACT step count of each arm —
//! 6, 6, 6, **41**, **22** — by `Eq.refl`, so the cost function the activation
//! induction will need is validated by computation before a line of it is
//! written. An off-by-one is a build failure here, not a wrong theorem later.
//!
//! `DerivedProved`, empty axiom closures. Census stays 11: every definition is
//! either a literal or an `Eq.refl` the kernel discharges by running the
//! machine.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The authored deref model: seven nodes in one block, function id 1.
///
/// The last two — `const i64 16` and a `gep` by it — are what make this model
/// compute `&*x` rather than `x`. See the `ARC DATA OFFSET` section of the
/// module doc: `<Arc<T> as Deref>::deref` returns the address of the Arc's
/// DATA, past the strong/weak header, and a model that returned the loaded
/// field word unchanged was describing a different function.
const SRC_DEREF_B0: &str = "def ir_lzb_deref_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (@IRList.cons IRNode (ir_nd1 (IRInst.load IRTy.ptr_ ir_d0 Bool.false) ir_d1) (@IRList.cons IRNode (ir_nd1 (IRInst.const_ IRTy.ptr_ IRConst.null_) ir_d2) (@IRList.cons IRNode (ir_nd1 (IRInst.icmp IRICmpOp.ne_ IRTy.ptr_ ir_d1 ir_d2) ir_d3) (@IRList.cons IRNode (ir_nd (IRInst.assert ir_d3)) (ir_bd3 (ir_nd1 (IRInst.const_ (IRTy.int_ 64) (IRConst.int_ ir_d16)) ir_d4) (ir_nd1 (IRInst.gep (IRTy.int_ ir_d8) ir_d1 (ir_nl1 ir_d4) Bool.true) ir_d5) (ir_nd (IRInst.ret (ir_nl1 ir_d5))))))))";

const SRC_DEREF: &str = "def ir_lzb_deref : IRFunc := IRFunc.mk ir_d1 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_lzb_deref_b0 ir_blk0)";

/// Function 0 is `ir_lz_func` BY NAME. There is no transcription here.
const SRC_MODULE: &str = "def ir_lzb_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_lz_func (@IRList.cons IRFunc ir_lzb_deref (@IRList.nil IRFunc))) (@IRList.nil IRGlobal)";

const ARGS0: &str = "(ir_vl1 (IRScalar.ptr_ ir_d0))";

/// Field-addressed heaps with the Arc header modelled: the enum value at `a`,
/// the two `LevelArc` pointers at `a+8` and `a+16`, and each child `Level`
/// SIXTEEN CELLS PAST the pointer stored in its field — where
/// `<Arc<T> as Deref>::deref` looks, not where the field points.
///
/// So a field holding `ptr 1` names an Arc allocation at 1 whose `Level` sits
/// at 17: cells 1 and 9 would be the strong and weak counts, and the machine
/// never reads them, so the heaps do not carry them.
const HEAP_ZERO: &str = "(ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0)";
const HEAP_SUCC: &str = "(ir_cell ir_d0 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d1))) (ir_cell ir_d8 (IRScalar.ptr_ ir_d1) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) ir_mem0)))";
const HEAP_PARAM: &str = "(ir_cell ir_d0 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ir_mem0)";
const HEAP_MAXZZ: &str = "(ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d8 (IRScalar.ptr_ ir_d1) (ir_cell ir_d16 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))";
const HEAP_IMAXPZ: &str = "(ir_cell ir_d0 (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d8 (IRScalar.ptr_ ir_d1) (ir_cell ir_d16 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))";
const HEAP_NULLFIELD: &str = "(ir_cell ir_d8 IRScalar.nullptr_ ir_mem0)";

const RET_TRUE: &str = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const RET_FALSE: &str = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

fn run(fid: &str, args: &str, heap: &str, na: &str) -> String {
    format!("(ir_eval ir_fuel ir_lzb_module {fid} {args} {heap} {na})")
}

fn init(heap: &str, na: &str) -> String {
    format!("(ir_init ir_lzb_module ir_d0 {ARGS0} {heap} {na})")
}

/// A witness proved by `Eq.refl`: the kernel runs the machine and compares.
fn witness(
    name: &str,
    binder: &str,
    fid: &str,
    args: &str,
    heap: &str,
    na: &str,
    out: &str,
) -> String {
    format!(
        "def {name} {binder}: @Eq IROutcome {} {out} := @Eq.refl IROutcome {out}",
        run(fid, args, heap, na)
    )
}

/// The exact step count of one arm, as a configuration equation.
fn halts(name: &str, binder: &str, heap: &str, na: &str, steps: u32, ans: &str) -> String {
    let tgt = format!("(IRConfig.halted (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.{ans}))))");
    format!(
        "def {name} {binder}: @Eq IRConfig (ir_steps ir_d{steps} ir_lzb_module {}) {tgt} := @Eq.refl IRConfig {tgt}",
        init(heap, na)
    )
}

impl Specification {
    /// Option B step one: the deref model, the two-function module, and the
    /// arms that now run. Needs only the IR types, the numerals, the builders,
    /// `ir_fuel` and `ir_lz_func`, so it belongs to the EvalIr bundle and is
    /// called from `add_eval_ir_crystal` immediately after the minted module.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check. A wrong step count in `halts` fails HERE, by computation.
    pub(super) fn add_eval_ir_lzb_module(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_DEREF_B0, "ir_lzb_deref_b0: *** AN ASSUMPTION, LABELLED. *** The authored model of <LevelArc as Deref>::deref -- Option::as_deref followed by Option::expect on a LevelArc(Option<Arc<Level>>). Seven nodes: load the pointer out of the FIELD ADDRESS it was given, compare it against null, assert non-null, then gep it by the Arc header (const i64 16) and return THAT -- the Arc's DATA address, which is what <Arc<T> as Deref>::deref yields and what the recursive call is then entered at. This is a STATED MODEL of two core functions the artifact carries as declarations ONLY -- re-measured 2026-08-26 from the trust-ir text artifact itself: Option::as_deref and Option::expect both appear there by name, among 309 std/core/alloc-named entries, and all 309 are EMPTY (a name, a `; #producer` line, 0 instructions between them). Three walls were long conflated here and only one is a floor: (1) rustc has no cross-crate THIR (thir_body takes a LocalDefId, no thir_of_instance) and (2) every body-producing path keys on is_local() -- both real, both BUILD ITEMS; (3) expect's closure ends at a declaration with no body ANYWHERE (expect -> expect_failed -> panic_display -> panic_fmt -> panic_impl, and panic_impl is `unsafe extern \"Rust\"` in core/src/panicking.rs:67-70, supplied at link time from std/src/panicking.rs:611) -- that one is the FLOOR, and no lowering fixes it. Note what this model is NOT: splitting it into separate as_deref and expect models would not shrink the assumption, it would turn one clearly-stated semantic assumption into three (two unavailable callee models plus the niche layout), so the collapse here is deliberate. What it assumes is exactly: Option<Arc<Level>>'s None is the null niche, and as_deref().expect() is load + null-check + assert + the Arc data offset. The THIRD clause audit r16 M16-6 measured -- that the stored field word IS the child's address, which was FALSE by 16 bytes -- is discharged rather than stated: the gep is in the body above, EncodesLevelArcF places each child at stored+16 to match, and the two @Eq.refl cost equations moved 37 -> 41 and 20 -> 22. No gate in this repository can promote it to a derivation and none is claimed to; it is the residual of the whole chain. The assert is load-bearing, not decoration: ir_lzb_deref_refuses_none computes ub assert_failed on a null field. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_DEREF, "ir_lzb_deref: the deref model as a function at canonical id 1 -- the id the minted body's three `call 1` sites name, pinned to <level::LevelArc as std::ops::Deref>::deref (crate id 3894) by the committed tag table's funcs lane and by tests/crystal_a2_mint/callee_identity.rs. One ptr parameter, one block, entry b0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MODULE, "ir_lzb_module: the designated target's minted body WITH a deref model beside it -- Option B's module. Function 0 is ir_lz_func, the MINTED term, by name: there is no second transcription of the emitted body anywhere in this file, and ir_lzb_func0_is_minted is the kernel-checked equation that says so. Function 1 is the authored assumption. \
\
It is a THIRD module and not an edit of ir_lz_module because FOUR gates refuse an authored function inside a minted one, each correctly: mint's declared-bodies rule ('a body the table does not declare has no pinned interface and no name prefix, so minting it would invent both'), M3's byte comparison against what mint reproduces, M4/reader-C's decode against ir_lz.core.txt (reader A's projection of a binary that has no deref body), and callee_identity.rs's funcs.len() == 1. So this module sits OUTSIDE the mint lineage under the synthetic-module labelling convention already used for ir_frs_module and SRC_IR_HLB_HEADLESS, and ir_lz_module stays byte-frozen, artifact-equal, and refuted. DerivedProved, zero axiom_deps.")?;

        for (name, idx, f) in [
            ("ir_lzb_func0_is_minted", "ir_d0", "ir_lz_func"),
            ("ir_lzb_func1_is_the_deref_model", "ir_d1", "ir_lzb_deref"),
        ] {
            let tgt = format!("(@IROption.some IRFunc {f})");
            self.add_recursive_def(
                &format!("def {name} : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs ir_lzb_module) {idx}) {tgt} := @Eq.refl (IROption IRFunc) {tgt}"),
                if idx == "ir_d0" {
                    "ir_lzb_func0_is_minted: *** THE DERIVED HALF CANNOT DRIFT INTO THE ASSUMED HALF. *** ir_func_find resolves id 0 of this module to ir_lz_func itself -- the term replayed line for line from generated/ir_lz.defs.txt and checked by three independent readers. Eq.refl, so the kernel walks the function list and compares the whole body. Anything that edited the emitted half while adding the assumed half would fail here. DerivedProved, zero axiom_deps."
                } else {
                    "ir_lzb_func1_is_the_deref_model: id 1 resolves to the authored model, so the three `call 1` sites are no longer stuck. This is the ONE thing that changed relative to ir_lz_module, stated as an equation rather than left to be inferred from the witnesses. DerivedProved, zero axiom_deps."
                },
            )?;
        }

        self.add_recursive_def(
            &witness("ir_lzb_deref_reads_the_field", "", "ir_d1", "(ir_vl1 (IRScalar.ptr_ ir_d8))", HEAP_MAXZZ, "ir_d17", "(IROutcome.ret (ir_vl1 (IRScalar.ptr_ ir_d17)))"),
            "ir_lzb_deref_reads_the_field: the model in isolation. Entered at the FIELD ADDRESS the minted b4 geps to (cell 8 of the Max(Zero, Zero) heap), it loads the pointer stored there and returns that pointer PLUS THE ARC HEADER -- ptr 1 in the field, ptr 17 out, which is where the child Level lives. Seven steps: the five that check the field, then the const and the gep that make the answer the Arc's DATA address rather than the stored word. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &witness("ir_lzb_deref_refuses_none", "", "ir_d1", "(ir_vl1 (IRScalar.ptr_ ir_d8))", HEAP_NULLFIELD, "ir_d9", "(IROutcome.ub IRFault.assert_failed)"),
            "ir_lzb_deref_refuses_none: *** THE MODEL IS NOT TOTAL. *** On a field holding nullptr -- LevelArc(None) -- it halts ub assert_failed, which is how a Rust panic appears in this semantics. A deref model that returned something here would be a strictly stronger assumption than Option::expect, and every theorem built on it would be quietly wrong on None. The assert is therefore observable, and this is the observation. DerivedProved, zero axiom_deps.",
        )?;

        for (name, binder, heap, na, out, doc) in [
            ("ir_lzb_on_zero", "", HEAP_ZERO, "ir_d1", RET_TRUE, "ir_lzb_on_zero: Zero is true -- b0, b1, then the join b6 with the answer as a block argument. Unchanged from ir_lz_on_zero: the constant arms never reach a call, so adding the deref model cannot have moved them, and this witness is what says so. DerivedProved, zero axiom_deps."),
            ("ir_lzb_on_succ", "", HEAP_SUCC, "ir_d9", RET_FALSE, "ir_lzb_on_succ: Succ(Zero) is false. Succ is a LEAF arm -- the edge is present in the heap, at the field cell 8 as well as inline, and is still not followed. DerivedProved, zero axiom_deps."),
            ("ir_lzb_on_param", "(n : Nat) ", HEAP_PARAM, "ir_d1", RET_FALSE, "ir_lzb_on_param: Param n is false for EVERY n, through the emitted body's own b3. DerivedProved, zero axiom_deps."),
            ("ir_lzb_on_max", "", HEAP_MAXZZ, "ir_d17", RET_TRUE, "ir_lzb_on_max: *** THE ARM THAT WENT STUCK NOW RETURNS THE RIGHT ANSWER. *** Max(Zero, Zero) is TRUE, which is what Level::is_zero answers and what ir_lz_on_max_stuck could not reach: over ir_lz_module the first `call 1` halts stuck no_func. Here b4 geps the receiver to offsets 8 and 16, calls the deref model on the first field address, recurses into function 0 on the child it returns, takes the CondBr's then-edge, reaches b7, derefs and recurses on the second, and joins through b9 to b6. Two deref frames and two self frames pushed and popped, and the kernel executed all of it to compare. DerivedProved, zero axiom_deps."),
            ("ir_lzb_on_imax", "(n : Nat) ", HEAP_IMAXPZ, "ir_d17", RET_TRUE, "ir_lzb_on_imax: IMax(Param n, Zero) is TRUE for every n -- the impredicative collapse -- reached through the switch DEFAULT edge to b5, which geps to offset 16 only. The first operand is a Param in the heap and is never read; a semantics that read it would answer false and this would fail to typecheck. The second arm ir_lz_on_imax_stuck could not reach either. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(&witness(name, binder, "ir_d0", ARGS0, heap, na, out), doc)?;
        }

        Ok(())
    }

    /// The five EXACT step counts. A separate stage, and the split is a
    /// dependency, not tidiness: these are the only declarations here that name
    /// `ir_steps`, which `add_eval_ir_steps` registers — and that stage runs
    /// AFTER `add_eval_ir`, inside which `add_eval_ir_lzb_module` is called.
    /// Registered together with the module they cost, the `ir_steps` head is not
    /// yet in the environment and the elaborator reports it as a BOGUS ARITY
    /// ERROR ("`IRConfig` is not a function type, but 3 argument(s) remain"),
    /// not as an unknown identifier — the exact trap `bundles.rs` warns about
    /// three times, and it cost this lane one 68-minute build to hit.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check. A wrong step count fails HERE, by computation.
    pub(super) fn add_eval_ir_lzb_steps(&mut self) -> Result<(), SpecError> {
        for (name, binder, heap, na, steps, ans, doc) in [
            ("ir_lzb_cost_halts_zero", "", HEAP_ZERO, "ir_d1", 6u32, "true", "ir_lzb_cost_halts_zero: SIX steps exactly -- b0's load, extractfield and switch, b1's const and br, and b6's ret. The hand model's leaf cost was five, because it returned from the arm instead of branching to a join. @Eq.refl on a CONFIGURATION, so the count is pinned, not bounded. DerivedProved, zero axiom_deps."),
            ("ir_lzb_cost_halts_succ", "", HEAP_SUCC, "ir_d9", 6, "false", "ir_lzb_cost_halts_succ: six, through b2. DerivedProved, zero axiom_deps."),
            ("ir_lzb_cost_halts_param", "(n : Nat) ", HEAP_PARAM, "ir_d1", 6, "false", "ir_lzb_cost_halts_param: six for every n, through b3 -- which the emitted body does not share with b2, so the equal count is a coincidence of length and not of path. DerivedProved, zero axiom_deps."),
            ("ir_lzb_cost_halts_max", "", HEAP_MAXZZ, "ir_d17", 41, "true", "ir_lzb_cost_halts_max: *** FORTY-ONE STEPS. *** The interesting count. Four frame pushes and pops (two deref, two self), two field geps, two null checks, two ARC-HEADER geps inside the deref frames, a CondBr taking its then-edge, and two joins. 16 before the first self activation, 6 for it, 13 after including the second deref and self pair at 8 + 6. It read 37 while the deref model returned the stored word unchanged; the two extra nodes that make it return the Arc DATA address cost two steps per deref frame, and there are two. This is the arithmetic ir_lzb_cost must reproduce, VALIDATED BY THE KERNEL before the cost function is written -- an off-by-one is a build failure here rather than a wrong theorem in the activation induction later. DerivedProved, zero axiom_deps."),
            ("ir_lzb_cost_halts_imax", "(n : Nat) ", HEAP_IMAXPZ, "ir_d17", 22, "true", "ir_lzb_cost_halts_imax: twenty-two, for every n: 14 before the self activation on the second operand, 6 for it, 2 after. One deref frame and one self frame; the deref pays 8 rather than the 6 it paid before the Arc-header gep landed. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(&halts(name, binder, heap, na, steps, ans), doc)?;
        }
        Ok(())
    }
}
