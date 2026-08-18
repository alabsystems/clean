// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The SECOND complete width-one chain: `level::Level::kind_ord`.**
//!
//! One shipped kernel function carried the whole way from its real source to a
//! Clean-kernel-checked theorem, with every link a real mechanism: the emitted
//! trust-ir recorded verbatim, the proved module gated against that emission,
//! the codegen flip and its A-LIN lineage digest pinned, the semantics, the
//! refinement theorem, and the kernel check.
//!
//! ## Why this body, measured rather than chosen
//!
//! Whole-crate release differential of `clean-kernel` at `fcecd8d7e`, stage1
//! trustc `5cd23255…` (`scripts/trust_ir_build.sh`'s profile), reproduced by two
//! independent clean non-incremental builds with byte-identical coverage:
//!
//! ```text
//! bodies                                                    13769
//! {agreed & markers_exact & unsupported [] & spliced}         1058
//!   ... AND a flip event carrying a lineage digest             185   (153 codegen + 32 CTFE)
//!   ... flip-event lineage != coverage-row lineage               0
//!   ... with any call at all (so all closures are bodyful)       0
//! of the 153 codegen bodies: single-block                      138
//!   containing an icmp / arithmetic / cast / condbr / gep / call  0
//!   with a switch of 3 or more explicit cases                    10
//! ```
//!
//! So **no fully-chainable body in this crate exercises recursion, arithmetic,
//! a comparison, or a call** — that is a property of the flip gate's current
//! reach, not a choice made here, and it is stated rather than worked around.
//! Within what is chainable today, `Level::kind_ord` covers the most new ground
//! relative to `CleanMode::has_cubical_layer` (the only previously complete
//! chain):
//!
//! | axis | `has_cubical_layer` | `kind_ord` |
//! |---|---|---|
//! | blocks | 5 | **7** |
//! | explicit switch cases | 2 + default | **4 + default** |
//! | distinct answers | 2 (a `Bool`) | **5 (a `u8`)** |
//! | join-block parameter | `bool` | **`u8`** |
//! | constant lane in the semantics | `IRConst.bool_` | **`IRConst.int_` → `ir_const_int_eval`'s width-8 residue** |
//! | subject type | `CleanMode`, FIELDLESS | **`Level`, payload-bearing and RECURSIVE** |
//! | representation premise | pins the whole payload | **payload-agnostic: the spine is universally quantified** |
//! | emitted arms executed by witnesses | 4 of 6 | **5 of 5** |
//! | A5 endpoint | the reflected predicate | **`level_eval`, a denotational fact** |
//!
//! Two candidates cover more control flow — `mode::CleanMode::from_source_system`
//! (14 blocks, 11 explicit cases) and `<tc::expr_location::ExprPathStep as
//! Clone>::clone` (13 blocks, 10 cases) — and **neither was chainable when this
//! module was written**: both return an enum by value as `const enum.N { k }`,
//! i.e. a `trust_ir::Constant::Aggregate`, and Clean's `IRConst` had seven
//! constructors and no aggregate form. That is a link-3 gap and therefore a
//! build item (extend `IRConst` and `ir_const_eval`), not a reason to pretend
//! the link holds.
//!
//! **UPDATE, same day.** The build item was built: `IRConst` now carries an
//! inline element spine (`aggv`/`vnil`/`vcons`, ten constructors) and
//! `ir_const_agg_eval` is its typed evaluator, so
//! `mode::CleanMode::from_source_system` is a COMPLETE third chain —
//! [`super::eval_ir_from_source`]. The `ExprPathStep` clone body emits the
//! identical constant shape and is unblocked by the same work; it has not been
//! chained.
//!
//! ## What is proved
//!
//! For EVERY `Level`, every heap carrying its tag with ANY payload, and every
//! fuel at or above 6, the machine returns exactly `level_kind_ord l`
//! (`ir_ko_correct`); if it answers `n` then `level_kind_ord l = n`
//! (`ir_ko_machine_sound`); if it answers `0` then under EVERY assignment the
//! level evaluates to zero (`ir_ko_machine_sound_denot`); the answer is always
//! at most 4, so it is a total ordering key (`ir_ko_kind_bound`); and on any
//! represented level it never faults, never traps and never exhausts fuel
//! (`ir_ko_never_faults`). All five emitted arms are executed by the kernel as
//! witnesses.
//!
//! ## What this does NOT establish
//!
//! The link between the proved module and the emitted one is STRUCTURAL — same
//! CFG, checked by `tests/crystal_a1_lineage.rs` — not a semantic proof that
//! Clean's `IRInst` encoding of `switch`/`br` means what trust-ir's does. The
//! lineage digest is RECORDED, not recomputed from the artifact by the Clean
//! side. Everything past the flip seam (the ~45 MIR optimisation passes, LLVM,
//! linking) is downstream and covered by nothing here. And this is width one:
//! by itself it retires no kernel-wide trust assumption.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_LEVEL_KIND_TAG: &str = "def level_kind_tag (l : Level) : Nat := Level.rec (fun (_ : Level) => Nat) ir_d0 (fun (_ : Level) (_ : Nat) => ir_d1) (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => ir_d2) (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => ir_d3) (fun (_ : Name) => ir_d4) l";

const SRC_LEVEL_KIND_ORD: &str = "def level_kind_ord (l : Level) : Nat := Level.rec (fun (_ : Level) => Nat) ir_d0 (fun (_ : Level) (_ : Nat) => ir_d1) (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => ir_d2) (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => ir_d3) (fun (_ : Name) => ir_d4) l";

const SRC_ENCODESLEVELKINDCELL: &str = "inductive EncodesLevelKindCell (mem : IRList IRMemSlot) : IRScalar -> Level -> Type\n| mk : forall (a : Nat) (fs : IRScalar) (l : Level), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag l) fs) Bool.true)) -> EncodesLevelKindCell mem (IRScalar.ptr_ a) l";

const SRC_ENCODES_LEVEL_KIND_OF_ARC: &str = "def encodes_level_kind_of_arc (mem : IRList IRMemSlot) (s : IRScalar) (l : Level) (d : EncodesLevelArc mem s l) : EncodesLevelKindCell mem s l := EncodesLevelArc.rec mem (fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelArc mem s0 l0) => EncodesLevelKindCell mem s0 l0) (fun (a : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true))) => EncodesLevelKindCell.mk mem a ir_sp0 Level.zero h) (fun (a : Nat) (b : Nat) (l0 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b))) Bool.true))) (_arc : EncodesLevelArc mem (IRScalar.ptr_ b) l0) (_ih : EncodesLevelKindCell mem (IRScalar.ptr_ b) l0) => EncodesLevelKindCell.mk mem a (ir_sp1 (IRScalar.ptr_ b)) (Level.succ l0) h) (fun (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1) (_arc2 : EncodesLevelArc mem (IRScalar.ptr_ b2) l2) (_ih1 : EncodesLevelKindCell mem (IRScalar.ptr_ b1) l1) (_ih2 : EncodesLevelKindCell mem (IRScalar.ptr_ b2) l2) => EncodesLevelKindCell.mk mem a (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2)) (Level.max l1 l2) h) (fun (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1) (_arc2 : EncodesLevelArc mem (IRScalar.ptr_ b2) l2) (_ih1 : EncodesLevelKindCell mem (IRScalar.ptr_ b1) l1) (_ih2 : EncodesLevelKindCell mem (IRScalar.ptr_ b2) l2) => EncodesLevelKindCell.mk mem a (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2)) (Level.imax l1 l2) h) (fun (a : Nat) (w : IRScalar) (nm : Name) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 (ir_sp1 w)) Bool.true))) => EncodesLevelKindCell.mk mem a (ir_sp1 w) (Level.param nm) h) s l d";

const SRC_IR_KO_TENUM: &str = "def ir_ko_tenum : IRTy := IRTy.enum_ ir_d2";

const SRC_IR_KO_B0: &str = "def ir_ko_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.load ir_ko_tenum ir_d0 Bool.false) ir_d2) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3) (ir_nd (IRInst.switch ir_d3 ir_d5 ir_nl0 (ir_sc ir_d0 ir_d1 (ir_sc ir_d1 ir_d2 (ir_sc ir_d2 ir_d3 (ir_sc ir_d3 ir_d4 ir_sc0)))) Bool.false)))";

const SRC_IR_KO_B1: &str = "def ir_ko_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_tU8 (IRConst.int_ ir_d0)) ir_d4) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d4))))";

const SRC_IR_KO_B2: &str = "def ir_ko_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_tU8 (IRConst.int_ ir_d1)) ir_d5) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d5))))";

const SRC_IR_KO_B3: &str = "def ir_ko_b3 : IRBlock := IRBlock.mk ir_d3 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_tU8 (IRConst.int_ ir_d2)) ir_d6) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d6))))";

const SRC_IR_KO_B4: &str = "def ir_ko_b4 : IRBlock := IRBlock.mk ir_d4 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_tU8 (IRConst.int_ ir_d3)) ir_d7) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d7))))";

const SRC_IR_KO_B5: &str = "def ir_ko_b5 : IRBlock := IRBlock.mk ir_d5 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_tU8 (IRConst.int_ ir_d4)) ir_d8) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d8))))";

const SRC_IR_KO_B6: &str = "def ir_ko_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d1) (ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d1))))";

const SRC_IR_KO_FUNC: &str = "def ir_ko_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_ko_b0 (ir_blk ir_ko_b1 (ir_blk ir_ko_b2 (ir_blk ir_ko_b3 (ir_blk ir_ko_b4 (ir_blk ir_ko_b5 (ir_blk ir_ko_b6 ir_blk0)))))))";

const SRC_IR_KO_MODULE: &str = "def ir_ko_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_ko_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

const SRC_IR_KO_ON_ZERO: &str = "def ir_ko_on_zero : Eq IROutcome (ir_eval ir_d6 ir_ko_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0)))";

const SRC_IR_KO_ON_SUCC: &str = "def ir_ko_on_succ : Eq IROutcome (ir_eval ir_d6 ir_ko_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d0))) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d1))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d1)))";

const SRC_IR_KO_ON_MAX: &str = "def ir_ko_on_max : Eq IROutcome (ir_eval ir_d6 ir_ko_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d0) (IRScalar.ptr_ ir_d0))) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d2))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d2)))";

const SRC_IR_KO_ON_IMAX: &str = "def ir_ko_on_imax : Eq IROutcome (ir_eval ir_d6 ir_ko_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ ir_d0) (IRScalar.ptr_ ir_d0))) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d3))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d3)))";

const SRC_IR_KO_ON_PARAM: &str = "def ir_ko_on_param : Eq IROutcome (ir_eval ir_d6 ir_ko_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d4 (ir_sp1 IRScalar.undef_)) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d4))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d4)))";

const SRC_IR_KO_MACH0: &str = "def ir_ko_mach0 (mem : IRList IRMemSlot) (a : Nat) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.ptr_ a)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_KO_AFTER_LOAD: &str = "def ir_ko_after_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (o : (IROption IRMemSlot)) : IRConfig := ir_bind_result (ir_ko_mach0 mem a na) (ir_nl1 ir_d2) (ir_load_slot o)";

const SRC_IR_KO_EXACT: &str = "def ir_ko_exact (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) (l : Level) : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag l) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l)))) := Level.rec (fun (l0 : Level) => Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag l0) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ko_module (ir_ko_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0))))) (fun (_p : Level) (_ih : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag _p) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord _p))))) => (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ko_module (ir_ko_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d1)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d1)))))) (fun (_p : Level) (_q : Level) (_ih1 : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag _p) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord _p))))) (_ih2 : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag _q) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord _q))))) => (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ko_module (ir_ko_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d2)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d2)))))) (fun (_p : Level) (_q : Level) (_ih1 : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag _p) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord _p))))) (_ih2 : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag _q) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ko_module (IRConfig.running (ir_ko_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord _q))))) => (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ko_module (ir_ko_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d3)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d3)))))) (fun (_nm : Name) => (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ko_module (ir_ko_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d4)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d4)))))) l";

const SRC_IR_KO_CORRECT: &str = "def ir_ko_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (henc : EncodesLevelKindCell mem r l) : Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l)))) := EncodesLevelKindCell.rec mem (fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelKindCell mem s0 l0) => Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 s0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l0))))) (fun (a : Nat) (fs : IRScalar) (l0 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (level_kind_tag l0) fs) Bool.true))) (hle : Le ir_d6 fuel) => ir_run_le_ret ir_ko_module ir_d6 fuel hle (IRConfig.running (ir_ko_mach0 mem a na)) (ir_vl1 (IRScalar.int_ (level_kind_ord l0))) (ir_ko_exact mem a na fs l0 h)) r l henc";

const SRC_IR_SCALAR_NAT: &str = "def ir_scalar_nat (s : IRScalar) : Nat := IRScalar.rec (fun (_ : IRScalar) => Nat) Nat.zero (fun (_ : Bool) => Nat.zero) (fun (n : Nat) => n) (fun (_ : Nat) => Nat.zero) Nat.zero (fun (_ : Nat) => Nat.zero) Nat.zero (fun (_ : Nat) (_ : Nat) => Nat.zero) (fun (_ : Nat) => Nat.zero) (fun (_ : IRScalar) (_ : Nat) => Nat.zero) Nat.zero (fun (_ : IRScalar) (_ : IRScalar) (_ : Nat) (_ : Nat) => Nat.zero) s";

const SRC_IR_VALS_HEAD_NAT: &str = "def ir_vals_head_nat (v : IRList IRScalar) : Nat := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat) Nat.zero (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Nat) => ir_scalar_nat x) v";

const SRC_IR_OUTCOME_NAT: &str = "def ir_outcome_nat (o : IROutcome) : Nat := IROutcome.rec (fun (_ : IROutcome) => Nat) (fun (v : IRList IRScalar) => ir_vals_head_nat v) (fun (_ : IRFault) => Nat.zero) (fun (_ : IRFault) => Nat.zero) (fun (_ : IRFault) => Nat.zero) (fun (_ : IRFault) => Nat.zero) Nat.zero o";

const SRC_IR_KO_MACHINE_SOUND: &str = "def ir_ko_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (n : Nat) (henc : EncodesLevelKindCell mem r l) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ n)))) : Eq Nat (level_kind_ord l) n := Eq.cong IROutcome Nat ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ n))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l)))) (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ n))) (Eq.symm IROutcome (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l)))) (ir_ko_correct mem fuel na r l henc hle)) hret)";

const SRC_LEVEL_KIND_ZERO_IS_ZERO: &str = "def level_kind_zero_is_zero (l : Level) : Eq Nat (level_kind_ord l) ir_d0 -> Eq Bool (level_is_zero l) Bool.true := Level.rec (fun (l0 : Level) => Eq Nat (level_kind_ord l0) ir_d0 -> Eq Bool (level_is_zero l0) Bool.true) (fun (_h : Eq Nat (level_kind_ord Level.zero) ir_d0) => Eq.refl Bool Bool.true) (fun (p : Level) (_ih : Eq Nat (level_kind_ord p) ir_d0 -> Eq Bool (level_is_zero p) Bool.true) (h : Eq Nat (level_kind_ord (Level.succ p)) ir_d0) => nat_discr_p (Eq Bool (level_is_zero (Level.succ p)) Bool.true) (level_kind_ord (Level.succ p)) ir_d0 h (Eq.refl Bool Bool.false)) (fun (p : Level) (q : Level) (_ih1 : Eq Nat (level_kind_ord p) ir_d0 -> Eq Bool (level_is_zero p) Bool.true) (_ih2 : Eq Nat (level_kind_ord q) ir_d0 -> Eq Bool (level_is_zero q) Bool.true) (h : Eq Nat (level_kind_ord (Level.max p q)) ir_d0) => nat_discr_p (Eq Bool (level_is_zero (Level.max p q)) Bool.true) (level_kind_ord (Level.max p q)) ir_d0 h (Eq.refl Bool Bool.false)) (fun (p : Level) (q : Level) (_ih1 : Eq Nat (level_kind_ord p) ir_d0 -> Eq Bool (level_is_zero p) Bool.true) (_ih2 : Eq Nat (level_kind_ord q) ir_d0 -> Eq Bool (level_is_zero q) Bool.true) (h : Eq Nat (level_kind_ord (Level.imax p q)) ir_d0) => nat_discr_p (Eq Bool (level_is_zero (Level.imax p q)) Bool.true) (level_kind_ord (Level.imax p q)) ir_d0 h (Eq.refl Bool Bool.false)) (fun (nm : Name) (h : Eq Nat (level_kind_ord (Level.param nm)) ir_d0) => nat_discr_p (Eq Bool (level_is_zero (Level.param nm)) Bool.true) (level_kind_ord (Level.param nm)) ir_d0 h (Eq.refl Bool Bool.false)) l";

const SRC_IR_KO_MACHINE_SOUND_DENOT: &str = "def ir_ko_machine_sound_denot (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (henc : EncodesLevelKindCell mem r l) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0)))) : forall (rho : Name -> Nat), Eq Nat (level_eval rho l) Nat.zero := level_is_zero_sound l (level_kind_zero_is_zero l (ir_ko_machine_sound mem fuel na r l ir_d0 henc hle hret))";

const SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS: &str = "def ir_ko_machine_sound_denot_witness : forall (rho : Name -> Nat), Eq Nat (level_eval rho Level.zero) Nat.zero := ir_ko_machine_sound_denot (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) Level.zero (EncodesLevelKindCell.mk (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d0 ir_sp0 Level.zero (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d0 ir_sp0) Bool.true)))) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0))))";

const SRC_IR_KO_MACHINE_SOUND_WITNESS: &str = "def ir_ko_machine_sound_witness (l1 : Level) (l2 : Level) : Eq Nat (level_kind_ord (Level.max l1 l2)) ir_d2 := ir_ko_machine_sound (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 IRScalar.undef_ IRScalar.undef_)) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) (Level.max l1 l2) ir_d2 (EncodesLevelKindCell.mk (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 IRScalar.undef_ IRScalar.undef_)) ir_mem0) ir_d0 (ir_sp2 IRScalar.undef_ IRScalar.undef_) (Level.max l1 l2) (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d2 (ir_sp2 IRScalar.undef_ IRScalar.undef_)) Bool.true)))) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d2))))";

const SRC_IR_KO_NEVER_FAULTS: &str = "def ir_ko_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (henc : EncodesLevelKindCell mem r l) (hle : Le ir_d6 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_ko_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (level_kind_ord l)))) (ir_ko_correct mem fuel na r l henc hle)";

const SRC_IR_KO_KIND_BOUND: &str = "def ir_ko_kind_bound (l : Level) : Le (level_kind_ord l) ir_d4 := Level.rec (fun (l0 : Level) => Le (level_kind_ord l0) ir_d4) (Le.step ir_d0 ir_d3 (Le.step ir_d0 ir_d2 (Le.step ir_d0 ir_d1 (Le.step ir_d0 ir_d0 (Le.refl ir_d0))))) (fun (_p : Level) (_ih : Le (level_kind_ord _p) ir_d4) => (Le.step ir_d1 ir_d3 (Le.step ir_d1 ir_d2 (Le.step ir_d1 ir_d1 (Le.refl ir_d1))))) (fun (_p : Level) (_q : Level) (_ih1 : Le (level_kind_ord _p) ir_d4) (_ih2 : Le (level_kind_ord _q) ir_d4) => (Le.step ir_d2 ir_d3 (Le.step ir_d2 ir_d2 (Le.refl ir_d2)))) (fun (_p : Level) (_q : Level) (_ih1 : Le (level_kind_ord _p) ir_d4) (_ih2 : Le (level_kind_ord _q) ir_d4) => (Le.step ir_d3 ir_d3 (Le.refl ir_d3))) (fun (_nm : Name) => (Le.refl ir_d4)) l";

impl Specification {
    /// The width-one chain over the EMITTED shape of `Level::kind_ord`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_kind_ord(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_LEVEL_KIND_TAG, "level_kind_tag: the DISCRIMINANT the trust-ir producer assigns each Level variant -- declaration index 0..4, tag at spine slot 0 (the ir_var convention). This is a LAYOUT fact about the emitted artifact, not a fact about the source function. It is registered separately from level_kind_ord on purpose: the two coincide for Level and that coincidence is exactly why kind_ord is a five-constant switch in the shipped kernel, but they are different KINDS of claim and a layout change must be able to move one without the other. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_LEVEL_KIND_ORD, "level_kind_ord: the reflected Level::kind_ord (level/mod.rs:598-605) -- Lean 4's level_kind order, Zero=0 Succ=1 Max=2 IMax=3 Param=4, the key is_norm_lt sorts normalized levels by. The reflected SOURCE function. Unlike clean_mode_has_cubical this is not a predicate: it has FIVE distinct answers, so the equality theorem below cannot be discharged by a two-valued case split. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESLEVELKINDCELL, "EncodesLevelKindCell mem p l: the heap at p represents a Level whose TAG is l's, with an ARBITRARY payload. \n\nThis is deliberately WEAKER than EncodesLevelArc, and the weakness is the point. kind_ord reads field 0 and nothing else -- measured, in the emitted body: one load, one extractfield at index 0, then a switch. So the honest premise binds the tag and leaves the payload spine `fs` universally quantified: no child pointers, no liveness of children, no recursive structure. EncodesCleanMode could pin the whole payload (ir_sp0) because CleanMode is FIELDLESS; Level is payload-bearing and recursive, so this relation must be payload-agnostic or it would smuggle in facts the body never observes. \n\nStated as an EQUATION on ir_mem_lookup for the same reason as EncodesLevelArc: membership would be satisfied by a shadowed duplicate while the machine reads a different cell. The cell is pinned live because ir_load_cell faults ub bad_addr on a dead one, and the index is IRScalar.ptr_ a because ir_load_at faults ub null_deref on nullptr_. \n\nSAME OPEN LAYOUT OBLIGATION as eval_ir_repr's, carried forward rather than laundered: the tags here are trust-ir DECLARATION-INDEX tags, which is what the emitted body switches on. The Rust Level is niche-encoded downstream of trust-ir; that gap belongs to a layout-adequacy theorem nobody has earned yet. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENCODES_LEVEL_KIND_OF_ARC, "encodes_level_kind_of_arc: every heap the is_zero chain's A2 relation accepts is also accepted here. \n\nThe bridge from EncodesLevelArc, by EncodesLevelArc.rec, one arm per Level constructor, each discharging EncodesLevelKindCell.mk with that constructor's actual payload spine (ir_sp0 / ir_sp1 / ir_sp2). It makes the weakening CHECKED rather than asserted: if EncodesLevelKindCell had drifted to demand anything the recursive relation does not supply, this would not elaborate. It also means every witness the Level chain already builds is a witness here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_TENUM, "ir_ko_tenum: enum.2, the enum id the emitted body names in `load enum.2, ptr %0`. The cell-addressed semantics never consults it -- a load returns the stored value whatever its declared shape -- so it is transcribed for fidelity, not because anything dispatches on it.")?;
        self.add_recursive_def(SRC_IR_KO_B0, "ir_ko_b0: entry block, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/level_kind_ord.trust-ir.txt). Load *self, read the discriminant at field 0, dispatch. FOUR explicit switch cases (0->b1 Zero, 1->b2 Succ, 2->b3 Max, 3->b4 IMax) and a DEFAULT EDGE that carries the reachable Param arm -- not a five-way table and not an unreachable trap. exhaustive_enum_unreachable is Bool.false and that is the honest value: the default is reached on every Param. The flag is not printed by the text dumper and the semantics does not dispatch on it, so the CFG gate does not check it; it is recorded as a claim, not as evidence. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_KO_B1,
            "ir_ko_b1: Zero => 0u8, then br to the join. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_KO_B2, "ir_ko_b2: Succ => 1u8. A SEPARATE block from every other arm, as emitted -- five distinct constant blocks, not a shared one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_KO_B3,
            "ir_ko_b3: Max => 2u8. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_IR_KO_B4,
            "ir_ko_b4: IMax => 3u8. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_KO_B5, "ir_ko_b5: the DEFAULT edge => 4u8, i.e. Param. The emitted body routes the fifth variant through the switch default rather than listing it, so the default carries a real answer. This is the same shape Level::is_zero's emitted body has (its default carries the IMax arm) and the opposite of the hand-authored ir_lz_b6, which is an unreachable trap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_B6, "ir_ko_b6: the JOIN block, taking a u8 block PARAMETER. Five arms funnel through br into bb6(%1: u8) and the block returns its parameter. NOT a Bool parameter: this is the first chain in the spec whose join carries an integer, which is what routes the answer through ir_const_int_eval's width-8 residue rather than through IRConst.bool_. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_FUNC, "ir_ko_func: Level::kind_ord as EvalIR -- one parameter (the &Level receiver, SSA id 0), entry block 0, SEVEN blocks, matching the emitted body's control-flow graph exactly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_MODULE, "ir_ko_module: the module for Level::kind_ord, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/level_kind_ord.trust-ir.txt and checked graph-for-graph against this module by tests/crystal_a1_lineage.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_ON_ZERO, "GATE WITNESS: Zero, explicit switch case 0. Eq.refl -- the kernel runs the machine for 6 steps and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_ON_SUCC, "GATE WITNESS: Succ, explicit case 1, with a payload present (a child pointer) that the body must not read. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_ON_MAX, "GATE WITNESS: Max, explicit case 2, two-field payload. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_KO_ON_IMAX,
            "GATE WITNESS: IMax, explicit case 3. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_KO_ON_PARAM, "GATE WITNESS: Param, reached through the DEFAULT EDGE, and the payload is IRScalar.undef_ -- a value the semantics treats as unreadable. The machine still answers 4, which is the executable proof that this body never touches the payload. All FIVE emitted arms are executed by these witnesses; the has_cubical_layer chain executes four of six. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_MACH0, "ir_ko_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_AFTER_LOAD, "ir_ko_after_load: the entry step with the heap lookup made SYNTACTIC, so Eq.subst has something to rewrite. Binds %2, matching the emitted SSA numbering. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_EXACT, "ir_ko_exact: the machine agrees with the reflected kind_ord at EXACTLY 6 steps -- 3 in the entry block, 2 in an arm, 1 in the join -- for every Level constructor. Level.rec with a convoy motive carrying the lookup hypothesis, so all five tags compute; the payload spine fs stays a free variable throughout, which is what makes the four payload-bearing arms real rather than instantiated. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_CORRECT, "ir_ko_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE. *** For every Level l, every heap whose cell at the receiver carries l's tag with ANY payload, every next-address counter and every fuel at or above 6, ir_eval on ir_ko_module returns exactly IROutcome.ret [int (level_kind_ord l)]. \n\nThis is the second complete width-one chain in the repository and the first over a body that is not a two-valued predicate: the conclusion ranges over five distinct integers, the answer is carried through a u8 join-block parameter, and the subject type is Level -- payload-bearing and recursive -- rather than a fieldless enum. \n\nA0 is measured on the SHIPPED kernel at clean fcecd8d7e: lowered, spliced, unsupported [], derived_mir.verdict agreed (10 canonical lines identical), markers_exact TRUE, zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage.rs, which parses the recorded emitted trust-ir and requires this module to encode the same graph. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SCALAR_NAT, "ir_scalar_nat: read a Nat off a runtime value; zero on the eleven non-integer constructors. The integer counterpart of ir_scalar_bool, needed because this body's answer is a u8 and not a Bool. Its default collides with a real answer (0), exactly as ir_scalar_bool's Bool.false does -- harmless, because it is only ever applied by Eq.cong to two sides that are both IRScalar.int_. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VALS_HEAD_NAT, "ir_vals_head_nat: the Nat in the first returned value. kind_ord returns exactly one value. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_OUTCOME_NAT, "ir_outcome_nat: the Nat a successful outcome carries; zero for every fault and for exhaustion. Makes the A5 composition an equality argument rather than an inversion through three injectivity lemmas: apply the projection to both sides with Eq.cong and let the kernel compute. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_MACHINE_SOUND, "ir_ko_machine_sound: *** A5, THE INVERSION. *** If the MACHINE answers n, then the reflected kind_ord of the represented level IS n -- for every n, not just for a chosen one. Goes through A4 rather than restating it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_LEVEL_KIND_ZERO_IS_ZERO, "level_kind_zero_is_zero: kind_ord l = 0 implies Level::is_zero l -- the link that turns an ordering key into a fact about the level. By Level.rec: the Zero arm computes, and the four other arms are absurd via nat_discr_p, whose mismatch premise is literally Eq.refl Bool Bool.false because the numerals compute. \n\nONE-DIRECTIONAL and necessarily so: level_is_zero Level.max(zero,zero) is true while its kind_ord is 2, so the converse is false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_MACHINE_SOUND_DENOT, "ir_ko_machine_sound_denot: *** A5 REACHING MATHEMATICS. *** If the machine running the EMITTED kind_ord answers 0, then for EVERY assignment of parameters to naturals the level evaluates to 0. \n\nThis is the same denotational endpoint ir_lz_machine_sound reaches, arrived at through a DIFFERENT shipped kernel function -- and unlike ir_h2_machine_sound, which stops at the reflected predicate because there is no CleanMode semantics to compose with, this one composes: A4 gives kind_ord, level_kind_zero_is_zero converts an ordering key of 0 into definite-zeroness, and level_is_zero_sound converts that into level_eval rho l = 0. Both of A4's premises are carried through unchanged because neither can be dropped: without the representation the machine reads an unrelated heap, and without the fuel bound it may return fuel_out, which is not a return at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS, "ir_ko_machine_sound_denot_witness: A5 is not vacuous, and the witness RUNS THE MACHINE. Every premise discharged concretely at the one-cell heap encoding Level.zero: the representation by EncodesLevelKindCell.mk, the fuel bound by Le.refl at exactly 6, and the observation by Eq.refl, which the kernel discharges by executing the body. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_MACHINE_SOUND_WITNESS, "ir_ko_machine_sound_witness: the inversion is not vacuous at a PAYLOAD-BEARING tag, and the payload is genuinely unread. Instantiated at Max over two ARBITRARY sub-levels l1 l2, on a heap whose two payload fields are IRScalar.undef_ -- a value the semantics refuses to load through and cannot compare. The machine still answers 2 and the premises still discharge, which is the executable form of the claim that EncodesLevelKindCell's payload-agnosticism is real rather than decorative. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_NEVER_FAULTS, "ir_ko_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented level. *** A corollary of A4. IROutcome separates success from ub, type_error, unmodelled, stuck and fuel_out, so proving the outcome is a ret rules out all five at once. Concretely for the emitted body: the load never faults bad_addr or null_deref, the extractfield never faults not_agg, the default edge is a real answer rather than a trap, and 6 steps always suffice. All earned by EncodesLevelKindCell's premise, not assumed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_KO_KIND_BOUND, "ir_ko_kind_bound: the shipped kind_ord always returns a value at or below 4 -- it is a total five-valued ordering key, never out of domain. This is a statement the has_cubical_layer chain has no analogue of, because a Bool has no range to bound; it is the property is_norm_lt relies on when it sorts normalized levels by kind. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The switch must be FOUR explicit cases plus a default that carries the
    /// fifth answer — the emitted shape. A five-case table, or a default
    /// routed to a trap, is a different body.
    #[test]
    fn test_switch_matches_emitted_four_cases_plus_reachable_default() {
        assert!(SRC_IR_KO_B0
            .contains("(ir_sc ir_d0 ir_d1 (ir_sc ir_d1 ir_d2 (ir_sc ir_d2 ir_d3 (ir_sc ir_d3 ir_d4 ir_sc0))))"));
        assert!(
            !SRC_IR_KO_B0.contains("ir_sc ir_d4"),
            "the emitted switch lists no tag-4 case; Param goes through the default"
        );
        // the default target is b5, and b5 is a real answer, not a trap
        assert!(SRC_IR_KO_B0.contains("IRInst.switch ir_d3 ir_d5 ir_nl0"));
        assert!(SRC_IR_KO_B5.contains("IRConst.int_ ir_d4"));
        for s in [
            SRC_IR_KO_B0,
            SRC_IR_KO_B1,
            SRC_IR_KO_B2,
            SRC_IR_KO_B3,
            SRC_IR_KO_B4,
            SRC_IR_KO_B5,
            SRC_IR_KO_B6,
        ] {
            assert!(
                !s.contains("unreachable"),
                "the emitted body has no trap block"
            );
        }
    }

    /// Five SEPARATE constant blocks with five DISTINCT answers. This is what
    /// makes the chain more than a predicate: collapsing any two is a
    /// different CFG and a different theorem.
    #[test]
    fn test_five_distinct_constant_arms() {
        let arms = [
            (SRC_IR_KO_B1, "ir_d0"),
            (SRC_IR_KO_B2, "ir_d1"),
            (SRC_IR_KO_B3, "ir_d2"),
            (SRC_IR_KO_B4, "ir_d3"),
            (SRC_IR_KO_B5, "ir_d4"),
        ];
        for (src, val) in arms {
            assert!(
                src.contains(&format!("IRConst.int_ {val}")),
                "arm must materialize {val}"
            );
            assert!(
                src.contains("IRInst.br ir_d6"),
                "every arm branches to the join"
            );
            assert!(
                !src.contains("IRConst.bool_"),
                "this body's answers are integers, not Bools"
            );
        }
        let mut seen: Vec<&str> = arms.iter().map(|(s, _)| *s).collect();
        seen.sort_unstable();
        seen.dedup();
        assert_eq!(seen.len(), 5, "five distinct arm blocks, as emitted");
    }

    /// The join block takes a `u8` parameter, not a `bool`. That is the
    /// difference that routes the answer through `ir_const_int_eval`.
    #[test]
    fn test_join_block_takes_an_integer_parameter() {
        assert!(SRC_IR_KO_B6.contains("IRBlock.mk ir_d6 (ir_nl1 ir_d1)"));
        assert!(SRC_IR_KO_B6.contains("IRInst.ret (ir_nl1 ir_d1)"));
        for src in [
            SRC_IR_KO_B1,
            SRC_IR_KO_B2,
            SRC_IR_KO_B3,
            SRC_IR_KO_B4,
            SRC_IR_KO_B5,
        ] {
            assert!(src.contains("IRInst.const_ ir_tU8"));
        }
    }

    /// The representation premise must stay PAYLOAD-AGNOSTIC. Pinning the
    /// spine would smuggle in facts the emitted body never observes, and would
    /// make this chain a re-run of the fieldless-enum one.
    #[test]
    fn test_representation_is_payload_agnostic() {
        assert!(SRC_ENCODESLEVELKINDCELL.contains("(fs : IRScalar)"));
        assert!(SRC_ENCODESLEVELKINDCELL.contains("(ir_var (level_kind_tag l) fs)"));
        for pinned in ["ir_sp0)", "ir_sp1", "ir_sp2"] {
            assert!(
                !SRC_ENCODESLEVELKINDCELL.contains(pinned),
                "the payload spine must not be pinned to {pinned}"
            );
        }
        // exactly one lookup EQUATION; membership would be satisfiable by a
        // shadowed duplicate while the machine reads a different cell
        assert_eq!(
            SRC_ENCODESLEVELKINDCELL
                .matches("ir_mem_lookup mem")
                .count(),
            1
        );
        assert!(SRC_ENCODESLEVELKINDCELL.contains("(IRScalar.ptr_ a)"));
        assert!(SRC_ENCODESLEVELKINDCELL.contains("Bool.true"));
        for bad in ["Exists", "Sigma"] {
            assert!(!SRC_ENCODESLEVELKINDCELL.contains(bad));
        }
    }

    /// The bridge makes the weakening CHECKED: every heap the recursive `Level`
    /// relation accepts is accepted here, one arm per constructor.
    #[test]
    fn test_bridge_covers_every_level_constructor() {
        for ctor in [
            "Level.zero",
            "Level.succ",
            "Level.max",
            "Level.imax",
            "Level.param",
        ] {
            assert!(
                SRC_ENCODES_LEVEL_KIND_OF_ARC.contains(ctor),
                "no bridge arm for {ctor}"
            );
        }
        assert!(SRC_ENCODES_LEVEL_KIND_OF_ARC.contains("EncodesLevelArc.rec mem"));
        assert!(SRC_ENCODES_LEVEL_KIND_OF_ARC
            .contains("(_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1)"));
    }

    /// A4 stays universally quantified over `Level`, over the heap, and over
    /// the fuel. Naming a constructor in the statement would make it a sample.
    #[test]
    fn test_a4_shape() {
        let statement = SRC_IR_KO_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(l : Level)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(SRC_IR_KO_CORRECT.contains("Le ir_d6 fuel ->"));
        assert!(SRC_IR_KO_CORRECT.contains("ir_run_le_ret"));
        for c in ["Level.zero", "Level.succ", "Level.max", "Level.imax"] {
            assert!(
                !statement.contains(c),
                "A4's STATEMENT must not mention {c}"
            );
        }
        assert!(
            !statement.contains("ir_cell"),
            "a concrete heap would make this a witness, not a theorem"
        );
    }

    /// A5 exists, composes with A4 through `ir_outcome_nat`, and reaches a
    /// denotational conclusion rather than stopping at the reflected function.
    /// The `has_cubical_layer` chain lost its A5 once, silently, to a
    /// re-authoring; nothing noticed for two days. This is what notices.
    #[test]
    fn test_a5_is_present_and_reaches_level_eval() {
        assert!(SRC_IR_KO_MACHINE_SOUND.contains("ir_eval fuel ir_ko_module"));
        assert!(SRC_IR_KO_MACHINE_SOUND.contains(": Eq Nat (level_kind_ord l) n"));
        assert!(SRC_IR_KO_MACHINE_SOUND.contains("ir_ko_correct mem fuel na r l henc hle"));
        assert!(SRC_IR_KO_MACHINE_SOUND.contains("ir_outcome_nat"));
        // …and the denotational step, which ir_h2_machine_sound has no
        // analogue of because there is no CleanMode semantics to compose with.
        assert!(SRC_IR_KO_MACHINE_SOUND_DENOT.contains("level_is_zero_sound"));
        assert!(SRC_IR_KO_MACHINE_SOUND_DENOT.contains("level_kind_zero_is_zero"));
        assert!(SRC_IR_KO_MACHINE_SOUND_DENOT
            .contains("forall (rho : Name -> Nat), Eq Nat (level_eval rho l) Nat.zero"));
        assert!(SRC_IR_KO_NEVER_FAULTS.contains("ir_outcome_is_ret"));
    }

    /// Every premise of A5 is discharged concretely, and the payload-bearing
    /// witness runs on `undef_` payloads over ARBITRARY sub-levels — the
    /// executable form of payload-agnosticism.
    #[test]
    fn test_a5_witnesses_are_concrete_and_run_the_machine() {
        assert!(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS.contains("EncodesLevelKindCell.mk"));
        assert!(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS.contains("Le.refl ir_d6"));
        assert!(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS.contains("Eq.refl IROutcome"));
        assert!(SRC_IR_KO_MACHINE_SOUND_WITNESS.contains("(l1 : Level) (l2 : Level)"));
        assert!(
            SRC_IR_KO_MACHINE_SOUND_WITNESS.contains("(ir_sp2 IRScalar.undef_ IRScalar.undef_)")
        );
    }

    /// All FIVE emitted arms are executed, including the default edge, and the
    /// default-edge witness carries an unreadable payload.
    #[test]
    fn test_every_emitted_arm_has_an_executed_witness() {
        let witnesses = [
            (SRC_IR_KO_ON_ZERO, "ir_var ir_d0", "ir_d0"),
            (SRC_IR_KO_ON_SUCC, "ir_var ir_d1", "ir_d1"),
            (SRC_IR_KO_ON_MAX, "ir_var ir_d2", "ir_d2"),
            (SRC_IR_KO_ON_IMAX, "ir_var ir_d3", "ir_d3"),
            (SRC_IR_KO_ON_PARAM, "ir_var ir_d4", "ir_d4"),
        ];
        for (src, cell, ans) in witnesses {
            assert!(src.contains(cell), "witness must encode {cell}");
            assert!(src.contains(&format!("IRScalar.int_ {ans}")));
            assert!(src.contains("Eq.refl IROutcome"), "discharged by execution");
        }
        assert!(
            SRC_IR_KO_ON_PARAM.contains("IRScalar.undef_"),
            "the default-edge witness must carry an unreadable payload"
        );
    }

    /// The fuel bound must match the transcribed module's cost: 3 steps in the
    /// entry block, 2 in an arm, 1 in the join.
    #[test]
    fn test_fuel_bound_matches_the_transcribed_module() {
        for src in [
            SRC_IR_KO_CORRECT,
            SRC_IR_KO_MACHINE_SOUND,
            SRC_IR_KO_MACHINE_SOUND_DENOT,
            SRC_IR_KO_NEVER_FAULTS,
        ] {
            assert!(src.contains("Le ir_d6 fuel"));
        }
        assert!(SRC_IR_KO_EXACT.contains("ir_run ir_d6 ir_ko_module"));
    }

    /// `level_kind_tag` (a LAYOUT claim) and `level_kind_ord` (the reflected
    /// SOURCE function) coincide for `Level` and must stay separately stated,
    /// so a layout change can move one without silently moving the other.
    #[test]
    fn test_tag_and_ord_are_separate_declarations() {
        assert!(SRC_LEVEL_KIND_TAG.starts_with("def level_kind_tag"));
        assert!(SRC_LEVEL_KIND_ORD.starts_with("def level_kind_ord"));
        assert_eq!(
            SRC_LEVEL_KIND_TAG.replace("level_kind_tag", "X"),
            SRC_LEVEL_KIND_ORD.replace("level_kind_ord", "X"),
            "they coincide today; that is a measured fact about Level, and it is \
             exactly why the two must remain distinguishable"
        );
        // the relation is stated with the LAYOUT function…
        assert!(SRC_ENCODESLEVELKINDCELL.contains("level_kind_tag"));
        // …and the theorem's conclusion with the SOURCE one
        assert!(SRC_IR_KO_CORRECT.contains("IRScalar.int_ (level_kind_ord l)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_LEVEL_KIND_TAG,
            SRC_LEVEL_KIND_ORD,
            SRC_ENCODESLEVELKINDCELL,
            SRC_ENCODES_LEVEL_KIND_OF_ARC,
            SRC_IR_KO_B0,
            SRC_IR_KO_MODULE,
            SRC_IR_KO_EXACT,
            SRC_IR_KO_CORRECT,
            SRC_IR_KO_MACHINE_SOUND,
            SRC_LEVEL_KIND_ZERO_IS_ZERO,
            SRC_IR_KO_MACHINE_SOUND_DENOT,
            SRC_IR_KO_NEVER_FAULTS,
            SRC_IR_KO_KIND_BOUND,
        ] {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count());
        }
    }
}
