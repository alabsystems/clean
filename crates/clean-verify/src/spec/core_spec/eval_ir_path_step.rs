// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The SEVENTH complete width-one chain — the widest dispatch in the program,
//! and the first whose subject is a DERIVED impl:
//! `<tc::expr_location::ExprPathStep as Clone>::clone`.**
//!
//! ```text
//! #[derive(Debug, Clone, PartialEq, Eq)]
//! #[non_exhaustive]
//! pub enum ExprPathStep { AppFn, AppArg, LamBody, /* … */ ProjExpr }   // 11 variants
//! ```
//!
//! Thirteen blocks, ten explicit switch cases plus a reachable default, eleven
//! aggregate constants, one `load`, one `extractfield`, one join block carrying
//! a structured value. Nobody wrote this body: `#[derive(Clone)]` did, and the
//! chain is a theorem about what the DERIVE expanded to in the shipped
//! artifact.
//!
//! ## What this chain adds over the six that exist
//!
//! | axis | earlier chains | `ExprPathStep::clone` |
//! |---|---|---|
//! | blocks | 14 max (`from_source_system`) | **13** |
//! | authorship | hand-written kernel code | **`#[derive(Clone)]` expansion** |
//! | argument | by value (3rd, 4th, 5th, 6th) or `&` + `load` (1st, 2nd) | **`&` + `load`, answering an AGGREGATE** |
//! | answer | `bool`, `u8`, `CleanMode` tag | **the argument's own type** |
//! | theorem | "the machine computes f" | **"the machine's answer DECODES BACK to the variant it was handed"** |
//!
//! It is the first chain to combine the two shapes the earlier ones had
//! separately: `has_cubical_layer`'s `load` + `extractfield` prologue (its
//! argument is `&self`) with `from_source_system`'s aggregate-constant arms and
//! aggregate-carrying join block. No build item was needed — the `IRConst`
//! aggregate spine that the third chain landed is exactly what this body needs,
//! which is why the 2026-08-12 candidate measurement recorded these two bodies
//! as emitting the SAME constant shape (`const enum.13 { k }` /
//! `const enum.181 { k }`) and refused both for the same reason.
//!
//! ## The theorem is the clone contract, not a tautology
//!
//! `expr_path_step_clone` is written as an ELEVEN-ARM case analysis, because
//! that is what the compiler emitted — eleven separate blocks, each
//! materialising its own constant. It is *not* written as `fun s => s`, which
//! would be a claim about the derive rather than a transcription of it.
//! `expr_path_step_clone_id` then proves, by eleven `Eq.refl`s, that the emitted
//! eleven-arm dispatch IS the identity; and `ir_ep_machine_sound_step` composes
//! that with a total left inverse of the tag to conclude
//!
//! > if the machine running the EMITTED body answers a value tagged `t`, then
//! > `expr_path_step_of_tag t` is the very variant the caller passed in.
//!
//! That is the property `Clone` is supposed to have, proved about the artifact
//! rather than about the source.
//!
//! ## `markers_exact` here is VACUOUS, and it is said rather than implied
//!
//! Measured at HEAD: this body's coverage row carries `markers_exact: true`
//! with `markers_detail: "0 marker line(s) identical"` — two EMPTY marker
//! sequences compared. It is in the vacuous 1,057 of 1,084, with the first
//! three chains and unlike the fourth, fifth and sixth (8, 21 and 12 real
//! lines). What the marker channel contributed to this chain's certification is
//! **nothing**. What did back it is not small and is unchanged: `agreed` over
//! **16 canonical lines** (the longest canonical comparison of any chained
//! body), `unsupported: []`, zero calls, and a codegen flip event whose A-LIN
//! lineage equals the coverage row's.
//!
//! The producer's own interpreter differential is `not-run` here, and the
//! recorded reason is specific rather than generic: *"param 0 (ptr) is READ
//! (dereferenced/used) — opaque sampling refused"*.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `EncodesExprPathStep` speaks about trust-ir DECLARATION-INDEX tags, which is
//! what the emitted body switches on; the Rust enum is niche-encoded downstream
//! of trust-ir, and that open layout obligation is inherited from
//! `eval_ir_repr`, not discharged here. `expr_path_step_of_tag` is total, so it
//! answers `projexpr` for every `n >= 10`; that arbitrariness is harmless
//! because `expr_path_step_of_tag_tag` only ever applies it to a real tag, and
//! it is stated rather than hidden.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/expr_path_step_clone.rs`. Everything past the flip
//! seam is downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_EXPRPATHSTEPR: &str = "inductive ExprPathStepR : Type\n| appfn : ExprPathStepR\n| apparg : ExprPathStepR\n| lambody : ExprPathStepR\n| lamtype : ExprPathStepR\n| pidom : ExprPathStepR\n| pibody : ExprPathStepR\n| lettype : ExprPathStepR\n| letval : ExprPathStepR\n| letbody : ExprPathStepR\n| mdataexpr : ExprPathStepR\n| projexpr : ExprPathStepR";
const SRC_EXPR_PATH_STEP_TAG: &str = "def expr_path_step_tag (s : ExprPathStepR) : Nat := ExprPathStepR.rec (fun (_ : ExprPathStepR) => Nat) ir_d0 ir_d1 ir_d2 ir_d3 ir_d4 ir_d5 ir_d6 ir_d7 ir_d8 ir_d9 ir_d10 s";
const SRC_EXPR_PATH_STEP_CLONE: &str = "def expr_path_step_clone (s : ExprPathStepR) : ExprPathStepR := ExprPathStepR.rec (fun (_ : ExprPathStepR) => ExprPathStepR) ExprPathStepR.appfn ExprPathStepR.apparg ExprPathStepR.lambody ExprPathStepR.lamtype ExprPathStepR.pidom ExprPathStepR.pibody ExprPathStepR.lettype ExprPathStepR.letval ExprPathStepR.letbody ExprPathStepR.mdataexpr ExprPathStepR.projexpr s";
const SRC_EXPR_PATH_STEP_OF_TAG: &str = "def expr_path_step_of_tag (n : Nat) : ExprPathStepR := Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (Bool.rec (fun (_ : Bool) => ExprPathStepR) (ExprPathStepR.projexpr) ExprPathStepR.mdataexpr (ir_nat_eqb n ir_d9)) ExprPathStepR.letbody (ir_nat_eqb n ir_d8)) ExprPathStepR.letval (ir_nat_eqb n ir_d7)) ExprPathStepR.lettype (ir_nat_eqb n ir_d6)) ExprPathStepR.pibody (ir_nat_eqb n ir_d5)) ExprPathStepR.pidom (ir_nat_eqb n ir_d4)) ExprPathStepR.lamtype (ir_nat_eqb n ir_d3)) ExprPathStepR.lambody (ir_nat_eqb n ir_d2)) ExprPathStepR.apparg (ir_nat_eqb n ir_d1)) ExprPathStepR.appfn (ir_nat_eqb n ir_d0)";
const SRC_EXPR_PATH_STEP_CLONE_ID: &str = "def expr_path_step_clone_id (s : ExprPathStepR) : Eq ExprPathStepR (expr_path_step_clone s) s := ExprPathStepR.rec (fun (s0 : ExprPathStepR) => Eq ExprPathStepR (expr_path_step_clone s0) s0) (Eq.refl ExprPathStepR ExprPathStepR.appfn) (Eq.refl ExprPathStepR ExprPathStepR.apparg) (Eq.refl ExprPathStepR ExprPathStepR.lambody) (Eq.refl ExprPathStepR ExprPathStepR.lamtype) (Eq.refl ExprPathStepR ExprPathStepR.pidom) (Eq.refl ExprPathStepR ExprPathStepR.pibody) (Eq.refl ExprPathStepR ExprPathStepR.lettype) (Eq.refl ExprPathStepR ExprPathStepR.letval) (Eq.refl ExprPathStepR ExprPathStepR.letbody) (Eq.refl ExprPathStepR ExprPathStepR.mdataexpr) (Eq.refl ExprPathStepR ExprPathStepR.projexpr) s";
const SRC_EXPR_PATH_STEP_OF_TAG_TAG: &str = "def expr_path_step_of_tag_tag (s : ExprPathStepR) : Eq ExprPathStepR (expr_path_step_of_tag (expr_path_step_tag s)) s := ExprPathStepR.rec (fun (s0 : ExprPathStepR) => Eq ExprPathStepR (expr_path_step_of_tag (expr_path_step_tag s0)) s0) (Eq.refl ExprPathStepR ExprPathStepR.appfn) (Eq.refl ExprPathStepR ExprPathStepR.apparg) (Eq.refl ExprPathStepR ExprPathStepR.lambody) (Eq.refl ExprPathStepR ExprPathStepR.lamtype) (Eq.refl ExprPathStepR ExprPathStepR.pidom) (Eq.refl ExprPathStepR ExprPathStepR.pibody) (Eq.refl ExprPathStepR ExprPathStepR.lettype) (Eq.refl ExprPathStepR ExprPathStepR.letval) (Eq.refl ExprPathStepR ExprPathStepR.letbody) (Eq.refl ExprPathStepR ExprPathStepR.mdataexpr) (Eq.refl ExprPathStepR ExprPathStepR.projexpr) s";
const SRC_ENCODESEXPRPATHSTEP: &str = "inductive EncodesExprPathStep (mem : IRList IRMemSlot) : IRScalar -> ExprPathStepR -> Type\n| mk : forall (a : Nat) (s : ExprPathStepR) (fs : IRScalar), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (expr_path_step_tag s) fs) Bool.true)) -> EncodesExprPathStep mem (IRScalar.ptr_ a) s";
const SRC_IR_EP_TSTEP: &str = "def ir_ep_tstep : IRTy := IRTy.enum_ 181";
const SRC_IR_EP_B0: &str = "def ir_ep_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.load ir_ep_tstep ir_d0 Bool.false) ir_d2) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3) (ir_nd (IRInst.switch ir_d3 ir_d11 ir_nl0 (ir_sc ir_d0 ir_d1 (ir_sc ir_d1 ir_d2 (ir_sc ir_d2 ir_d3 (ir_sc ir_d3 ir_d4 (ir_sc ir_d4 ir_d5 (ir_sc ir_d5 ir_d6 (ir_sc ir_d6 ir_d7 (ir_sc ir_d7 ir_d8 (ir_sc ir_d8 ir_d9 (ir_sc ir_d9 ir_d10 ir_sc0)))))))))) Bool.false)))";
const SRC_IR_EP_B1: &str = "def ir_ep_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d0)) ir_d4) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d4))))";
const SRC_IR_EP_B2: &str = "def ir_ep_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d1)) ir_d5) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d5))))";
const SRC_IR_EP_B3: &str = "def ir_ep_b3 : IRBlock := IRBlock.mk ir_d3 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d2)) ir_d6) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d6))))";
const SRC_IR_EP_B4: &str = "def ir_ep_b4 : IRBlock := IRBlock.mk ir_d4 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d3)) ir_d7) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d7))))";
const SRC_IR_EP_B5: &str = "def ir_ep_b5 : IRBlock := IRBlock.mk ir_d5 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d4)) ir_d8) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d8))))";
const SRC_IR_EP_B6: &str = "def ir_ep_b6 : IRBlock := IRBlock.mk ir_d6 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d5)) ir_d9) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d9))))";
const SRC_IR_EP_B7: &str = "def ir_ep_b7 : IRBlock := IRBlock.mk ir_d7 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d6)) ir_d10) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d10))))";
const SRC_IR_EP_B8: &str = "def ir_ep_b8 : IRBlock := IRBlock.mk ir_d8 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d7)) ir_d11) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d11))))";
const SRC_IR_EP_B9: &str = "def ir_ep_b9 : IRBlock := IRBlock.mk ir_d9 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d8)) ir_d12) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d12))))";
const SRC_IR_EP_B10: &str = "def ir_ep_b10 : IRBlock := IRBlock.mk ir_d10 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d9)) ir_d13) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d13))))";
const SRC_IR_EP_B11: &str = "def ir_ep_b11 : IRBlock := IRBlock.mk ir_d11 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d10)) ir_d14) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d14))))";
const SRC_IR_EP_B12: &str = "def ir_ep_b12 : IRBlock := IRBlock.mk ir_d12 (ir_nl1 ir_d1) (ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d1))))";
const SRC_IR_EP_FUNC: &str = "def ir_ep_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_ep_b0 (ir_blk ir_ep_b1 (ir_blk ir_ep_b2 (ir_blk ir_ep_b3 (ir_blk ir_ep_b4 (ir_blk ir_ep_b5 (ir_blk ir_ep_b6 (ir_blk ir_ep_b7 (ir_blk ir_ep_b8 (ir_blk ir_ep_b9 (ir_blk ir_ep_b10 (ir_blk ir_ep_b11 (ir_blk ir_ep_b12 ir_blk0)))))))))))))";
const SRC_IR_EP_MODULE: &str = "def ir_ep_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_ep_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";
const SRC_IR_EP_ON_APPFN: &str = "def ir_ep_on_appfn : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0)))";
const SRC_IR_EP_ON_APPARG: &str = "def ir_ep_on_apparg : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0)))";
const SRC_IR_EP_ON_LAMBODY: &str = "def ir_ep_on_lambody : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d2 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0)))";
const SRC_IR_EP_ON_LAMTYPE: &str = "def ir_ep_on_lamtype : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d3 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d3 ir_sp0)))";
const SRC_IR_EP_ON_PIDOM: &str = "def ir_ep_on_pidom : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d4 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_EP_ON_PIBODY: &str = "def ir_ep_on_pibody : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d5 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0)))";
const SRC_IR_EP_ON_LETTYPE: &str = "def ir_ep_on_lettype : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d6 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d6 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d6 ir_sp0)))";
const SRC_IR_EP_ON_LETVAL: &str = "def ir_ep_on_letval : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d7 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d7 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d7 ir_sp0)))";
const SRC_IR_EP_ON_LETBODY: &str = "def ir_ep_on_letbody : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d8 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d8 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d8 ir_sp0)))";
const SRC_IR_EP_ON_MDATAEXPR: &str = "def ir_ep_on_mdataexpr : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d9 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d9 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d9 ir_sp0)))";
const SRC_IR_EP_ON_PROJEXPR: &str = "def ir_ep_on_projexpr : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d10 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0)))";
const SRC_IR_EP_ON_PAYLOAD_JUNK: &str = "def ir_ep_on_payload_junk : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d10 (ir_sp2 IRScalar.undef_ IRScalar.vnil)) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0)))";
const SRC_IR_EP_MACH0: &str = "def ir_ep_mach0 (mem : IRList IRMemSlot) (a : Nat) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.ptr_ a)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_EP_AFTER_LOAD: &str = "def ir_ep_after_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (o : (IROption IRMemSlot)) : IRConfig := ir_bind_result (ir_ep_mach0 mem a na) (ir_nl1 ir_d2) (ir_load_slot o)";
const SRC_IR_EP_EXACT: &str = "def ir_ep_exact (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) (s : ExprPathStepR) : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (expr_path_step_tag s) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ep_module (IRConfig.running (ir_ep_mach0 mem a na))) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s)) ir_sp0))) := ExprPathStepR.rec (fun (s0 : ExprPathStepR) => Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (expr_path_step_tag s0) fs) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_ep_module (IRConfig.running (ir_ep_mach0 mem a na))) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s0)) ir_sp0)))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d3 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d3 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d5 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d5 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d5 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d6 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d6 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d6 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d6 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d6 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d7 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d7 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d7 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d7 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d7 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d8 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d8 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d8 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d8 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d8 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d9 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d9 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d9 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d9 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d9 ir_sp0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d10 fs) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_ep_module (ir_ep_after_load mem a na o)) (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d10 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d10 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0))))) s";
const SRC_IR_EP_CORRECT: &str = "def ir_ep_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : ExprPathStepR) (henc : EncodesExprPathStep mem r s) : Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s)) ir_sp0))) := EncodesExprPathStep.rec mem (fun (r0 : IRScalar) (s0 : ExprPathStepR) (_ : EncodesExprPathStep mem r0 s0) => Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r0) mem na) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s0)) ir_sp0)))) (fun (a : Nat) (s0 : ExprPathStepR) (fs : IRScalar) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (expr_path_step_tag s0) fs) Bool.true))) (hle : Le ir_d6 fuel) => ir_run_le_ret ir_ep_module ir_d6 fuel hle (IRConfig.running (ir_ep_mach0 mem a na)) (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s0)) ir_sp0)) (ir_ep_exact mem a na fs s0 h)) r s henc";
const SRC_IR_EP_MACHINE_SOUND: &str = "def ir_ep_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : ExprPathStepR) (t : Nat) (henc : EncodesExprPathStep mem r s) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0)))) : Eq Nat (expr_path_step_tag (expr_path_step_clone s)) t := Eq.cong IROutcome Nat ir_outcome_disc (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s)) ir_sp0))) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s)) ir_sp0))) (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0))) (Eq.symm IROutcome (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s)) ir_sp0))) (ir_ep_correct mem fuel na r s henc hle)) hret)";
const SRC_IR_EP_MACHINE_SOUND_STEP: &str = "def ir_ep_machine_sound_step (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : ExprPathStepR) (t : Nat) (henc : EncodesExprPathStep mem r s) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0)))) : Eq ExprPathStepR (expr_path_step_of_tag t) s := Eq.trans ExprPathStepR (expr_path_step_of_tag t) (expr_path_step_of_tag (expr_path_step_tag s)) s (Eq.symm ExprPathStepR (expr_path_step_of_tag (expr_path_step_tag s)) (expr_path_step_of_tag t) (Eq.cong Nat ExprPathStepR expr_path_step_of_tag (expr_path_step_tag s) t (Eq.trans Nat (expr_path_step_tag s) (expr_path_step_tag (expr_path_step_clone s)) t (Eq.symm Nat (expr_path_step_tag (expr_path_step_clone s)) (expr_path_step_tag s) (Eq.cong ExprPathStepR Nat expr_path_step_tag (expr_path_step_clone s) s (expr_path_step_clone_id s))) (ir_ep_machine_sound mem fuel na r s t henc hle hret)))) (expr_path_step_of_tag_tag s)";
const SRC_IR_EP_NEVER_FAULTS: &str = "def ir_ep_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : ExprPathStepR) (henc : EncodesExprPathStep mem r s) (hle : Le ir_d6 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_ep_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone s)) ir_sp0))) (ir_ep_correct mem fuel na r s henc hle)";
const SRC_IR_EP_CORRECT_WITNESS: &str = "def ir_ep_correct_witness : Eq IROutcome (ir_eval ir_d6 ir_ep_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (ir_var (expr_path_step_tag (expr_path_step_clone ExprPathStepR.lamtype)) ir_sp0))) := ir_ep_correct (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) ExprPathStepR.lamtype (EncodesExprPathStep.mk (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d0 ExprPathStepR.lamtype ir_sp0 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d3 ir_sp0) Bool.true)))) (Le.refl ir_d6)";
const SRC_IR_EP_MACHINE_SOUND_WITNESS: &str = "def ir_ep_machine_sound_witness : Eq Nat (expr_path_step_tag (expr_path_step_clone ExprPathStepR.lamtype)) ir_d3 := ir_ep_machine_sound (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) ExprPathStepR.lamtype ir_d3 (EncodesExprPathStep.mk (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d0 ExprPathStepR.lamtype ir_sp0 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d3 ir_sp0) Bool.true)))) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d3 ir_sp0))))";
const SRC_IR_EP_MACHINE_SOUND_STEP_WITNESS: &str = "def ir_ep_machine_sound_step_witness : Eq ExprPathStepR (expr_path_step_of_tag ir_d3) ExprPathStepR.lamtype := ir_ep_machine_sound_step (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) ExprPathStepR.lamtype ir_d3 (EncodesExprPathStep.mk (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d0 ExprPathStepR.lamtype ir_sp0 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d3 ir_sp0) Bool.true)))) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d3 ir_sp0))))";
const SRC_IR_EP_MACHINE_SOUND_JUNK_WITNESS: &str = "def ir_ep_machine_sound_junk_witness : Eq ExprPathStepR (expr_path_step_of_tag ir_d10) ExprPathStepR.projexpr := ir_ep_machine_sound_step (ir_cell ir_d0 (ir_var ir_d10 (ir_sp2 IRScalar.undef_ IRScalar.vnil)) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) ExprPathStepR.projexpr ir_d10 (EncodesExprPathStep.mk (ir_cell ir_d0 (ir_var ir_d10 (ir_sp2 IRScalar.undef_ IRScalar.vnil)) ir_mem0) ir_d0 ExprPathStepR.projexpr (ir_sp2 IRScalar.undef_ IRScalar.vnil) (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d10 (ir_sp2 IRScalar.undef_ IRScalar.vnil)) Bool.true)))) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d10 ir_sp0))))";

impl Specification {
    /// Register the SEVENTH complete width-one chain, and the first whose
    /// subject was written by a derive macro rather than by hand:
    /// `<tc::expr_location::ExprPathStep as Clone>::clone`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_path_step(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_EXPRPATHSTEPR, "ExprPathStepR: the reflected ExprPathStep (tc/expr_location.rs:22-44). ELEVEN fieldless variants in declaration order, so a value IS its discriminant -- which is why the derive expands to a plain discriminant switch and why this body is in the class the flip gate accepts. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_PATH_STEP_TAG, "expr_path_step_tag: each variant's discriminant, 0..10 in declaration order. The ONE place the reflected argument type meets the emitted layout, and the reason the emitted switch lists 0..9 explicitly and routes tag 10 (ProjExpr) through the default edge. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_PATH_STEP_CLONE, "expr_path_step_clone: the reflected `<ExprPathStep as Clone>::clone`, written as an ELEVEN-ARM case analysis because that is what #[derive(Clone)] expanded to -- eleven separate blocks each materializing its own constant. It is deliberately NOT written as `fun s => s`: that would be a claim about the derive rather than a transcription of it. The identity is PROVED separately, by expr_path_step_clone_id. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_PATH_STEP_OF_TAG, "expr_path_step_of_tag: a total left inverse of expr_path_step_tag on 0..10, by a chain of decidable Nat equalities. Total means it must answer somewhere off the tag range: every n >= 10 answers projexpr, which is correct AT 10 and arbitrary above it. Harmless and stated rather than hidden -- expr_path_step_of_tag_tag only applies it to a real tag, and the A5 that uses it obtains its argument from expr_path_step_tag. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_PATH_STEP_CLONE_ID, "expr_path_step_clone_id: *** THE EMITTED ELEVEN-ARM DISPATCH IS THE IDENTITY. *** Eleven Eq.refl arms; the kernel selects each variant's constant and compares it with the variant. This is the fact that turns a transcription of a derive into the clone contract, and it is proved rather than assumed precisely because the module above transcribes the eleven arms instead of collapsing them. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_PATH_STEP_OF_TAG_TAG, "expr_path_step_of_tag_tag: expr_path_step_of_tag inverts expr_path_step_tag on every ExprPathStepR, by ExprPathStepR.rec with eleven Eq.refl arms -- the kernel computes each tag and re-selects the variant. This is what upgrades the A5 below from a statement about a NUMBER to a statement about a VARIANT. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESEXPRPATHSTEP, "EncodesExprPathStep mem v s: the IRScalar v is the BY-REFERENCE representation of path step s. \n\nA heap premise, unlike the third chain's: this body's argument is `&self` (`bb0(%0: ptr)`) and the emitted body LOADS through it, so there is a cell to pin and it is pinned. Stated as an EQUATION ON ir_mem_lookup, never as list membership -- ir_mem_lookup is head-first first-match, so a membership premise would be satisfied by a SHADOWED DUPLICATE while the machine reads a different cell. \n\nPayload-agnostic on purpose: the element spine fs is universally quantified, because the body reads field 0 and nothing else -- measured, in the emitted body: one load, one extractfield at index 0, then a switch. ExprPathStep is fieldless so a real value's spine is ir_sp0, but quantifying makes the 'reads only the tag' claim checked rather than asserted, and ir_ep_machine_sound_junk_witness runs it on a junk spine. \n\nSAME OPEN LAYOUT OBLIGATION as eval_ir_repr's, carried forward rather than laundered: these are trust-ir DECLARATION-INDEX tags, which is what the emitted body switches on; the Rust enum is niche-encoded downstream of trust-ir. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_TSTEP, "ir_ep_tstep: enum.181, the ExprPathStep enum id the emitted body names in both `load enum.181, ptr %0` and `const enum.181 { k }`. SEMANTIC INPUT, not decoration: ir_const_agg_eval consults ir_ty_is_agg on it, so an aggregate constant at a scalar type is type_error not_agg. The particular id 181 is not consulted. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B0, "ir_ep_b0: entry block, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/expr_path_step_clone.trust-ir.txt). LOAD through the &self pointer into %2, read the discriminant with extractfield u8 %2, 0 into %3, then switch. TEN explicit cases (0..9) and a reachable DEFAULT to bb11; exhaustive_enum_unreachable is Bool.false and that is the honest value, since the default is taken on every ProjExpr. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B1, "ir_ep_b1: AppFn => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 0 }` into %4. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B2, "ir_ep_b2: AppArg => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 1 }` into %5. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B3, "ir_ep_b3: LamBody => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 2 }` into %6. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B4, "ir_ep_b4: LamType => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 3 }` into %7. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B5, "ir_ep_b5: PiDom => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 4 }` into %8. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B6, "ir_ep_b6: PiBody => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 5 }` into %9. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B7, "ir_ep_b7: LetType => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 6 }` into %10. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B8, "ir_ep_b8: LetVal => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 7 }` into %11. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B9, "ir_ep_b9: LetBody => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 8 }` into %12. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B10, "ir_ep_b10: MDataExpr => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 9 }` into %13. Its own block: the compiler shares no arms even though every arm has the same shape, and a module that collapsed them would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B11, "ir_ep_b11: ProjExpr => itself, materialized as the AGGREGATE CONSTANT `const enum.181 { 10 }` into %14. Reached by the DEFAULT edge, not by an explicit case -- the emitted switch lists 0..9 and routes tag 10 here, so the default is neither a trap nor unreachable but one specific real variant. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_B12, "ir_ep_b12: the JOIN block, taking an AGGREGATE block parameter (bb12(%1: enum.181)) and returning it. Like the third chain's join and unlike the first two, the answer travels through the machine as an IRScalar aggregate rather than as a scalar. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_FUNC, "ir_ep_func: <ExprPathStep as Clone>::clone as EvalIR -- one parameter (&self, SSA id 0), entry block 0, THIRTEEN blocks, matching the emitted control-flow graph exactly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MODULE, "ir_ep_module: the module for <ExprPathStep as Clone>::clone, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/expr_path_step_clone.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the load, extractfield and aggregate-constant lanes, by tests/crystal_a1_lineage/expr_path_step_clone.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_APPFN, "GATE WITNESS: AppFn, explicit switch case 0. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_APPARG, "GATE WITNESS: AppArg, explicit switch case 1. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_LAMBODY, "GATE WITNESS: LamBody, explicit switch case 2. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_LAMTYPE, "GATE WITNESS: LamType, explicit switch case 3. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_PIDOM, "GATE WITNESS: PiDom, explicit switch case 4. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_PIBODY, "GATE WITNESS: PiBody, explicit switch case 5. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_LETTYPE, "GATE WITNESS: LetType, explicit switch case 6. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_LETVAL, "GATE WITNESS: LetVal, explicit switch case 7. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_LETBODY, "GATE WITNESS: LetBody, explicit switch case 8. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_MDATAEXPR, "GATE WITNESS: MDataExpr, explicit switch case 9. Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_PROJEXPR, "GATE WITNESS: ProjExpr, the DEFAULT edge (tag 10, no explicit case). Eq.refl -- the kernel runs the machine for 6 steps (3 in the entry block, 2 in an arm, 1 in the join) over a one-cell heap and compares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_ON_PAYLOAD_JUNK, "GATE WITNESS: the default edge with a JUNK PAYLOAD -- tag 10 carried on a two-element spine holding an undef, which no well-formed ExprPathStep produces. The machine reads field 0, ignores the rest, and answers the aggregate tagged 10 with an EMPTY spine. This is the executed evidence that the body reads only the discriminant. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MACH0, "ir_ep_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds ONE parameter, a pointer. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_AFTER_LOAD, "ir_ep_after_load: the configuration after the load has bound %2, as a function of the LOOKUP RESULT. The device that lets each arm of ir_ep_exact rewrite with its own heap premise instead of restating the machine eleven times. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_EXACT, "ir_ep_exact: the machine agrees with the reflected clone at EXACTLY 6 steps (load, extractfield, switch, const_, br, ret), for every path step, every address, every spine and every heap satisfying the premise. Eleven minors, each an Eq.subst that rewrites the heap lookup with that variant's premise and then lets the kernel run the machine. Measured 2.8 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_CORRECT, "ir_ep_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR A DERIVED IMPL. *** For every path step, every value representing it in the heap, every next-address counter and every fuel at or above 6, ir_eval on ir_ep_module returns exactly the aggregate tagged expr_path_step_tag (expr_path_step_clone s). \n\nThe widest dispatch chained so far measured by explicit cases: ten plus a reachable default over eleven variants, eleven aggregate constants, and a join block carrying a structured value. Nobody wrote this body; #[derive(Clone)] did. \n\nA0 is measured on the SHIPPED kernel: lowered, spliced, unsupported [], derived_mir.verdict agreed over SIXTEEN canonical lines -- the longest canonical comparison of any chained body -- markers_exact true but VACUOUS (0 marker lines, see the module doc), interpreter differential not-run because param 0 is a dereferenced pointer, zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage/expr_path_step_clone.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MACHINE_SOUND, "ir_ep_machine_sound: *** A5, THE INVERSION. *** If the MACHINE answers a value tagged t, then t IS the tag of the cloned step. Goes through A4 rather than restating it, and reads the tag out of the returned AGGREGATE with ir_outcome_disc (the third chain's projector). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MACHINE_SOUND_STEP, "ir_ep_machine_sound_step: *** A5 LIFTED OFF THE TAG ONTO THE VARIANT -- THE CLONE CONTRACT. *** If the machine running the EMITTED body answers a value tagged t, then expr_path_step_of_tag t is the very variant the caller passed in. Composes three things that are each proved elsewhere: the inversion, expr_path_step_clone_id (the emitted eleven-arm dispatch is the identity), and expr_path_step_of_tag_tag (the decoder inverts the tag). This is the property Clone is supposed to have, stated about the shipped artifact. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_NEVER_FAULTS, "ir_ep_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented path step. *** A corollary of A4. Concretely for this body: the load never faults on a missing or dead cell, the extractfield never faults on a non-aggregate, the switch always finds an edge (ten cases or the default), the join binds its parameter, and 6 steps always suffice. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_CORRECT_WITNESS, "ir_ep_correct_witness: A4's premises are all SATISFIABLE, discharged concretely on a one-cell heap with the exact fuel bound by Le.refl and an EncodesExprPathStep.mk whose heap equation is an Eq.refl -- so the KERNEL runs ir_mem_lookup and compares, rather than the premise being asserted. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MACHINE_SOUND_WITNESS, "ir_ep_machine_sound_witness: A5's premises are SATISFIABLE including the observation premise, which is an Eq.refl here because this machine's answer IS computable. Concludes the tag of LamType is 3. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MACHINE_SOUND_STEP_WITNESS, "ir_ep_machine_sound_step_witness: the CLONE CONTRACT, executed. From an observation that the machine answered a value tagged 3, the decoder returns ExprPathStepR.lamtype -- the variant that was in the heap. Not a restatement: its conclusion is an equation between VARIANTS that the kernel decides by running the decoder. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_EP_MACHINE_SOUND_JUNK_WITNESS, "ir_ep_machine_sound_junk_witness: the same contract on the DEFAULT edge and on a JUNK PAYLOAD. The heap cell carries tag 10 (ProjExpr, the variant with no explicit switch case) with a two-element spine holding an undef -- a value no well-formed ExprPathStep produces. The machine still routes through the default edge, still answers the aggregate tagged 10 with an EMPTY spine, and the decoder still returns projexpr. This is what makes the spine quantification in the premise checked rather than decorative. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The switch lists TEN cases and routes the eleventh variant through the
    /// default. A case table transcribed as 0..10 would misroute nothing and
    /// still be a different graph; one transcribed as 0..9 with an unreachable
    /// default would silently drop `ProjExpr`.
    #[test]
    fn test_ten_explicit_cases_and_a_reachable_default() {
        assert_eq!(
            SRC_IR_EP_B0.matches("ir_sc ").count(),
            10,
            "ten explicit switch cases, 0..9"
        );
        assert!(SRC_IR_EP_B0.contains("IRInst.switch ir_d3 ir_d11 ir_nl0"));
        assert!(
            SRC_IR_EP_B0.contains("ir_sc ir_d9 ir_d10 ir_sc0"),
            "the last explicit case is 9 -> bb10; tag 10 has none"
        );
        assert!(
            SRC_IR_EP_B0.ends_with("Bool.false)))"),
            "exhaustive_enum_unreachable is FALSE: the default is taken on every ProjExpr"
        );
    }

    /// The prologue is a `load` through `&self` followed by a field-0 read.
    /// This is the shape the first chain has and the third does not.
    #[test]
    fn test_the_argument_is_loaded_then_its_tag_read() {
        assert!(SRC_IR_EP_B0.contains("IRInst.load ir_ep_tstep ir_d0 Bool.false) ir_d2"));
        assert!(SRC_IR_EP_B0.contains("IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3"));
        // …and the premise pins the cell that load reads, by an equation on
        // ir_mem_lookup rather than by membership.
        assert!(SRC_ENCODESEXPRPATHSTEP.contains("ir_mem_lookup mem a"));
        assert!(
            !SRC_ENCODESEXPRPATHSTEP.contains("IRList.cons IRMemSlot"),
            "a membership premise would be satisfiable by a SHADOWED duplicate"
        );
    }

    /// Eleven arms, eleven distinct aggregate constants, eleven distinct result
    /// ids, and every one of them branches to the same join block.
    #[test]
    fn test_eleven_distinct_aggregate_arms() {
        let arms = [
            SRC_IR_EP_B1,
            SRC_IR_EP_B2,
            SRC_IR_EP_B3,
            SRC_IR_EP_B4,
            SRC_IR_EP_B5,
            SRC_IR_EP_B6,
            SRC_IR_EP_B7,
            SRC_IR_EP_B8,
            SRC_IR_EP_B9,
            SRC_IR_EP_B10,
            SRC_IR_EP_B11,
        ];
        for (k, arm) in arms.iter().enumerate() {
            assert!(
                arm.contains(&format!("IRInst.const_ ir_ep_tstep (ir_cvar ir_d{k})")),
                "arm {k} must materialize the aggregate constant for tag {k}"
            );
            assert!(
                arm.contains(&format!("IRInst.br ir_d12 (ir_nl1 ir_d{})", k + 4)),
                "arm {k} binds %{} and carries it to the join",
                k + 4
            );
        }
        assert!(SRC_IR_EP_B12.contains("IRBlock.mk ir_d12 (ir_nl1 ir_d1)"));
        assert!(SRC_IR_EP_B12.contains("IRInst.ret (ir_nl1 ir_d1)"));
    }

    /// The reflected clone is the ELEVEN-ARM dispatch the derive emitted, and
    /// the identity is a separate proved fact rather than the definition.
    #[test]
    fn test_clone_is_transcribed_not_collapsed() {
        assert!(
            SRC_EXPR_PATH_STEP_CLONE.contains("ExprPathStepR.rec"),
            "the emitted body dispatches; so does the reflection"
        );
        assert_eq!(
            SRC_EXPR_PATH_STEP_CLONE.matches("ExprPathStepR.").count(),
            12,
            "one `.rec` and eleven constructor arms"
        );
        assert!(
            !SRC_EXPR_PATH_STEP_CLONE.contains("(s : ExprPathStepR) : ExprPathStepR := s"),
            "collapsing the derive to `fun s => s` would be a claim, not a transcription"
        );
        assert_eq!(
            SRC_EXPR_PATH_STEP_CLONE_ID
                .matches("Eq.refl ExprPathStepR")
                .count(),
            11,
            "the identity is PROVED, one arm at a time"
        );
    }

    /// A4 stays universally quantified; A5 reaches past the tag onto the
    /// variant, which is the clone contract.
    #[test]
    fn test_a4_a5_shape() {
        let statement = SRC_IR_EP_CORRECT.split(":=").next().unwrap_or("");
        assert!(
            statement.contains("(mem : IRList IRMemSlot)") && statement.contains("(fuel : Nat)")
        );
        assert!(SRC_IR_EP_CORRECT.contains("Le ir_d6 fuel ->"));
        assert!(SRC_IR_EP_CORRECT.contains("ir_run_le_ret"));
        assert!(
            !statement.contains("ir_mem0"),
            "a concrete heap would make this a witness, not a theorem"
        );
        assert!(SRC_IR_EP_MACHINE_SOUND.contains("ir_outcome_disc"));
        assert!(
            SRC_IR_EP_MACHINE_SOUND_STEP.contains(": Eq ExprPathStepR (expr_path_step_of_tag t) s")
        );
        assert!(SRC_IR_EP_MACHINE_SOUND_STEP.contains("expr_path_step_clone_id s"));
        assert!(SRC_IR_EP_MACHINE_SOUND_STEP.contains("expr_path_step_of_tag_tag s"));
    }

    /// Every emitted arm is executed as a witness, including the default edge
    /// and a junk payload on it.
    #[test]
    fn test_a_witness_per_emitted_arm() {
        let ons = [
            SRC_IR_EP_ON_APPFN,
            SRC_IR_EP_ON_APPARG,
            SRC_IR_EP_ON_LAMBODY,
            SRC_IR_EP_ON_LAMTYPE,
            SRC_IR_EP_ON_PIDOM,
            SRC_IR_EP_ON_PIBODY,
            SRC_IR_EP_ON_LETTYPE,
            SRC_IR_EP_ON_LETVAL,
            SRC_IR_EP_ON_LETBODY,
            SRC_IR_EP_ON_MDATAEXPR,
            SRC_IR_EP_ON_PROJEXPR,
        ];
        assert_eq!(ons.len(), 11, "one per emitted arm");
        for (k, on) in ons.iter().enumerate() {
            assert!(on.contains(&format!("ir_cell ir_d0 (ir_var ir_d{k} ir_sp0) ir_mem0")));
            assert!(on.contains(":= Eq.refl IROutcome"));
            assert!(on.contains("ir_eval ir_d6 ir_ep_module"));
        }
        // …and the junk-payload run goes through the DEFAULT edge with a spine
        // no well-formed value has.
        assert!(SRC_IR_EP_ON_PAYLOAD_JUNK.contains("ir_sp2 IRScalar.undef_ IRScalar.vnil"));
        assert!(SRC_IR_EP_ON_PAYLOAD_JUNK.contains("(ir_var ir_d10 ir_sp0)"));
        assert!(SRC_IR_EP_MACHINE_SOUND_JUNK_WITNESS
            .contains("Eq ExprPathStepR (expr_path_step_of_tag ir_d10) ExprPathStepR.projexpr"));
    }
}
