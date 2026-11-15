// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness of `KernelAcceptsTcIn` into `TypingTcIn`, and the two embeddings
//! that make them successors: `KernelAcceptsIn` embeds into the algorithmic
//! family (its whnf traces and `DefEqCDPIn` premises become conversions) and
//! `TypingProjIn` embeds into the target.
//!
//! One recursion per statement, no lemma about the target's metatheory: every
//! algorithmic arm maps to its declarative rule after `conv` along the
//! premise's conversion. The typed conversion arms (`proof_irrel`, `eta`,
//! `unit_like`, `struct_eta`) map to the declarative rule at the whnf'd type the
//! deployed branch compares, which is where `conv` puts the subject.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "lctx_decls_lookup",
        r"forall (G : ListType KExpr) (i : Nat), Eq (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls G) i) (lctx_opt_decl (ctx_lookup G i))",
        r"fun (G : ListType KExpr) => ListType.rec KExpr
  (fun (H : ListType KExpr) => forall (i : Nat), Eq (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls H) i) (lctx_opt_decl (ctx_lookup H i)))
  (fun (i : Nat) => Eq.refl (OptionType CtxEntryIn) (OptionType.none CtxEntryIn))
  (fun (a : KExpr) (rest : ListType KExpr)
    (ih : forall (i : Nat), Eq (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls rest) i) (lctx_opt_decl (ctx_lookup rest i)))
    (i : Nat) =>
    Nat.rec (fun (j : Nat) => Eq (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls (ListType.cons KExpr a rest)) j) (lctx_opt_decl (ctx_lookup (ListType.cons KExpr a rest) j)))
      (Eq.refl (OptionType CtxEntryIn) (OptionType.some CtxEntryIn (CtxEntryIn.decl a)))
      (fun (n : Nat) (_ih2 : Eq (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls (ListType.cons KExpr a rest)) n) (lctx_opt_decl (ctx_lookup (ListType.cons KExpr a rest) n))) => ih n)
      i)
  G",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (b : Bool) (G : ListType CtxEntryIn) (x : KExpr) (y : KExpr), KernelAcceptsTcIn R tenv b G x y -> TypingTcIn R tenv b G x y",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (b : Bool) (G : ListType CtxEntryIn) (x : KExpr) (y : KExpr)
(h : KernelAcceptsTcIn R tenv b G x y) =>
KernelAcceptsTcIn.rec R tenv
  (fun (b0 : Bool) (G0 : ListType CtxEntryIn) (x0 : KExpr) (y0 : KExpr) (_h : KernelAcceptsTcIn R tenv b0 G0 x0 y0) => TypingTcIn R tenv b0 G0 x0 y0)
  (fun (G0 : ListType CtxEntryIn) (u : Level) => TypingTcIn.sort R tenv G0 u)
  (fun (G0 : ListType CtxEntryIn) (i : Nat) (ent : CtxEntryIn) (get : Eq (OptionType CtxEntryIn) (ctx_entry_lookup G0 i) (OptionType.some CtxEntryIn ent)) => TypingTcIn.var R tenv G0 i ent get)
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level) (r : Level)
    (_ha : KernelAcceptsTcIn R tenv Bool.true G0 A SA) (_hwa : KernelAcceptsTcIn R tenv Bool.false G0 SA (KExpr.sort u))
    (_hb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) B SB) (_hwb : KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) SB (KExpr.sort v))
    (hr : levelEqSem (Level.imax u v) r)
    (iha : TypingTcIn R tenv Bool.true G0 A SA) (ihwa : TypingTcIn R tenv Bool.false G0 SA (KExpr.sort u))
    (ihb : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) B SB) (ihwb : TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) SB (KExpr.sort v)) =>
    TypingTcIn.conv R tenv G0 (KExpr.pi A B) (KExpr.sort (Level.imax u v)) (KExpr.sort r)
      (TypingTcIn.pi R tenv G0 A B u v
        (TypingTcIn.conv R tenv G0 A SA (KExpr.sort u) iha ihwa)
        (TypingTcIn.conv R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) B SB (KExpr.sort v) ihb ihwb))
      (TypingTcIn.cdp R tenv G0 (KExpr.sort (Level.imax u v)) (KExpr.sort r)
        (DefEqCDPIn.levels R (KExpr.sort (Level.imax u v)) (KExpr.sort r) (KExprUniverseEq.sort (Level.imax u v) r hr))))
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (_ha : KernelAcceptsTcIn R tenv Bool.true G0 A SA) (_hwa : KernelAcceptsTcIn R tenv Bool.false G0 SA (KExpr.sort u)) (_hb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b B)
    (iha : TypingTcIn R tenv Bool.true G0 A SA) (ihwa : TypingTcIn R tenv Bool.false G0 SA (KExpr.sort u)) (ihb : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b B) =>
    TypingTcIn.lam R tenv G0 A b B u (TypingTcIn.conv R tenv G0 A SA (KExpr.sort u) iha ihwa) ihb)
  (fun (G0 : ListType CtxEntryIn) (n : Name) (us : ListType Level) (A : KExpr) (T0 : KExpr)
    (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) (result : KExprUniverseEq A T0) =>
    TypingTcIn.conv R tenv G0 (KExpr.const n us) A T0 (TypingTcIn.const R tenv G0 n us A get)
      (TypingTcIn.cdp R tenv G0 A T0 (DefEqCDPIn.levels R A T0 result)))
  (fun (G0 : ListType CtxEntryIn) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A2 : KExpr)
    (_hf : KernelAcceptsTcIn R tenv Bool.true G0 f F) (_hw : KernelAcceptsTcIn R tenv Bool.false G0 F (KExpr.pi A B))
    (_ha : KernelAcceptsTcIn R tenv Bool.true G0 a A2) (_heq : KernelAcceptsTcIn R tenv Bool.false G0 A2 A)
    (ihf : TypingTcIn R tenv Bool.true G0 f F) (ihw : TypingTcIn R tenv Bool.false G0 F (KExpr.pi A B))
    (iha : TypingTcIn R tenv Bool.true G0 a A2) (iheq : TypingTcIn R tenv Bool.false G0 A2 A) =>
    TypingTcIn.app R tenv G0 f a A B (TypingTcIn.conv R tenv G0 f F (KExpr.pi A B) ihf ihw) (TypingTcIn.conv R tenv G0 a A2 A iha iheq))
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelAcceptsTcIn R tenv Bool.true G0 A Ty) (_hw : KernelAcceptsTcIn R tenv Bool.false G0 Ty (KExpr.sort u)) (_hv : KernelAcceptsTcIn R tenv Bool.true G0 v Tv)
    (_heq : KernelAcceptsTcIn R tenv Bool.false G0 Tv A) (_hb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b B)
    (iht : TypingTcIn R tenv Bool.true G0 A Ty) (ihw : TypingTcIn R tenv Bool.false G0 Ty (KExpr.sort u)) (ihv : TypingTcIn R tenv Bool.true G0 v Tv)
    (iheq : TypingTcIn R tenv Bool.false G0 Tv A) (ihb : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b B) =>
    TypingTcIn.let_ R tenv G0 A v b B u (TypingTcIn.conv R tenv G0 A Ty (KExpr.sort u) iht ihw) (TypingTcIn.conv R tenv G0 v Tv A ihv iheq) ihb)
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelAcceptsTcIn R tenv Bool.true G0 A Ty) (_hw : KernelAcceptsTcIn R tenv Bool.false G0 Ty (KExpr.sort u)) (_hv : KernelAcceptsTcIn R tenv Bool.true G0 v Tv)
    (_heq : KernelAcceptsTcIn R tenv Bool.false G0 Tv A) (_hb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.defn A v) G0) b B)
    (iht : TypingTcIn R tenv Bool.true G0 A Ty) (ihw : TypingTcIn R tenv Bool.false G0 Ty (KExpr.sort u)) (ihv : TypingTcIn R tenv Bool.true G0 v Tv)
    (iheq : TypingTcIn R tenv Bool.false G0 Tv A) (ihb : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.defn A v) G0) b B) =>
    TypingTcIn.let_def R tenv G0 A v b B u (TypingTcIn.conv R tenv G0 A Ty (KExpr.sort u) iht ihw) (TypingTcIn.conv R tenv G0 v Tv A ihv iheq) ihb)
  (fun (G0 : ListType CtxEntryIn) (n : Nat) => TypingTcIn.lit_nat R tenv G0 n)
  (fun (G0 : ListType CtxEntryIn) (n : Nat) => TypingTcIn.lit_string R tenv G0 n)
  (fun (G0 : ListType CtxEntryIn) (S : Name) (idx : Nat) (e0 : KExpr) (E : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr)
    (_he : KernelAcceptsTcIn R tenv Bool.true G0 e0 E) (_hw : KernelAcceptsTcIn R tenv Bool.false G0 E W) (hs : ProjStructIn R S idx W im cm)
    (hp : ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start) (hf : ProjFieldIn R S e0 Nat.zero idx start F)
    (ihe : TypingTcIn R tenv Bool.true G0 e0 E) (ihw : TypingTcIn R tenv Bool.false G0 E W) =>
    TypingTcIn.proj R tenv G0 S idx e0 W im cm start F (TypingTcIn.conv R tenv G0 e0 E W ihe ihw) hs hp hf)
  (fun (G0 : ListType CtxEntryIn) (a : KExpr) (b : KExpr) (h : DefEqCDPIn R a b) => TypingTcIn.cdp R tenv G0 a b h)
  (fun (G0 : ListType CtxEntryIn) (a : KExpr) (b : KExpr) (_h : KernelAcceptsTcIn R tenv Bool.false G0 a b) (ih : TypingTcIn R tenv Bool.false G0 a b) => TypingTcIn.symm R tenv G0 a b ih)
  (fun (G0 : ListType CtxEntryIn) (a : KExpr) (m : KExpr) (b : KExpr) (_h1 : KernelAcceptsTcIn R tenv Bool.false G0 a m) (_h2 : KernelAcceptsTcIn R tenv Bool.false G0 m b)
    (ih1 : TypingTcIn R tenv Bool.false G0 a m) (ih2 : TypingTcIn R tenv Bool.false G0 m b) => TypingTcIn.trans R tenv G0 a m b ih1 ih2)
  (fun (G0 : ListType CtxEntryIn) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (_h1 : KernelAcceptsTcIn R tenv Bool.false G0 f f2) (_h2 : KernelAcceptsTcIn R tenv Bool.false G0 a a2)
    (ih1 : TypingTcIn R tenv Bool.false G0 f f2) (ih2 : TypingTcIn R tenv Bool.false G0 a a2) => TypingTcIn.app_cong R tenv G0 f f2 a a2 ih1 ih2)
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (_h1 : KernelAcceptsTcIn R tenv Bool.false G0 A A2) (_h2 : KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b b2)
    (ih1 : TypingTcIn R tenv Bool.false G0 A A2) (ih2 : TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b b2) => TypingTcIn.lam_cong R tenv G0 A A2 b b2 ih1 ih2)
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (_h1 : KernelAcceptsTcIn R tenv Bool.false G0 A A2) (_h2 : KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) B B2)
    (ih1 : TypingTcIn R tenv Bool.false G0 A A2) (ih2 : TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) B B2) => TypingTcIn.pi_cong R tenv G0 A A2 B B2 ih1 ih2)
  (fun (G0 : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
    (_h1 : KernelAcceptsTcIn R tenv Bool.false G0 A A2) (_h2 : KernelAcceptsTcIn R tenv Bool.false G0 v v2) (_h3 : KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b b2)
    (ih1 : TypingTcIn R tenv Bool.false G0 A A2) (ih2 : TypingTcIn R tenv Bool.false G0 v v2) (ih3 : TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G0) b b2) =>
    TypingTcIn.let_cong R tenv G0 A A2 v v2 b b2 ih1 ih2 ih3)
  (fun (G0 : ListType CtxEntryIn) (n : Name) (i : Nat) (e0 : KExpr) (e2 : KExpr) (_h : KernelAcceptsTcIn R tenv Bool.false G0 e0 e2) (ih : TypingTcIn R tenv Bool.false G0 e0 e2) =>
    TypingTcIn.proj_cong R tenv G0 n i e0 e2 ih)
  (fun (G0 : ListType CtxEntryIn) (a : KExpr) (A : KExpr) (W : KExpr) (S : KExpr) (b : KExpr) (B : KExpr)
    (_ha : KernelAcceptsTcIn R tenv Bool.true G0 a A) (_hAW : KernelAcceptsTcIn R tenv Bool.false G0 A W) (_hW : KernelAcceptsTcIn R tenv Bool.true G0 W S)
    (_hS : KernelAcceptsTcIn R tenv Bool.false G0 S (KExpr.sort Level.zero)) (_hb : KernelAcceptsTcIn R tenv Bool.true G0 b B) (_hAB : KernelAcceptsTcIn R tenv Bool.false G0 A B)
    (iha : TypingTcIn R tenv Bool.true G0 a A) (ihAW : TypingTcIn R tenv Bool.false G0 A W) (ihW : TypingTcIn R tenv Bool.true G0 W S)
    (ihS : TypingTcIn R tenv Bool.false G0 S (KExpr.sort Level.zero)) (ihb : TypingTcIn R tenv Bool.true G0 b B) (ihAB : TypingTcIn R tenv Bool.false G0 A B) =>
    TypingTcIn.proof_irrel R tenv G0 a W b
      (TypingTcIn.conv R tenv G0 a A W iha ihAW)
      (TypingTcIn.conv R tenv G0 W S (KExpr.sort Level.zero) ihW ihS)
      (TypingTcIn.conv R tenv G0 b B W ihb (TypingTcIn.trans R tenv G0 B A W (TypingTcIn.symm R tenv G0 A B ihAB) ihAW)))
  (fun (G0 : ListType CtxEntryIn) (f : KExpr) (F : KExpr) (A : KExpr) (B : KExpr)
    (_hf : KernelAcceptsTcIn R tenv Bool.true G0 f F) (_hF : KernelAcceptsTcIn R tenv Bool.false G0 F (KExpr.pi A B))
    (ihf : TypingTcIn R tenv Bool.true G0 f F) (ihF : TypingTcIn R tenv Bool.false G0 F (KExpr.pi A B)) =>
    TypingTcIn.eta R tenv G0 f A B (TypingTcIn.conv R tenv G0 f F (KExpr.pi A B) ihf ihF))
  (fun (G0 : ListType CtxEntryIn) (a : KExpr) (A : KExpr) (W : KExpr) (b : KExpr) (B : KExpr)
    (_ha : KernelAcceptsTcIn R tenv Bool.true G0 a A) (_hAW : KernelAcceptsTcIn R tenv Bool.false G0 A W) (hu : UnitLikeIn R W)
    (_hb : KernelAcceptsTcIn R tenv Bool.true G0 b B) (_hBW : KernelAcceptsTcIn R tenv Bool.false G0 B W)
    (iha : TypingTcIn R tenv Bool.true G0 a A) (ihAW : TypingTcIn R tenv Bool.false G0 A W)
    (ihb : TypingTcIn R tenv Bool.true G0 b B) (ihBW : TypingTcIn R tenv Bool.false G0 B W) =>
    TypingTcIn.unit_like R tenv G0 a b W (TypingTcIn.conv R tenv G0 a A W iha ihAW) (TypingTcIn.conv R tenv G0 b B W ihb ihBW) hu)
  (fun (G0 : ListType CtxEntryIn) (t : KExpr) (s : KExpr) (S : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta)
    (hc : StructCtorIn R t im cm) (_hs : KernelAcceptsTcIn R tenv Bool.true G0 s S) (_hSW : KernelAcceptsTcIn R tenv Bool.false G0 S W)
    (hname : Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name (kctor_parent cm)))
    (_hfields : forall (i : Nat), Eq Bool (nat_leb (Nat.succ i) (kctor_num_fields cm)) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G0 (KExpr.proj (kctor_parent cm) i s) (accepts_kexpr_nth (kapp_args t) (Nat.add (kctor_num_params cm) i)))
    (ihs : TypingTcIn R tenv Bool.true G0 s S) (ihSW : TypingTcIn R tenv Bool.false G0 S W)
    (ihfields : forall (i : Nat) (hi : Eq Bool (nat_leb (Nat.succ i) (kctor_num_fields cm)) Bool.true), TypingTcIn R tenv Bool.false G0 (KExpr.proj (kctor_parent cm) i s) (accepts_kexpr_nth (kapp_args t) (Nat.add (kctor_num_params cm) i))) =>
    TypingTcIn.struct_eta R tenv G0 t s W im cm hc (TypingTcIn.conv R tenv G0 s S W ihs ihSW) hname ihfields)
  (fun (G0 : ListType CtxEntryIn) (i : Nat) (A : KExpr) (v : KExpr) (get : Eq (OptionType CtxEntryIn) (ctx_entry_lookup G0 i) (OptionType.some CtxEntryIn (CtxEntryIn.defn A v))) =>
    TypingTcIn.zeta_local R tenv G0 i A v get)
  (fun (G0 : ListType CtxEntryIn) => TypingTcIn.lit_zero R tenv G0)
  (fun (G0 : ListType CtxEntryIn) (n : Nat) => TypingTcIn.lit_succ R tenv G0 n)
  (fun (G0 : ListType CtxEntryIn) (ul : ListType Level) (A : KExpr) (r : KExpr) (B : KExpr) (f : KExpr) (h0 : KExpr) (um : ListType Level) (A2 : KExpr) (r2 : KExpr) (a : KExpr) =>
    TypingTcIn.quot_lift R tenv G0 ul A r B f h0 um A2 r2 a)
  (fun (G0 : ListType CtxEntryIn) (ul : ListType Level) (A : KExpr) (r : KExpr) (B : KExpr) (f : KExpr) (um : ListType Level) (A2 : KExpr) (r2 : KExpr) (a : KExpr) =>
    TypingTcIn.quot_ind R tenv G0 ul A r B f um A2 r2 a)
  (fun (G0 : ListType CtxEntryIn) (rn : Name) (I : Name) (mta : RecMeta) (cn : Name) (cus : ListType Level) (major : KExpr) (M : KExpr) (W : KExpr) (C : KExpr)
    (hadm : RecKAdmitIn R rn I mta cn)
    (_hm : KernelAcceptsTcIn R tenv Bool.true G0 major M) (_hMW : KernelAcceptsTcIn R tenv Bool.false G0 M W)
    (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name I))
    (_hc : KernelAcceptsTcIn R tenv Bool.true G0 (apply_spine (list_take (recmeta_num_params mta) (kapp_args W)) (KExpr.const cn cus)) C) (_hWC : KernelAcceptsTcIn R tenv Bool.false G0 W C)
    (ihm : TypingTcIn R tenv Bool.true G0 major M) (ihMW : TypingTcIn R tenv Bool.false G0 M W)
    (ihc : TypingTcIn R tenv Bool.true G0 (apply_spine (list_take (recmeta_num_params mta) (kapp_args W)) (KExpr.const cn cus)) C) (ihWC : TypingTcIn R tenv Bool.false G0 W C) =>
    TypingTcIn.k_like R tenv G0 rn I mta cn major W (apply_spine (list_take (recmeta_num_params mta) (kapp_args W)) (KExpr.const cn cus)) hadm
      (TypingTcIn.conv R tenv G0 major M W ihm ihMW)
      (TypingTcIn.conv R tenv G0 (apply_spine (list_take (recmeta_num_params mta) (kapp_args W)) (KExpr.const cn cus)) C W ihc (TypingTcIn.symm R tenv G0 W C ihWC)) hhead)
  (fun (G0 : ListType CtxEntryIn) (cs : ListType Nat) (hadm : StringLitAdmitIn R) (hvalid : Eq Bool (string_lit_chars_valid cs) Bool.true) =>
    TypingTcIn.lit_string_expand R tenv G0 cs hadm hvalid)
  b G x y h",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_to_tc_in",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), KernelAcceptsIn R tenv G e T -> KernelAcceptsTcIn R tenv Bool.true (lctx_decls G) e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : KernelAcceptsIn R tenv G e T) =>
KernelAcceptsIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : KernelAcceptsIn R tenv G0 e0 T0) => KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) e0 T0)
  (fun (G0 : ListType KExpr) (u : Level) => KernelAcceptsTcIn.sort R tenv (lctx_decls G0) u)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) (get : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => KernelAcceptsTcIn.bvar R tenv (lctx_decls G0) i (CtxEntryIn.decl A) (Eq.trans (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls G0) i) (lctx_opt_decl (ctx_lookup G0 i)) (OptionType.some CtxEntryIn (CtxEntryIn.decl A)) (lctx_decls_lookup G0 i) (Eq.cong (OptionType KExpr) (OptionType CtxEntryIn) lctx_opt_decl (ctx_lookup G0 i) (OptionType.some KExpr A) get)))
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level) (r : Level)
    (_ha : KernelAcceptsIn R tenv G0 A SA) (hwa : par_reduces_cdp_star R SA (KExpr.sort u))
    (_hb : KernelAcceptsIn R tenv (ListType.cons KExpr A G0) B SB) (hwb : par_reduces_cdp_star R SB (KExpr.sort v)) (hr : levelEqSem (Level.imax u v) r)
    (iha : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) A SA) (ihb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) B SB) =>
    KernelAcceptsTcIn.pi R tenv (lctx_decls G0) A B SA u SB v r
      iha (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) SA (KExpr.sort u) (par_reduces_cdp_star_to_def_eq_cdp_in R SA (KExpr.sort u) hwa))
      ihb (KernelAcceptsTcIn.cdp R tenv (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) SB (KExpr.sort v) (par_reduces_cdp_star_to_def_eq_cdp_in R SB (KExpr.sort v) hwb)) hr)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (_ha : KernelAcceptsIn R tenv G0 A SA) (hwa : par_reduces_cdp_star R SA (KExpr.sort u)) (_hb : KernelAcceptsIn R tenv (ListType.cons KExpr A G0) b B)
    (iha : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) A SA) (ihb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) b B) =>
    KernelAcceptsTcIn.lam R tenv (lctx_decls G0) A b B SA u iha (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) SA (KExpr.sort u) (par_reduces_cdp_star_to_def_eq_cdp_in R SA (KExpr.sort u) hwa)) ihb)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T0 : KExpr)
    (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) (result : KExprUniverseEq A T0) =>
    KernelAcceptsTcIn.const R tenv (lctx_decls G0) n us A T0 get result)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A2 : KExpr)
    (_hf : KernelAcceptsIn R tenv G0 f F) (hw : par_reduces_cdp_star R F (KExpr.pi A B))
    (_ha : KernelAcceptsIn R tenv G0 a A2) (heq : DefEqCDPIn R A2 A)
    (ihf : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) f F) (iha : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) a A2) =>
    KernelAcceptsTcIn.app R tenv (lctx_decls G0) f a F A B A2
      ihf (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) F (KExpr.pi A B) (par_reduces_cdp_star_to_def_eq_cdp_in R F (KExpr.pi A B) hw)) iha (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) A2 A heq))
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelAcceptsIn R tenv G0 A Ty) (hw : par_reduces_cdp_star R Ty (KExpr.sort u))
    (_hv : KernelAcceptsIn R tenv G0 v Tv) (heq : DefEqCDPIn R Tv A) (_hb : KernelAcceptsIn R tenv (ListType.cons KExpr A G0) b B)
    (iht : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) A Ty) (ihv : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) v Tv) (ihb : KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) b B) =>
    KernelAcceptsTcIn.let_ R tenv (lctx_decls G0) A v b Ty u Tv B
      iht (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) Ty (KExpr.sort u) (par_reduces_cdp_star_to_def_eq_cdp_in R Ty (KExpr.sort u) hw)) ihv (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) Tv A heq) ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => KernelAcceptsTcIn.lit_nat R tenv (lctx_decls G0) n)
  (fun (G0 : ListType KExpr) (n : Nat) => KernelAcceptsTcIn.lit_string R tenv (lctx_decls G0) n)
  (fun (G0 : ListType KExpr) (S : Name) (idx : Nat) (e0 : KExpr) (E : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr)
    (_he : KernelAcceptsIn R tenv G0 e0 E) (hw : par_reduces_cdp_star R E W) (hs : ProjStructIn R S idx W im cm)
    (hp : ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start) (hf : ProjFieldIn R S e0 Nat.zero idx start F)
    (ihe : KernelAcceptsTcIn R tenv Bool.true (lctx_decls G0) e0 E) =>
    KernelAcceptsTcIn.proj R tenv (lctx_decls G0) S idx e0 E W im cm start F ihe (KernelAcceptsTcIn.cdp R tenv (lctx_decls G0) E W (par_reduces_cdp_star_to_def_eq_cdp_in R E W hw)) hs hp hf)
  G e T h",
    ),
    DeclarationInput::Proof(
        "typing_proj_in_to_tc_in",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), TypingProjIn R tenv G e T -> TypingTcIn R tenv Bool.true (lctx_decls G) e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : TypingProjIn R tenv G e T) =>
TypingProjIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : TypingProjIn R tenv G0 e0 T0) => TypingTcIn R tenv Bool.true (lctx_decls G0) e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) (get : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => TypingTcIn.var R tenv (lctx_decls G0) i (CtxEntryIn.decl A) (Eq.trans (OptionType CtxEntryIn) (ctx_entry_lookup (lctx_decls G0) i) (lctx_opt_decl (ctx_lookup G0 i)) (OptionType.some CtxEntryIn (CtxEntryIn.decl A)) (lctx_decls_lookup G0 i) (Eq.cong (OptionType KExpr) (OptionType CtxEntryIn) lctx_opt_decl (ctx_lookup G0 i) (OptionType.some KExpr A) get)))
  (fun (G0 : ListType KExpr) (u : Level) => TypingTcIn.sort R tenv (lctx_decls G0) u)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
    (_hA : TypingProjIn R tenv G0 A (KExpr.sort u)) (_hB : TypingProjIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
    (ihA : TypingTcIn R tenv Bool.true (lctx_decls G0) A (KExpr.sort u)) (ihB : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) B (KExpr.sort v)) =>
    TypingTcIn.pi R tenv (lctx_decls G0) A B u v ihA ihB)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
    (_hA : TypingProjIn R tenv G0 A (KExpr.sort u)) (_hb : TypingProjIn R tenv (ListType.cons KExpr A G0) b B)
    (ihA : TypingTcIn R tenv Bool.true (lctx_decls G0) A (KExpr.sort u)) (ihb : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) b B) =>
    TypingTcIn.lam R tenv (lctx_decls G0) A b B u ihA ihb)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
    (_hf : TypingProjIn R tenv G0 f (KExpr.pi A B)) (_ha : TypingProjIn R tenv G0 a A)
    (ihf : TypingTcIn R tenv Bool.true (lctx_decls G0) f (KExpr.pi A B)) (iha : TypingTcIn R tenv Bool.true (lctx_decls G0) a A) =>
    TypingTcIn.app R tenv (lctx_decls G0) f a A B ihf iha)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
    (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) =>
    TypingTcIn.const R tenv (lctx_decls G0) n us A get)
  (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr) (_he : TypingProjIn R tenv G0 e0 A) (heq : DefEqCDPIn R A B)
    (ihe : TypingTcIn R tenv Bool.true (lctx_decls G0) e0 A) =>
    TypingTcIn.conv R tenv (lctx_decls G0) e0 A B ihe (TypingTcIn.cdp R tenv (lctx_decls G0) A B heq))
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
    (_hA : TypingProjIn R tenv G0 A (KExpr.sort u)) (_hv : TypingProjIn R tenv G0 v A) (_hb : TypingProjIn R tenv (ListType.cons KExpr A G0) b B)
    (ihA : TypingTcIn R tenv Bool.true (lctx_decls G0) A (KExpr.sort u)) (ihv : TypingTcIn R tenv Bool.true (lctx_decls G0) v A) (ihb : TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) (lctx_decls G0)) b B) =>
    TypingTcIn.let_ R tenv (lctx_decls G0) A v b B u ihA ihv ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => TypingTcIn.lit_nat R tenv (lctx_decls G0) n)
  (fun (G0 : ListType KExpr) (n : Nat) => TypingTcIn.lit_string R tenv (lctx_decls G0) n)
  (fun (G0 : ListType KExpr) (S : Name) (idx : Nat) (e0 : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr)
    (_he : TypingProjIn R tenv G0 e0 W) (hs : ProjStructIn R S idx W im cm)
    (hp : ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start) (hf : ProjFieldIn R S e0 Nat.zero idx start F)
    (ihe : TypingTcIn R tenv Bool.true (lctx_decls G0) e0 W) =>
    TypingTcIn.proj R tenv (lctx_decls G0) S idx e0 W im cm start F ihe hs hp hf)
  G e T h",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_tc_sound",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), KernelAcceptsIn R tenv G e T -> TypingTcIn R tenv Bool.true (lctx_decls G) e T",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : KernelAcceptsIn R tenv G e T) =>
kernel_accepts_tc_in_sound R tenv Bool.true (lctx_decls G) e T (kernel_accepts_in_to_tc_in R tenv G e T h)",
    ),
];
