// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The TYPED-CONVERSION successors of `KernelAcceptsIn` and `TypingProjIn`.
//!
//! The deployed `is_def_eq` has conversion families that consult TYPES: proof
//! irrelevance, lambda eta, unit-like structures and structure eta infer the
//! type of a side and compare. A conversion relation that can carry them needs
//! the typing judgment, and typing needs conversion, so the two are one
//! judgment. The spec elaborator has no mutual inductives, so each successor is
//! a SINGLE family indexed by a `Bool` judgment kind: `Bool.true` is typing
//! `G |- e : T`, `Bool.false` is conversion `G |- a == b`.
//!
//! `KernelAcceptsTcIn` is the algorithmic relation, in CHECK mode. Its whnf and
//! conversion premises are conversion judgments of the same family (a
//! reduction trace is a conversion), so a typed family reached inside a whnf
//! (structure eta on a recursor major) is carried by its conversion rule. Its
//! typed-conversion arms read the deployed checks: the premises are exactly the
//! facts the deployed branch establishes before it answers `true`, stated as
//! check-mode derivations. The deployed branch infers in INFER-ONLY mode; that
//! the two agree on the subjects that reach `is_def_eq` is the inventory's
//! `infer_only_conditional` obligation, not a premise discharged here.
//!
//! Contexts are lists of ENTRIES (`CtxEntryIn`): a declaration carries a type,
//! a definition a type and a value. The algorithmic `let_def` arm types the
//! body under a definition entry, as the deployed Let arm does, and
//! `zeta_local` unfolds a let-bound variable to its value, as the deployed
//! `whnf` does. The declarations-only `let_` arm is kept so the earlier
//! relations (contexts of types, `lctx_decls`) embed arm for arm.
//!
//! `TypingTcIn` is the declarative target: `TypingProjIn`'s rules plus a
//! conversion half with contextual congruence and Lean 4's typed rules. It
//! over-approximates Lean where the deployed check is weaker than Lean's: the
//! structure-eta rule, like the deployed one, does not compare the constructor
//! application's parameters with the subject's type. The Nat literal rules key
//! on the reflected `Nat.zero` / `Nat.succ` names, as the deployed
//! `nat_lit_to_constructor` keys on the names. The quotient rules are Lean 4's
//! `Quot.lift f h (Quot.mk r a) ~> f a` and `Quot.ind f (Quot.mk r a) ~> f a`
//! (`quot_reduce_rec`: exactly three arguments on the `Quot.mk` major, the
//! function at argument 3), keyed on the reflected `Quot.lift` / `Quot.ind` /
//! `Quot.mk` names as the deployed `try_quot_reduction` keys on the kernel
//! names, with no environment gate on either side. Trailing arguments and the
//! major's own whnf are carried by `app_cong` and the conversion around it.
//!
//! Not extracted Rust execution. The metatheory of the target (consistency,
//! subject reduction under the new rules) is not claimed.

use super::DeclarationInput;

/// A total list index (default `Sort 0`, never read in range): the i-th
/// argument of an application spine, for the structure-eta field premise.
pub(super) const KEXPR_NTH: &str = r"def accepts_kexpr_nth (xs : ListType KExpr) : Nat -> KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => Nat -> KExpr) (fun (_ : Nat) => KExpr.sort Level.zero) (fun (a : KExpr) (rest : ListType KExpr) (ih : Nat -> KExpr) => fun (i : Nat) => Nat.rec (fun (_ : Nat) => KExpr) a (fun (n : Nat) (_ : KExpr) => ih n) i) xs";

/// A local-context entry: a declaration (lambda / Pi binder: type only) or a
/// definition (let binder: type AND value). The deployed Let arm pushes a
/// let-local WITH its value (`ctx_push_let`) and `whnf` unfolds it; a context
/// of types alone cannot say that, which is why the typed-conversion families
/// index their contexts by entries.
pub(super) const CTX_ENTRY: &str = r"inductive CtxEntryIn : Type
| decl : KExpr -> CtxEntryIn
| defn : KExpr -> KExpr -> CtxEntryIn";

pub(super) const CTX_ENTRY_TYPE: &str = r"def ctx_entry_type (ent : CtxEntryIn) : KExpr := CtxEntryIn.rec (fun (_ : CtxEntryIn) => KExpr) (fun (A : KExpr) => A) (fun (A : KExpr) (v : KExpr) => A) ent";

/// Entry `i` of a context, counted from the innermost binder (as `ctx_lookup`).
pub(super) const CTX_ENTRY_LOOKUP: &str = r"def ctx_entry_lookup (g : ListType CtxEntryIn) : Nat -> OptionType CtxEntryIn := ListType.rec CtxEntryIn (fun (_ : ListType CtxEntryIn) => Nat -> OptionType CtxEntryIn) (fun (_ : Nat) => OptionType.none CtxEntryIn) (fun (a : CtxEntryIn) (rest : ListType CtxEntryIn) (ih : Nat -> OptionType CtxEntryIn) => fun (i : Nat) => Nat.rec (fun (_ : Nat) => OptionType CtxEntryIn) (OptionType.some CtxEntryIn a) (fun (n : Nat) (_ : OptionType CtxEntryIn) => ih n) i) g";

/// The declarations-only context of a context of types: every earlier family's
/// context, as seen by the typed-conversion families.
pub(super) const LCTX_DECLS: &str = r"def lctx_decls (g : ListType KExpr) : ListType CtxEntryIn := ListType.rec KExpr (fun (_ : ListType KExpr) => ListType CtxEntryIn) (ListType.nil CtxEntryIn) (fun (a : KExpr) (rest : ListType KExpr) (ih : ListType CtxEntryIn) => ListType.cons CtxEntryIn (CtxEntryIn.decl a) ih) g";

pub(super) const LCTX_OPT_DECL: &str = r"def lctx_opt_decl (o : OptionType KExpr) : OptionType CtxEntryIn := OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType CtxEntryIn) (OptionType.none CtxEntryIn) (fun (a : KExpr) => OptionType.some CtxEntryIn (CtxEntryIn.decl a)) o";

/// `is_def_eq_unit_like`'s facts on the whnf'd type `W`: its head names a
/// structure-like inductive (one constructor, no indices) whose constructor
/// has no fields. Equations to computations over `R`'s tables.
pub(super) const UNIT_LIKE: &str = r"inductive UnitLikeIn (R : RedEnv) (W : KExpr) : Type
| mk : forall (I : Name) (im : KIndMeta) (cn : Name) (cm : KCtorMeta), Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name I) -> Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) I) (OptionType.some KIndMeta im) -> Eq (ListType Name) (kind_ctor_names im) (ListType.cons Name cn (ListType.nil Name)) -> Eq Bool (nat_eqb (kind_num_indices im) Nat.zero) Bool.true -> Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (OptionType.some KCtorMeta cm) -> Eq Bool (nat_eqb (kctor_num_fields cm) Nat.zero) Bool.true -> UnitLikeIn R W";

/// `try_structure_eta_core`'s facts on its constructor side `t`: a saturated
/// application of a constructor whose parent is structure-like (one
/// constructor, no indices). The parent is `kctor_parent cm`.
pub(super) const STRUCT_CTOR: &str = r"inductive StructCtorIn (R : RedEnv) (t : KExpr) : KIndMeta -> KCtorMeta -> Type
| mk : forall (C : Name) (im : KIndMeta) (cm : KCtorMeta), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name C) -> Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) C) (OptionType.some KCtorMeta cm) -> Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) (kctor_parent cm)) (OptionType.some KIndMeta im) -> Eq Bool (nat_eqb (name_list_len (kind_ctor_names im)) (Nat.succ Nat.zero)) Bool.true -> Eq Bool (nat_eqb (kind_num_indices im) Nat.zero) Bool.true -> Eq Bool (nat_eqb (list_length (kapp_args t)) (Nat.add (kctor_num_params cm) (kctor_num_fields cm))) Bool.true -> StructCtorIn R t im cm";

/// Whether a (signature) type is a Pi telescope ending in `Sort 0`: the
/// inductive it types lives in `Prop`.
pub(super) const ENDS_IN_PROP: &str = r"def kexpr_ends_in_prop (e : KExpr) : Bool := KExpr.rec (fun (_ : KExpr) => Bool) (fun (l : Level) => Level.rec (fun (_ : Level) => Bool) Bool.true (fun (_ : Level) (_ : Bool) => Bool.false) (fun (_ : Level) (_ : Level) (_ : Bool) (_ : Bool) => Bool.false) (fun (_ : Level) (_ : Level) (_ : Bool) (_ : Bool) => Bool.false) (fun (_ : Name) => Bool.false) l) (fun (_ : Nat) => Bool.false) (fun (_ : KExpr) (_ : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (_ : KExpr) (_ : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (_ : KExpr) (_ : KExpr) (_ : Bool) (ih : Bool) => ih) (fun (_ : Name) (_ : ListType Level) => Bool.false) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Bool) => Bool.false) (fun (_ : Nat) => Bool.false) e";

/// The ADMISSION fact a K-like recursor carries (`rec_val.is_k`, set when the
/// kernel admits the inductive; clean main `67288ad33` regenerates every
/// imported recursor, so every resident `is_k` is kernel-derived): the
/// recursor `rn` is K-flagged in `R`'s table, it has exactly one rule, for a
/// field-free constructor `cn` of `I`, and `I` is a non-mutual one-constructor
/// inductive whose stored signature ends in `Sort 0`. The deployed K step
/// checks none of this per step; it is what admission guarantees, stated over
/// `R`'s tables as the other typed-conversion guards are (`UnitLikeIn`,
/// `StructCtorIn`).
pub(super) const K_ADMIT: &str = r"inductive RecKAdmitIn (R : RedEnv) : Name -> Name -> RecMeta -> Name -> Type
| mk : forall (rn : Name) (I : Name) (mta : RecMeta) (cn : Name) (rhs : KExpr) (cm : KCtorMeta) (im : KIndMeta), Eq (OptionType RecMeta) (recmeta_for (red_rec R) rn) (OptionType.some RecMeta mta) -> Eq Nat (recmeta_k_flag mta) (Nat.succ Nat.zero) -> Eq (OptionType RecRules) (recrules_for (red_rec R) rn) (OptionType.some RecRules (RecRules.cons (RecRule.mk cn Nat.zero rhs) RecRules.nil)) -> Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) cn) (OptionType.some KCtorMeta cm) -> Eq Name (kctor_parent cm) I -> Eq Nat (kctor_num_fields cm) Nat.zero -> Eq (OptionType KIndMeta) (kind_for (red_ind_ctor R) I) (OptionType.some KIndMeta im) -> Eq (ListType Name) (kind_ctor_names im) (ListType.cons Name cn (ListType.nil Name)) -> Eq (ListType Name) (kind_all_names im) (ListType.cons Name I (ListType.nil Name)) -> Eq Bool (kexpr_ends_in_prop (kconst_type (kind_sig im))) Bool.true -> RecKAdmitIn R rn I mta cn";

/// The declarative target. `Bool.true`: typing; `Bool.false`: conversion.
pub(super) const TYPING_TC: &str = r"inductive TypingTcIn (R : RedEnv) (tenv : KDeclEnv) : Bool -> ListType CtxEntryIn -> KExpr -> KExpr -> Type
| var : forall (G : ListType CtxEntryIn) (i : Nat) (ent : CtxEntryIn), Eq (OptionType CtxEntryIn) (ctx_entry_lookup G i) (OptionType.some CtxEntryIn ent) -> TypingTcIn R tenv Bool.true G (KExpr.bvar i) (lift_at (ctx_entry_type ent) Nat.zero (Nat.succ i))
| sort : forall (G : ListType CtxEntryIn) (u : Level), TypingTcIn R tenv Bool.true G (KExpr.sort u) (KExpr.sort (Level.succ u))
| pi : forall (G : ListType CtxEntryIn) (A : KExpr) (B : KExpr) (u : Level) (v : Level), TypingTcIn R tenv Bool.true G A (KExpr.sort u) -> TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) B (KExpr.sort v) -> TypingTcIn R tenv Bool.true G (KExpr.pi A B) (KExpr.sort (Level.imax u v))
| lam : forall (G : ListType CtxEntryIn) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingTcIn R tenv Bool.true G A (KExpr.sort u) -> TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b B -> TypingTcIn R tenv Bool.true G (KExpr.lam A b) (KExpr.pi A B)
| app : forall (G : ListType CtxEntryIn) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), TypingTcIn R tenv Bool.true G f (KExpr.pi A B) -> TypingTcIn R tenv Bool.true G a A -> TypingTcIn R tenv Bool.true G (KExpr.app f a) (instantiate B a)
| const : forall (G : ListType CtxEntryIn) (n : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) -> TypingTcIn R tenv Bool.true G (KExpr.const n us) A
| conv : forall (G : ListType CtxEntryIn) (e : KExpr) (A : KExpr) (B : KExpr), TypingTcIn R tenv Bool.true G e A -> TypingTcIn R tenv Bool.false G A B -> TypingTcIn R tenv Bool.true G e B
| let_ : forall (G : ListType CtxEntryIn) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingTcIn R tenv Bool.true G A (KExpr.sort u) -> TypingTcIn R tenv Bool.true G v A -> TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b B -> TypingTcIn R tenv Bool.true G (KExpr.let_ A v b) (instantiate B v)
| let_def : forall (G : ListType CtxEntryIn) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingTcIn R tenv Bool.true G A (KExpr.sort u) -> TypingTcIn R tenv Bool.true G v A -> TypingTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.defn A v) G) b B -> TypingTcIn R tenv Bool.true G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType CtxEntryIn) (n : Nat), TypingTcIn R tenv Bool.true G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType CtxEntryIn) (n : Nat), TypingTcIn R tenv Bool.true G (literal_string n) literal_string_type
| proj : forall (G : ListType CtxEntryIn) (S : Name) (idx : Nat) (e : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr), TypingTcIn R tenv Bool.true G e W -> ProjStructIn R S idx W im cm -> ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start -> ProjFieldIn R S e Nat.zero idx start F -> TypingTcIn R tenv Bool.true G (KExpr.proj S idx e) F
| cdp : forall (G : ListType CtxEntryIn) (a : KExpr) (b : KExpr), DefEqCDPIn R a b -> TypingTcIn R tenv Bool.false G a b
| symm : forall (G : ListType CtxEntryIn) (a : KExpr) (b : KExpr), TypingTcIn R tenv Bool.false G a b -> TypingTcIn R tenv Bool.false G b a
| trans : forall (G : ListType CtxEntryIn) (a : KExpr) (m : KExpr) (b : KExpr), TypingTcIn R tenv Bool.false G a m -> TypingTcIn R tenv Bool.false G m b -> TypingTcIn R tenv Bool.false G a b
| app_cong : forall (G : ListType CtxEntryIn) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr), TypingTcIn R tenv Bool.false G f f2 -> TypingTcIn R tenv Bool.false G a a2 -> TypingTcIn R tenv Bool.false G (KExpr.app f a) (KExpr.app f2 a2)
| lam_cong : forall (G : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr), TypingTcIn R tenv Bool.false G A A2 -> TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b b2 -> TypingTcIn R tenv Bool.false G (KExpr.lam A b) (KExpr.lam A2 b2)
| pi_cong : forall (G : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr), TypingTcIn R tenv Bool.false G A A2 -> TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) B B2 -> TypingTcIn R tenv Bool.false G (KExpr.pi A B) (KExpr.pi A2 B2)
| let_cong : forall (G : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr), TypingTcIn R tenv Bool.false G A A2 -> TypingTcIn R tenv Bool.false G v v2 -> TypingTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b b2 -> TypingTcIn R tenv Bool.false G (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2)
| proj_cong : forall (G : ListType CtxEntryIn) (n : Name) (i : Nat) (e : KExpr) (e2 : KExpr), TypingTcIn R tenv Bool.false G e e2 -> TypingTcIn R tenv Bool.false G (KExpr.proj n i e) (KExpr.proj n i e2)
| proof_irrel : forall (G : ListType CtxEntryIn) (p : KExpr) (P : KExpr) (q : KExpr), TypingTcIn R tenv Bool.true G p P -> TypingTcIn R tenv Bool.true G P (KExpr.sort Level.zero) -> TypingTcIn R tenv Bool.true G q P -> TypingTcIn R tenv Bool.false G p q
| eta : forall (G : ListType CtxEntryIn) (f : KExpr) (A : KExpr) (B : KExpr), TypingTcIn R tenv Bool.true G f (KExpr.pi A B) -> TypingTcIn R tenv Bool.false G f (KExpr.lam A (KExpr.app (lift_at f Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))
| unit_like : forall (G : ListType CtxEntryIn) (a : KExpr) (b : KExpr) (W : KExpr), TypingTcIn R tenv Bool.true G a W -> TypingTcIn R tenv Bool.true G b W -> UnitLikeIn R W -> TypingTcIn R tenv Bool.false G a b
| struct_eta : forall (G : ListType CtxEntryIn) (t : KExpr) (s : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta), StructCtorIn R t im cm -> TypingTcIn R tenv Bool.true G s W -> Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name (kctor_parent cm)) -> (forall (i : Nat), Eq Bool (nat_leb (Nat.succ i) (kctor_num_fields cm)) Bool.true -> TypingTcIn R tenv Bool.false G (KExpr.proj (kctor_parent cm) i s) (accepts_kexpr_nth (kapp_args t) (Nat.add (kctor_num_params cm) i))) -> TypingTcIn R tenv Bool.false G t s
| zeta_local : forall (G : ListType CtxEntryIn) (i : Nat) (A : KExpr) (v : KExpr), Eq (OptionType CtxEntryIn) (ctx_entry_lookup G i) (OptionType.some CtxEntryIn (CtxEntryIn.defn A v)) -> TypingTcIn R tenv Bool.false G (KExpr.bvar i) (lift_at v Nat.zero (Nat.succ i))
| lit_zero : forall (G : ListType CtxEntryIn), TypingTcIn R tenv Bool.false G (literal_nat Nat.zero) (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level))
| lit_succ : forall (G : ListType CtxEntryIn) (n : Nat), TypingTcIn R tenv Bool.false G (literal_nat (Nat.succ n)) (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))
| quot_lift : forall (G : ListType CtxEntryIn) (ul : ListType Level) (A : KExpr) (r : KExpr) (B : KExpr) (f : KExpr) (h : KExpr) (um : ListType Level) (A2 : KExpr) (r2 : KExpr) (a : KExpr), TypingTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_lift_name ul) A) r) B) f) h) (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name um) A2) r2) a)) (KExpr.app f a)
| quot_ind : forall (G : ListType CtxEntryIn) (ul : ListType Level) (A : KExpr) (r : KExpr) (B : KExpr) (f : KExpr) (um : ListType Level) (A2 : KExpr) (r2 : KExpr) (a : KExpr), TypingTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_ind_name ul) A) r) B) f) (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name um) A2) r2) a)) (KExpr.app f a)
| k_like : forall (G : ListType CtxEntryIn) (rn : Name) (I : Name) (mta : RecMeta) (cn : Name) (major : KExpr) (W : KExpr) (ctor : KExpr), RecKAdmitIn R rn I mta cn -> TypingTcIn R tenv Bool.true G major W -> TypingTcIn R tenv Bool.true G ctor W -> Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name I) -> TypingTcIn R tenv Bool.false G major ctor
| lit_string_expand : forall (G : ListType CtxEntryIn) (cs : ListType Nat), StringLitAdmitIn R -> Eq Bool (string_lit_chars_valid cs) Bool.true -> TypingTcIn R tenv Bool.false G (literal_string (string_lit_code cs)) (string_lit_expansion cs)";

/// The algorithmic relation, CHECK mode. Typing arms output the type the
/// deployed arm returns; every whnf premise is a conversion of this family.
pub(super) const ACCEPTS_TC: &str = r"inductive KernelAcceptsTcIn (R : RedEnv) (tenv : KDeclEnv) : Bool -> ListType CtxEntryIn -> KExpr -> KExpr -> Type
| sort : forall (G : ListType CtxEntryIn) (u : Level), KernelAcceptsTcIn R tenv Bool.true G (KExpr.sort u) (KExpr.sort (Level.succ u))
| bvar : forall (G : ListType CtxEntryIn) (i : Nat) (ent : CtxEntryIn), Eq (OptionType CtxEntryIn) (ctx_entry_lookup G i) (OptionType.some CtxEntryIn ent) -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.bvar i) (lift_at (ctx_entry_type ent) Nat.zero (Nat.succ i))
| pi : forall (G : ListType CtxEntryIn) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level) (r : Level), KernelAcceptsTcIn R tenv Bool.true G A SA -> KernelAcceptsTcIn R tenv Bool.false G SA (KExpr.sort u) -> KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) B SB -> KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) SB (KExpr.sort v) -> levelEqSem (Level.imax u v) r -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.pi A B) (KExpr.sort r)
| lam : forall (G : ListType CtxEntryIn) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level), KernelAcceptsTcIn R tenv Bool.true G A SA -> KernelAcceptsTcIn R tenv Bool.false G SA (KExpr.sort u) -> KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b B -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.lam A b) (KExpr.pi A B)
| const : forall (G : ListType CtxEntryIn) (n : Name) (us : ListType Level) (A : KExpr) (T : KExpr), Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) -> KExprUniverseEq A T -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.const n us) T
| app : forall (G : ListType CtxEntryIn) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A2 : KExpr), KernelAcceptsTcIn R tenv Bool.true G f F -> KernelAcceptsTcIn R tenv Bool.false G F (KExpr.pi A B) -> KernelAcceptsTcIn R tenv Bool.true G a A2 -> KernelAcceptsTcIn R tenv Bool.false G A2 A -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.app f a) (instantiate B a)
| let_ : forall (G : ListType CtxEntryIn) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr), KernelAcceptsTcIn R tenv Bool.true G A Ty -> KernelAcceptsTcIn R tenv Bool.false G Ty (KExpr.sort u) -> KernelAcceptsTcIn R tenv Bool.true G v Tv -> KernelAcceptsTcIn R tenv Bool.false G Tv A -> KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b B -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.let_ A v b) (instantiate B v)
| let_def : forall (G : ListType CtxEntryIn) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr), KernelAcceptsTcIn R tenv Bool.true G A Ty -> KernelAcceptsTcIn R tenv Bool.false G Ty (KExpr.sort u) -> KernelAcceptsTcIn R tenv Bool.true G v Tv -> KernelAcceptsTcIn R tenv Bool.false G Tv A -> KernelAcceptsTcIn R tenv Bool.true (ListType.cons CtxEntryIn (CtxEntryIn.defn A v) G) b B -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType CtxEntryIn) (n : Nat), KernelAcceptsTcIn R tenv Bool.true G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType CtxEntryIn) (n : Nat), KernelAcceptsTcIn R tenv Bool.true G (literal_string n) literal_string_type
| proj : forall (G : ListType CtxEntryIn) (S : Name) (idx : Nat) (e : KExpr) (E : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta) (start : KExpr) (F : KExpr), KernelAcceptsTcIn R tenv Bool.true G e E -> KernelAcceptsTcIn R tenv Bool.false G E W -> ProjStructIn R S idx W im cm -> ProjParamsIn R (projection_ctor_type (kconst_params (kind_sig im)) (kctor_sig cm) (kexpr_const_levels (kapp_fn W))) (list_take (kctor_num_params cm) (kapp_args W)) start -> ProjFieldIn R S e Nat.zero idx start F -> KernelAcceptsTcIn R tenv Bool.true G (KExpr.proj S idx e) F
| cdp : forall (G : ListType CtxEntryIn) (a : KExpr) (b : KExpr), DefEqCDPIn R a b -> KernelAcceptsTcIn R tenv Bool.false G a b
| symm : forall (G : ListType CtxEntryIn) (a : KExpr) (b : KExpr), KernelAcceptsTcIn R tenv Bool.false G a b -> KernelAcceptsTcIn R tenv Bool.false G b a
| trans : forall (G : ListType CtxEntryIn) (a : KExpr) (m : KExpr) (b : KExpr), KernelAcceptsTcIn R tenv Bool.false G a m -> KernelAcceptsTcIn R tenv Bool.false G m b -> KernelAcceptsTcIn R tenv Bool.false G a b
| app_cong : forall (G : ListType CtxEntryIn) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr), KernelAcceptsTcIn R tenv Bool.false G f f2 -> KernelAcceptsTcIn R tenv Bool.false G a a2 -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.app f a) (KExpr.app f2 a2)
| lam_cong : forall (G : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr), KernelAcceptsTcIn R tenv Bool.false G A A2 -> KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b b2 -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.lam A b) (KExpr.lam A2 b2)
| pi_cong : forall (G : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr), KernelAcceptsTcIn R tenv Bool.false G A A2 -> KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) B B2 -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.pi A B) (KExpr.pi A2 B2)
| let_cong : forall (G : ListType CtxEntryIn) (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr), KernelAcceptsTcIn R tenv Bool.false G A A2 -> KernelAcceptsTcIn R tenv Bool.false G v v2 -> KernelAcceptsTcIn R tenv Bool.false (ListType.cons CtxEntryIn (CtxEntryIn.decl A) G) b b2 -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2)
| proj_cong : forall (G : ListType CtxEntryIn) (n : Name) (i : Nat) (e : KExpr) (e2 : KExpr), KernelAcceptsTcIn R tenv Bool.false G e e2 -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.proj n i e) (KExpr.proj n i e2)
| proof_irrel : forall (G : ListType CtxEntryIn) (a : KExpr) (A : KExpr) (W : KExpr) (S : KExpr) (b : KExpr) (B : KExpr), KernelAcceptsTcIn R tenv Bool.true G a A -> KernelAcceptsTcIn R tenv Bool.false G A W -> KernelAcceptsTcIn R tenv Bool.true G W S -> KernelAcceptsTcIn R tenv Bool.false G S (KExpr.sort Level.zero) -> KernelAcceptsTcIn R tenv Bool.true G b B -> KernelAcceptsTcIn R tenv Bool.false G A B -> KernelAcceptsTcIn R tenv Bool.false G a b
| eta : forall (G : ListType CtxEntryIn) (f : KExpr) (F : KExpr) (A : KExpr) (B : KExpr), KernelAcceptsTcIn R tenv Bool.true G f F -> KernelAcceptsTcIn R tenv Bool.false G F (KExpr.pi A B) -> KernelAcceptsTcIn R tenv Bool.false G f (KExpr.lam A (KExpr.app (lift_at f Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))
| unit_like : forall (G : ListType CtxEntryIn) (a : KExpr) (A : KExpr) (W : KExpr) (b : KExpr) (B : KExpr), KernelAcceptsTcIn R tenv Bool.true G a A -> KernelAcceptsTcIn R tenv Bool.false G A W -> UnitLikeIn R W -> KernelAcceptsTcIn R tenv Bool.true G b B -> KernelAcceptsTcIn R tenv Bool.false G B W -> KernelAcceptsTcIn R tenv Bool.false G a b
| struct_eta : forall (G : ListType CtxEntryIn) (t : KExpr) (s : KExpr) (S : KExpr) (W : KExpr) (im : KIndMeta) (cm : KCtorMeta), StructCtorIn R t im cm -> KernelAcceptsTcIn R tenv Bool.true G s S -> KernelAcceptsTcIn R tenv Bool.false G S W -> Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name (kctor_parent cm)) -> (forall (i : Nat), Eq Bool (nat_leb (Nat.succ i) (kctor_num_fields cm)) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.proj (kctor_parent cm) i s) (accepts_kexpr_nth (kapp_args t) (Nat.add (kctor_num_params cm) i))) -> KernelAcceptsTcIn R tenv Bool.false G t s
| zeta_local : forall (G : ListType CtxEntryIn) (i : Nat) (A : KExpr) (v : KExpr), Eq (OptionType CtxEntryIn) (ctx_entry_lookup G i) (OptionType.some CtxEntryIn (CtxEntryIn.defn A v)) -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.bvar i) (lift_at v Nat.zero (Nat.succ i))
| lit_zero : forall (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G (literal_nat Nat.zero) (KExpr.const accepts_tc_nat_zero_name (ListType.nil Level))
| lit_succ : forall (G : ListType CtxEntryIn) (n : Nat), KernelAcceptsTcIn R tenv Bool.false G (literal_nat (Nat.succ n)) (KExpr.app (KExpr.const accepts_tc_nat_succ_name (ListType.nil Level)) (literal_nat n))
| quot_lift : forall (G : ListType CtxEntryIn) (ul : ListType Level) (A : KExpr) (r : KExpr) (B : KExpr) (f : KExpr) (h : KExpr) (um : ListType Level) (A2 : KExpr) (r2 : KExpr) (a : KExpr), KernelAcceptsTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_lift_name ul) A) r) B) f) h) (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name um) A2) r2) a)) (KExpr.app f a)
| quot_ind : forall (G : ListType CtxEntryIn) (ul : ListType Level) (A : KExpr) (r : KExpr) (B : KExpr) (f : KExpr) (um : ListType Level) (A2 : KExpr) (r2 : KExpr) (a : KExpr), KernelAcceptsTcIn R tenv Bool.false G (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_ind_name ul) A) r) B) f) (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name um) A2) r2) a)) (KExpr.app f a)
| k_like : forall (G : ListType CtxEntryIn) (rn : Name) (I : Name) (mta : RecMeta) (cn : Name) (cus : ListType Level) (major : KExpr) (M : KExpr) (W : KExpr) (C : KExpr), RecKAdmitIn R rn I mta cn -> KernelAcceptsTcIn R tenv Bool.true G major M -> KernelAcceptsTcIn R tenv Bool.false G M W -> Eq (OptionType Name) (kexpr_const_name (kapp_fn W)) (OptionType.some Name I) -> KernelAcceptsTcIn R tenv Bool.true G (apply_spine (list_take (recmeta_num_params mta) (kapp_args W)) (KExpr.const cn cus)) C -> KernelAcceptsTcIn R tenv Bool.false G W C -> KernelAcceptsTcIn R tenv Bool.false G major (apply_spine (list_take (recmeta_num_params mta) (kapp_args W)) (KExpr.const cn cus))
| lit_string_expand : forall (G : ListType CtxEntryIn) (cs : ListType Nat), StringLitAdmitIn R -> Eq Bool (string_lit_chars_valid cs) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G (literal_string (string_lit_code cs)) (string_lit_expansion cs)";

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(CTX_ENTRY),
    DeclarationInput::Data(CTX_ENTRY_TYPE),
    DeclarationInput::Data(CTX_ENTRY_LOOKUP),
    DeclarationInput::Data(LCTX_DECLS),
    DeclarationInput::Data(LCTX_OPT_DECL),
    DeclarationInput::Data(KEXPR_NTH),
    DeclarationInput::Inductive(UNIT_LIKE),
    DeclarationInput::Inductive(STRUCT_CTOR),
    DeclarationInput::Data(ENDS_IN_PROP),
    DeclarationInput::Inductive(K_ADMIT),
    DeclarationInput::Inductive(TYPING_TC),
    DeclarationInput::Inductive(ACCEPTS_TC),
];
