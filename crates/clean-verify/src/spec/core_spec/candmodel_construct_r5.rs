// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R5 of the candidate-model construction ladder — the PAYOFF rung: the
//! Pi-CANDIDATE `PiSet` over reflected `KExpr` (corpus `Stratified/Cand.lean`
//! `PiSet`/`isCand_piSet`), a TYPE INTERPRETATION `candInterp` built from it,
//! and an UNCONDITIONAL strong-normalization capstone `fragTy_sn` for a shaped
//! fragment judgment `FragTy` — the spec analogue of the corpus's own honest
//! end state (`CCU` -> `sn_ccu`).
//!
//! Port of `Stratified/Cand.lean` `PiSet`/`piSet_cr3_aux`/`isCand_piSet` and
//! the `CCUShape`/`CCUSN` shape-interpretation architecture, per
//! `designs/2026-08-23-spec-candmodel-port.md` §5 rungs R4/R5/R6 and §3 rows
//! 1/6/7. Builds on R0 (`IsCandSet`, `cand_var_mem`, `omega*`), R1
//! (`candExp_beta`, `betaStar`, `betaStar_bvar0_fam`, `lamHead_beta_inv`,
//! `selfLoop_not_whnfAcc`), R2 (`r2_const_no_beta_reduces` idiom), R3
//! (`beta_inv_body` scaffold, `natRecZ_iota_fires`, `sp`/`zcontract`) and R4
//! (`constSpine3_beta_inv`).
//!
//! ## The one obstruction, stated up front
//!
//! `IsCandSet`'s cr3 face quantifies over EVERY `Neutral e`. For the Pi-set
//! `PiSet CA CB t = forall a, CA a -> CB a (app t a)` the cr3 obligation must
//! classify every one-step reduct of `app e a`. In the corpus that set is
//! `{beta, appL, appR}` because eliminators there are SATURATED CONSTRUCTORS
//! (`.natrec m z s n`), so applying a neutral to one more argument can never
//! create a fresh redex. In the spec's `KExpr` eliminators are CONST-HEADED
//! SPINES, so `app e a` genuinely can be a fresh iota redex that `e` is not —
//! and cr3's hypothesis says NOTHING about that reduct. The gap is registered,
//! not described: `piSet_cr3_headFree_necessary` exhibits
//! `e = Nat.rec (bvar 0) (bvar 0) (bvar 0)` at the REAL reflected env with all
//! four facts machine-checked — `e` is `Neutral`, `e` is NOT head-free, `e`
//! has NO `whnf_step` at all (so cr3's premise is satisfied VACUOUSLY), and
//! `app e Nat.zero` iota-fires to the real `Nat.rec` zero-rule contractum.
//! With zero information available about that contractum, no derivation of
//! `CB a contractum` from cr3's data exists. Full `IsCandSet (PiSet CA CB)` is
//! therefore NOT an R5 theorem.
//!
//! What IS an R5 theorem is the HEAD-FREE-restricted candidate interface
//! `IsCandHF` (cr1 + cr2 + `candCr3HF`, whose cr3 additionally assumes
//! `HeadFree e`, i.e. `kexpr_const_name (kapp_fn e) = none`). That restriction
//! is exactly enough — head-freeness passes through application definitionally
//! (`kapp_fn (app e a)` REDUCES to `kapp_fn e`), so both the iota and the
//! delta legs of `app e a` die — and it costs the ladder nothing: every cr3
//! use in this rung and in R1's beta engine is at an `app (lam ..) ..` or a
//! `bvar` head, all head-free by `Eq.refl`.
//!
//! ## What is landed, at what scope
//!
//! - **A (the Pi-candidate).** `PiSet` + `piSet_cr1`/`piSet_cr2`/`piSet_cr3`
//!   + `isCandHF_piSet`. cr1 and cr2 are UNRESTRICTED; cr3 is the head-free
//!   face. The corpus's `hinv` step-invariance side condition is KEPT (design
//!   §6.6: do not simplify it away) in the exact direction the proof consumes
//!   it, as `candStepInv CA CB`; for a constant codomain family it is the
//!   identity, which is how the interpretation discharges it. New supporting
//!   infrastructure, none of which existed spec-side: `deltaStep_app_gen` (a
//!   delta step lifts under ANY application, generalizing R3's
//!   `delta_app_lift` off the bare-const head via `r5_spine_snoc`),
//!   `whnfStep_app_left` (the full one-step app-left congruence, beta AND
//!   delta legs) and `whnfAcc_app_left` (the corpus's `sn_app_left`).
//! - **B (the interpretation).** `candInterp : KExpr -> KExpr -> Type` by
//!   `KExpr.rec`: sorts and every non-Pi former to the top candidate
//!   `whnf_acc` (`red_sort` holds definitionally), `pi A B` to
//!   `PiSet (candInterp A) (fun _ => candInterp B)`. `candInterp_isCandHF`
//!   proves candidate-hood at EVERY `T` — untyped, no shape discipline —
//!   which is more than the corpus gets (`isCand_cval` needs `CWK`) precisely
//!   because the Pi clause is NON-DEPENDENT. **That is the honest scope
//!   limit of B**: the codomain family ignores the argument, so this
//!   interprets the SIMPLE-type reading of `pi A B`. A dependent clause needs
//!   `candInterp (instantiate B a)`, which is not structural in `KExpr` and is
//!   exactly the corpus's shape/denotation split (design rung R5/R6 proper).
//!   The interpretation is NOT degenerate: `r5_interp_pi_proper` is the
//!   `micro_has_type`-trap guard — `r5_omegaLam` IS `whnf_acc` and is NOT in
//!   `candInterp (pi (sort 0) (sort 0))`, so the Pi interpretation is a PROPER
//!   subset of the top set, not the total predicate.
//! - **C (the fundamental theorem + capstone).** `FragTy : KExpr -> KExpr ->
//!   Type` with four rules (sortMem / var / app / lam), `fragTy_interp`
//!   (`FragTy T e -> candInterp T e`, by `FragTy.rec`) and
//!   `fragTy_sn : FragTy T e -> whnf_acc e`. **UNCONDITIONAL**: no
//!   `RecEnvClosed`, no `DefEnvClosed`, no `CandModel`, no carried premise of
//!   any kind. The lam rule takes R1's development-family premise rather than
//!   R2's corpus-spelling single contractum precisely so that no closedness
//!   hypothesis is carried — R2's `candExp_beta_subst` would have imported
//!   `RecEnvClosed (red_rec the_red_env)`, which is not dischargeable at this
//!   stage position, and the capstone would then have been conditional.
//!   `FragTy` is a SEMANTIC-premise judgment (its lam and app rules mention
//!   `candInterp`), not a syntactic typing derivation: a syntactic one needs
//!   contexts and parallel substitution, which is what R6 owes.
//! - **D (witnesses).** `fragTy_sn_witness` puts a genuine beta redex
//!   `app (lam (bvar 0) (bvar 0)) (bvar 1)` through the whole chain
//!   (`FragTy.lam` -> `fragTy_interp` -> `candExpHF_beta` -> `candInterp_cr1`);
//!   `r5_interp_pi_proper` and `fragTy_not_total` are the non-degeneracy pair;
//!   `piSet_cr3_headFree_necessary` is the added premise's necessity guard.
//! - **E (the premise-satisfiability witnesses).** Two of this rung's own
//!   predicates were ASSUMED everywhere and concluded nowhere, which the
//!   premise gate found. `PiSet` is a hypothesis of `piSet_cr2`/`piSet_cr3*`
//!   while every face concludes *about* it (`candCr1 (PiSet ..)`,
//!   `IsCandHF (PiSet ..)`) and never *in* it — so the faces could have been
//!   about an empty set; `piSet_id_witness` puts the identity lambda in it
//!   through `fragTy_interp`. `candStepInv` is carried by `piSet_cr3_aux`,
//!   `piSet_cr3` and `isCandHF_piSet`; `candStepInv_const` discharges it for
//!   every constant codomain family (the term the interpretation's pi arm
//!   already supplied inline) and `candStepInv_interp_witness` pins the closed
//!   instance.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`.** `IsCandHF` has no
//!   `pi_elim` in `CandModel`'s exact untyped-`T` sense, no `redTypeStep`, no
//!   `redRec*`, and `candInterp` is not an instance of the telescope.
//!   `fragTy_sn` is SN for `FragTy`, NOT for `TypingCtx`, and must never be
//!   described as advancing `whnf_terminates_well_typed_dependent` (design
//!   §6.2 — the wh3-loop retraction is the precedent for that overclaim).
//! - **`candExpHF_beta` is R1's engine at the weaker interface, DERIVED by
//!   textual weakening of R1's own builder, not retyped.** The three cr-uses
//!   it makes are `isCandSet_cr1/cr2` on the argument set and ONE `isCandSet_cr3`
//!   at the redex `app (lam ty0 b0) a0` — head-free by `Eq.refl`, which is why
//!   the weakening is sound and total. A shape guard pins that no
//!   `IsCandSet`/`isCandSet_` spelling survives the rewrite.
//! - **The delta congruence is REAL reduction, generically.**
//!   `deltaReduct_app_gen` proves `delta_reduct env (app e a) =
//!   opt_bind (delta_reduct env e) (fun x => some (app x a))` for EVERY `e` —
//!   two nested `OptionType.rec` case splits over the head-name and value
//!   lookups plus the snoc identity `apply_spine (xs ++ [a]) h =
//!   app (apply_spine xs h) a`. R3's `delta_app_lift` had this only for a BARE
//!   const head; `whnfAcc_app_left` and `piSet_cr2` need it at an arbitrary
//!   head, so it is generalized here rather than special-cased.
//! - **Prop/Type discipline.** `HeadFree` is Prop (it is an `Eq`), `Neutral`
//!   and `candInterp T` are Type. Every `(C : Type)` CPS eliminator
//!   (`option_none_ne_some_type`, `no_whnf_step_bvar`, `lam_ne_app`, …) is
//!   instantiated only at Type-valued goals; absurdities that must land in a
//!   Prop go through `Empty` first. Pinned by the shape guard.
//! - **Recursor-promotion.** `FragTy`'s first constructor `sortMem` leads with
//!   `(n : Level)` and concludes at the NON-variable index `KExpr.sort n`, so
//!   no uniform leading ctor-argument prefix exists and the measured
//!   2026-08-23 promotion cannot fire; `fragTy_interp` consumes `FragTy.rec`
//!   with a full three-binder motive, so a promotion would fail the rung
//!   loudly rather than silently. Both recursive premises are the LAST
//!   constructor field, so the minor-premise binder order is the same under
//!   either fields-then-IHs or interleaved convention.
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (plain defs via
//! `add_recursive_def`, one genuine inductive via `add_inductive`, theorems via
//! `add_definition` with kernel `add_decl` checking). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R5 SOURCES BEGIN (pure string builders; the pre-validation parse   ====
// ==== harness extracts this region together with R1's engine builder and ====
// ==== R3's 15-arm scaffold, both reused verbatim rather than duplicated. ====

use super::candmodel_construct_r1::{ty_candexp_beta, val_candexp_beta};
use super::candmodel_construct_r3::{beta_inv_body, sp, zcontract, Cont, NZERO};

/// `bvar 0` — the canonical irreducible neutral, used as every concrete
/// probe's inert component.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// The self-application body `app (bvar 0) (bvar 0)`.
const SELF_BODY: &str = "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";
/// `sort 0`, the fragment's only base type.
const S0: &str = "(KExpr.sort Level.zero)";
/// The identity lambda of the fragment witnesses.
const IDLAM: &str = "(KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// The map `fun x => some (app x a)` that the applied-delta reduct factors
/// through.
const FAP: &str = "(fun (qx : KExpr) => @OptionType.some KExpr (KExpr.app qx a))";
/// `candInterp (sort 0)` — the interpretation of the fragment's base type. It
/// is both the domain candidate and (constantly) the codomain family of the
/// Pi-candidate the two premise-satisfiability witnesses inhabit.
const INTERP_S0: &str = "(candInterp (KExpr.sort Level.zero))";

// ================================================================
// Group A — application congruence: the spine snoc identity, the GENERIC
// applied-delta transport, the one-step app-left congruence and the
// corpus `sn_app_left`.
// ================================================================

pub(super) const TY_R5_SPINE_SNOC: &str = "forall (a : KExpr) (xs : ListType KExpr) (h : KExpr), @Eq KExpr (apply_spine (list_append xs (@ListType.cons KExpr a (@ListType.nil KExpr))) h) (KExpr.app (apply_spine xs h) a)";

pub(super) const VAL_R5_SPINE_SNOC: &str = "fun (a : KExpr) (xs : ListType KExpr) => @ListType.rec KExpr (fun (ql : ListType KExpr) => forall (qh : KExpr), @Eq KExpr (apply_spine (list_append ql (@ListType.cons KExpr a (@ListType.nil KExpr))) qh) (KExpr.app (apply_spine ql qh) a)) (fun (qh : KExpr) => @Eq.refl KExpr (KExpr.app qh a)) (fun (qx : KExpr) (qrest : ListType KExpr) (qih : forall (qh : KExpr), @Eq KExpr (apply_spine (list_append qrest (@ListType.cons KExpr a (@ListType.nil KExpr))) qh) (KExpr.app (apply_spine qrest qh) a)) => fun (qh : KExpr) => qih (KExpr.app qh qx)) xs";

pub(super) const TY_DELTAREDUCT_APP_GEN: &str = "forall (env : DefEnv) (e : KExpr) (a : KExpr), @Eq (OptionType KExpr) (delta_reduct env (KExpr.app e a)) (opt_bind KExpr KExpr (delta_reduct env e) (fun (qx : KExpr) => @OptionType.some KExpr (KExpr.app qx a)))";

pub(super) fn val_deltareduct_app_gen() -> String {
    // The two value-level continuations of delta_reduct, at the plain spine
    // and at the snoc'ed spine (which is what `kapp_args (app e a)` REDUCES
    // to — `kapp_args` is structural on the app field).
    let l3e = "(fun (qv : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args e) qv))";
    let l3ea = "(fun (qv : KExpr) => @OptionType.some KExpr (apply_spine (list_append (kapp_args e) (@ListType.cons KExpr a (@ListType.nil KExpr))) qv))";
    // Inner split on `defval_for env qn`: none/none by refl, some/some by
    // congruence of `some` along the snoc identity.
    let inner = format!(
        "(fun (qn : Name) => @OptionType.rec KExpr (fun (qo : OptionType KExpr) => @Eq (OptionType KExpr) (opt_bind KExpr KExpr qo {l3ea}) (opt_bind KExpr KExpr (opt_bind KExpr KExpr qo {l3e}) {FAP})) (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)) (fun (qv : KExpr) => @Eq.cong KExpr (OptionType KExpr) (fun (qw : KExpr) => @OptionType.some KExpr qw) (apply_spine (list_append (kapp_args e) (@ListType.cons KExpr a (@ListType.nil KExpr))) qv) (KExpr.app (apply_spine (kapp_args e) qv) a) (r5_spine_snoc a (kapp_args e) qv)) (kdef_value_at env qn (kexpr_const_levels (kapp_fn e))))"
    );
    let mot = format!(
        "(fun (qm : OptionType Name) => @Eq (OptionType KExpr) (opt_bind Name KExpr qm (fun (qn : Name) => opt_bind KExpr KExpr (kdef_value_at env qn (kexpr_const_levels (kapp_fn e))) {l3ea})) (opt_bind KExpr KExpr (opt_bind Name KExpr qm (fun (qn : Name) => opt_bind KExpr KExpr (kdef_value_at env qn (kexpr_const_levels (kapp_fn e))) {l3e})) {FAP}))"
    );
    format!(
        "fun (env : DefEnv) (e : KExpr) (a : KExpr) => @OptionType.rec Name {mot} (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)) {inner} (kexpr_const_name (kapp_fn e))"
    )
}

pub(super) const TY_DELTASTEP_APP_GEN: &str = "forall (env : DefEnv) (e : KExpr) (v : KExpr) (a : KExpr), delta_step env e v -> delta_step env (KExpr.app e a) (KExpr.app v a)";

pub(super) fn val_deltastep_app_gen() -> String {
    format!(
        "fun (env : DefEnv) (e : KExpr) (v : KExpr) (a : KExpr) (hd : delta_step env e v) => @Eq.trans (OptionType KExpr) (delta_reduct env (KExpr.app e a)) (opt_bind KExpr KExpr (delta_reduct env e) {FAP}) (@OptionType.some KExpr (KExpr.app v a)) (deltaReduct_app_gen env e a) (@Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (qo : OptionType KExpr) => opt_bind KExpr KExpr qo {FAP}) (delta_reduct env e) (@OptionType.some KExpr v) hd)"
    )
}

pub(super) const TY_WHNFSTEP_APP_LEFT: &str = "forall (f : KExpr) (f2 : KExpr) (a : KExpr), whnf_step f f2 -> whnf_step (KExpr.app f a) (KExpr.app f2 a)";

pub(super) const VAL_WHNFSTEP_APP_LEFT: &str = "fun (f : KExpr) (f2 : KExpr) (a : KExpr) (hs : whnf_step f f2) => @whnf_step.rec f f2 (fun (_ : whnf_step f f2) => whnf_step (KExpr.app f a) (KExpr.app f2 a)) (fun (hbr : beta_reduces f f2) => whnf_step.beta (KExpr.app f a) (KExpr.app f2 a) (beta_reduces.app_left f f2 a hbr)) (fun (hdr : delta_reduces f f2) => whnf_step.delta (KExpr.app f a) (KExpr.app f2 a) (delta_step_to_reduces (KExpr.app f a) (KExpr.app f2 a) (deltaStep_app_gen (red_def the_red_env) f f2 a (delta_reduces_to_step f f2 hdr)))) hs";

pub(super) const TY_WHNFACC_APP_LEFT: &str =
    "forall (f : KExpr) (a : KExpr), whnf_acc (KExpr.app f a) -> whnf_acc f";

pub(super) const VAL_WHNFACC_APP_LEFT: &str = "fun (f : KExpr) (a : KExpr) (hacc : whnf_acc (KExpr.app f a)) => @whnf_acc.rec (fun (qx : KExpr) (_ : whnf_acc qx) => forall (qf : KExpr) (qa : KExpr), @Eq KExpr qx (KExpr.app qf qa) -> whnf_acc qf) (fun (qx : KExpr) (_qhs : forall (qy : KExpr), whnf_step qx qy -> whnf_acc qy) (qih : forall (qy : KExpr), whnf_step qx qy -> forall (qf : KExpr) (qa : KExpr), @Eq KExpr qy (KExpr.app qf qa) -> whnf_acc qf) (qf : KExpr) (qa : KExpr) (qeq : @Eq KExpr qx (KExpr.app qf qa)) => whnf_acc.intro qf (fun (qf2 : KExpr) (qstep : whnf_step qf qf2) => qih (KExpr.app qf2 qa) (@Eq.substType KExpr (fun (qz : KExpr) => whnf_step qz (KExpr.app qf2 qa)) (KExpr.app qf qa) qx (@Eq.symm KExpr qx (KExpr.app qf qa) qeq) (whnfStep_app_left qf qf2 qa qstep)) qf2 qa (@Eq.refl KExpr (KExpr.app qf2 qa)))) (KExpr.app f a) hacc f a (@Eq.refl KExpr (KExpr.app f a))";

// ================================================================
// Group B — HeadFree and the head-free candidate interface IsCandHF.
// ================================================================

pub(super) const SRC_HEAD_FREE: &str = "def HeadFree (e : KExpr) : Prop := @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)";

pub(super) const SRC_CAND_CR3HF: &str = "def candCr3HF (S : KExpr -> Type) : Type := forall (e : KExpr), HeadFree e -> Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> S e2) -> S e";

pub(super) const SRC_IS_CAND_HF: &str = "def IsCandHF (S : KExpr -> Type) : Type := AndType (candCr1 S) (AndType (candCr2 S) (candCr3HF S))";

pub(super) const TY_ISCANDHF_INTRO: &str =
    "forall (S : KExpr -> Type), candCr1 S -> candCr2 S -> candCr3HF S -> IsCandHF S";
pub(super) const VAL_ISCANDHF_INTRO: &str = "fun (S : KExpr -> Type) (h1 : candCr1 S) (h2 : candCr2 S) (h3 : candCr3HF S) => @AndType.intro (candCr1 S) (AndType (candCr2 S) (candCr3HF S)) h1 (@AndType.intro (candCr2 S) (candCr3HF S) h2 h3)";

pub(super) const TY_ISCANDHF_CR1: &str =
    "forall (S : KExpr -> Type), IsCandHF S -> forall (e : KExpr), S e -> whnf_acc e";
pub(super) const VAL_ISCANDHF_CR1: &str = "fun (S : KExpr -> Type) (hS : IsCandHF S) => AndType.left (candCr1 S) (AndType (candCr2 S) (candCr3HF S)) hS";

pub(super) const TY_ISCANDHF_CR2: &str = "forall (S : KExpr -> Type), IsCandHF S -> forall (e : KExpr) (e2 : KExpr), S e -> whnf_step e e2 -> S e2";
pub(super) const VAL_ISCANDHF_CR2: &str = "fun (S : KExpr -> Type) (hS : IsCandHF S) => AndType.left (candCr2 S) (candCr3HF S) (AndType.right (candCr1 S) (AndType (candCr2 S) (candCr3HF S)) hS)";

pub(super) const TY_ISCANDHF_CR3: &str = "forall (S : KExpr -> Type), IsCandHF S -> forall (e : KExpr), HeadFree e -> Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> S e2) -> S e";
pub(super) const VAL_ISCANDHF_CR3: &str = "fun (S : KExpr -> Type) (hS : IsCandHF S) => AndType.right (candCr2 S) (candCr3HF S) (AndType.right (candCr1 S) (AndType (candCr2 S) (candCr3HF S)) hS)";

pub(super) const TY_HEADFREE_APP: &str =
    "forall (e : KExpr) (a : KExpr), HeadFree e -> HeadFree (KExpr.app e a)";
pub(super) const VAL_HEADFREE_APP: &str = "fun (e : KExpr) (a : KExpr) (h : HeadFree e) => h";

pub(super) const TY_ISCANDSET_WEAKEN: &str =
    "forall (S : KExpr -> Type), IsCandSet S -> IsCandHF S";
pub(super) const VAL_ISCANDSET_WEAKEN: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) => isCandHF_intro S (isCandSet_cr1 S hS) (isCandSet_cr2 S hS) (fun (e : KExpr) (_hhf : HeadFree e) (hne : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> S e2) => isCandSet_cr3 S hS e hne hred)";

pub(super) const TY_ISCANDHF_WHNFACC: &str = "IsCandHF (fun (e : KExpr) => whnf_acc e)";
pub(super) const VAL_ISCANDHF_WHNFACC: &str =
    "isCandSet_weaken (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc";

pub(super) const TY_CANDHF_VAR_MEM: &str =
    "forall (S : KExpr -> Type), IsCandHF S -> forall (i : Nat), S (KExpr.bvar i)";
pub(super) const VAL_CANDHF_VAR_MEM: &str = "fun (S : KExpr -> Type) (hS : IsCandHF S) (i : Nat) => isCandHF_cr3 S hS (KExpr.bvar i) (@Eq.refl (OptionType Name) (@OptionType.none Name)) ConstFreeUnit.triv (fun (e2 : KExpr) (hs : whnf_step (KExpr.bvar i) e2) => no_whnf_step_bvar i e2 (S e2) hs)";

// ================================================================
// Group C — the Pi-candidate.
// ================================================================

pub(super) const SRC_PI_SET: &str = "def PiSet (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type) : KExpr -> Type := fun (t : KExpr) => forall (a : KExpr), CA a -> CB a (KExpr.app t a)";

pub(super) const SRC_CAND_STEP_INV: &str = "def candStepInv (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type) : Type := forall (a : KExpr) (a2 : KExpr) (w : KExpr), CA a -> whnf_step a a2 -> CB a2 w -> CB a w";

/// The three continuations of the head-free application inversion. Binders
/// are `z`-prefixed so they cannot collide with R3's `q`-prefixed scaffold
/// binders (the R3 capture-hazard rule).
fn app_conts() -> Vec<Cont> {
    vec![
        Cont {
            name: "kLam",
            ty: "forall (zA : KExpr) (zb : KExpr), @Eq KExpr e (KExpr.lam zA zb) -> C".to_string(),
        },
        Cont {
            name: "kFn",
            ty: "forall (zy : KExpr), beta_reduces e zy -> @Eq KExpr @R@ (KExpr.app zy a) -> C"
                .to_string(),
        },
        Cont {
            name: "kArg",
            ty: "forall (zy : KExpr), beta_reduces a zy -> @Eq KExpr @R@ (KExpr.app e zy) -> C"
                .to_string(),
        },
    ]
}

fn app_conts_ty(target: &str) -> String {
    app_conts()
        .iter()
        .map(|c| format!("({}) -> ", c.ty.replace("@R@", target)))
        .collect::<Vec<_>>()
        .join("")
}

pub(super) fn ty_apphf_beta_inv() -> String {
    format!(
        "forall (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type), HeadFree e -> beta_reduces (KExpr.app e a) g2 -> {}C",
        app_conts_ty("g2")
    )
}

pub(super) fn val_apphf_beta_inv() -> String {
    let redex = "(KExpr.app e a)";
    let inj_f = "(app_inj_fst qf qa e a heq)";
    let inj_a = "(app_inj_snd qf qa e a heq)";
    let live_beta = "kLam qA qb (@Eq.symm KExpr (KExpr.lam qA qb) e (app_inj_fst (KExpr.lam qA qb) qarg e a heq))".to_string();
    let live_appl = format!(
        "kFn qf2 (@Eq.substType KExpr (fun (qz : KExpr) => beta_reduces qz qf2) qf e {inj_f} qstep) (@Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qf2 qz) qa a {inj_a})"
    );
    let live_appr = format!(
        "kArg qa2 (@Eq.substType KExpr (fun (qz : KExpr) => beta_reduces qz qa2) qa a {inj_a} qstep) (@Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qz qa2) qf e {inj_f})"
    );
    let live_iota = format!(
        "iota_step_head_none_absurd_type (red_rec the_red_env) {redex} qe2 C hhf (iota_reduces_to_step {redex} qe2 (@Eq.substType KExpr (fun (qz : KExpr) => iota_reduces qz qe2) qe {redex} heq qio))"
    );
    let body = beta_inv_body(
        redex,
        "e",
        "a",
        &app_conts(),
        &live_beta,
        &live_appl,
        &live_appr,
        &live_iota,
    );
    let conts = app_conts()
        .iter()
        .map(|c| format!(" ({} : {})", c.name, c.ty.replace("@R@", "g2")))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "fun (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hhf : HeadFree e) (hb : beta_reduces {redex} g2){conts} => {body}"
    )
}

pub(super) fn ty_apphf_whnf_inv() -> String {
    format!(
        "forall (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type), HeadFree e -> whnf_step (KExpr.app e a) g2 -> {}C",
        app_conts_ty("g2")
    )
}

pub(super) fn val_apphf_whnf_inv() -> String {
    let redex = "(KExpr.app e a)";
    let conts = app_conts()
        .iter()
        .map(|c| format!(" ({} : {})", c.name, c.ty.replace("@R@", "g2")))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "fun (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hhf : HeadFree e) (hs : whnf_step {redex} g2){conts} => @whnf_step.rec {redex} g2 (fun (_ : whnf_step {redex} g2) => C) (fun (hbr : beta_reduces {redex} g2) => appHF_beta_inv e a g2 C hhf hbr kLam kFn kArg) (fun (hdr : delta_reduces {redex} g2) => delta_step_head_none_absurd_type (red_def the_red_env) {redex} g2 C hhf (delta_reduces_to_step {redex} g2 hdr)) hs"
    )
}

/// The shared binder prefix of the three `PiSet` faces.
const PI_BINDERS: &str = "(CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type)";

pub(super) const TY_PISET_CR1: &str = "forall (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type), IsCandHF CA -> (forall (a : KExpr), CA a -> IsCandHF (CB a)) -> candCr1 (PiSet CA CB)";
pub(super) const VAL_PISET_CR1: &str = "fun (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type) (hCA : IsCandHF CA) (hCB : forall (a : KExpr), CA a -> IsCandHF (CB a)) (e : KExpr) (he : PiSet CA CB e) => whnfAcc_app_left e (KExpr.bvar Nat.zero) (isCandHF_cr1 (CB (KExpr.bvar Nat.zero)) (hCB (KExpr.bvar Nat.zero) (candHF_var_mem CA hCA Nat.zero)) (KExpr.app e (KExpr.bvar Nat.zero)) (he (KExpr.bvar Nat.zero) (candHF_var_mem CA hCA Nat.zero)))";

pub(super) const TY_PISET_CR2: &str = "forall (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type), (forall (a : KExpr), CA a -> IsCandHF (CB a)) -> candCr2 (PiSet CA CB)";
pub(super) const VAL_PISET_CR2: &str = "fun (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type) (hCB : forall (a : KExpr), CA a -> IsCandHF (CB a)) (e : KExpr) (e2 : KExpr) (he : PiSet CA CB e) (hs : whnf_step e e2) (a : KExpr) (ha : CA a) => isCandHF_cr2 (CB a) (hCB a ha) (KExpr.app e a) (KExpr.app e2 a) (he a ha) (whnfStep_app_left e e2 a hs)";

pub(super) fn ty_piset_cr3_aux() -> String {
    format!(
        "forall {PI_BINDERS}, IsCandHF CA -> (forall (a : KExpr), CA a -> IsCandHF (CB a)) -> candStepInv CA CB -> forall (e : KExpr), HeadFree e -> Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> PiSet CA CB e2) -> forall (a : KExpr), whnf_acc a -> CA a -> CB a (KExpr.app e a)"
    )
}

pub(super) fn val_piset_cr3_aux() -> String {
    let k_lam = "(fun (zA : KExpr) (zb : KExpr) (zeq : @Eq KExpr e (KExpr.lam zA zb)) => @Empty.rec (fun (_ : Empty) => CB qa0 qw) (@Eq.substType KExpr (fun (qz : KExpr) => Neutral qz) e (KExpr.lam zA zb) zeq hne))";
    let k_fn = "(fun (zy : KExpr) (zst : beta_reduces e zy) (zeq : @Eq KExpr qw (KExpr.app zy qa0)) => @Eq.substType KExpr (fun (qz : KExpr) => CB qa0 qz) (KExpr.app zy qa0) qw (@Eq.symm KExpr qw (KExpr.app zy qa0) zeq) (hred zy (whnf_step.beta e zy zst) qa0 qhca))";
    let k_arg = "(fun (zy : KExpr) (zst : beta_reduces qa0 zy) (zeq : @Eq KExpr qw (KExpr.app e zy)) => @Eq.substType KExpr (fun (qz : KExpr) => CB qa0 qz) (KExpr.app e zy) qw (@Eq.symm KExpr qw (KExpr.app e zy) zeq) (hinv qa0 zy (KExpr.app e zy) qhca (whnf_step.beta qa0 zy zst) (qiha zy (whnf_step.beta qa0 zy zst) (isCandHF_cr2 CA hCA qa0 zy qhca (whnf_step.beta qa0 zy zst)))))";
    let core = format!(
        "isCandHF_cr3 (CB qa0) (hCB qa0 qhca) (KExpr.app e qa0) hhf ConstFreeUnit.triv (fun (qw : KExpr) (qstep : whnf_step (KExpr.app e qa0) qw) => appHF_whnf_inv e qa0 qw (CB qa0 qw) hhf qstep {k_lam} {k_fn} {k_arg})"
    );
    format!(
        "fun {PI_BINDERS} (hCA : IsCandHF CA) (hCB : forall (a : KExpr), CA a -> IsCandHF (CB a)) (hinv : candStepInv CA CB) (e : KExpr) (hhf : HeadFree e) (hne : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> PiSet CA CB e2) (a : KExpr) (hacc : whnf_acc a) => @whnf_acc.rec (fun (qa0 : KExpr) (_ : whnf_acc qa0) => CA qa0 -> CB qa0 (KExpr.app e qa0)) (fun (qa0 : KExpr) (_qhas : forall (qa2 : KExpr), whnf_step qa0 qa2 -> whnf_acc qa2) (qiha : forall (qa2 : KExpr), whnf_step qa0 qa2 -> CA qa2 -> CB qa2 (KExpr.app e qa2)) (qhca : CA qa0) => {core}) a hacc"
    )
}

pub(super) fn ty_piset_cr3() -> String {
    format!(
        "forall {PI_BINDERS}, IsCandHF CA -> (forall (a : KExpr), CA a -> IsCandHF (CB a)) -> candStepInv CA CB -> candCr3HF (PiSet CA CB)"
    )
}

pub(super) fn val_piset_cr3() -> String {
    format!(
        "fun {PI_BINDERS} (hCA : IsCandHF CA) (hCB : forall (a : KExpr), CA a -> IsCandHF (CB a)) (hinv : candStepInv CA CB) (e : KExpr) (hhf : HeadFree e) (hne : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> PiSet CA CB e2) (a : KExpr) (hca : CA a) => piSet_cr3_aux CA CB hCA hCB hinv e hhf hne hred a (isCandHF_cr1 CA hCA a hca) hca"
    )
}

pub(super) fn ty_iscandhf_piset() -> String {
    format!(
        "forall {PI_BINDERS}, IsCandHF CA -> (forall (a : KExpr), CA a -> IsCandHF (CB a)) -> candStepInv CA CB -> IsCandHF (PiSet CA CB)"
    )
}

pub(super) fn val_iscandhf_piset() -> String {
    format!(
        "fun {PI_BINDERS} (hCA : IsCandHF CA) (hCB : forall (a : KExpr), CA a -> IsCandHF (CB a)) (hinv : candStepInv CA CB) => isCandHF_intro (PiSet CA CB) (piSet_cr1 CA CB hCA hCB) (piSet_cr2 CA CB hCB) (piSet_cr3 CA CB hCA hCB hinv)"
    )
}

pub(super) fn ty_piset_app() -> String {
    format!(
        "forall {PI_BINDERS} (t : KExpr), PiSet CA CB t -> forall (a : KExpr), CA a -> CB a (KExpr.app t a)"
    )
}

pub(super) fn val_piset_app() -> String {
    format!("fun {PI_BINDERS} (t : KExpr) (h : PiSet CA CB t) => h")
}

// ================================================================
// Group D — R1's Tait beta engine at the weaker interface, DERIVED by
// textual weakening of R1's own builder (never retyped).
// ================================================================

/// R1's `candExp_beta` uses exactly three candidate faces: `isCandSet_cr1`
/// and `isCandSet_cr2` on the ARGUMENT set, and ONE `isCandSet_cr3` at the
/// redex `app (lam ty0 b0) a0` — whose spine head is `lam ty0 b0`, so
/// `kexpr_const_name (kapp_fn ..)` computes to `none` and the head-free
/// premise is `Eq.refl`. The rewrite is therefore total and sound; the shape
/// guard pins that no `IsCandSet` spelling survives it.
fn hf_weaken(src: &str) -> String {
    src.replace(
        "isCandSet_cr3 S hS (KExpr.app (KExpr.lam ty0 b0) a0) ConstFreeUnit.triv",
        "isCandHF_cr3 S hS (KExpr.app (KExpr.lam ty0 b0) a0) (@Eq.refl (OptionType Name) (@OptionType.none Name)) ConstFreeUnit.triv",
    )
    .replace("isCandSet_cr", "isCandHF_cr")
    .replace("IsCandSet ", "IsCandHF ")
}

pub(super) fn ty_candexphf_beta() -> String {
    hf_weaken(&ty_candexp_beta())
}

pub(super) fn val_candexphf_beta() -> String {
    hf_weaken(&val_candexp_beta())
}

// ================================================================
// Group E — the type interpretation.
// ================================================================

/// The top-candidate clause every non-Pi former takes.
const TOPSET: &str = "(fun (e : KExpr) => whnf_acc e)";

pub(super) fn src_cand_interp() -> String {
    format!(
        "def candInterp (T : KExpr) : KExpr -> Type := @KExpr.rec (fun (_ : KExpr) => KExpr -> Type) \
         (fun (_ : Level) => {TOPSET}) \
         (fun (_ : Nat) => {TOPSET}) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr -> Type) (_ : KExpr -> Type) => {TOPSET}) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr -> Type) (_ : KExpr -> Type) => {TOPSET}) \
         (fun (_ : KExpr) (_ : KExpr) (qihd : KExpr -> Type) (qihc : KExpr -> Type) => PiSet qihd (fun (_ : KExpr) => qihc)) \
         (fun (_ : Name) (_ : ListType Level) => {TOPSET}) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr -> Type) (_ : KExpr -> Type) (_ : KExpr -> Type) => {TOPSET}) \
         (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr -> Type) => {TOPSET}) \
         (fun (_ : Nat) => {TOPSET}) T"
    )
}

pub(super) const TY_CANDINTERP_ISCANDHF: &str = "forall (T : KExpr), IsCandHF (candInterp T)";

pub(super) fn val_candinterp_iscandhf() -> String {
    let top = "isCandHF_whnfAcc";
    let pi_arm = "(fun (qd : KExpr) (qc : KExpr) (qihd : IsCandHF (candInterp qd)) (qihc : IsCandHF (candInterp qc)) => isCandHF_piSet (candInterp qd) (fun (_ : KExpr) => candInterp qc) qihd (fun (qa : KExpr) (_ : candInterp qd qa) => qihc) (fun (qa : KExpr) (qa2 : KExpr) (qw : KExpr) (_ : candInterp qd qa) (_ : whnf_step qa qa2) (qh : candInterp qc qw) => qh))";
    format!(
        "fun (T : KExpr) => @KExpr.rec (fun (qT : KExpr) => IsCandHF (candInterp qT)) \
         (fun (_ : Level) => {top}) \
         (fun (_ : Nat) => {top}) \
         (fun (qf : KExpr) (qa : KExpr) (_ : IsCandHF (candInterp qf)) (_ : IsCandHF (candInterp qa)) => {top}) \
         (fun (qd : KExpr) (qc : KExpr) (_ : IsCandHF (candInterp qd)) (_ : IsCandHF (candInterp qc)) => {top}) \
         {pi_arm} \
         (fun (_ : Name) (_ : ListType Level) => {top}) \
         (fun (qd : KExpr) (qv : KExpr) (qc : KExpr) (_ : IsCandHF (candInterp qd)) (_ : IsCandHF (candInterp qv)) (_ : IsCandHF (candInterp qc)) => {top}) \
         (fun (_ : Name) (_ : Nat) (qs : KExpr) (_ : IsCandHF (candInterp qs)) => {top}) \
         (fun (_ : Nat) => {top}) T"
    )
}

pub(super) const TY_CANDINTERP_CR1: &str =
    "forall (T : KExpr) (e : KExpr), candInterp T e -> whnf_acc e";
pub(super) const VAL_CANDINTERP_CR1: &str = "fun (T : KExpr) (e : KExpr) (h : candInterp T e) => isCandHF_cr1 (candInterp T) (candInterp_isCandHF T) e h";

pub(super) const TY_CANDINTERP_VAR: &str =
    "forall (T : KExpr) (i : Nat), candInterp T (KExpr.bvar i)";
pub(super) const VAL_CANDINTERP_VAR: &str =
    "fun (T : KExpr) (i : Nat) => candHF_var_mem (candInterp T) (candInterp_isCandHF T) i";

pub(super) const TY_CANDINTERP_SORT_MEM: &str =
    "forall (n : Level) (e : KExpr), whnf_acc e -> candInterp (KExpr.sort n) e";
pub(super) const VAL_CANDINTERP_SORT_MEM: &str =
    "fun (n : Level) (e : KExpr) (h : whnf_acc e) => h";

pub(super) const TY_CANDINTERP_APP: &str = "forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), candInterp (KExpr.pi A B) f -> candInterp A a -> candInterp B (KExpr.app f a)";
pub(super) const VAL_CANDINTERP_APP: &str = "fun (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) (hf : candInterp (KExpr.pi A B) f) (ha : candInterp A a) => hf a ha";

pub(super) const TY_CANDINTERP_LAM: &str = "forall (A : KExpr) (B : KExpr) (ty : KExpr) (b : KExpr), whnf_acc ty -> whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (a : KExpr), candInterp A a -> candInterp B (instantiate b2 a)) -> candInterp (KExpr.pi A B) (KExpr.lam ty b)";
pub(super) const VAL_CANDINTERP_LAM: &str = "fun (A : KExpr) (B : KExpr) (ty : KExpr) (b : KExpr) (hty : whnf_acc ty) (hb : whnf_acc b) (hfam : forall (b2 : KExpr), betaStar b b2 -> forall (a : KExpr), candInterp A a -> candInterp B (instantiate b2 a)) (a : KExpr) (ha : candInterp A a) => candExpHF_beta (candInterp B) (candInterp A) (candInterp_isCandHF B) (candInterp_isCandHF A) ty hty b hb hfam a ha";

// ================================================================
// Group F — the shaped fragment judgment, its fundamental theorem and the
// unconditional SN capstone.
// ================================================================

pub(super) const SRC_FRAG_TY: &str = "inductive FragTy : KExpr -> KExpr -> Type\n| sortMem : forall (n : Level) (e : KExpr), whnf_acc e -> FragTy (KExpr.sort n) e\n| var : forall (T : KExpr) (i : Nat), FragTy T (KExpr.bvar i)\n| app : forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), candInterp A a -> FragTy (KExpr.pi A B) f -> FragTy B (KExpr.app f a)\n| lam : forall (A : KExpr) (B : KExpr) (ty : KExpr) (b : KExpr), whnf_acc ty -> whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (a : KExpr), candInterp A a -> FragTy B (instantiate b2 a)) -> FragTy (KExpr.pi A B) (KExpr.lam ty b)";

pub(super) const TY_FRAGTY_INTERP: &str =
    "forall (T : KExpr) (e : KExpr), FragTy T e -> candInterp T e";
pub(super) const VAL_FRAGTY_INTERP: &str = "fun (T : KExpr) (e : KExpr) (h : FragTy T e) => @FragTy.rec (fun (qT : KExpr) (qe : KExpr) (_ : FragTy qT qe) => candInterp qT qe) (fun (_ : Level) (qe : KExpr) (qh : whnf_acc qe) => qh) (fun (qT : KExpr) (qi : Nat) => candInterp_var qT qi) (fun (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (qha : candInterp qA qa) (_qhf : FragTy (KExpr.pi qA qB) qf) (qihf : candInterp (KExpr.pi qA qB) qf) => candInterp_app qA qB qf qa qihf qha) (fun (qA : KExpr) (qB : KExpr) (qty : KExpr) (qb : KExpr) (qhty : whnf_acc qty) (qhb : whnf_acc qb) (_qprem : forall (b2 : KExpr), betaStar qb b2 -> forall (a : KExpr), candInterp qA a -> FragTy qB (instantiate b2 a)) (qih : forall (b2 : KExpr), betaStar qb b2 -> forall (a : KExpr), candInterp qA a -> candInterp qB (instantiate b2 a)) => candInterp_lam qA qB qty qb qhty qhb qih) T e h";

pub(super) const TY_FRAGTY_SN: &str = "forall (T : KExpr) (e : KExpr), FragTy T e -> whnf_acc e";
pub(super) const VAL_FRAGTY_SN: &str =
    "fun (T : KExpr) (e : KExpr) (h : FragTy T e) => candInterp_cr1 T e (fragTy_interp T e h)";

// ================================================================
// Group G — the discriminating witnesses.
// ================================================================

pub(super) fn src_r5_omega_lam() -> String {
    format!("def r5_omegaLam : KExpr := KExpr.lam {V0} {SELF_BODY}")
}

pub(super) const SRC_R5_OMEGA_V: &str =
    "def r5_omegaV : KExpr := KExpr.app r5_omegaLam r5_omegaLam";

/// Inline `KExpr.rec` discriminator into `Type`: the `bvar` constructor maps
/// to `Empty`, every other constructor to `Nat` (the R2 `kexpr_discr` idiom).
fn kexpr_discr_bvar() -> String {
    "(@KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => Nat) (fun (_ : Nat) => Empty) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : ListType Level) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) (fun (_ : Nat) => Nat))".to_string()
}

pub(super) const TY_R5_LAM_NE_BVAR: &str = "forall (A : KExpr) (b : KExpr) (i : Nat) (R : Type), @Eq KExpr (KExpr.lam A b) (KExpr.bvar i) -> R";

pub(super) fn val_r5_lam_ne_bvar() -> String {
    format!(
        "fun (A : KExpr) (b : KExpr) (i : Nat) (R : Type) (h : @Eq KExpr (KExpr.lam A b) (KExpr.bvar i)) => @Empty.rec (fun (_ : Empty) => R) (@Eq.substType KExpr {} (KExpr.lam A b) (KExpr.bvar i) h Nat.zero)",
        kexpr_discr_bvar()
    )
}

pub(super) fn ty_r5_bvarapp_no_beta() -> String {
    format!("forall (g2 : KExpr) (C : Type), beta_reduces {SELF_BODY} g2 -> C")
}

pub(super) fn val_r5_bvarapp_no_beta() -> String {
    let live_beta = format!(
        "r5_lam_ne_bvar qA qb Nat.zero C (app_inj_fst (KExpr.lam qA qb) qarg {V0} {V0} heq)"
    );
    let live_appl = format!(
        "no_whnf_step_bvar Nat.zero qf2 C (whnf_step.beta {V0} qf2 (@Eq.substType KExpr (fun (qz : KExpr) => beta_reduces qz qf2) qf {V0} (app_inj_fst qf qa {V0} {V0} heq) qstep))"
    );
    let live_appr = format!(
        "no_whnf_step_bvar Nat.zero qa2 C (whnf_step.beta {V0} qa2 (@Eq.substType KExpr (fun (qz : KExpr) => beta_reduces qz qa2) qa {V0} (app_inj_snd qf qa {V0} {V0} heq) qstep))"
    );
    let live_iota = format!(
        "iota_step_head_none_absurd_type (red_rec the_red_env) {SELF_BODY} qe2 C (@Eq.refl (OptionType Name) (@OptionType.none Name)) (iota_reduces_to_step {SELF_BODY} qe2 (@Eq.substType KExpr (fun (qz : KExpr) => iota_reduces qz qe2) qe {SELF_BODY} heq qio))"
    );
    let body = beta_inv_body(
        SELF_BODY,
        V0,
        V0,
        &[],
        &live_beta,
        &live_appl,
        &live_appr,
        &live_iota,
    );
    format!("fun (g2 : KExpr) (C : Type) (hb : beta_reduces {SELF_BODY} g2) => {body}")
}

pub(super) const TY_R5_WHNFACC_OMEGALAM: &str = "whnf_acc r5_omegaLam";

pub(super) fn val_r5_whnfacc_omegalam() -> String {
    format!(
        "whnf_acc.intro r5_omegaLam (fun (qe2 : KExpr) (qhs : whnf_step r5_omegaLam qe2) => @whnf_step.rec r5_omegaLam qe2 (fun (_ : whnf_step r5_omegaLam qe2) => whnf_acc qe2) (fun (qhbr : beta_reduces r5_omegaLam qe2) => lamHead_beta_inv {V0} {SELF_BODY} qe2 (whnf_acc qe2) qhbr (fun (qt2 : KExpr) (qst : beta_reduces {V0} qt2) (_qeq : @Eq KExpr qe2 (KExpr.lam qt2 {SELF_BODY})) => no_whnf_step_bvar Nat.zero qt2 (whnf_acc qe2) (whnf_step.beta {V0} qt2 qst)) (fun (qb2 : KExpr) (qsb : beta_reduces {SELF_BODY} qb2) (_qeq : @Eq KExpr qe2 (KExpr.lam {V0} qb2)) => r5_bvarApp_no_beta qb2 (whnf_acc qe2) qsb)) (fun (qhdr : delta_reduces r5_omegaLam qe2) => delta_step_head_none_absurd_type (red_def the_red_env) r5_omegaLam qe2 (whnf_acc qe2) (@Eq.refl (OptionType Name) (@OptionType.none Name)) (delta_reduces_to_step r5_omegaLam qe2 qhdr)) qhs)"
    )
}

pub(super) const TY_R5_OMEGAV_STEP_SELF: &str = "whnf_step r5_omegaV r5_omegaV";

pub(super) fn val_r5_omegav_step_self() -> String {
    format!("whnf_step.beta r5_omegaV r5_omegaV (beta_reduces.beta {V0} {SELF_BODY} r5_omegaLam)")
}

pub(super) const TY_R5_OMEGAV_NOT_WHNFACC: &str = "whnf_acc r5_omegaV -> Empty";
pub(super) const VAL_R5_OMEGAV_NOT_WHNFACC: &str =
    "selfLoop_not_whnfAcc r5_omegaV r5_omegaV_step_self";

pub(super) fn ty_candinterp_pi_not_total() -> String {
    format!("candInterp {PI00} r5_omegaLam -> Empty")
}

pub(super) fn val_candinterp_pi_not_total() -> String {
    format!(
        "fun (h : candInterp {PI00} r5_omegaLam) => r5_omegaV_not_whnfAcc (h r5_omegaLam r5_whnfAcc_omegaLam)"
    )
}

pub(super) fn ty_r5_interp_pi_proper() -> String {
    format!("AndType (whnf_acc r5_omegaLam) (candInterp {PI00} r5_omegaLam -> Empty)")
}

pub(super) fn val_r5_interp_pi_proper() -> String {
    format!(
        "@AndType.intro (whnf_acc r5_omegaLam) (candInterp {PI00} r5_omegaLam -> Empty) r5_whnfAcc_omegaLam candInterp_pi_not_total"
    )
}

pub(super) fn ty_fragty_id() -> String {
    format!("FragTy {PI00} {IDLAM}")
}

pub(super) fn val_fragty_id() -> String {
    format!(
        "FragTy.lam {S0} {S0} {V0} {V0} cand_var_witness cand_var_witness (fun (qb2 : KExpr) (qstar : betaStar {V0} qb2) (qa : KExpr) (qha : candInterp {S0} qa) => FragTy.sortMem Level.zero (instantiate qb2 qa) (betaStar_bvar0_fam (fun (qe : KExpr) => whnf_acc qe) qb2 qstar qa qha))"
    )
}

/// The applied witness: the identity lambda of the fragment applied to a
/// FREE VARIABLE distinct from the one it binds, so the redex is not R1's
/// already-registered `candExp_beta_base_witness` term.
fn redex_witness() -> String {
    format!("(KExpr.app {IDLAM} (KExpr.bvar (Nat.succ Nat.zero)))")
}

pub(super) fn ty_fragty_app_witness() -> String {
    format!("FragTy {S0} {}", redex_witness())
}

pub(super) fn val_fragty_app_witness() -> String {
    format!(
        "FragTy.app {S0} {S0} {IDLAM} (KExpr.bvar (Nat.succ Nat.zero)) (cand_var_mem (fun (qe : KExpr) => whnf_acc qe) isCand_whnfAcc (Nat.succ Nat.zero)) fragTy_id"
    )
}

pub(super) fn ty_fragty_sn_witness() -> String {
    format!("whnf_acc {}", redex_witness())
}

pub(super) fn val_fragty_sn_witness() -> String {
    format!("fragTy_sn {S0} {} fragTy_app_witness", redex_witness())
}

pub(super) fn ty_fragty_not_total() -> String {
    format!("FragTy {PI00} r5_omegaLam -> Empty")
}

pub(super) fn val_fragty_not_total() -> String {
    format!(
        "fun (h : FragTy {PI00} r5_omegaLam) => candInterp_pi_not_total (fragTy_interp {PI00} r5_omegaLam h)"
    )
}

// ---- the head-free premise's necessity guard ----

/// The three-argument `Nat.rec` spine over inert variables: `Neutral`, with
/// NO `whnf_step` at all, and yet `app <it> Nat.zero` iota-fires.
fn e3() -> String {
    sp(&[V0, V0, V0])
}

pub(super) fn ty_r5_natrecv3_delta_none() -> String {
    format!(
        "@Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) {}) (@OptionType.none KExpr)",
        e3()
    )
}

pub(super) const VAL_R5_NATRECV3_DELTA_NONE: &str =
    "@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)";

pub(super) fn ty_r5_natrecv3_no_whnf_step() -> String {
    format!("forall (g2 : KExpr), whnf_step {} g2 -> Empty", e3())
}

pub(super) fn val_r5_natrecv3_no_whnf_step() -> String {
    let redex = e3();
    // The head's iota-deadness below and at arity 3, over the real env: the
    // major-premise slot of a four-argument recursor is absent, so each is
    // one Eq.refl with the argument slots free.
    let dead = |k: usize| {
        let binders = (1..=k)
            .map(|i| format!("(qy{i} : KExpr) "))
            .collect::<Vec<_>>()
            .join("");
        format!("(fun {binders}=> @Eq.refl (OptionType KExpr) (@OptionType.none KExpr))")
    };
    // The argument-slot continuations: every slot holds `bvar 0`, which takes
    // no whnf_step at all.
    let cont = |i: usize| {
        let mut slots: Vec<&str> = vec![V0, V0, V0];
        slots[i] = "qy";
        format!(
            "(fun (qy : KExpr) (qst : beta_reduces {V0} qy) (_qeq : @Eq KExpr g2 {}) => no_whnf_step_bvar Nat.zero qy Empty (whnf_step.beta {V0} qy qst))",
            sp(&slots)
        )
    };
    let delta_arm = format!(
        "(fun (qhdr : delta_reduces {redex} g2) => option_none_ne_some_type KExpr g2 Empty (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (delta_reduct (red_def the_red_env) {redex}) (@OptionType.some KExpr g2) (@Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) {redex}) (@OptionType.none KExpr) r5_natRecV3_delta_none) (delta_reduces_to_step {redex} g2 qhdr)))"
    );
    let beta_arm = format!(
        "(fun (qhbr : beta_reduces {redex} g2) => constSpine3_beta_inv fixture_nat_rec_name kcre_witness_rec_levels {d1} {d2} {d3} {V0} {V0} {V0} g2 Empty qhbr {k1} {k2} {k3})",
        d1 = dead(1),
        d2 = dead(2),
        d3 = dead(3),
        k1 = cont(0),
        k2 = cont(1),
        k3 = cont(2),
    );
    format!(
        "fun (g2 : KExpr) (qhs : whnf_step {redex} g2) => @whnf_step.rec {redex} g2 (fun (_ : whnf_step {redex} g2) => Empty) {beta_arm} {delta_arm} qhs"
    )
}

pub(super) fn ty_piset_cr3_headfree_necessary() -> String {
    let redex = e3();
    format!(
        "AndType (Neutral {redex}) (AndType (HeadFree {redex} -> Empty) (AndType (forall (g2 : KExpr), whnf_step {redex} g2 -> Empty) (iota_reduces (KExpr.app {redex} {NZERO}) {})))",
        zcontract(V0, V0, V0)
    )
}

pub(super) fn val_piset_cr3_headfree_necessary() -> String {
    let redex = e3();
    let zc = zcontract(V0, V0, V0);
    let no_step = format!("(forall (g2 : KExpr), whnf_step {redex} g2 -> Empty)");
    let fires_ty = format!("(iota_reduces (KExpr.app {redex} {NZERO}) {zc})");
    let hf_absurd = format!(
        "(fun (h : HeadFree {redex}) => option_none_ne_some_type Name fixture_nat_rec_name Empty (@Eq.symm (OptionType Name) (@OptionType.some Name fixture_nat_rec_name) (@OptionType.none Name) h))"
    );
    let fires = format!(
        "(iota_step_to_reduces (KExpr.app {redex} {NZERO}) {zc} (natRecZ_iota_fires {V0} {V0} {V0}))"
    );
    format!(
        "@AndType.intro (Neutral {redex}) (AndType (HeadFree {redex} -> Empty) (AndType {no_step} {fires_ty})) ConstFreeUnit.triv (@AndType.intro (HeadFree {redex} -> Empty) (AndType {no_step} {fires_ty}) {hf_absurd} (@AndType.intro {no_step} {fires_ty} r5_natRecV3_no_whnf_step {fires}))"
    )
}

// ================================================================
// Group H — the premise-satisfiability witnesses: PiSet and candStepInv
// are ASSUMED all over this rung and were concluded by nothing.
// ================================================================

/// `PiSet` is inhabited, at the interpretation of `pi (sort 0) (sort 0)` and
/// at the fragment's identity lambda — an actual FUNCTION, not just a
/// variable. `candInterp (pi A B)` REDUCES to `PiSet (candInterp A) (fun _ =>
/// candInterp B)`, so `fragTy_interp` at `fragTy_id` lands in the Pi-candidate
/// definitionally and the witness needs no new proof.
pub(super) fn ty_piset_id_witness() -> String {
    format!("PiSet {INTERP_S0} (fun (_ : KExpr) => {INTERP_S0}) {IDLAM}")
}

pub(super) fn val_piset_id_witness() -> String {
    format!("fragTy_interp {PI00} {IDLAM} fragTy_id")
}

/// The corpus `hinv` side condition holds for every CONSTANT codomain family:
/// `CB a2 w` and `CB a w` are the same type, so the transport is the identity.
/// This is the term `candInterp_isCandHF`'s pi arm supplies inline; naming it
/// is what makes `candStepInv` a satisfiable premise rather than an assumed
/// one.
pub(super) const TY_CAND_STEP_INV_CONST: &str =
    "forall (CA : KExpr -> Type) (CB : KExpr -> Type), candStepInv CA (fun (_ : KExpr) => CB)";

pub(super) const VAL_CAND_STEP_INV_CONST: &str = "fun (CA : KExpr -> Type) (CB : KExpr -> Type) (a : KExpr) (a2 : KExpr) (w : KExpr) (_hca : CA a) (_hstep : whnf_step a a2) (h : CB w) => h";

/// The CLOSED instance of the side condition, at the same families the
/// Pi-candidate witness above is stated over.
pub(super) fn ty_cand_step_inv_interp() -> String {
    format!("candStepInv {INTERP_S0} (fun (_ : KExpr) => {INTERP_S0})")
}

pub(super) fn val_cand_step_inv_interp() -> String {
    format!("candStepInv_const {INTERP_S0} {INTERP_S0}")
}

// ==== R5 SOURCES END ====

/// Register one value-bearing theorem. A free function rather than a closure
/// over `&mut self`, because this stage interleaves `add_definition` with
/// `add_recursive_def` / `add_inductive` calls and a capturing closure would
/// hold the unique borrow across them.
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Register the R5 Pi-candidate, the type interpretation built from it,
    /// the shaped fragment judgment, its fundamental theorem, the
    /// unconditional SN capstone and the discriminating witnesses.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r0..r4` (the
    /// candidate interface, the beta engine, `betaStar`, the 15-arm scaffold
    /// consumers, `constSpine3_beta_inv`, `natRecZ_iota_fires`),
    /// `add_dependent_sn_richmodel` (`Neutral`, `no_whnf_step_bvar`),
    /// `add_whnf_reduction`, `add_iota_step` (`apply_spine`, `kapp_args`,
    /// `kexpr_const_name`, `opt_bind`), `add_delta_step_core`
    /// (`delta_reduct`, `defval_for`) and the iota/delta bridges.
    ///
    /// Port of `Stratified/Cand.lean` `PiSet`/`isCand_piSet` plus the
    /// `CCUShape`/`CCUSN` interpretation-and-capstone architecture per
    /// `designs/2026-08-23-spec-candmodel-port.md` §5 R5/R6; see the module
    /// docs for the head-free restriction, its registered necessity guard,
    /// and the non-dependent scope limit of the interpretation.
    pub(super) fn add_candmodel_construct_r5(&mut self) -> Result<(), SpecError> {
        // --- Group A: application congruence ---
        add_thm(
            self,
            "r5_spine_snoc",
            TY_R5_SPINE_SNOC.to_string(),
            VAL_R5_SPINE_SNOC.to_string(),
            &["apply_spine", "list_append", "ListType.rec"],
            "apply_spine (xs ++ [a]) h = app (apply_spine xs h) a — the snoc identity of the \
             left-nested application spine, by ListType.rec with the head generalized. This is \
             the ONE arithmetic fact the generic applied-delta transport needs, and it is why \
             R3's bare-const delta_app_lift generalizes to an arbitrary spine head. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "deltaReduct_app_gen",
            TY_DELTAREDUCT_APP_GEN.to_string(),
            val_deltareduct_app_gen(),
            &[
                "delta_reduct",
                "opt_bind",
                "OptionType.rec",
                "r5_spine_snoc",
                "Eq.cong",
            ],
            "THE GENERIC APPLIED-DELTA REDUCT: delta_reduct env (app e a) = opt_bind \
             (delta_reduct env e) (fun x => some (app x a)), for EVERY e. delta_reduct looks the \
             definition name up at kapp_fn (the spine head) and re-applies kapp_args, and both \
             REDUCE through the application (kapp_fn (app e a) = kapp_fn e; kapp_args (app e a) \
             = kapp_args e ++ [a]), so the whole identity is two nested OptionType.rec splits \
             (head name, then value) whose only non-refl leaf is one Eq.cong along \
             r5_spine_snoc. Generalizes R3's delta_app_lift off the BARE-CONST head, which is \
             what whnfStep_app_left and piSet_cr2 need. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "deltaStep_app_gen",
            TY_DELTASTEP_APP_GEN.to_string(),
            val_deltastep_app_gen(),
            &["deltaReduct_app_gen", "delta_step", "Eq.trans", "Eq.cong"],
            "A delta step lifts under ANY application: delta_step env e v gives delta_step env \
             (app e a) (app v a). One Eq.trans of deltaReduct_app_gen with the congruence of \
             opt_bind along the hypothesis. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "whnfStep_app_left",
            TY_WHNFSTEP_APP_LEFT.to_string(),
            VAL_WHNFSTEP_APP_LEFT.to_string(),
            &[
                "whnf_step.rec",
                "beta_reduces.app_left",
                "deltaStep_app_gen",
                "delta_step_to_reduces",
                "delta_reduces_to_step",
            ],
            "THE FULL one-step app-left congruence of the spec's env-fixed whnf_step: the beta \
             leg is the beta_reduces.app_left constructor, and the DELTA leg — which \
             beta_reduces does not carry, and which no landed lemma covered at a generic head — \
             goes through deltaStep_app_gen. Consumed by whnfAcc_app_left and by the Pi-set's \
             cr2. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "whnfAcc_app_left",
            TY_WHNFACC_APP_LEFT.to_string(),
            VAL_WHNFACC_APP_LEFT.to_string(),
            &["whnf_acc.rec", "whnfStep_app_left", "Eq.substType"],
            "SN of an application gives SN of its function: whnf_acc (app f a) -> whnf_acc f. \
             The corpus sn_app_left (Stratified/SN.lean), by Acc induction with the redex \
             generalized through an equation, mapping each step of f into a step of app f a with \
             whnfStep_app_left. This is what makes the Pi-candidate's cr1 face true: PiSet \
             members are SN because their application to bvar 0 is. Zero axiom_deps.",
        )?;

        // --- Group B: the head-free candidate interface ---
        self.add_recursive_def(
            SRC_HEAD_FREE,
            "HeadFree e — the spine head of e is not a constant: kexpr_const_name (kapp_fn e) = \
             none. Prop-valued (it is an Eq). The exact side condition under which BOTH \
             computational legs of the spec's step relation die at e and at every application of \
             e: iota_reduct and delta_reduct each begin with that lookup, and kapp_fn (app e a) \
             REDUCES to kapp_fn e, so head-freeness passes through application definitionally \
             (headFree_app is the identity function). Reducible plain def.",
        )?;
        self.add_recursive_def(
            SRC_CAND_CR3HF,
            "candCr3HF S — the HEAD-FREE cr3 face: a Neutral term whose spine head is not a \
             constant and all of whose one-step reducts are in S is in S. The corpus IsCand.cr3 \
             restricted by exactly the premise that makes the Pi-candidate's cr3 provable in a \
             calculus whose eliminators are const-headed SPINES rather than saturated \
             constructors. See piSet_cr3_headFree_necessary for the machine-checked witness that \
             the restriction is not a convenience. Type-valued plain def.",
        )?;
        self.add_recursive_def(
            SRC_IS_CAND_HF,
            "IsCandHF S — the head-free candidate-set interface: AndType (candCr1 S) (AndType \
             (candCr2 S) (candCr3HF S)). Strictly weaker than R0's IsCandSet (isCandSet_weaken is \
             the projection), and strictly weaker than CandModel: no red_sort, no pi_elim/\
             pi_intro at untyped T, no redRec*, no redTypeStep. Inhabiting it makes NO claim on \
             the M hypothesis of whnf_terminates_well_typed_dependent. Reducible plain def.",
        )?;
        add_thm(
            self,
            "isCandHF_intro",
            TY_ISCANDHF_INTRO.to_string(),
            VAL_ISCANDHF_INTRO.to_string(),
            &["IsCandHF", "AndType.intro"],
            "Constructor of the head-free candidate interface from its three faces. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "isCandHF_cr1",
            TY_ISCANDHF_CR1.to_string(),
            VAL_ISCANDHF_CR1.to_string(),
            &["IsCandHF", "AndType.left"],
            "cr1 projection: every member of a head-free candidate set is strongly normalizing \
             for the spec's full env-fixed whnf_step. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "isCandHF_cr2",
            TY_ISCANDHF_CR2.to_string(),
            VAL_ISCANDHF_CR2.to_string(),
            &["IsCandHF", "AndType.left", "AndType.right"],
            "cr2 projection: a head-free candidate set is closed under one whnf_step. \
             UNRESTRICTED — the head-free premise touches cr3 only. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "isCandHF_cr3",
            TY_ISCANDHF_CR3.to_string(),
            VAL_ISCANDHF_CR3.to_string(),
            &["IsCandHF", "AndType.right"],
            "cr3 projection at a head-free Neutral. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "headFree_app",
            TY_HEADFREE_APP.to_string(),
            VAL_HEADFREE_APP.to_string(),
            &["HeadFree", "kapp_fn"],
            "Head-freeness passes through application, and it is the IDENTITY FUNCTION: kapp_fn \
             is structural on the app field, so kapp_fn (app e a) REDUCES to kapp_fn e and \
             HeadFree (app e a) is the very same proposition as HeadFree e. That definitional \
             identity is what lets the Pi-candidate's cr3 kill both the iota and the delta legs \
             of app e a from a hypothesis about e alone. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "isCandSet_weaken",
            TY_ISCANDSET_WEAKEN.to_string(),
            VAL_ISCANDSET_WEAKEN.to_string(),
            &["IsCandSet", "IsCandHF", "isCandHF_intro", "isCandSet_cr3"],
            "Every R0 candidate set is a head-free candidate set: cr1/cr2 transfer verbatim and \
             cr3 simply drops its extra premise. The direction is one-way by construction — \
             piSet_cr3_headFree_necessary records why the converse is not an R5 theorem for the \
             Pi-set. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "isCandHF_whnfAcc",
            TY_ISCANDHF_WHNFACC.to_string(),
            VAL_ISCANDHF_WHNFACC.to_string(),
            &["isCandSet_weaken", "isCand_whnfAcc"],
            "The whole-SN set is a head-free candidate set — the interpretation's clause for \
             sorts and for every non-Pi former, and hence the definitional content of red_sort. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candHF_var_mem",
            TY_CANDHF_VAR_MEM.to_string(),
            VAL_CANDHF_VAR_MEM.to_string(),
            &["isCandHF_cr3", "no_whnf_step_bvar", "ConstFreeUnit"],
            "Every variable inhabits every head-free candidate set (corpus IsCand.var_mem). A \
             bvar is Neutral, is head-free by Eq.refl (kapp_fn (bvar i) = bvar i, whose \
             kexpr_const_name is none) and takes no whnf_step, so cr3 applies with an empty \
             reduct obligation. Zero axiom_deps.",
        )?;

        // --- Group C: the Pi-candidate ---
        self.add_recursive_def(
            SRC_PI_SET,
            "PiSet CA CB — the dependent-Pi candidate over reflected KExpr (corpus PiSet, \
             Stratified/Cand.lean:89): t is reducible at the function space when applying it to \
             any CA-member a lands in the TERM-INDEXED family CB a. The term index is kept (the \
             corpus's own formulation) even though the interpretation instantiates it at a \
             constant family, so a later dependent clause needs no restatement. Reducible plain \
             def.",
        )?;
        self.add_recursive_def(
            SRC_CAND_STEP_INV,
            "candStepInv CA CB — the corpus's hinv step-invariance side condition (isCand_piSet, \
             Stratified/Cand.lean:164) in the exact direction the cr3 proof consumes it: when the \
             argument steps a -> a2, membership in the codomain family at a2 transfers back to a. \
             Design note §6.6 says explicitly not to simplify this away, so it is CARRIED as a \
             premise of piSet_cr3/isCandHF_piSet rather than hidden; for a constant codomain \
             family (which is what the non-dependent interpretation supplies) it is the identity \
             function. Type-valued plain def.",
        )?;
        add_thm(
            self,
            "appHF_beta_inv",
            ty_apphf_beta_inv(),
            val_apphf_beta_inv(),
            &[
                "beta_reduces.rec",
                "app_inj_fst",
                "app_inj_snd",
                "iota_step_head_none_absurd_type",
                "lam_ne_app",
            ],
            "Complete beta_reduces reduct classification of app e a at a HEAD-FREE e, in CPS: \
             the top-beta arm reports e = lam (which the caller refutes from Neutral e), the two \
             congruence arms report a step of e or of a, and the spine's own iota arm is killed \
             from the head-free hypothesis rather than by computing the real env — which is what \
             makes the inversion generic in e. 15-arm beta_reduces.rec on R3's shared scaffold, \
             every recursive structural minor binding its beta_reduces premise before its IH. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "appHF_whnf_inv",
            ty_apphf_whnf_inv(),
            val_apphf_whnf_inv(),
            &[
                "appHF_beta_inv",
                "whnf_step.rec",
                "delta_step_head_none_absurd_type",
                "delta_reduces_to_step",
            ],
            "The whnf_step classification of app e a at a head-free e: appHF_beta_inv's three \
             continuations, with the DELTA leg killed from the same head-free hypothesis \
             (delta_reduct also begins at kexpr_const_name (kapp_fn ..)). This is the complete \
             reduct set the Pi-candidate's cr3 must survive. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_cr1",
            TY_PISET_CR1.to_string(),
            VAL_PISET_CR1.to_string(),
            &[
                "PiSet",
                "whnfAcc_app_left",
                "candHF_var_mem",
                "isCandHF_cr1",
            ],
            "cr1 of the Pi-candidate, UNRESTRICTED: apply the member to bvar 0 (which inhabits \
             CA by candHF_var_mem), take cr1 of the codomain candidate there, and project the \
             function out with whnfAcc_app_left. Corpus isCand_piSet.cr1. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_cr2",
            TY_PISET_CR2.to_string(),
            VAL_PISET_CR2.to_string(),
            &["PiSet", "whnfStep_app_left", "isCandHF_cr2"],
            "cr2 of the Pi-candidate, UNRESTRICTED: a step of the function lifts to a step of \
             the application (whnfStep_app_left — beta AND delta legs), and the codomain \
             candidate's cr2 absorbs it. Corpus isCand_piSet.cr2. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_cr3_aux",
            ty_piset_cr3_aux(),
            val_piset_cr3_aux(),
            &[
                "PiSet",
                "appHF_whnf_inv",
                "isCandHF_cr3",
                "candStepInv",
                "whnf_acc.rec",
                "Empty.rec",
            ],
            "The inner Acc induction of the Pi-candidate's cr3 (corpus piSet_cr3_aux, \
             Stratified/Cand.lean:96): by induction on SN of the argument, apply the codomain \
             candidate's cr3 at the Neutral application app e a — head-free because e is — and \
             classify its reducts with appHF_whnf_inv. The top-beta case contradicts Neutral e \
             through Empty.rec (the spec's Neutral sends lam to Empty, and the goal is \
             Type-valued so no Prop/Type detour is needed); the function-step case consumes the \
             cr3 hypothesis at the reduct; the argument-step case consumes the IH and transports \
             back along candStepInv. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_cr3",
            ty_piset_cr3(),
            val_piset_cr3(),
            &["piSet_cr3_aux", "isCandHF_cr1"],
            "cr3 of the Pi-candidate AT THE HEAD-FREE FACE: the aux with SN of the argument \
             supplied by cr1 of the domain candidate. The head-free premise is not decorative — \
             piSet_cr3_headFree_necessary exhibits a Neutral, NON-head-free e over the REAL \
             reflected env that takes no whnf_step at all (so the cr3 hypothesis is satisfied \
             vacuously) and yet whose application to Nat.zero iota-fires, leaving the codomain \
             obligation with no derivation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "isCandHF_piSet",
            ty_iscandhf_piset(),
            val_iscandhf_piset(),
            &["isCandHF_intro", "piSet_cr1", "piSet_cr2", "piSet_cr3"],
            "THE Pi-CANDIDATE (corpus isCand_piSet, Stratified/Cand.lean:112): given a head-free \
             candidate domain, a head-free candidate codomain family over its members, and the \
             hinv side condition, the function space PiSet CA CB is itself a head-free candidate \
             set. This is the construction R3 and R4 both named as the blocker for unconditional \
             membership at a real iota redex (design rows 6/7). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_app",
            ty_piset_app(),
            val_piset_app(),
            &["PiSet"],
            "pi_elim for the Pi-candidate: a member applied to a domain member lands in the \
             codomain family. Definitional (PiSet is that implication), registered so consumers \
             name the law rather than unfold the def. Zero axiom_deps.",
        )?;

        // --- Group D: the beta engine at the weaker interface ---
        add_thm(
            self,
            "candExpHF_beta",
            ty_candexphf_beta(),
            val_candexphf_beta(),
            &[
                "IsCandHF",
                "isCandHF_cr3",
                "isCandHF_cr2",
                "isCandHF_cr1",
                "betaRedex_whnf_inv",
                "betaStar",
                "whnf_acc.rec",
            ],
            "R1's Tait head-expansion engine candExp_beta AT THE HEAD-FREE INTERFACE, derived by \
             textual weakening of R1's own builder rather than retyped: the engine uses cr1 and \
             cr2 on the argument set and exactly ONE cr3, at the redex app (lam ty0 b0) a0, whose \
             spine head is a lam and is therefore head-free by Eq.refl. Needed because the \
             interpretation's Pi clause is only an IsCandHF, never an IsCandSet — the R5 \
             obstruction — so R1's engine could not be applied to it as stated. Carries NO \
             closedness premise (that is why the capstone is unconditional; R2's corpus-spelling \
             candExp_beta_subst would have imported RecEnvClosed). Zero axiom_deps.",
        )?;

        // --- Group E: the interpretation ---
        self.add_recursive_def(
            &src_cand_interp(),
            "candInterp T — the type interpretation over reflected KExpr, by KExpr.rec: every \
             former except pi goes to the TOP candidate whnf_acc (so red_sort holds \
             definitionally and junk types are interpreted, not excluded), and pi A B goes to \
             PiSet (candInterp A) (fun _ => candInterp B). SCOPE, stated honestly: the codomain \
             family IGNORES the argument, so this is the SIMPLE-type reading of pi — a genuinely \
             dependent clause would need candInterp (instantiate B a), which is not structural in \
             KExpr and is exactly the corpus's shape/denotation split (Shapes.lean cval). What it \
             buys in exchange is candidate-hood at EVERY untyped T with no shape discipline, \
             which the corpus's isCand_cval does not have (it needs CWK). Non-degenerate: \
             r5_interp_pi_proper. Reducible plain def.",
        )?;
        add_thm(
            self,
            "candInterp_isCandHF",
            TY_CANDINTERP_ISCANDHF.to_string(),
            val_candinterp_iscandhf(),
            &[
                "candInterp",
                "KExpr.rec",
                "isCandHF_piSet",
                "isCandHF_whnfAcc",
            ],
            "EVERY type's interpretation is a head-free candidate set, by KExpr.rec over the \
             type: eight formers are isCandHF_whnfAcc and the pi former is isCandHF_piSet at the \
             two recursive results, whose hinv side condition is discharged by the identity \
             because the codomain family is constant. No typing or shape hypothesis anywhere — \
             the corpus analogue isCand_cval needs a CWK derivation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_cr1",
            TY_CANDINTERP_CR1.to_string(),
            VAL_CANDINTERP_CR1.to_string(),
            &["candInterp_isCandHF", "isCandHF_cr1"],
            "THE SN PROJECTION: membership in any type's interpretation implies strong \
             normalization for the spec's full env-fixed whnf_step. The capstone's second half. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_var",
            TY_CANDINTERP_VAR.to_string(),
            VAL_CANDINTERP_VAR.to_string(),
            &["candInterp_isCandHF", "candHF_var_mem"],
            "Every variable inhabits every type's interpretation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_sort_mem",
            TY_CANDINTERP_SORT_MEM.to_string(),
            VAL_CANDINTERP_SORT_MEM.to_string(),
            &["candInterp"],
            "red_sort for the interpretation: the interpretation of a sort IS the whole-SN set, \
             definitionally, at every Level. Levels are semantically inert here exactly as in the \
             corpus shape model (CCUShape.lean:182 discards the level), which is what makes the \
             spec's imax-concluding pi rule harmless to this construction. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_app",
            TY_CANDINTERP_APP.to_string(),
            VAL_CANDINTERP_APP.to_string(),
            &["candInterp", "PiSet"],
            "pi_elim at the interpretation: an inhabitant of pi A B applied to an inhabitant of \
             A inhabits B. Definitional through PiSet. Note this is EXACT for the non-dependent \
             clause and is the law that the degenerate top-everywhere model refutes (design \
             §0.4), which is what r5_interp_pi_proper witnesses. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_lam",
            TY_CANDINTERP_LAM.to_string(),
            VAL_CANDINTERP_LAM.to_string(),
            &["candExpHF_beta", "candInterp_isCandHF", "betaStar"],
            "pi_intro at the interpretation: a lambda whose body lands in the codomain \
             interpretation for every domain member (and every betaStar-development of the body) \
             inhabits the function type. This is where the Tait head-expansion engine does the \
             real work — SN of a beta redex is NOT SN of its parts, as R1's appOmega witness \
             shows. Takes R1's development-family premise, not R2's single-contractum spelling, \
             so that no RecEnvClosed hypothesis is carried into the capstone. Zero axiom_deps.",
        )?;

        // --- Group F: the fragment judgment and the capstone ---
        self.add_inductive(
            SRC_FRAG_TY,
            "FragTy T e — the shaped fragment judgment: e is fragment-typed at T. Four rules — \
             sortMem (any SN term at any sort), var (any variable at any type), app (pi-elim, \
             with the ARGUMENT required only to inhabit the interpretation) and lam (pi-intro, \
             with the body's instances required to be fragment-typed). SCOPE, stated honestly: \
             this is a SEMANTIC-PREMISE judgment — its app and lam rules mention candInterp — not \
             a syntactic typing derivation; a syntactic one needs contexts and parallel \
             substitution, which is R6's work. The lam premise is strictly positive (the \
             recursive occurrence is the conclusion of the premise type), and it is the last \
             field of its constructor, so the recursor's minor-premise binder order is the same \
             under either convention. sortMem leads with a Level and concludes at the \
             non-variable index KExpr.sort n, so no uniform leading ctor-argument prefix exists \
             and the measured recursor-parameter promotion cannot fire. ZERO new axioms.",
        )?;
        add_thm(
            self,
            "fragTy_interp",
            TY_FRAGTY_INTERP.to_string(),
            VAL_FRAGTY_INTERP.to_string(),
            &[
                "FragTy.rec",
                "candInterp_var",
                "candInterp_app",
                "candInterp_lam",
            ],
            "THE FUNDAMENTAL THEOREM for the fragment: every fragment-typed term inhabits the \
             interpretation of its type. One FragTy.rec with a full three-binder motive; the four \
             arms are candInterp_sort_mem (definitionally the identity), candInterp_var, \
             candInterp_app and candInterp_lam. Corpus analogue: ccu_sound (StratifiedU/CCU.lean). \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "fragTy_sn",
            TY_FRAGTY_SN.to_string(),
            VAL_FRAGTY_SN.to_string(),
            &["fragTy_interp", "candInterp_cr1"],
            "THE R5 CAPSTONE — UNCONDITIONAL strong normalization for the shaped fragment: \
             FragTy T e implies whnf_acc e, for the spec's FULL env-fixed one-step reduction \
             (beta, zeta, iota at red_rec the_red_env with full congruence, and delta at red_def \
             the_red_env). NO carried premise of any kind: no CandModel, no RecEnvClosed, no \
             DefEnvClosed, no acyclicity. Corpus analogue: sn_ccu (StratifiedU/CCUSN.lean). \
             HONESTY: this is SN for FragTy, NOT for TypingCtx — it neither discharges nor \
             advances the M : CandModel tenv hypothesis of \
             whnf_terminates_well_typed_dependent, and must never be described as doing so \
             (design §6.2). Zero axiom_deps.",
        )?;

        // --- Group G: the discriminating witnesses ---
        self.add_recursive_def(
            &src_r5_omega_lam(),
            "r5_omegaLam — the self-application lambda with an INERT annotation: lam (bvar 0) \
             (app (bvar 0) (bvar 0)). R0's selfApp annotates with sort 0; this one annotates with \
             a variable so that the lam_ty leg of its own SN proof closes by no_whnf_step_bvar \
             instead of needing a sort step-inversion. Reducible plain def.",
        )?;
        self.add_recursive_def(
            SRC_R5_OMEGA_V,
            "r5_omegaV — the self-application loop app r5_omegaLam r5_omegaLam, whose beta \
             contractum computes back to itself. Reducible plain def.",
        )?;
        add_thm(
            self,
            "r5_lam_ne_bvar",
            TY_R5_LAM_NE_BVAR.to_string(),
            val_r5_lam_ne_bvar(),
            &["KExpr.rec", "Eq.substType", "Empty.rec"],
            "lam and bvar are distinct constructors, into any Type: the R2 kexpr_discr idiom \
             (bvar to Empty, every other former to Nat) transported along the false equation. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_bvarApp_no_beta",
            ty_r5_bvarapp_no_beta(),
            val_r5_bvarapp_no_beta(),
            &[
                "beta_reduces.rec",
                "no_whnf_step_bvar",
                "r5_lam_ne_bvar",
                "app_inj_fst",
                "app_inj_snd",
            ],
            "app (bvar 0) (bvar 0) takes NO beta_reduces step: the top-beta arm needs the head to \
             be a lam (r5_lam_ne_bvar), the two congruence arms need a step of a bvar \
             (no_whnf_step_bvar), and the iota arm dies computationally because the spine head is \
             a bvar. 15-arm beta_reduces.rec on R3's scaffold with NO live continuation. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_whnfAcc_omegaLam",
            TY_R5_WHNFACC_OMEGALAM.to_string(),
            val_r5_whnfacc_omegalam(),
            &[
                "whnf_acc.intro",
                "lamHead_beta_inv",
                "r5_bvarApp_no_beta",
                "delta_step_head_none_absurd_type",
            ],
            "r5_omegaLam IS strongly normalizing — it takes no whnf_step at all. The load-bearing \
             half of the non-degeneracy witness: the term the Pi-interpretation excludes is one \
             the TOP candidate contains, so the exclusion is genuine content and not an artifact \
             of non-termination. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_omegaV_step_self",
            TY_R5_OMEGAV_STEP_SELF.to_string(),
            val_r5_omegav_step_self(),
            &["whnf_step.beta", "beta_reduces.beta"],
            "r5_omegaV beta-steps to ITSELF: the contractum instantiate (app (bvar 0) (bvar 0)) \
             r5_omegaLam computes back to app r5_omegaLam r5_omegaLam. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_omegaV_not_whnfAcc",
            TY_R5_OMEGAV_NOT_WHNFACC.to_string(),
            VAL_R5_OMEGAV_NOT_WHNFACC.to_string(),
            &["selfLoop_not_whnfAcc", "r5_omegaV_step_self"],
            "r5_omegaV is NOT strongly normalizing, via R1's generic one-step self-loop \
             refutation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_pi_not_total",
            ty_candinterp_pi_not_total(),
            val_candinterp_pi_not_total(),
            &["candInterp", "r5_whnfAcc_omegaLam", "r5_omegaV_not_whnfAcc"],
            "THE NON-DEGENERACY WITNESS (design §6.1; the micro_has_type trap): r5_omegaLam does \
             NOT inhabit candInterp (pi (sort 0) (sort 0)). Instantiating the Pi-membership at \
             the domain member r5_omegaLam — which IS in the domain interpretation, since that is \
             the whole-SN set and r5_whnfAcc_omegaLam holds — would produce SN of the \
             self-application loop. So the interpretation is not the total predicate, and \
             specifically not the top-everywhere degenerate model that design §0.4 shows refutes \
             pi_elim. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_interp_pi_proper",
            ty_r5_interp_pi_proper(),
            val_r5_interp_pi_proper(),
            &[
                "r5_whnfAcc_omegaLam",
                "candInterp_pi_not_total",
                "AndType.intro",
            ],
            "The two halves together: r5_omegaLam is SN AND is not in the Pi-interpretation — so \
             candInterp (pi (sort 0) (sort 0)) is a PROPER subset of the top candidate, not equal \
             to it. This is the discrimination no automated gate performs (the axiom census \
             counts axioms; an interpretation is value-full and census-invisible). Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "fragTy_id",
            ty_fragty_id(),
            val_fragty_id(),
            &[
                "FragTy.lam",
                "FragTy.sortMem",
                "betaStar_bvar0_fam",
                "cand_var_witness",
            ],
            "The fragment's identity function: lam (bvar 0) (bvar 0) is fragment-typed at pi \
             (sort 0) (sort 0). The lam rule's development family is discharged with R1's \
             betaStar_bvar0_fam — every betaStar-development of bvar 0 is bvar 0, and \
             instantiate (bvar 0) a is a. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "fragTy_app_witness",
            ty_fragty_app_witness(),
            val_fragty_app_witness(),
            &["FragTy.app", "fragTy_id", "cand_var_mem"],
            "A genuine BETA REDEX in the fragment: app (lam (bvar 0) (bvar 0)) (bvar 1) is \
             fragment-typed at sort 0, by the pi-elim rule at the identity function and a free \
             variable distinct from the bound one. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "fragTy_sn_witness",
            ty_fragty_sn_witness(),
            val_fragty_sn_witness(),
            &["fragTy_sn", "fragTy_app_witness"],
            "THE POSITIVE WITNESS, obtained THROUGH the capstone: whnf_acc of a beta redex, \
             derived as fragTy_sn applied to fragTy_app_witness — i.e. through FragTy.lam, the \
             fundamental theorem, the Tait engine candExpHF_beta inside candInterp_lam, and the \
             cr1 projection. Not by a direct whnf_acc.intro, and not R1's already-registered \
             candExp_beta_base_witness term (the argument is a different variable). Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "fragTy_not_total",
            ty_fragty_not_total(),
            val_fragty_not_total(),
            &["fragTy_interp", "candInterp_pi_not_total"],
            "The JUDGMENT is not total either: r5_omegaLam — a strongly normalizing term — is \
             NOT fragment-typed at pi (sort 0) (sort 0), because the fundamental theorem would \
             put it in the interpretation that candInterp_pi_not_total excludes. So neither the \
             interpretation nor the judgment is a disguised restatement of whnf_acc. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_natRecV3_delta_none",
            ty_r5_natrecv3_delta_none(),
            VAL_R5_NATRECV3_DELTA_NONE.to_string(),
            &["delta_reduct", "the_red_env"],
            "The three-argument Nat.rec spine is delta-DEAD over the REAL reflected env, by \
             Eq.refl: fixture_nat_rec_name has no defval_for entry. The arity-3 analogue of R3's \
             natRecSpine4_delta_none. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r5_natRecV3_no_whnf_step",
            ty_r5_natrecv3_no_whnf_step(),
            val_r5_natrecv3_no_whnf_step(),
            &[
                "constSpine3_beta_inv",
                "no_whnf_step_bvar",
                "r5_natRecV3_delta_none",
                "option_none_ne_some_type",
            ],
            "Nat.rec (bvar 0) (bvar 0) (bvar 0) takes NO whnf_step at all over the real reflected \
             env: every argument slot is an irreducible variable (R4's constSpine3_beta_inv with \
             its three continuations closed by no_whnf_step_bvar), the head is iota-dead below \
             and at arity 3 (Eq.refl, the major-premise slot of a four-argument recursor being \
             absent) and delta-dead (r5_natRecV3_delta_none). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_cr3_headFree_necessary",
            ty_piset_cr3_headfree_necessary(),
            val_piset_cr3_headfree_necessary(),
            &[
                "HeadFree",
                "Neutral",
                "r5_natRecV3_no_whnf_step",
                "natRecZ_iota_fires",
                "iota_step_to_reduces",
            ],
            "THE NECESSITY GUARD for the head-free premise, and the R5 OBSTRUCTION made \
             mechanical rather than rhetorical. Four facts about e = Nat.rec (bvar 0) (bvar 0) \
             (bvar 0) over the REAL reflected env: (1) e is Neutral, so an unrestricted cr3 WOULD \
             apply to it; (2) e is NOT head-free, so the restricted face does not; (3) e takes no \
             whnf_step at all, so cr3's hypothesis 'every reduct of e is in the set' is satisfied \
             VACUOUSLY and carries zero information; (4) app e Nat.zero nonetheless iota-fires to \
             the real Nat.rec zero-rule contractum. An unrestricted cr3 for PiSet would therefore \
             have to produce membership of that contractum from nothing — which is why full \
             IsCandSet (PiSet CA CB) is NOT an R5 theorem and IsCandHF is the honest interface. \
             The structural cause is that spec eliminators are const-headed SPINES, so applying a \
             neutral can create a fresh redex, whereas corpus eliminators are saturated \
             constructors and cannot. Zero axiom_deps.",
        )?;

        // --- Group H: the premise-satisfiability witnesses ---
        add_thm(
            self,
            "candStepInv_const",
            TY_CAND_STEP_INV_CONST.to_string(),
            VAL_CAND_STEP_INV_CONST.to_string(),
            &["candStepInv", "whnf_step"],
            "PREMISE-SATISFIABILITY WITNESS for the corpus hinv side condition: candStepInv IS \
             SATISFIABLE, for EVERY constant codomain family. It was carried as a hypothesis by \
             piSet_cr3_aux, piSet_cr3 and isCandHF_piSet and concluded by nothing, which would \
             have made the whole Pi-candidate conditional on an obligation no term was known to \
             meet — the shape the hnf capstone had. At a constant family CB a2 w and CB a w are \
             the SAME type, so the transport is the identity and the proof is `h`. This is \
             exactly the term candInterp_isCandHF's pi arm already supplied inline; the design's \
             instruction was to KEEP the side condition (§6.6), not to simplify it away, so it \
             is discharged here rather than removed. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candStepInv_interp_witness",
            ty_cand_step_inv_interp(),
            val_cand_step_inv_interp(),
            &["candStepInv_const", "candInterp"],
            "The CLOSED instance of the side condition: candStepInv (candInterp (sort 0)) \
             (fun _ => candInterp (sort 0)), at the exact families the Pi-candidate witness \
             below is stated over. Registered beside the general lemma because a premise \
             witnessed only under a universally quantified family is one instantiation away \
             from being witnessed at nothing. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_id_witness",
            ty_piset_id_witness(),
            val_piset_id_witness(),
            &["PiSet", "candInterp", "fragTy_interp", "fragTy_id"],
            "PREMISE-SATISFIABILITY WITNESS for the Pi-candidate itself: PiSet IS INHABITED — \
             the identity lambda lam (bvar 0) (bvar 0) is a member of PiSet (candInterp (sort \
             0)) (fun _ => candInterp (sort 0)). PiSet is assumed as a hypothesis by piSet_cr2, \
             piSet_cr3_aux and piSet_cr3 (cr3's `every reduct is in the set' premise) and was \
             concluded by nothing: piSet_cr1/cr2/cr3 conclude candCr1/candCr2/candCr3HF OF it, \
             isCandHF_piSet concludes IsCandHF of it, and piSet_app concludes in the codomain \
             family. So every one of those faces could have been about a set with no members. \
             The witness is a FUNCTION rather than a variable, and it is obtained through the \
             ladder's own engine: candInterp (pi A B) reduces to PiSet (candInterp A) (fun _ => \
             candInterp B), so fragTy_interp at fragTy_id — which runs through FragTy.lam, \
             candInterp_lam and the Tait engine candExpHF_beta — inhabits it definitionally. \
             Zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(String, String, String)> {
        vec![
            (
                "r5_spine_snoc".to_string(),
                TY_R5_SPINE_SNOC.to_string(),
                VAL_R5_SPINE_SNOC.to_string(),
            ),
            (
                "deltaReduct_app_gen".to_string(),
                TY_DELTAREDUCT_APP_GEN.to_string(),
                val_deltareduct_app_gen(),
            ),
            (
                "deltaStep_app_gen".to_string(),
                TY_DELTASTEP_APP_GEN.to_string(),
                val_deltastep_app_gen(),
            ),
            (
                "whnfStep_app_left".to_string(),
                TY_WHNFSTEP_APP_LEFT.to_string(),
                VAL_WHNFSTEP_APP_LEFT.to_string(),
            ),
            (
                "whnfAcc_app_left".to_string(),
                TY_WHNFACC_APP_LEFT.to_string(),
                VAL_WHNFACC_APP_LEFT.to_string(),
            ),
            (
                "isCandHF_intro".to_string(),
                TY_ISCANDHF_INTRO.to_string(),
                VAL_ISCANDHF_INTRO.to_string(),
            ),
            (
                "isCandHF_cr1".to_string(),
                TY_ISCANDHF_CR1.to_string(),
                VAL_ISCANDHF_CR1.to_string(),
            ),
            (
                "isCandHF_cr2".to_string(),
                TY_ISCANDHF_CR2.to_string(),
                VAL_ISCANDHF_CR2.to_string(),
            ),
            (
                "isCandHF_cr3".to_string(),
                TY_ISCANDHF_CR3.to_string(),
                VAL_ISCANDHF_CR3.to_string(),
            ),
            (
                "headFree_app".to_string(),
                TY_HEADFREE_APP.to_string(),
                VAL_HEADFREE_APP.to_string(),
            ),
            (
                "isCandSet_weaken".to_string(),
                TY_ISCANDSET_WEAKEN.to_string(),
                VAL_ISCANDSET_WEAKEN.to_string(),
            ),
            (
                "isCandHF_whnfAcc".to_string(),
                TY_ISCANDHF_WHNFACC.to_string(),
                VAL_ISCANDHF_WHNFACC.to_string(),
            ),
            (
                "candHF_var_mem".to_string(),
                TY_CANDHF_VAR_MEM.to_string(),
                VAL_CANDHF_VAR_MEM.to_string(),
            ),
            (
                "appHF_beta_inv".to_string(),
                ty_apphf_beta_inv(),
                val_apphf_beta_inv(),
            ),
            (
                "appHF_whnf_inv".to_string(),
                ty_apphf_whnf_inv(),
                val_apphf_whnf_inv(),
            ),
            (
                "piSet_cr1".to_string(),
                TY_PISET_CR1.to_string(),
                VAL_PISET_CR1.to_string(),
            ),
            (
                "piSet_cr2".to_string(),
                TY_PISET_CR2.to_string(),
                VAL_PISET_CR2.to_string(),
            ),
            (
                "piSet_cr3_aux".to_string(),
                ty_piset_cr3_aux(),
                val_piset_cr3_aux(),
            ),
            ("piSet_cr3".to_string(), ty_piset_cr3(), val_piset_cr3()),
            (
                "isCandHF_piSet".to_string(),
                ty_iscandhf_piset(),
                val_iscandhf_piset(),
            ),
            ("piSet_app".to_string(), ty_piset_app(), val_piset_app()),
            (
                "candExpHF_beta".to_string(),
                ty_candexphf_beta(),
                val_candexphf_beta(),
            ),
            (
                "candInterp_isCandHF".to_string(),
                TY_CANDINTERP_ISCANDHF.to_string(),
                val_candinterp_iscandhf(),
            ),
            (
                "candInterp_cr1".to_string(),
                TY_CANDINTERP_CR1.to_string(),
                VAL_CANDINTERP_CR1.to_string(),
            ),
            (
                "candInterp_var".to_string(),
                TY_CANDINTERP_VAR.to_string(),
                VAL_CANDINTERP_VAR.to_string(),
            ),
            (
                "candInterp_sort_mem".to_string(),
                TY_CANDINTERP_SORT_MEM.to_string(),
                VAL_CANDINTERP_SORT_MEM.to_string(),
            ),
            (
                "candInterp_app".to_string(),
                TY_CANDINTERP_APP.to_string(),
                VAL_CANDINTERP_APP.to_string(),
            ),
            (
                "candInterp_lam".to_string(),
                TY_CANDINTERP_LAM.to_string(),
                VAL_CANDINTERP_LAM.to_string(),
            ),
            (
                "fragTy_interp".to_string(),
                TY_FRAGTY_INTERP.to_string(),
                VAL_FRAGTY_INTERP.to_string(),
            ),
            (
                "fragTy_sn".to_string(),
                TY_FRAGTY_SN.to_string(),
                VAL_FRAGTY_SN.to_string(),
            ),
            (
                "r5_lam_ne_bvar".to_string(),
                TY_R5_LAM_NE_BVAR.to_string(),
                val_r5_lam_ne_bvar(),
            ),
            (
                "r5_bvarApp_no_beta".to_string(),
                ty_r5_bvarapp_no_beta(),
                val_r5_bvarapp_no_beta(),
            ),
            (
                "r5_whnfAcc_omegaLam".to_string(),
                TY_R5_WHNFACC_OMEGALAM.to_string(),
                val_r5_whnfacc_omegalam(),
            ),
            (
                "r5_omegaV_step_self".to_string(),
                TY_R5_OMEGAV_STEP_SELF.to_string(),
                val_r5_omegav_step_self(),
            ),
            (
                "r5_omegaV_not_whnfAcc".to_string(),
                TY_R5_OMEGAV_NOT_WHNFACC.to_string(),
                VAL_R5_OMEGAV_NOT_WHNFACC.to_string(),
            ),
            (
                "candInterp_pi_not_total".to_string(),
                ty_candinterp_pi_not_total(),
                val_candinterp_pi_not_total(),
            ),
            (
                "r5_interp_pi_proper".to_string(),
                ty_r5_interp_pi_proper(),
                val_r5_interp_pi_proper(),
            ),
            ("fragTy_id".to_string(), ty_fragty_id(), val_fragty_id()),
            (
                "fragTy_app_witness".to_string(),
                ty_fragty_app_witness(),
                val_fragty_app_witness(),
            ),
            (
                "fragTy_sn_witness".to_string(),
                ty_fragty_sn_witness(),
                val_fragty_sn_witness(),
            ),
            (
                "fragTy_not_total".to_string(),
                ty_fragty_not_total(),
                val_fragty_not_total(),
            ),
            (
                "r5_natRecV3_delta_none".to_string(),
                ty_r5_natrecv3_delta_none(),
                VAL_R5_NATRECV3_DELTA_NONE.to_string(),
            ),
            (
                "r5_natRecV3_no_whnf_step".to_string(),
                ty_r5_natrecv3_no_whnf_step(),
                val_r5_natrecv3_no_whnf_step(),
            ),
            (
                "piSet_cr3_headFree_necessary".to_string(),
                ty_piset_cr3_headfree_necessary(),
                val_piset_cr3_headfree_necessary(),
            ),
            (
                "candStepInv_const".to_string(),
                TY_CAND_STEP_INV_CONST.to_string(),
                VAL_CAND_STEP_INV_CONST.to_string(),
            ),
            (
                "candStepInv_interp_witness".to_string(),
                ty_cand_step_inv_interp(),
                val_cand_step_inv_interp(),
            ),
            (
                "piSet_id_witness".to_string(),
                ty_piset_id_witness(),
                val_piset_id_witness(),
            ),
        ]
    }

    /// The plain defs and the one inductive, as full declaration sources.
    fn decl_sources() -> Vec<(String, String)> {
        vec![
            ("HeadFree".to_string(), SRC_HEAD_FREE.to_string()),
            ("candCr3HF".to_string(), SRC_CAND_CR3HF.to_string()),
            ("IsCandHF".to_string(), SRC_IS_CAND_HF.to_string()),
            ("PiSet".to_string(), SRC_PI_SET.to_string()),
            ("candStepInv".to_string(), SRC_CAND_STEP_INV.to_string()),
            ("candInterp".to_string(), src_cand_interp()),
            ("FragTy".to_string(), SRC_FRAG_TY.to_string()),
            ("r5_omegaLam".to_string(), src_r5_omega_lam()),
            ("r5_omegaV".to_string(), SRC_R5_OMEGA_V.to_string()),
        ]
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (assembly mistakes invisible to `cargo check`).
    #[test]
    fn test_candmodel_r5_sources_parse() {
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
        for (name, src) in decl_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
        }
    }

    /// PER-STRING paren balance on every source.
    #[test]
    fn test_candmodel_r5_sources_paren_balanced() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (n, src) in decl_sources() {
            all.push((format!("{n}::decl"), src));
        }
        for (name, src) in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {name}: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in {name}: {src}");
        }
    }

    /// Skip a run of parenthesised binder groups starting at `i`, returning
    /// (index after the groups, how many groups were skipped).
    fn skip_binder_groups(b: &[char], mut i: usize) -> (usize, usize) {
        let mut n = 0usize;
        loop {
            while i < b.len() && b[i] == ' ' {
                i += 1;
            }
            if i >= b.len() || b[i] != '(' {
                break;
            }
            let mut d = 0i64;
            while i < b.len() {
                if b[i] == '(' {
                    d += 1;
                } else if b[i] == ')' {
                    d -= 1;
                    if d == 0 {
                        i += 1;
                        break;
                    }
                }
                i += 1;
            }
            n += 1;
        }
        while i < b.len() && b[i] == ' ' {
            i += 1;
        }
        (i, n)
    }

    /// STRUCTURAL GUARD: a `forall` binder run must be terminated by a COMMA
    /// and a `fun` binder run by `=>`.
    #[test]
    fn test_candmodel_r5_binder_runs_terminated() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (name, src) in &all {
            let b: Vec<char> = src.chars().collect();
            for (kw, close) in [("forall ", ","), ("fun ", "=>")] {
                let mut from = 0usize;
                while let Some(rel) = src[from..].find(kw) {
                    let start = from + rel;
                    from = start + 1;
                    let ci = src[..start].chars().count() + kw.chars().count();
                    let (after, groups) = skip_binder_groups(&b, ci);
                    assert!(groups > 0, "{name}: `{kw}` with no parenthesised binder");
                    let tail: String = b[after..(after + 2).min(b.len())].iter().collect();
                    assert!(
                        tail.starts_with(close),
                        "{name}: `{kw}` binder run is not terminated by `{close}` — found \
                         `{tail}`"
                    );
                }
            }
        }
    }

    /// Shape guards.
    #[test]
    fn test_candmodel_r5_shape_guards() {
        // (1) The engine really is R1's, weakened — no IsCandSet spelling may
        // survive the rewrite, and exactly one cr3 use may gain the head-free
        // argument.
        let eng = val_candexphf_beta();
        assert!(
            !eng.contains("IsCandSet") && !eng.contains("isCandSet_"),
            "candExpHF_beta must carry no IsCandSet spelling after the weakening"
        );
        assert!(
            !ty_candexphf_beta().contains("IsCandSet"),
            "candExpHF_beta's TYPE must be at the head-free interface"
        );
        assert_eq!(
            eng.matches("isCandHF_cr3").count(),
            1,
            "the engine uses exactly one cr3, at the lam-headed redex"
        );
        assert!(
            eng.contains(
                "isCandHF_cr3 S hS (KExpr.app (KExpr.lam ty0 b0) a0) (@Eq.refl (OptionType Name) \
                 (@OptionType.none Name))"
            ),
            "the engine's single cr3 must be discharged head-free BY Eq.refl at the \
             lam-headed redex — that is what makes the weakening sound"
        );
        assert_eq!(
            eng.matches("whnf_acc.rec").count(),
            3,
            "R1's triple Acc nesting must survive the rewrite unchanged"
        );

        // (2) ARM-ARITY PIN: every 15-arm beta_reduces.rec binds the recursive
        // premise of each recursive minor BEFORE its IH.
        for (name, v) in [
            ("appHF_beta_inv", val_apphf_beta_inv()),
            ("r5_bvarApp_no_beta", val_r5_bvarapp_no_beta()),
        ] {
            assert_eq!(
                v.matches("(_qstep : beta_reduces ").count(),
                10,
                "{name}: the 10 recursive structural minors each bind their premise"
            );
            assert_eq!(
                v.matches("(qstep : beta_reduces ").count(),
                2,
                "{name}: app_left and app_right bind their beta_reduces premise"
            );
            assert_eq!(
                v.matches("(qio : iota_reduces ").count(),
                1,
                "{name}: the iota minor binds an iota_reduces premise and has no IH"
            );
        }

        // (3) The head-free inversion must refute BOTH computational legs from
        // the hypothesis, never by computing the real env — that is what makes
        // it generic in e.
        let bi = val_apphf_beta_inv();
        assert!(
            bi.contains(
                "iota_step_head_none_absurd_type (red_rec the_red_env) (KExpr.app e a) qe2 C hhf"
            ),
            "appHF_beta_inv must kill its iota arm FROM the head-free hypothesis"
        );
        assert!(
            !bi.contains("Eq.refl (OptionType Name) (OptionType.none Name)")
                && !bi.contains("@Eq.refl (OptionType Name) (@OptionType.none Name)"),
            "a generic-head inversion may not compute head-freeness"
        );
        assert!(
            val_apphf_whnf_inv().contains(
                "delta_step_head_none_absurd_type (red_def the_red_env) (KExpr.app e a) g2 C hhf"
            ),
            "appHF_whnf_inv must kill its delta arm from the same hypothesis"
        );

        // (4) The interpretation is a NINE-arm KExpr.rec whose ONLY non-top
        // clause is pi, and the hinv side condition is discharged, not dropped.
        let ci = src_cand_interp();
        assert_eq!(
            ci.matches(TOPSET).count(),
            8,
            "exactly eight of the nine KExpr formers take the top candidate"
        );
        assert_eq!(
            ci.matches("PiSet ").count(),
            1,
            "exactly one former (pi) takes the Pi-candidate"
        );
        assert!(
            val_candinterp_iscandhf().contains("isCandHF_piSet"),
            "candidate-hood of the interpretation must go through the Pi-candidate"
        );
        assert!(
            ty_iscandhf_piset().contains("candStepInv CA CB"),
            "the corpus hinv side condition must be CARRIED by the Pi-candidate, not dropped"
        );

        // (5) The capstone is UNCONDITIONAL: no closedness or model premise
        // may appear anywhere in the fragment chain.
        for (name, ty) in [
            ("fragTy_sn", TY_FRAGTY_SN.to_string()),
            ("fragTy_interp", TY_FRAGTY_INTERP.to_string()),
            ("candInterp_lam", TY_CANDINTERP_LAM.to_string()),
            ("candExpHF_beta", ty_candexphf_beta()),
            ("FragTy", SRC_FRAG_TY.to_string()),
        ] {
            for forbidden in ["RecEnvClosed", "DefEnvClosed", "CandModel", "cm_Red"] {
                assert!(
                    !ty.contains(forbidden),
                    "{name} must carry no {forbidden} premise — the capstone is unconditional"
                );
            }
        }

        // (6) RECURSOR-SHAPE PIN: FragTy's first constructor leads with a
        // Level and concludes at a NON-variable index, so no uniform leading
        // ctor-argument prefix exists and the measured promotion cannot fire.
        assert!(
            SRC_FRAG_TY.contains(
                "| sortMem : forall (n : Level) (e : KExpr), whnf_acc e -> FragTy (KExpr.sort n) e"
            ),
            "FragTy's first constructor must lead with a Level at a non-variable index"
        );
        // Both recursive premises are the LAST field of their constructor, so
        // the minor-premise binder order is convention-independent (fields
        // then IHs, or interleaved, give the same sequence).
        assert!(
            SRC_FRAG_TY
                .contains("candInterp A a -> FragTy (KExpr.pi A B) f -> FragTy B (KExpr.app f a)"),
            "FragTy.app's recursive premise must be its LAST field"
        );
        assert!(
            SRC_FRAG_TY.contains(
                "candInterp A a -> FragTy B (instantiate b2 a)) -> FragTy (KExpr.pi A B) \
                 (KExpr.lam ty b)"
            ),
            "FragTy.lam's recursive (development-family) premise must be its LAST field, and \
             the recursive occurrence must sit in the premise's CONCLUSION (strict positivity)"
        );

        // (7) PROP/TYPE PIN: the spec's Eq is Prop and the kernel is
        // NON-CUMULATIVE, so a (C : Type)-parameterised CPS eliminator may
        // never be instantiated at an Eq goal.
        for (name, ty, val) in theorem_sources() {
            for src in [&ty, &val] {
                for (elim, c_index) in [
                    ("option_none_ne_some_type", 2usize),
                    ("no_whnf_step_bvar", 2),
                    ("r5_lam_ne_bvar", 3),
                    ("lam_ne_app", 4),
                    ("pi_ne_app", 4),
                    ("let_ne_app", 5),
                    ("proj_ne_app", 5),
                ] {
                    for c in type_valued_c_slots(src, elim, c_index) {
                        assert!(
                            !c.starts_with("(Eq ") && c != "Prop",
                            "{name}: {elim}'s C parameter is (C : Type) but got the Prop term \
                             {c}"
                        );
                    }
                }
            }
        }

        // (8) The necessity guard must be about the REAL reflected env and
        // must consume R3's fire, never restate it.
        let nec = val_piset_cr3_headfree_necessary();
        assert!(
            nec.contains("natRecZ_iota_fires") && nec.contains("r5_natRecV3_no_whnf_step"),
            "the necessity guard must consume both the fire and the no-step fact"
        );
        assert!(
            ty_piset_cr3_headfree_necessary().contains("fixture_nat_rec_name"),
            "the guard must name the generated reflected atom, not a hand-written name"
        );
    }

    /// Paren-aware extraction of the `c_index`-th argument of every
    /// application of `elim` in `src` (0-based from the first argument).
    fn type_valued_c_slots(src: &str, elim: &str, c_index: usize) -> Vec<String> {
        let bytes: Vec<char> = src.chars().collect();
        let mut out = Vec::new();
        let mut from = 0usize;
        while let Some(rel) = src[from..].find(elim) {
            let start = from + rel;
            from = start + elim.len();
            let before_ok =
                start == 0 || !src[..start].ends_with(|c: char| c.is_alphanumeric() || c == '_');
            let after = src[start + elim.len()..].chars().next();
            if !before_ok || after != Some(' ') {
                continue;
            }
            let mut i = src[..start].chars().count() + elim.chars().count();
            let mut args: Vec<String> = Vec::new();
            while i < bytes.len() && args.len() <= c_index {
                while i < bytes.len() && bytes[i] == ' ' {
                    i += 1;
                }
                if i >= bytes.len() || bytes[i] == ')' {
                    break;
                }
                let s = i;
                if bytes[i] == '(' {
                    let mut d = 0i64;
                    while i < bytes.len() {
                        if bytes[i] == '(' {
                            d += 1;
                        } else if bytes[i] == ')' {
                            d -= 1;
                            if d == 0 {
                                i += 1;
                                break;
                            }
                        }
                        i += 1;
                    }
                } else {
                    while i < bytes.len() && bytes[i] != ' ' && bytes[i] != ')' {
                        i += 1;
                    }
                }
                args.push(bytes[s..i].iter().collect());
            }
            if let Some(c) = args.get(c_index) {
                out.push(c.clone());
            }
        }
        out
    }

    /// Registration + kernel re-verification against the substitution bundle.
    #[test]
    fn test_candmodel_r5_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for (n, _) in decl_sources() {
            names.push(n);
        }
        for name in &names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r5 stage"
            );
        }
        for (name, _, _) in theorem_sources() {
            spec.verify_definition(&name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
