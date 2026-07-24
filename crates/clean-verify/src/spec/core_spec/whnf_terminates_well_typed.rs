// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strong normalization of the FULL WHNF step union for well-typed terms —
//! retirement of the census axiom `whnf_terminates_well_typed`
//! (`whnf_lemmas.rs`).
//!
//! Clean-kernel port of the Aristotle-proven Lean development
//! `scratch/aristotle-typed-sn/TypedSn.lean` **Part 1** (0 sorry,
//! `#print axioms` = propext + Quot.sound). The Lean file is the STRATEGY
//! guide; every term here is a closed spec proof term re-checked by the Clean
//! kernel at spec build (`DerivedProved`, empty non-foundational closure). No
//! Lean tactic output is trusted.
//!
//! ## What is proved (and the honest scope)
//!
//! The census axiom was
//!
//!   `whnf_terminates_well_typed : forall e T, has_type e T -> terminates_whnf e`
//!
//! with `has_type e T := Typing e T` (`typing_def_eq.rs`, reducible alias) and
//! `terminates_whnf e := whnf_acc e` (`whnf_reduction.rs`), where `whnf_acc` is
//! accessibility under `whnf_step = beta_reduces ∪ delta_reduces` and
//! `beta_reduces` itself folds in the `iota` leg. So the three legs of the step
//! union are β, δ, ι. This module discharges the FULL union as a genuine
//! zero-domain-axiom proof.
//!
//! It is provable — NOT Gödel-blocked — because the spec's `Typing` judgment is
//! CONTEXT-FREE: it is generated solely by `sort / pi / lam / app` (+ the
//! subject-preserving `conv`), with NO `bvar` rule and NO `const` rule
//! (`typing_def_eq.rs:44-104`). Hence every typable term is simultaneously
//! `bvar`-free AND `const`-free, and three consequences close SN elementarily:
//!
//!   * `const`-free ⇒ neither δ nor ι ever fires: both `delta_reduct` and
//!     `iota_reduct` are gated on a `const` head (`kexpr_const_name (kapp_fn e)`),
//!     which is `none` on a `const`-free term — discharged via the landed
//!     `delta_step_head_none_absurd_type` / `iota_step_head_none_absurd_type`;
//!   * `bvar`-free ⇒ every β redex `(λA.body) arg ⇒ instantiate body arg` has
//!     `instantiate body arg = body`, so each β step strictly shrinks `expr_size`
//!     (this is the landed `beta_bd_sn` termination over the iota-free
//!     `beta_reduces_bd`);
//!   * therefore `whnf_acc` follows: every `whnf_step` out of a typable term is
//!     really an iota-free `beta_reduces_bd` step (δ/ι vacuous), and the term
//!     stays `bvar`/`const`-free, so accessibility transports off the landed
//!     `beta_bd_acc` (`beta_bd_sn_has_type`).
//!
//! ## HONESTY (load-bearing)
//!
//! This proves SN for the spec's ACTUAL `has_type` = the context-free `Typing`
//! fragment, which is DEGENERATE (no var/const ⇒ constant lambdas, no δ/ι). It
//! is a GENUINE proof of the axiom AS STATED (the axiom quantified over this same
//! `has_type`), removing a provable assumption from the trusted set — it is NOT a
//! claim of full dependent-CIC strong normalization. The REAL dependent SN (with
//! a `var` rule and a typing context `TypingCtx`) is a SEPARATE, strictly harder
//! statement, provable only modulo a Tait–Girard reducibility-candidate model
//! (the isolated Gödel floor; see `TypedSn.lean` Part 2). Nothing here touches
//! that.
//!
//! ## Ladder (all `DerivedProved`, zero domain axiom_deps)
//!
//!   1. `typable_const_free` — every typable term is `const`-free (`Typing.rec`;
//!      the `const`-analogue of the landed `typable_bvar_ceiling_zero`).
//!   2. `const_free_kapp_fn` / `const_free_head_name_none` /
//!      `const_free_head_const_name_none` — `const`-freeness kills the head
//!      `const` name (`kexpr_const_name (kapp_fn e) = none`), the discharge
//!      condition of the δ/ι head-none absurdities.
//!   3. `beta_reduces_to_bd_cf` — a FULL `beta_reduces` step (14 arms incl. the
//!      `iota` arm) out of a `bvar`-free `const`-free term is an iota-free
//!      `beta_reduces_bd` step (the `iota` arm is vacuous by const-freeness).
//!   4. `whnf_step_to_bd_cf` — a FULL `whnf_step` (β∪δ) out of such a term is a
//!      `beta_reduces_bd` step (the δ arm is vacuous by const-freeness).
//!   5. `whnf_terminates_well_typed` — `beta_bd_acc.rec` on `beta_bd_sn_has_type`
//!      transports accessibility from `beta_reduces_bd` to `whnf_step`, threading
//!      bvar-freeness (`beta_bd_step_preserves_ceiling_zero`) and const-freeness
//!      (`const_free_preserved_bd`) along each step. Concludes `terminates_whnf e`
//!      (= `whnf_acc e`).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the full-union WHNF strong-normalization ladder and the retired
    /// census axiom `whnf_terminates_well_typed` as a `DerivedProved` theorem.
    ///
    /// Must run AFTER `add_typing_def_eq` (`Typing` / `has_type` / `DefEq`),
    /// `add_typing_def_eq_reduction_families` (`delta_reduces` / `iota_reduces`),
    /// `add_iota_step_bridge` (`iota_reduces_to_step`), `add_delta_step_bridge`
    /// (`delta_reduces_to_step`), `add_par_reduces_c`
    /// (`iota_step_head_none_absurd_type`), `add_par_reduces_d_diamond`
    /// (`delta_step_head_none_absurd_type`), `add_whnf_reduction` (`whnf_step` /
    /// `whnf_acc` / `terminates_whnf` / `beta_reduces`), `add_beta_bd_sn`
    /// (`beta_bd_acc` / `beta_bd_sn_has_type` / `typable_bvar_ceiling_zero` /
    /// `beta_bd_step_preserves_ceiling_zero`), `add_whnf_progress` (`const_free`),
    /// and `add_whnf_normalizes` (`const_free_preserved_bd`). Purely additive;
    /// zero new axioms — it REMOVES one (the census axiom flips to a theorem).
    pub(super) fn add_whnf_terminates_well_typed(&mut self) -> Result<(), SpecError> {
        self.add_wt_typable_const_free()?;
        self.add_wt_const_free_head_none()?;
        self.add_wt_beta_reduces_to_bd_cf()?;
        self.add_wt_whnf_step_to_bd_cf()?;
        self.add_wt_theorem()?;
        Ok(())
    }

    /// `typable_const_free` — every typable term is `const`-free. `Typing.rec`
    /// with motive `const_free e`; `sort` is a closed leaf (`ConstFreeUnit.triv`),
    /// `pi`/`lam`/`app` recompose the child witnesses via `AndType.intro` (the
    /// node's `const_free` reduces to the `AndType` of the child witnesses), and
    /// `conv` forwards the IH (the subject term is unchanged). The `const`
    /// analogue of the landed `typable_bvar_ceiling_zero`; no box needed since
    /// `const_free` is already `Type`-valued.
    fn add_wt_typable_const_free(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "typable_const_free".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), Typing e T -> const_free e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (T0 : KExpr) (h0 : Typing e0 T0) => ",
                    "Typing.rec ",
                    "(fun (e : KExpr) (T : KExpr) (_ : Typing e T) => const_free e) ",
                    // sort n
                    "(fun (n : Level) => ConstFreeUnit.triv) ",
                    // pi A B n m
                    "(fun (A : KExpr) (B : KExpr) (n : Level) (m : Level) ",
                    "(_hA : Typing A (KExpr.sort n)) (_hB : Typing B (KExpr.sort m)) ",
                    "(ihA : const_free A) (ihB : const_free B) => ",
                    "AndType.intro (const_free A) (const_free B) ihA ihB) ",
                    // lam A b B u
                    "(fun (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
                    "(_hA : Typing A (KExpr.sort u)) (_hb : Typing b B) ",
                    "(ihA : const_free A) (ihb : const_free b) => ",
                    "AndType.intro (const_free A) (const_free b) ihA ihb) ",
                    // app f a A B
                    "(fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A B)) (_ha : Typing a A) ",
                    "(ihf : const_free f) (iha : const_free a) => ",
                    "AndType.intro (const_free f) (const_free a) ihf iha) ",
                    // conv e A B — subject unchanged, forward the IH.
                    "(fun (e : KExpr) (A : KExpr) (B : KExpr) ",
                    "(_he : Typing e A) (_eq : DefEq A B) ",
                    "(ihe : const_free e) => ihe) ",
                    // indices + major
                    "e0 T0 h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Every typable term is const-free: Typing e T -> const_free e. Typing.rec with ",
                "motive const_free e; sort is a closed leaf (ConstFreeUnit.triv), pi/lam/app ",
                "recompose the child witnesses via AndType.intro (const_free of a binder/app node ",
                "reduces to the AndType of the child witnesses), conv forwards the IH (subject ",
                "unchanged). Sound because the spec's context-free Typing fragment has NO rule for ",
                "const (or bvar). The const analogue of typable_bvar_ceiling_zero; no box needed ",
                "(const_free is already Type-valued). DerivedProved, zero axiom_deps. Part of the ",
                "whnf_terminates_well_typed retirement (Aristotle TypedSn.lean Part 1 port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing".to_string(),
                "Typing.rec".to_string(),
                "DefEq".to_string(),
                "const_free".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "AndType.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// `const_free_kapp_fn`, `const_free_head_name_none`, and their composition
    /// `const_free_head_const_name_none` — const-freeness forces the head const
    /// name to `none`, the discharge condition of the δ/ι head-none absurdities.
    /// Mirrors the Lean `kapp_fn_noConst` + `noConst_kexpr_const_name_none`.
    fn add_wt_const_free_head_none(&mut self) -> Result<(), SpecError> {
        // const_free_kapp_fn: const-freeness is inherited by the spine head.
        // KExpr.rec on e; the app arm peels to the head via the IH (kapp_fn (app
        // f a) = kapp_fn f, const_free (app f a) = AndType (const_free f) ...), the
        // other constructors are their own kapp_fn head so the hypothesis passes
        // through unchanged.
        self.add_definition(SpecDefinition {
            name: "const_free_kapp_fn".to_string(),
            type_src: "forall (e : KExpr), const_free e -> const_free (kapp_fn e)".to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) => ",
                    "KExpr.rec ",
                    "(fun (x : KExpr) => const_free x -> const_free (kapp_fn x)) ",
                    // sort n
                    "(fun (n : Level) (h : const_free (KExpr.sort n)) => h) ",
                    // bvar i
                    "(fun (i : Nat) (h : const_free (KExpr.bvar i)) => h) ",
                    // app f a — kapp_fn (app f a) = kapp_fn f; forward via ihf.
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ihf : const_free f -> const_free (kapp_fn f)) ",
                    "(_iha : const_free a -> const_free (kapp_fn a)) ",
                    "(h : const_free (KExpr.app f a)) => ",
                    "ihf (AndType.left (const_free f) (const_free a) h)) ",
                    // lam ty b — kapp_fn is itself.
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_ihty : const_free ty -> const_free (kapp_fn ty)) ",
                    "(_ihb : const_free b -> const_free (kapp_fn b)) ",
                    "(h : const_free (KExpr.lam ty b)) => h) ",
                    // pi ty b — kapp_fn is itself.
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_ihty : const_free ty -> const_free (kapp_fn ty)) ",
                    "(_ihb : const_free b -> const_free (kapp_fn b)) ",
                    "(h : const_free (KExpr.pi ty b)) => h) ",
                    // const nm us — kapp_fn is itself (h : Empty, passes through).
                    "(fun (nm : Name) (us : ListType Level) ",
                    "(h : const_free (KExpr.const nm us)) => h) ",
                    // let_ ty v b — kapp_fn is itself (a let_ is its own spine head).
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) ",
                    "(_ihty : const_free ty -> const_free (kapp_fn ty)) ",
                    "(_ihv : const_free v -> const_free (kapp_fn v)) ",
                    "(_ihb : const_free b -> const_free (kapp_fn b)) ",
                    "(h : const_free (KExpr.let_ ty v b)) => h) ",
                    // proj s i sub — kapp_fn is itself (a proj is its own spine head).
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(_ihsub : const_free sub -> const_free (kapp_fn sub)) ",
                    "(h : const_free (KExpr.proj s i sub)) => h) ",
                    // lit v — kapp_fn is itself.
                    "(fun (v : Nat) (h : const_free (KExpr.lit v)) => h) ",
                    "e0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "const-freeness is inherited by the application-spine head: const_free e -> ",
                "const_free (kapp_fn e). KExpr.rec on e; the app arm peels to the head via the IH ",
                "(kapp_fn (app f a) = kapp_fn f by refl, const_free (app f a) = AndType of children), ",
                "the sort/bvar/lam/pi/const/let_ constructors are their own kapp_fn head so the ",
                "hypothesis passes through (a let_ is never an app spine). Mirrors kapp_fn_noConst ",
                "in the Aristotle Lean source. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "const_free".to_string(),
                "kapp_fn".to_string(),
                "AndType.left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // const_free_head_name_none: a const-free head has no const name.
        // KExpr.rec (case analysis) on e; sort/bvar/app/lam/pi give
        // kexpr_const_name = none by refl, the const case is refuted by
        // const_free (const n us) = Empty via Empty.rec.
        self.add_definition(SpecDefinition {
            name: "const_free_head_name_none".to_string(),
            type_src: concat!(
                "forall (e : KExpr), const_free e -> ",
                "Eq (OptionType Name) (kexpr_const_name e) (OptionType.none Name)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) => ",
                    "KExpr.rec ",
                    "(fun (x : KExpr) => const_free x -> ",
                    "Eq (OptionType Name) (kexpr_const_name x) (OptionType.none Name)) ",
                    // sort n
                    "(fun (n : Level) (_ : const_free (KExpr.sort n)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // bvar i
                    "(fun (i : Nat) (_ : const_free (KExpr.bvar i)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // app f a
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(_ihf : const_free f -> Eq (OptionType Name) (kexpr_const_name f) (OptionType.none Name)) ",
                    "(_iha : const_free a -> Eq (OptionType Name) (kexpr_const_name a) (OptionType.none Name)) ",
                    "(_ : const_free (KExpr.app f a)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // lam ty b
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_ihty : const_free ty -> Eq (OptionType Name) (kexpr_const_name ty) (OptionType.none Name)) ",
                    "(_ihb : const_free b -> Eq (OptionType Name) (kexpr_const_name b) (OptionType.none Name)) ",
                    "(_ : const_free (KExpr.lam ty b)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // pi ty b
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_ihty : const_free ty -> Eq (OptionType Name) (kexpr_const_name ty) (OptionType.none Name)) ",
                    "(_ihb : const_free b -> Eq (OptionType Name) (kexpr_const_name b) (OptionType.none Name)) ",
                    "(_ : const_free (KExpr.pi ty b)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // const nm us — const_free (const nm us) = Empty.
                    "(fun (nm : Name) (us : ListType Level) ",
                    "(h : const_free (KExpr.const nm us)) => ",
                    "Empty.rec (fun (_ : Empty) => ",
                    "Eq (OptionType Name) (kexpr_const_name (KExpr.const nm us)) (OptionType.none Name)) ",
                    "h) ",
                    // let_ ty v b — kexpr_const_name (let_ ...) = none by refl.
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) ",
                    "(_ihty : const_free ty -> Eq (OptionType Name) (kexpr_const_name ty) (OptionType.none Name)) ",
                    "(_ihv : const_free v -> Eq (OptionType Name) (kexpr_const_name v) (OptionType.none Name)) ",
                    "(_ihb : const_free b -> Eq (OptionType Name) (kexpr_const_name b) (OptionType.none Name)) ",
                    "(_ : const_free (KExpr.let_ ty v b)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // proj s i sub — kexpr_const_name (proj ..) = none by refl.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(_ihsub : const_free sub -> Eq (OptionType Name) (kexpr_const_name sub) (OptionType.none Name)) ",
                    "(_ : const_free (KExpr.proj s i sub)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    // lit v — kexpr_const_name (lit v) = none by refl.
                    "(fun (v : Nat) (_ : const_free (KExpr.lit v)) => ",
                    "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    "e0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A const-free term has no head const name: const_free e -> ",
                "kexpr_const_name e = none. KExpr.rec on e; sort/bvar/app/lam/pi/let_ give none by ",
                "refl (kexpr_const_name matches only const), the const case is refuted by ",
                "const_free (const n us) = Empty via Empty.rec. Mirrors noConst_kexpr_const_name_none ",
                "in the Aristotle Lean source. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "const_free".to_string(),
                "kexpr_const_name".to_string(),
                "Eq.refl".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // const_free_head_const_name_none: compose the two — the head after
        // kapp_fn has no const name. The exact discharge condition of
        // delta_step_head_none_absurd_type / iota_step_head_none_absurd_type.
        self.add_definition(SpecDefinition {
            name: "const_free_head_const_name_none".to_string(),
            type_src: concat!(
                "forall (e : KExpr), const_free e -> ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (hcf : const_free e) => ",
                    "const_free_head_name_none (kapp_fn e) (const_free_kapp_fn e hcf)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A const-free term's application-spine head has no const name: const_free e -> ",
                "kexpr_const_name (kapp_fn e) = none. Composes const_free_head_name_none with ",
                "const_free_kapp_fn. The exact discharge condition of the δ/ι head-none absurdities ",
                "(delta_step_head_none_absurd_type / iota_step_head_none_absurd_type). DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "const_free_head_name_none".to_string(),
                "const_free_kapp_fn".to_string(),
                "kapp_fn".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// `beta_reduces_to_bd_cf` — a FULL `beta_reduces` step (14 arms, incl. the
    /// `iota` arm) out of a `bvar`-free `const`-free term is an iota-free
    /// `beta_reduces_bd` step. `beta_reduces.rec` (full index-motive shape); the
    /// 13 structural arms map directly to the matching `beta_reduces_bd`
    /// constructor (threading the split bvar-ceiling and const-freeness through
    /// the IH exactly as the landed bd step lemmas), and the `iota` arm is VACUOUS
    /// on a const-free term (discharged via `iota_step_head_none_absurd_type`).
    fn add_wt_beta_reduces_to_bd_cf(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "beta_reduces_to_bd_cf".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), beta_reduces e e' -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> beta_reduces_bd e e'"
            )
            .to_string(),
            value_src: Some(beta_reduces_to_bd_cf_proof()),
            is_axiom: false,
            description: concat!(
                "A single FULL beta_reduces step (all 14 constructors including the env-dependent ",
                "iota arm) out of a bvar-free const-free term is an IOTA-FREE beta_reduces_bd step: ",
                "beta_reduces e e' -> bvar_ceiling e = 0 -> const_free e -> beta_reduces_bd e e'. ",
                "beta_reduces.rec; the 13 structural arms (beta + zeta head contractions, ",
                "app/lam/pi/forall_ and let_ty/let_val/let_body congruences) map directly to the ",
                "matching beta_reduces_bd constructor, threading the split bvar-ceiling ",
                "(nat_add_eq_zero_left/right) and const-freeness (AndType.left/right) through the ",
                "IH — the beta/zeta contraction arms need no rewriting (identical contracta on ",
                "both sides of the map). The iota ",
                "arm is VACUOUS on a const-free term: iota_reduces e e' carries an iota_step over ",
                "the_red_env, and a const-free head forces kexpr_const_name (kapp_fn e) = none, so ",
                "iota_step_head_none_absurd_type discharges it. Mirrors step_clean_and_lt's iota ",
                "discharge in the Aristotle Lean source. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces".to_string(),
                "beta_reduces.rec".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.beta".to_string(),
                "beta_reduces_bd.app_left".to_string(),
                "beta_reduces_bd.app_right".to_string(),
                "beta_reduces_bd.lam_ty".to_string(),
                "beta_reduces_bd.lam_body".to_string(),
                "beta_reduces_bd.pi_dom".to_string(),
                "beta_reduces_bd.pi_cod".to_string(),
                "beta_reduces_bd.forall_congr_dom".to_string(),
                "beta_reduces_bd.forall_congr_cod".to_string(),
                "beta_reduces_bd.zeta".to_string(),
                "beta_reduces_bd.let_ty".to_string(),
                "beta_reduces_bd.let_val".to_string(),
                "beta_reduces_bd.let_body".to_string(),
                "bvar_ceiling".to_string(),
                "const_free".to_string(),
                "instantiate".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_add_eq_zero_right".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "Nat.add".to_string(),
                "iota_reduces".to_string(),
                "iota_reduces_to_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "const_free_head_const_name_none".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// `whnf_step_to_bd_cf` — a FULL `whnf_step` (β ∪ δ) out of a `bvar`-free
    /// `const`-free term is an iota-free `beta_reduces_bd` step. `whnf_step.rec`
    /// (promoted-parameter shape); the β leg forwards to `beta_reduces_to_bd_cf`,
    /// the δ leg is VACUOUS on a const-free term (discharged via
    /// `delta_step_head_none_absurd_type`).
    fn add_wt_whnf_step_to_bd_cf(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "whnf_step_to_bd_cf".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), whnf_step e e' -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> beta_reduces_bd e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (hstep : whnf_step e e') => ",
                    "whnf_step.rec e e' ",
                    "(fun (_ : whnf_step e e') => ",
                    "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> beta_reduces_bd e e') ",
                    // beta leg: forward to beta_reduces_to_bd_cf.
                    "(fun (hb : beta_reduces e e') => beta_reduces_to_bd_cf e e' hb) ",
                    // delta leg: vacuous on a const-free term.
                    "(fun (hd : delta_reduces e e') ",
                    "(_hceil : Eq Nat (bvar_ceiling e) Nat.zero) (hcf : const_free e) => ",
                    "delta_step_head_none_absurd_type (red_def the_red_env) e e' ",
                    "(beta_reduces_bd e e') ",
                    "(const_free_head_const_name_none e hcf) ",
                    "(delta_reduces_to_step e e' hd)) ",
                    "hstep"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A single FULL whnf_step (the union beta_reduces ∪ delta_reduces) out of a bvar-free ",
                "const-free term is an IOTA-FREE beta_reduces_bd step: whnf_step e e' -> ",
                "bvar_ceiling e = 0 -> const_free e -> beta_reduces_bd e e'. whnf_step.rec ",
                "(promoted-parameter shape, motive over the major only); the beta leg forwards to ",
                "beta_reduces_to_bd_cf, the delta leg is VACUOUS on a const-free term ",
                "(delta_reduces e e' carries a delta_step over the_red_env, and a const-free head ",
                "forces kexpr_const_name (kapp_fn e) = none, so delta_step_head_none_absurd_type ",
                "discharges it). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "whnf_step.rec".to_string(),
                "beta_reduces".to_string(),
                "beta_reduces_to_bd_cf".to_string(),
                "beta_reduces_bd".to_string(),
                "bvar_ceiling".to_string(),
                "const_free".to_string(),
                "delta_reduces".to_string(),
                "delta_reduces_to_step".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "const_free_head_const_name_none".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// `whnf_terminates_well_typed` — the retired census axiom, now a
    /// `DerivedProved` theorem. `beta_bd_acc.rec` on the landed
    /// `beta_bd_sn_has_type` accessibility witness, with the measure motive
    /// `bvar_ceiling e = 0 -> const_free e -> whnf_acc e`; at each accessible node
    /// `whnf_acc.intro` demands accessibility of every `whnf_step` reduct, which
    /// `whnf_step_to_bd_cf` turns into a `beta_reduces_bd` reduct so the
    /// per-reduct IH applies (threading `beta_bd_step_preserves_ceiling_zero` for
    /// bvar-freeness and `const_free_preserved_bd` for const-freeness).
    fn add_wt_theorem(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "whnf_terminates_well_typed".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), has_type e T -> terminates_whnf e"
                .to_string(),
            value_src: Some(whnf_terminates_well_typed_proof()),
            is_axiom: false,
            description: concat!(
                "WHNF reduction terminates on well-typed expressions: has_type e T -> ",
                "terminates_whnf e (= whnf_acc e, accessibility under the FULL whnf_step = ",
                "beta_reduces ∪ delta_reduces union, beta_reduces itself carrying the iota arm). ",
                "RETIRED census axiom, now a genuine zero-domain-axiom theorem. beta_bd_acc.rec on ",
                "the landed beta_bd_sn_has_type witness with motive bvar_ceiling e = 0 -> ",
                "const_free e -> whnf_acc e; whnf_acc.intro demands accessibility of every whnf_step ",
                "reduct, whnf_step_to_bd_cf turns each into a beta_reduces_bd reduct (the δ and ι ",
                "legs are vacuous on the bvar-free const-free typable fragment) so the per-reduct IH ",
                "applies, threading beta_bd_step_preserves_ceiling_zero (bvar-freeness) and ",
                "const_free_preserved_bd (const-freeness). Bvar/const-freeness of typable terms come ",
                "from typable_bvar_ceiling_zero / typable_const_free. Kernel-checked port of ",
                "scratch/aristotle-typed-sn/TypedSn.lean Part 1 (whnf_terminates_well_typed, 0 sorry, ",
                "#print axioms = propext + Quot.sound). HONEST SCOPE: this discharges SN for the ",
                "spec's ACTUAL has_type = the context-free Typing fragment, which is DEGENERATE (no ",
                "var/const rule ⇒ constant lambdas, no δ/ι) — a genuine proof of the axiom AS STATED, ",
                "NOT a claim of full dependent-CIC SN (that needs a var rule + a Tait-Girard ",
                "reducibility-candidate model, the isolated Gödel floor, a SEPARATE statement). ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "has_type".to_string(),
                "Typing".to_string(),
                "terminates_whnf".to_string(),
                "whnf_acc".to_string(),
                "whnf_acc.intro".to_string(),
                "whnf_step".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_bd_acc".to_string(),
                "beta_bd_acc.rec".to_string(),
                "beta_bd_sn_has_type".to_string(),
                "typable_bvar_ceiling_zero".to_string(),
                "typable_const_free".to_string(),
                "whnf_step_to_bd_cf".to_string(),
                "beta_bd_step_preserves_ceiling_zero".to_string(),
                "const_free_preserved_bd".to_string(),
                "bvar_ceiling".to_string(),
                "const_free".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `beta_reduces_to_bd_cf`. `beta_reduces.rec` (full
/// index-motive shape) with motive
/// `bvar_ceiling e = 0 -> const_free e -> beta_reduces_bd e e'` (14 arms). The
/// arm order matches the `beta_reduces` constructor order (beta, app_left,
/// app_right, lam_ty, lam_body, pi_dom, pi_cod, forall_congr_dom,
/// forall_congr_cod, zeta, let_ty, let_val, let_body, iota).
fn beta_reduces_to_bd_cf_proof() -> String {
    concat!(
        "fun (s : KExpr) (t : KExpr) (hst : beta_reduces s t) => ",
        "beta_reduces.rec ",
        "(fun (e : KExpr) (e' : KExpr) (_ : beta_reduces e e') => ",
        "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> beta_reduces_bd e e') ",
        // beta A body arg : the head redex; maps straight to beta_reduces_bd.beta.
        "(fun (A : KExpr) (body : KExpr) (arg : KExpr) ",
        "(_hc : Eq Nat (bvar_ceiling (KExpr.app (KExpr.lam A body) arg)) Nat.zero) ",
        "(_hcf : const_free (KExpr.app (KExpr.lam A body) arg)) => ",
        "beta_reduces_bd.beta A body arg) ",
        // app_left f f' a
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
        "(_hstep : beta_reduces f f') ",
        "(ih : Eq Nat (bvar_ceiling f) Nat.zero -> const_free f -> beta_reduces_bd f f') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ",
        "(hcf : const_free (KExpr.app f a)) => ",
        "beta_reduces_bd.app_left f f' a ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hc) ",
        "(AndType.left (const_free f) (const_free a) hcf))) ",
        // app_right f a a'
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hstep : beta_reduces a a') ",
        "(ih : Eq Nat (bvar_ceiling a) Nat.zero -> const_free a -> beta_reduces_bd a a') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ",
        "(hcf : const_free (KExpr.app f a)) => ",
        "beta_reduces_bd.app_right f a a' ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) hc) ",
        "(AndType.right (const_free f) (const_free a) hcf))) ",
        // lam_ty ty ty' body
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
        "(_hstep : beta_reduces ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> beta_reduces_bd ty ty') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) ",
        "(hcf : const_free (KExpr.lam ty body)) => ",
        "beta_reduces_bd.lam_ty ty ty' body ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) (bvar_ceiling body) hc) ",
        "(AndType.left (const_free ty) (const_free body) hcf))) ",
        // lam_body ty body body'
        "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hstep : beta_reduces body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> beta_reduces_bd body body') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) ",
        "(hcf : const_free (KExpr.lam ty body)) => ",
        "beta_reduces_bd.lam_body ty body body' ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling ty) (bvar_ceiling body) hc) ",
        "(AndType.right (const_free ty) (const_free body) hcf))) ",
        // pi_dom dom dom' body
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hstep : beta_reduces dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> const_free dom -> beta_reduces_bd dom dom') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.pi dom body)) => ",
        "beta_reduces_bd.pi_dom dom dom' body ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) hc) ",
        "(AndType.left (const_free dom) (const_free body) hcf))) ",
        // pi_cod dom body body'
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hstep : beta_reduces body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> beta_reduces_bd body body') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.pi dom body)) => ",
        "beta_reduces_bd.pi_cod dom body body' ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) hc) ",
        "(AndType.right (const_free dom) (const_free body) hcf))) ",
        // forall_congr_dom dom dom' body — forall_ is the reducible pi alias.
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hstep : beta_reduces dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> const_free dom -> beta_reduces_bd dom dom') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.forall_ dom body)) => ",
        "beta_reduces_bd.forall_congr_dom dom dom' body ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) hc) ",
        "(AndType.left (const_free dom) (const_free body) hcf))) ",
        // forall_congr_cod dom body body'
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hstep : beta_reduces body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> beta_reduces_bd body body') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.forall_ dom body)) => ",
        "beta_reduces_bd.forall_congr_cod dom body body' ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) hc) ",
        "(AndType.right (const_free dom) (const_free body) hcf))) ",
        // zeta ty val body — the genuine let_ head contraction; maps straight to
        // beta_reduces_bd.zeta (identical contractum instantiate body val).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(_hc : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(_hcf : const_free (KExpr.let_ ty val body)) => ",
        "beta_reduces_bd.zeta ty val body) ",
        // let_ty ty ty' val body — plain congruence; triple splits
        // (bvar_ceiling (let_ ty val body) = add (ceil ty) (add (ceil val) (ceil body)),
        // const_free (let_ ty val body) = AndType cf_ty (AndType cf_val cf_body)).
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
        "(_hstep : beta_reduces ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> beta_reduces_bd ty ty') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "beta_reduces_bd.let_ty ty ty' val body ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hc) ",
        "(AndType.left (const_free ty) (AndType (const_free val) (const_free body)) hcf))) ",
        // let_val ty val val' body
        "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
        "(_hstep : beta_reduces val val') ",
        "(ih : Eq Nat (bvar_ceiling val) Nat.zero -> const_free val -> beta_reduces_bd val val') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "beta_reduces_bd.let_val ty val val' body ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hc)) ",
        "(AndType.left (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf)))) ",
        // let_body ty val body body' — now a PLAIN one-position congruence (the
        // old bundled instantiate premise is gone; zeta carries the contraction).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hstep : beta_reduces body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> beta_reduces_bd body body') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "beta_reduces_bd.let_body ty val body body' ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hc)) ",
        "(AndType.right (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf)))) ",
        // iota e e' : VACUOUS on a const-free term.
        "(fun (e : KExpr) (e' : KExpr) (hir : iota_reduces e e') ",
        "(_hc : Eq Nat (bvar_ceiling e) Nat.zero) (hcf : const_free e) => ",
        "iota_step_head_none_absurd_type (red_rec the_red_env) e e' ",
        "(beta_reduces_bd e e') ",
        "(const_free_head_const_name_none e hcf) ",
        "(iota_reduces_to_step e e' hir)) ",
        // proj ps pidx sub sub' (proj/lit rung): scrutinee congruence maps straight
        // to beta_reduces_bd.proj; bvar_ceiling/const_free reduce through proj (defeq).
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hstep : beta_reduces sub sub') ",
        "(ih : Eq Nat (bvar_ceiling sub) Nat.zero -> const_free sub -> beta_reduces_bd sub sub') ",
        "(hc : Eq Nat (bvar_ceiling (KExpr.proj ps pidx sub)) Nat.zero) ",
        "(hcf : const_free (KExpr.proj ps pidx sub)) => ",
        "beta_reduces_bd.proj ps pidx sub sub' (ih hc hcf)) ",
        // indices + major
        "s t hst"
    )
    .to_string()
}

/// Closed proof term for `whnf_terminates_well_typed` (the retired census
/// axiom). `beta_bd_acc.rec` on `beta_bd_sn_has_type`, transporting
/// accessibility from `beta_reduces_bd` to the full `whnf_step` union.
fn whnf_terminates_well_typed_proof() -> String {
    concat!(
        "fun (e0 : KExpr) (T0 : KExpr) (ht : has_type e0 T0) => ",
        "beta_bd_acc.rec ",
        "(fun (e : KExpr) (_ : beta_bd_acc e) => ",
        "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> whnf_acc e) ",
        // minor: at an accessible node e, with per-reduct IH ih, build whnf_acc e.
        "(fun (e : KExpr) ",
        "(_h : forall (e' : KExpr), beta_reduces_bd e e' -> beta_bd_acc e') ",
        "(ih : forall (e' : KExpr), beta_reduces_bd e e' -> ",
        "Eq Nat (bvar_ceiling e') Nat.zero -> const_free e' -> whnf_acc e') ",
        "(hceil : Eq Nat (bvar_ceiling e) Nat.zero) ",
        "(hcf : const_free e) => ",
        "whnf_acc.intro e ",
        "(fun (y : KExpr) (hstep : whnf_step e y) => ",
        "(fun (hbd : beta_reduces_bd e y) => ",
        "ih y hbd ",
        "(beta_bd_step_preserves_ceiling_zero e y hbd hceil) ",
        "(const_free_preserved_bd e y hbd hceil hcf)) ",
        "(whnf_step_to_bd_cf e y hstep hceil hcf))) ",
        // motive indices + majors
        "e0 (beta_bd_sn_has_type e0 T0 ht) ",
        "(typable_bvar_ceiling_zero e0 T0 ht) (typable_const_free e0 T0 ht)"
    )
    .to_string()
}

#[cfg(test)]
#[path = "whnf_terminates_well_typed_tests.rs"]
mod whnf_terminates_well_typed_tests;
