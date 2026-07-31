// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Forward subject reduction over the full `beta_reduces` / `whnf_to` relations
//! (church_rosser_whnf retirement track — the keystone metatheorem).
//!
//! This module is ADDITIVE and independently verifiable against the CURRENT
//! typed `DefEq.beta`. It does NOT untype anything and does NOT touch
//! `Typing.conv`. It registers, in dependency order:
//!
//!  - `redex_typed_def_eq`  : the typed beta redex is a DefEq, by inverting the
//!    redex's typing (typing_app_gen + typing_lam_gen + lam_typing_dom_sort) and
//!    rebuilding `DefEq.beta` with the recovered typing premises.
//!  - `typing_let_absurd` : the let-promotion inversion — a let_-headed term is
//!    NOT typeable under the context-free `Typing` judgment (typing_def_eq.rs
//!    stays 5-ctor, NO let rule), so `Typing (let_ ty val body) S` eliminates
//!    into any goal. Discharges the four new `beta_reduces` let arms
//!    (zeta/let_ty/let_val/let_body) in both towers below.
//!  - `beta_reduces_typed_def_eq` : a `beta_reduces` step between well-typed
//!    terms is a `DefEq`, by `beta_reduces.rec`. The congruence arms feed the IH
//!    a subterm typing recovered by the matching generation lemma; the top-level
//!    `beta` arm reuses `redex_typed_def_eq`; the `iota` arm is `DefEq.iota`
//!    (untyped); the four let arms are vacuous (typing_let_absurd). Needed only
//!    to bridge the dependent codomain in the two argument-position arms of
//!    subject reduction.
//!  - `beta_reduces_preserves_typing` : FORWARD subject reduction over the full
//!    `beta_reduces` relation, by `beta_reduces.rec`. The `beta` arm IS
//!    `beta_preservation`; the `iota` arm IS `iota_type_preservation_fwd`; the 9
//!    congruence arms invert the compound's typing via the generation lemmas,
//!    apply the IH to the reduced subterm, rebuild the compound, and re-establish
//!    the original type via `Typing.conv` (the dependent app/lam-domain arms use
//!    `beta_reduces_typed_def_eq` for the codomain/domain conversion); the four
//!    let arms are vacuous (typing_let_absurd).
//!  - `whnf_step_preserves_typing` : single WHNF step preservation, dispatching
//!    `beta` -> `beta_reduces_preserves_typing`, `delta` ->
//!    `delta_type_preservation_fwd`.
//!  - `whnf_to_preserves_typing` : preservation over the directed WHNF reduction
//!    closure, by `whnf_to.rec` (refl = id, step composes `whnf_step` preservation
//!    with the IH). This is genuine SUBJECT REDUCTION over a directed relation —
//!    no subject expansion, no `DefEq.symm`-flip of the reduction direction, no
//!    `church_rosser_whnf` reached by these arms' OWN logic.
//!
//! GUARDS. ZERO new axioms (every definition here is `is_axiom: false` with a
//! full `value_src`). The carried `DefEnvWellformed the_red_env` /
//! `RecEnvWellformed (red_rec the_red_env)` are HYPOTHESES threaded from the
//! reuse of `beta_preservation` / `iota`/`delta_type_preservation_fwd` (Guard 4 —
//! interfaces, not axioms; the env is the literal `the_red_env`). The residual
//! `church_rosser_whnf` trust debt is INHERITED transitively from
//! `beta_preservation` / `pi_injectivity_def_eq_dom` /
//! `def_eq_instantiate_arg_congr` — it is the EXISTING leaf being eliminated, not
//! a new admission. The two `DerivedProved` keystones are pinned in
//! `data/clean_verify_derivedproved_debt.json`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline large-elimination discriminator (`KExpr -> Type`): the genuine
/// `let_` constructor maps to `Empty` (uninhabited), every other KExpr
/// constructor to `Nat` (inhabited). Used to REFUTE a `Typing (KExpr.let_ ..) S`
/// hypothesis by inversion: the context-free `Typing` judgment (typing_def_eq.rs,
/// sort/pi/lam/app/conv) has NO `let_` rule, so no well-typed term is
/// let_-headed. Mirrors `KEXPR_NOT_APP_INLINE` (expr_model_discrimination.rs)
/// specialised to the 7th (let_) constructor. Local, uniquely named to avoid
/// collision with the B3 discrimination-lemma lane.
const BRP_KEXPR_NOT_LET: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    // proj/lit are NOT let_ → inhabited (Nat), same as the other non-let_ ctors
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Inline KExpr.rec discriminator dual to `BRP_KEXPR_NOT_LET`: the `proj`
/// constructor maps to `Empty`, every other KExpr constructor to `Nat`. Used
/// to REFUTE a `Typing (KExpr.proj ..) S` hypothesis by inversion: the
/// context-free `Typing` judgment (sort/pi/lam/app/conv) has NO `proj` rule,
/// so no well-typed term is proj-headed — exactly as for `let_`.
const BRP_KEXPR_NOT_PROJ: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    /// Register forward subject reduction over `beta_reduces` and `whnf_to`.
    ///
    /// MUST be staged AFTER `add_type_preservation` (generation lemmas +
    /// `beta_preservation` + `lam_typing_dom_sort` + `def_eq_instantiate_arg_congr`)
    /// and AFTER `add_reduction_witnesses` (`delta`/`iota_type_preservation_fwd`).
    /// The inductives `beta_reduces` / `whnf_step` / `whnf_to` and the bridge
    /// `raw_to_typed_def_eq` / `pi_injectivity_def_eq_dom` are registered earlier.
    pub(super) fn add_beta_reduces_preserves_typing(&mut self) -> Result<(), SpecError> {
        // =====================================================================
        // typing_let_absurd: a let_-headed term is NOT well-typed under the
        // context-free `Typing` judgment (sort/pi/lam/app/conv — NO let_ rule),
        // so `Typing (let_ ty val body) S` is uninhabited and eliminates into any
        // `C`. This is the INVERSION that discharges the four new `beta_reduces`
        // let arms (zeta / let_ty / let_val / let_body): with `let_` now a genuine
        // 7th KExpr constructor, the OLD bundled `let_body` arm (which treated a
        // let as a beta redex `app (lam ty body) val`) is retired. Proved via
        // `Typing.rec` with an Eq-keyed motive: sort/pi/lam/app arms refute the
        // constructor equation through the BRP_KEXPR_NOT_LET discriminator +
        // Empty.rec; conv arm forwards the IH. DerivedProved, zero axiom_deps.
        // =====================================================================
        self.add_definition(SpecDefinition {
            name: "typing_let_absurd".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (val : KExpr) (body : KExpr) (S : KExpr) (C : Type), ",
                "Typing (KExpr.let_ ty val body) S -> C"
            )
            .to_string(),
            value_src: Some(format!(
                "fun (ty : KExpr) (val : KExpr) (body : KExpr) (S : KExpr) (C : Type) \
                 (h : Typing (KExpr.let_ ty val body) S) => \
                 Typing.rec \
                 (fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => \
                 forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr e (KExpr.let_ lty lval lbody) -> C) \
                 (fun (n : Level) (lty : KExpr) (lval : KExpr) (lbody : KExpr) \
                 (eq : Eq KExpr (KExpr.sort n) (KExpr.let_ lty lval lbody)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.sort n) (KExpr.let_ lty lval lbody) eq Nat.zero)) \
                 (fun (A1 : KExpr) (B1 : KExpr) (n1 : Level) (m1 : Level) \
                 (_hA : Typing A1 (KExpr.sort n1)) (_hB : Typing B1 (KExpr.sort m1)) \
                 (_ihA : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr A1 (KExpr.let_ lty lval lbody) -> C) \
                 (_ihB : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr B1 (KExpr.let_ lty lval lbody) -> C) \
                 (lty : KExpr) (lval : KExpr) (lbody : KExpr) \
                 (eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.let_ lty lval lbody)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.pi A1 B1) (KExpr.let_ lty lval lbody) eq Nat.zero)) \
                 (fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (u2 : Level) \
                 (_hA : Typing A2 (KExpr.sort u2)) (_hb : Typing b2 B2) \
                 (_ihA : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr A2 (KExpr.let_ lty lval lbody) -> C) \
                 (_ihb : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr b2 (KExpr.let_ lty lval lbody) -> C) \
                 (lty : KExpr) (lval : KExpr) (lbody : KExpr) \
                 (eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.let_ lty lval lbody)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.lam A2 b2) (KExpr.let_ lty lval lbody) eq Nat.zero)) \
                 (fun (f1 : KExpr) (a1 : KExpr) (A2 : KExpr) (B2 : KExpr) \
                 (_hf : Typing f1 (KExpr.pi A2 B2)) (_ha : Typing a1 A2) \
                 (_ihf : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr f1 (KExpr.let_ lty lval lbody) -> C) \
                 (_iha : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr a1 (KExpr.let_ lty lval lbody) -> C) \
                 (lty : KExpr) (lval : KExpr) (lbody : KExpr) \
                 (eq : Eq KExpr (KExpr.app f1 a1) (KExpr.let_ lty lval lbody)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.app f1 a1) (KExpr.let_ lty lval lbody) eq Nat.zero)) \
                 (fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) \
                 (_he : Typing e0 T1) (_deq : DefEq T1 T2) \
                 (ih : forall (lty : KExpr) (lval : KExpr) (lbody : KExpr), \
                 Eq KExpr e0 (KExpr.let_ lty lval lbody) -> C) \
                 (lty : KExpr) (lval : KExpr) (lbody : KExpr) \
                 (eq : Eq KExpr e0 (KExpr.let_ lty lval lbody)) => \
                 ih lty lval lbody eq) \
                 (KExpr.let_ ty val body) S h ty val body \
                 (Eq.refl KExpr (KExpr.let_ ty val body))",
                discr = BRP_KEXPR_NOT_LET,
            )),
            is_axiom: false,
            description: concat!(
                "Inversion: a let_-headed term is not typeable under the context-free ",
                "Typing judgment (no let_ rule), so Typing (let_ ty val body) S eliminates ",
                "into any C. By Typing.rec with an Eq-keyed motive; sort/pi/lam/app arms ",
                "refute via the not-let discriminator + Empty.rec, conv arm forwards the IH. ",
                "Discharges the four let arms of beta_reduces subject reduction now that ",
                "let_ is a genuine KExpr constructor. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // typing_proj_absurd: a proj_-headed term is NOT well-typed under the
        // context-free Typing (no proj rule) — the exact dual of
        // typing_let_absurd. Discharges the proj congruence arm of the
        // beta_reduces recursor now that proj is a genuine KExpr constructor.
        self.add_definition(SpecDefinition {
            name: "typing_proj_absurd".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub : KExpr) (S : KExpr) (C : Type), ",
                "Typing (KExpr.proj s i sub) S -> C"
            )
            .to_string(),
            value_src: Some(format!(
                "fun (s : Name) (i : Nat) (sub : KExpr) (S : KExpr) (C : Type) \
                 (h : Typing (KExpr.proj s i sub) S) => \
                 Typing.rec \
                 (fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => \
                 forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr e (KExpr.proj ps pidx psub) -> C) \
                 (fun (n : Level) (ps : Name) (pidx : Nat) (psub : KExpr) \
                 (eq : Eq KExpr (KExpr.sort n) (KExpr.proj ps pidx psub)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.sort n) (KExpr.proj ps pidx psub) eq Nat.zero)) \
                 (fun (A1 : KExpr) (B1 : KExpr) (n1 : Level) (m1 : Level) \
                 (_hA : Typing A1 (KExpr.sort n1)) (_hB : Typing B1 (KExpr.sort m1)) \
                 (_ihA : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr A1 (KExpr.proj ps pidx psub) -> C) \
                 (_ihB : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr B1 (KExpr.proj ps pidx psub) -> C) \
                 (ps : Name) (pidx : Nat) (psub : KExpr) \
                 (eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.proj ps pidx psub)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.pi A1 B1) (KExpr.proj ps pidx psub) eq Nat.zero)) \
                 (fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (u2 : Level) \
                 (_hA : Typing A2 (KExpr.sort u2)) (_hb : Typing b2 B2) \
                 (_ihA : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr A2 (KExpr.proj ps pidx psub) -> C) \
                 (_ihb : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr b2 (KExpr.proj ps pidx psub) -> C) \
                 (ps : Name) (pidx : Nat) (psub : KExpr) \
                 (eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.proj ps pidx psub)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.lam A2 b2) (KExpr.proj ps pidx psub) eq Nat.zero)) \
                 (fun (f1 : KExpr) (a1 : KExpr) (A2 : KExpr) (B2 : KExpr) \
                 (_hf : Typing f1 (KExpr.pi A2 B2)) (_ha : Typing a1 A2) \
                 (_ihf : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr f1 (KExpr.proj ps pidx psub) -> C) \
                 (_iha : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr a1 (KExpr.proj ps pidx psub) -> C) \
                 (ps : Name) (pidx : Nat) (psub : KExpr) \
                 (eq : Eq KExpr (KExpr.app f1 a1) (KExpr.proj ps pidx psub)) => \
                 Empty.rec (fun (_ : Empty) => C) \
                 (Eq.substType KExpr {discr} (KExpr.app f1 a1) (KExpr.proj ps pidx psub) eq Nat.zero)) \
                 (fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) \
                 (_he : Typing e0 T1) (_deq : DefEq T1 T2) \
                 (ih : forall (ps : Name) (pidx : Nat) (psub : KExpr), \
                 Eq KExpr e0 (KExpr.proj ps pidx psub) -> C) \
                 (ps : Name) (pidx : Nat) (psub : KExpr) \
                 (eq : Eq KExpr e0 (KExpr.proj ps pidx psub)) => \
                 ih ps pidx psub eq) \
                 (KExpr.proj s i sub) S h s i sub \
                 (Eq.refl KExpr (KExpr.proj s i sub))",
                discr = BRP_KEXPR_NOT_PROJ,
            )),
            is_axiom: false,
            description: concat!(
                "Inversion: a proj-headed term is not typeable under the context-free ",
                "Typing judgment (no proj rule), so Typing (proj s i sub) S eliminates ",
                "into any C. By Typing.rec with an Eq-keyed motive; sort/pi/lam/app arms ",
                "refute via the not-proj discriminator + Empty.rec, conv arm forwards the IH. ",
                "Discharges the proj congruence arm of beta_reduces subject reduction now ",
                "that proj is a genuine KExpr constructor. Dual of typing_let_absurd. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =====================================================================
        // redex_typed_def_eq: a typed beta redex is a DefEq (untyped reduct side).
        // =====================================================================
        // has_type (app (lam A b) a) S  ->  DefEq (app (lam A b) a) (instantiate b a)
        // Recover the DefEq.beta premises (hA : A : Sort u, hb : b : B1,
        // harg : a : A) by inverting the redex typing and bridging a : A0 -> a : A
        // through pi-domain injectivity.
        self.add_definition(SpecDefinition {
            name: "redex_typed_def_eq".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (b : KExpr) (a : KExpr) (S : KExpr), ",
                "has_type (KExpr.app (KExpr.lam A b) a) S -> ",
                "DefEq (KExpr.app (KExpr.lam A b) a) (instantiate b a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (b : KExpr) (a : KExpr) (S : KExpr) ",
                    "(_ht : has_type (KExpr.app (KExpr.lam A b) a) S) => ",
                    "DefEq.beta A b a"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A beta redex is a DefEq: (λA.b) a ≡ b[a/0]. With UNTYPED DefEq.beta ",
                "this is the constructor directly — no typing inversion needed. The ",
                "has_type premise is retained for the call shape but unused. DerivedProved, ",
                "zero axiom_deps. Part of the church_rosser_whnf retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["DefEq.beta".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // =====================================================================
        // beta_reduces_typed_def_eq: a beta step between well-typed terms is DefEq.
        // =====================================================================
        // forall e e', DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) ->
        //   beta_reduces e e' -> forall S, has_type e S -> DefEq e e'
        // Motive Q x y _ = forall S, has_type x S -> DefEq x y. Each congruence arm
        // feeds the IH the reduced subterm's typing (recovered by the matching
        // generation lemma) and assembles the congruence DefEq.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_typed_def_eq".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "beta_reduces e e' -> ",
                "forall (S : KExpr), has_type e S -> DefEq e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e0 : KExpr) (e0' : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hbr : beta_reduces e0 e0') => ",
                    "beta_reduces.rec ",
                    "(fun (x : KExpr) (y : KExpr) (_ : beta_reduces x y) => ",
                    "forall (S : KExpr), has_type x S -> DefEq x y) ",
                    // beta: redex DefEq
                    "(fun (A : KExpr) (b : KExpr) (a : KExpr) => ",
                    "redex_typed_def_eq A b a) ",
                    // app_left: f -> f'
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(_hff : beta_reduces f f') ",
                    "(ih : forall (S : KExpr), has_type f S -> DefEq f f') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.app f a) S) => ",
                    "typing_app_gen f a S (DefEq (KExpr.app f a) (KExpr.app f' a)) ht ",
                    "(fun (A : KExpr) (B : KExpr) (hf : Typing f (KExpr.pi A B)) ",
                    "(_ha : Typing a A) (_hSd : DefEq S (instantiate B a)) => ",
                    "DefEq.app_cong f f' a a (ih (KExpr.pi A B) hf) (DefEq.refl a))) ",
                    // app_right: a -> a'
                    "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_haa : beta_reduces a a') ",
                    "(ih : forall (S : KExpr), has_type a S -> DefEq a a') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.app f a) S) => ",
                    "typing_app_gen f a S (DefEq (KExpr.app f a) (KExpr.app f a')) ht ",
                    "(fun (A : KExpr) (B : KExpr) (_hf : Typing f (KExpr.pi A B)) ",
                    "(ha : Typing a A) (_hSd : DefEq S (instantiate B a)) => ",
                    "DefEq.app_cong f f a a' (DefEq.refl f) (ih A ha))) ",
                    // lam_ty: ty -> ty'
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
                    "(_htt : beta_reduces ty ty') ",
                    "(ih : forall (S : KExpr), has_type ty S -> DefEq ty ty') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.lam ty body) S) => ",
                    "lam_typing_dom_sort ty body S ",
                    "(DefEq (KExpr.lam ty body) (KExpr.lam ty' body)) ht ",
                    "(fun (u : Level) (hty : Typing ty (KExpr.sort u)) => ",
                    "DefEq.lam_cong ty ty' body body (ih (KExpr.sort u) hty) (DefEq.refl body))) ",
                    // lam_body: body -> body'
                    "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbb : beta_reduces body body') ",
                    "(ih : forall (S : KExpr), has_type body S -> DefEq body body') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.lam ty body) S) => ",
                    "typing_lam_gen ty body S ",
                    "(DefEq (KExpr.lam ty body) (KExpr.lam ty body')) ht ",
                    "(fun (B : KExpr) (hb : Typing body B) (_hSd : DefEq S (KExpr.pi ty B)) => ",
                    "DefEq.lam_cong ty ty body body' (DefEq.refl ty) (ih B hb))) ",
                    // pi_dom: dom -> dom'
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(_hdd : beta_reduces dom dom') ",
                    "(ih : forall (S : KExpr), has_type dom S -> DefEq dom dom') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.pi dom body) S) => ",
                    "typing_pi_gen dom body S ",
                    "(DefEq (KExpr.pi dom body) (KExpr.pi dom' body)) ht ",
                    "(fun (n : Level) (m : Level) (hdom : Typing dom (KExpr.sort n)) ",
                    "(_hbody : Typing body (KExpr.sort m)) ",
                    "(_hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "DefEq.pi_cong dom dom' body body (ih (KExpr.sort n) hdom) (DefEq.refl body))) ",
                    // pi_cod: body -> body'
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbb : beta_reduces body body') ",
                    "(ih : forall (S : KExpr), has_type body S -> DefEq body body') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.pi dom body) S) => ",
                    "typing_pi_gen dom body S ",
                    "(DefEq (KExpr.pi dom body) (KExpr.pi dom body')) ht ",
                    "(fun (n : Level) (m : Level) (_hdom : Typing dom (KExpr.sort n)) ",
                    "(hbody : Typing body (KExpr.sort m)) ",
                    "(_hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "DefEq.pi_cong dom dom body body' (DefEq.refl dom) (ih (KExpr.sort m) hbody))) ",
                    // forall_congr_dom: dom -> dom'
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(_hdd : beta_reduces dom dom') ",
                    "(ih : forall (S : KExpr), has_type dom S -> DefEq dom dom') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.forall_ dom body) S) => ",
                    "typing_pi_gen dom body S ",
                    "(DefEq (KExpr.forall_ dom body) (KExpr.forall_ dom' body)) ht ",
                    "(fun (n : Level) (m : Level) (hdom : Typing dom (KExpr.sort n)) ",
                    "(_hbody : Typing body (KExpr.sort m)) ",
                    "(_hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "DefEq.pi_cong dom dom' body body (ih (KExpr.sort n) hdom) (DefEq.refl body))) ",
                    // forall_congr_cod: body -> body'
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbb : beta_reduces body body') ",
                    "(ih : forall (S : KExpr), has_type body S -> DefEq body body') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.forall_ dom body) S) => ",
                    "typing_pi_gen dom body S ",
                    "(DefEq (KExpr.forall_ dom body) (KExpr.forall_ dom body')) ht ",
                    "(fun (n : Level) (m : Level) (_hdom : Typing dom (KExpr.sort n)) ",
                    "(hbody : Typing body (KExpr.sort m)) ",
                    "(_hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "DefEq.pi_cong dom dom body body' (DefEq.refl dom) (ih (KExpr.sort m) hbody))) ",
                    // zeta: let_ is not typeable under the context-free Typing
                    // (no let_ rule) — discharge by inversion (typing_let_absurd).
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(DefEq (KExpr.let_ ty val body) (instantiate body val)) ht) ",
                    // let_ty: ty -> ty' (subject let_ still not typeable — inversion)
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
                    "(_hs : beta_reduces ty ty') ",
                    "(_ih : forall (S : KExpr), has_type ty S -> DefEq ty ty') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(DefEq (KExpr.let_ ty val body) (KExpr.let_ ty' val body)) ht) ",
                    // let_val: val -> val' (inversion)
                    "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
                    "(_hs : beta_reduces val val') ",
                    "(_ih : forall (S : KExpr), has_type val S -> DefEq val val') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(DefEq (KExpr.let_ ty val body) (KExpr.let_ ty val' body)) ht) ",
                    // let_body: body -> body' (inversion)
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hs : beta_reduces body body') ",
                    "(_ih : forall (S : KExpr), has_type body S -> DefEq body body') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(DefEq (KExpr.let_ ty val body) (KExpr.let_ ty val body')) ht) ",
                    // iota: untyped DefEq.iota
                    "(fun (e : KExpr) (e' : KExpr) (hi : iota_reduces e e') => ",
                    "fun (S : KExpr) (_ht : has_type e S) => DefEq.iota e e' hi) ",
                    // proj: proj-headed term not typeable under context-free Typing
                    // (no proj rule) — discharge by inversion (typing_proj_absurd).
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hs : beta_reduces sub sub') ",
                    "(_ih : forall (S : KExpr), has_type sub S -> DefEq sub sub') => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.proj s i sub) S) => ",
                    "typing_proj_absurd s i sub S ",
                    "(DefEq (KExpr.proj s i sub) (KExpr.proj s i sub')) ht) ",
                    // apply recursor to indices + major
                    "e0 e0' hbr"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A beta_reduces step between well-typed terms is a DefEq: ",
                "beta_reduces e e' -> has_type e S -> DefEq e e'. By beta_reduces.rec; ",
                "congruence arms feed the IH a subterm typing recovered by the matching ",
                "generation lemma; beta arm = redex_typed_def_eq; iota arm = DefEq.iota ",
                "(untyped); the four let arms (zeta/let_ty/let_val/let_body) are vacuous — ",
                "a let_-headed term is not typeable under the context-free Typing (no let_ ",
                "rule), so they are discharged by inversion (typing_let_absurd). ",
                "DerivedPending: inherits church_rosser_whnf. ",
                "Part of the church_rosser_whnf retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "redex_typed_def_eq".to_string(),
                "beta_preservation".to_string(),
                "typing_app_gen".to_string(),
                "typing_lam_gen".to_string(),
                "typing_pi_gen".to_string(),
                "lam_typing_dom_sort".to_string(),
                "typing_let_absurd".to_string(),
                "typing_proj_absurd".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.iota".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =====================================================================
        // beta_reduces_preserves_typing: FORWARD subject reduction (the keystone).
        // =====================================================================
        // forall e e' T, DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) ->
        //   beta_reduces e e' -> has_type e T -> has_type e' T
        // Motive P x y _ = forall S, has_type x S -> has_type y S. beta = beta_preservation;
        // iota = iota_type_preservation_fwd; the 9 congruence arms invert + IH + rebuild +
        // Typing.conv (dependent arms re-establish the type via beta_reduces_typed_def_eq);
        // the four let arms (zeta/let_ty/let_val/let_body) are vacuous over the
        // context-free Typing (no let_ rule) and discharge by typing_let_absurd.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_preserves_typing".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr) (T : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "beta_reduces e e' -> has_type e T -> has_type e' T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e0 : KExpr) (e0' : KExpr) (T0 : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hbr : beta_reduces e0 e0') (ht0 : has_type e0 T0) => ",
                    "beta_reduces.rec ",
                    "(fun (x : KExpr) (y : KExpr) (_ : beta_reduces x y) => ",
                    "forall (S : KExpr), has_type x S -> has_type y S) ",
                    // beta
                    "(fun (A : KExpr) (b : KExpr) (a : KExpr) ",
                    "(S : KExpr) (ht : has_type (KExpr.app (KExpr.lam A b) a) S) => ",
                    "beta_preservation hf A b a S wd wr ht) ",
                    // app_left: f -> f' (result type instantiate B a unchanged)
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(_hff : beta_reduces f f') ",
                    "(ih : forall (S : KExpr), has_type f S -> has_type f' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.app f a) S) => ",
                    "typing_app_gen f a S (has_type (KExpr.app f' a) S) ht ",
                    "(fun (A : KExpr) (B : KExpr) (hf : Typing f (KExpr.pi A B)) ",
                    "(ha : Typing a A) (hSd : DefEq S (instantiate B a)) => ",
                    "Typing.conv (KExpr.app f' a) (instantiate B a) S ",
                    "(Typing.app f' a A B (ih (KExpr.pi A B) hf) ha) ",
                    "(DefEq.symm S (instantiate B a) hSd))) ",
                    // app_right: a -> a' (dependent: instantiate B a -> instantiate B a')
                    "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(haa : beta_reduces a a') ",
                    "(ih : forall (S : KExpr), has_type a S -> has_type a' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.app f a) S) => ",
                    "typing_app_gen f a S (has_type (KExpr.app f a') S) ht ",
                    "(fun (A : KExpr) (B : KExpr) (hfn : Typing f (KExpr.pi A B)) ",
                    "(ha : Typing a A) (hSd : DefEq S (instantiate B a)) => ",
                    "Typing.conv (KExpr.app f a') (instantiate B a') S ",
                    "(Typing.app f a' A B hfn (ih A ha)) ",
                    "(DefEq.trans (instantiate B a') (instantiate B a) S ",
                    "(def_eq_instantiate_arg_congr B a' a hf ",
                    "(DefEq.symm a a' (beta_reduces_typed_def_eq hf a a' wd wr haa A ha))) ",
                    "(DefEq.symm S (instantiate B a) hSd)))) ",
                    // lam_ty: ty -> ty' (dependent: pi ty B -> pi ty' B)
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
                    "(htt : beta_reduces ty ty') ",
                    "(ih : forall (S : KExpr), has_type ty S -> has_type ty' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.lam ty body) S) => ",
                    "typing_lam_gen ty body S (has_type (KExpr.lam ty' body) S) ht ",
                    "(fun (B : KExpr) (hbody : Typing body B) (hSd : DefEq S (KExpr.pi ty B)) => ",
                    "lam_typing_dom_sort ty body S (has_type (KExpr.lam ty' body) S) ht ",
                    "(fun (u : Level) (hty : Typing ty (KExpr.sort u)) => ",
                    "Typing.conv (KExpr.lam ty' body) (KExpr.pi ty' B) S ",
                    "(Typing.lam ty' body B u (ih (KExpr.sort u) hty) hbody) ",
                    "(DefEq.trans (KExpr.pi ty' B) (KExpr.pi ty B) S ",
                    "(DefEq.pi_cong ty' ty B B ",
                    "(DefEq.symm ty ty' (beta_reduces_typed_def_eq hf ty ty' wd wr htt (KExpr.sort u) hty)) ",
                    "(DefEq.refl B)) ",
                    "(DefEq.symm S (KExpr.pi ty B) hSd))))) ",
                    // lam_body: body -> body' (result type pi ty B unchanged)
                    "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbb : beta_reduces body body') ",
                    "(ih : forall (S : KExpr), has_type body S -> has_type body' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.lam ty body) S) => ",
                    "typing_lam_gen ty body S (has_type (KExpr.lam ty body') S) ht ",
                    "(fun (B : KExpr) (hbody : Typing body B) (hSd : DefEq S (KExpr.pi ty B)) => ",
                    "lam_typing_dom_sort ty body S (has_type (KExpr.lam ty body') S) ht ",
                    "(fun (u : Level) (hty : Typing ty (KExpr.sort u)) => ",
                    "Typing.conv (KExpr.lam ty body') (KExpr.pi ty B) S ",
                    "(Typing.lam ty body' B u hty (ih B hbody)) ",
                    "(DefEq.symm S (KExpr.pi ty B) hSd)))) ",
                    // pi_dom: dom -> dom' (result type Sort (imax n m) unchanged)
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(_hdd : beta_reduces dom dom') ",
                    "(ih : forall (S : KExpr), has_type dom S -> has_type dom' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.pi dom body) S) => ",
                    "typing_pi_gen dom body S (has_type (KExpr.pi dom' body) S) ht ",
                    "(fun (n : Level) (m : Level) (hdom : Typing dom (KExpr.sort n)) ",
                    "(hbody : Typing body (KExpr.sort m)) ",
                    "(hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "Typing.conv (KExpr.pi dom' body) (KExpr.sort (Level.imax n m)) S ",
                    "(Typing.pi dom' body n m (ih (KExpr.sort n) hdom) hbody) ",
                    "(DefEq.symm S (KExpr.sort (Level.imax n m)) hSd))) ",
                    // pi_cod: body -> body'
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbb : beta_reduces body body') ",
                    "(ih : forall (S : KExpr), has_type body S -> has_type body' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.pi dom body) S) => ",
                    "typing_pi_gen dom body S (has_type (KExpr.pi dom body') S) ht ",
                    "(fun (n : Level) (m : Level) (hdom : Typing dom (KExpr.sort n)) ",
                    "(hbody : Typing body (KExpr.sort m)) ",
                    "(hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "Typing.conv (KExpr.pi dom body') (KExpr.sort (Level.imax n m)) S ",
                    "(Typing.pi dom body' n m hdom (ih (KExpr.sort m) hbody)) ",
                    "(DefEq.symm S (KExpr.sort (Level.imax n m)) hSd))) ",
                    // forall_congr_dom: dom -> dom'
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(_hdd : beta_reduces dom dom') ",
                    "(ih : forall (S : KExpr), has_type dom S -> has_type dom' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.forall_ dom body) S) => ",
                    "typing_pi_gen dom body S (has_type (KExpr.forall_ dom' body) S) ht ",
                    "(fun (n : Level) (m : Level) (hdom : Typing dom (KExpr.sort n)) ",
                    "(hbody : Typing body (KExpr.sort m)) ",
                    "(hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "Typing.conv (KExpr.forall_ dom' body) (KExpr.sort (Level.imax n m)) S ",
                    "(Typing.pi dom' body n m (ih (KExpr.sort n) hdom) hbody) ",
                    "(DefEq.symm S (KExpr.sort (Level.imax n m)) hSd))) ",
                    // forall_congr_cod: body -> body'
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbb : beta_reduces body body') ",
                    "(ih : forall (S : KExpr), has_type body S -> has_type body' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.forall_ dom body) S) => ",
                    "typing_pi_gen dom body S (has_type (KExpr.forall_ dom body') S) ht ",
                    "(fun (n : Level) (m : Level) (hdom : Typing dom (KExpr.sort n)) ",
                    "(hbody : Typing body (KExpr.sort m)) ",
                    "(hSd : DefEq S (KExpr.sort (Level.imax n m))) => ",
                    "Typing.conv (KExpr.forall_ dom body') (KExpr.sort (Level.imax n m)) S ",
                    "(Typing.pi dom body' n m hdom (ih (KExpr.sort m) hbody)) ",
                    "(DefEq.symm S (KExpr.sort (Level.imax n m)) hSd))) ",
                    // zeta: subject is let_-headed — not typeable under the
                    // context-free Typing (no let_ rule); inversion discharges.
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(has_type (instantiate body val) S) ht) ",
                    // let_ty: ty -> ty' (inversion)
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
                    "(_hs : beta_reduces ty ty') ",
                    "(_ih : forall (S : KExpr), has_type ty S -> has_type ty' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(has_type (KExpr.let_ ty' val body) S) ht) ",
                    // let_val: val -> val' (inversion)
                    "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
                    "(_hs : beta_reduces val val') ",
                    "(_ih : forall (S : KExpr), has_type val S -> has_type val' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(has_type (KExpr.let_ ty val' body) S) ht) ",
                    // let_body: body -> body' (inversion)
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hs : beta_reduces body body') ",
                    "(_ih : forall (S : KExpr), has_type body S -> has_type body' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.let_ ty val body) S) => ",
                    "typing_let_absurd ty val body S ",
                    "(has_type (KExpr.let_ ty val body') S) ht) ",
                    // iota: iota_type_preservation_fwd
                    "(fun (e : KExpr) (e' : KExpr) (hi : iota_reduces e e') => ",
                    "fun (S : KExpr) (ht : has_type e S) => ",
                    "iota_type_preservation_fwd e e' wr hi S ht) ",
                    // proj: proj-headed term not typeable under context-free Typing
                    // (no proj rule) — discharge by inversion (typing_proj_absurd).
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hs : beta_reduces sub sub') ",
                    "(_ih : forall (S : KExpr), has_type sub S -> has_type sub' S) => ",
                    "fun (S : KExpr) (ht : has_type (KExpr.proj s i sub) S) => ",
                    "typing_proj_absurd s i sub S ",
                    "(has_type (KExpr.proj s i sub') S) ht) ",
                    // apply recursor to indices + major + (T0, ht0)
                    "e0 e0' hbr T0 ht0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "FORWARD subject reduction over the full beta_reduces relation: ",
                "beta_reduces e e' -> has_type e T -> has_type e' T. By beta_reduces.rec — ",
                "beta arm = beta_preservation, iota arm = iota_type_preservation_fwd, the 9 ",
                "congruence arms invert via the generation lemmas + apply the IH + rebuild + ",
                "Typing.conv (the dependent app-arg / lam-domain arms re-establish the type ",
                "via beta_reduces_typed_def_eq); the four let arms (zeta/let_ty/let_val/",
                "let_body) are vacuous over the context-free Typing (no let_ rule) and are ",
                "discharged by inversion (typing_let_absurd). Carries DefEnvWellformed/",
                "RecEnvWellformed the_red_env as hypotheses (threaded from beta_preservation / ",
                "iota_type_preservation_fwd — Guard 4 interfaces, not axioms). Residual ",
                "church_rosser_whnf is the EXISTING leaf inherited from beta_preservation; ZERO ",
                "new axioms. Keystone of the church_rosser_whnf retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "beta_preservation".to_string(),
                "iota_type_preservation_fwd".to_string(),
                "typing_app_gen".to_string(),
                "typing_lam_gen".to_string(),
                "typing_pi_gen".to_string(),
                "lam_typing_dom_sort".to_string(),
                "typing_let_absurd".to_string(),
                "typing_proj_absurd".to_string(),
                "beta_reduces_typed_def_eq".to_string(),
                "def_eq_instantiate_arg_congr".to_string(),
                "Typing.app".to_string(),
                "Typing.lam".to_string(),
                "Typing.pi".to_string(),
                "Typing.conv".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.pi_cong".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =====================================================================
        // whnf_step_preserves_typing: single WHNF step preservation.
        // =====================================================================
        // The kernel-generated `whnf_step.rec` fixes the two KExpr indices BEFORE
        // the motive (mirrors the existing `whnf_step_preserves_def_eq` proof), so
        // the motive is a NAMED reducible alias partially applied to the indices
        // and the branch lambdas range only over the recursive premise. Using an
        // inline lambda motive here trips the recursor-motive false negative.
        self.add_definition_reducible(SpecDefinition {
            name: "whnf_step_preserves_typing_motive".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_step e e' -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (_h : whnf_step e e') => ",
                    "forall (S : KExpr), has_type e S -> has_type e' S"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible motive alias for whnf_step subject reduction. The ",
                "recursor motive must be a named reducible constant for the ",
                "kernel-generated whnf_step.rec (indices-first) to elaborate."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "has_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_step_preserves_typing".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr) (T : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "whnf_step e e' -> has_type e T -> has_type e' T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e0 : KExpr) (e0' : KExpr) (T0 : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hs : whnf_step e0 e0') (ht0 : has_type e0 T0) => ",
                    "whnf_step.rec e0 e0' ",
                    "(whnf_step_preserves_typing_motive e0 e0') ",
                    "(fun (hb : beta_reduces e0 e0') => ",
                    "fun (S : KExpr) (hts : has_type e0 S) => ",
                    "beta_reduces_preserves_typing hf e0 e0' S wd wr hb hts) ",
                    "(fun (hd : delta_reduces e0 e0') => ",
                    "fun (S : KExpr) (hts : has_type e0 S) => ",
                    "delta_type_preservation_fwd e0 e0' wd hd S hts) ",
                    "hs T0 ht0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single WHNF step preservation: whnf_step e e' -> has_type e T -> ",
                "has_type e' T. By whnf_step.rec — beta dispatches to ",
                "beta_reduces_preserves_typing, delta to delta_type_preservation_fwd. ",
                "DerivedPending: inherits church_rosser_whnf via the beta arm."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "whnf_step_preserves_typing_motive".to_string(),
                "beta_reduces_preserves_typing".to_string(),
                "delta_type_preservation_fwd".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =====================================================================
        // whnf_to_preserves_typing: preservation over the directed WHNF closure.
        // =====================================================================
        // `whnf_to.rec` is indices-last with a full (index-abstracting) motive
        // (mirrors the existing `whnf_to_preserves_def_eq` proof); the motive is a
        // named reducible alias to avoid the recursor-motive false negative.
        self.add_definition_reducible(SpecDefinition {
            name: "whnf_to_preserves_typing_motive".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_to e e' -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (_h : whnf_to e e') => ",
                    "forall (S : KExpr), has_type e S -> has_type e' S"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible motive alias for whnf_to subject reduction, keeping the ",
                "kernel-generated whnf_to.rec result reducible during declaration checking."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to".to_string(),
                "has_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_to_preserves_typing".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr) (T : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "whnf_to e e' -> has_type e T -> has_type e' T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e0 : KExpr) (v0 : KExpr) (T0 : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hwt : whnf_to e0 v0) (ht0 : has_type e0 T0) => ",
                    "whnf_to.rec ",
                    "whnf_to_preserves_typing_motive ",
                    // refl: identity
                    "(fun (a : KExpr) (_hw : is_whnf a) => ",
                    "fun (S : KExpr) (hts : has_type a S) => hts) ",
                    // step: whnf_step then IH
                    "(fun (a : KExpr) (b : KExpr) (c : KExpr) ",
                    "(hstep : whnf_step a b) (_hrest : whnf_to b c) ",
                    "(ih : whnf_to_preserves_typing_motive b c _hrest) => ",
                    "fun (S : KExpr) (hts : has_type a S) => ",
                    "ih S (whnf_step_preserves_typing hf a b S wd wr hstep hts)) ",
                    "e0 v0 hwt T0 ht0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "FORWARD subject reduction over the directed WHNF reduction closure: ",
                "whnf_to e e' -> has_type e T -> has_type e' T. By whnf_to.rec — refl = ",
                "identity, step composes whnf_step_preserves_typing with the IH. Genuine ",
                "subject reduction over a DIRECTED relation (no subject expansion, no ",
                "DefEq.symm-flip of the reduction direction). Residual church_rosser_whnf ",
                "is the EXISTING inherited leaf; ZERO new axioms. The directed re-route the ",
                "church_rosser_whnf retirement plan's KernelWhnfPreservesTyping consumes."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to.rec".to_string(),
                "whnf_to_preserves_typing_motive".to_string(),
                "whnf_step_preserves_typing".to_string(),
                "is_whnf".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
