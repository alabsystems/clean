// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Parallel reduction (`par_reduces`) — Tait-Martin-Löf confluence, Packet 1.
//!
//! Introduces the `par_reduces` inductive relation and basic lemmas connecting
//! it to `beta_reduces`. This is the first of five packets for #2859, which
//! derives `church_rosser_whnf` constructively from the widened `beta_reduces`
//! (14 constructors including binder congruence and the genuine-let_ zeta +
//! let_ty/let_val/let_body arms).
//!
//! # Design
//!
//! `par_reduces` permits *simultaneous* reductions at disjoint positions of an
//! expression. Unlike `beta_reduces`, which commits to one redex per step and
//! has a non-trivial diamond, `par_reduces` enjoys the diamond property by
//! structural induction on derivations. Confluence of `beta_reduces` then
//! follows from the standard chain
//!
//! ```text
//! beta_reduces  ⊆  par_reduces  ⊆  beta_reduces_star
//! ```
//!
//! Packet 1 delivers:
//! - `par_reduces` inductive (9 constructors: refl, beta, app, lam, pi,
//!   forall_, let_ (the zeta contraction), iota, let_cong (the positional
//!   let congruence — `KExpr.let_` is a GENUINE constructor, no longer the
//!   reducible `app (lam ty body) val` alias)).
//! - `beta_reduces_star` reflexive-transitive closure of `beta_reduces`.
//! - `par_refl` named alias of the reflexivity constructor.
//! - `beta_subsumes_par_star` : `par_reduces e e' → beta_reduces_star e e'`.
//!
//! Packet 2 delivers (this file):
//! - `par_strips_witness` inductive — packaged `(e3, par_reduces e1 e3,
//!   par_reduces e2 e3)` existential (no `Sigma`/`Exists` in-tree spec).
//!
//! DELETED (owner-approved 2026-07-01, false/unprovable single-step
//! statements over the iota-ful `par_reduces`; see the tombstones inline):
//! `par_subsumes_beta`, `par_subst`, `par_strips`. The honest counterparts
//! are `beta_subsumes_par_star` (star embedding), `par_subst_bd` /
//! `par_strips_bd` (iota-free single-step, this file), and `par_subst_c` /
//! `par_subst_full_c` + the cd-star join machinery (star, iota-ful).
//!
//! # Stage placement
//!
//! Registered after `whnf_lemmas` because `par_reduces` references the widened
//! `beta_reduces` inductive and `iota_reduces` witness family, both finalised
//! by that stage. See `bundles.rs` for the ordered registration plan.
//!
//! # References
//!
//! - `designs/2026-04-20-phase-1-next-keystone-2859.md` (primary design).
//! - `designs/2026-04-20-2859-design-addendum.md` (spot-check addendum).
//! - Tait (1975), Martin-Löf (1972) parallel-reduction technique.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Packet 1 of #2859: `par_reduces` inductive + basic lemmas.
    pub(super) fn add_par_reduction(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // par_reduces inductive — parallel reduction relation
        // =========================================================
        //
        // Constructors:
        //   refl     : forall e, par_reduces e e
        //   beta     : A ⇒ A' → b ⇒ b' → arg ⇒ arg'
        //              → (λA.b) arg ⇒ instantiate b' arg'
        //   app      : f ⇒ f' → a ⇒ a' → (f a) ⇒ (f' a')
        //   lam      : τ ⇒ τ' → b ⇒ b' → (λτ.b) ⇒ (λτ'.b')
        //   pi       : d ⇒ d' → b ⇒ b' → (Πd.b) ⇒ (Πd'.b')
        //   forall_  : d ⇒ d' → b ⇒ b' → (∀d.b) ⇒ (∀d'.b')
        //   let_     : τ ⇒ τ' → v ⇒ v' → b ⇒ b'
        //              → (let τ v b) ⇒ instantiate b' v'   (the ZETA contraction)
        //   iota     : iota_reduces e e' → par_reduces e e'
        //   let_cong : τ ⇒ τ' → v ⇒ v' → b ⇒ b'
        //              → (let τ v b) ⇒ (let τ' v' b')      (positional congruence)
        //
        // `KExpr.let_` is a GENUINE constructor (7th KExpr constructor, let-
        // promotion): a let is let_-headed, disjoint from app/lam/pi. The `let_`
        // arm here IS the parallel zeta (premises reduce the components, the
        // conclusion is the instantiate contractum — exactly the beta shape with
        // the annotation dropped); `let_cong` is the plain three-position
        // congruence a non-firing let needs (before the promotion a let WAS an
        // app-headed beta redex, so `app`+`beta` covered it; no longer).
        //
        // Unlike `beta_reduces`, parallel reduction is reflexive by construction
        // (`refl` constructor), so non-reduced subterms need no explicit framing.
        self.add_inductive(
            r"inductive par_reduces : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces A A' → par_reduces body body' → par_reduces arg arg' → par_reduces (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces f f' → par_reduces a a' → par_reduces (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces ty ty' → par_reduces body body' → par_reduces (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces dom dom' → par_reduces body body' → par_reduces (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces dom dom' → par_reduces body body' → par_reduces (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces ty ty' → par_reduces val val' → par_reduces body body' → par_reduces (KExpr.let_ ty val body) (instantiate body' val')
| iota : forall (e : KExpr) (e' : KExpr), iota_reduces e e' → par_reduces e e'
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces ty ty' → par_reduces val val' → par_reduces body body' → par_reduces (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces sub sub' → par_reduces (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces e e' holds if e parallel-reduces to e' in one step, simultaneously contracting any subset of beta/zeta/iota redexes (including zero, via refl) and lifting reductions under binders — the let_ constructor is the parallel zeta on the genuine KExpr.let_ constructor, let_cong its positional congruence. Part of #2859 Packet 1 — parallel reduction relation for the Tait-Martin-Löf confluence proof.",
        )?;

        // =========================================================
        // beta_reduces_star — reflexive-transitive closure of beta_reduces
        // =========================================================
        //
        // beta_reduces is single-step; beta_reduces_star is multi-step. The
        // final confluence statement (Packet C's beta_confluent) lives at the
        // star level, so we register it here for downstream packets.
        self.add_inductive(
            r"inductive beta_reduces_star : KExpr → KExpr → Type
| refl : forall (e : KExpr), beta_reduces_star e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), beta_reduces e e' → beta_reduces_star e' e'' → beta_reduces_star e e''",
            "beta_reduces_star e e'' is the reflexive-transitive closure of beta_reduces: either e = e'' (refl) or e beta-reduces to an intermediate e' that continues to e''. Part of #2859 Packet 1.",
        )?;

        // =========================================================
        // par_refl — named alias for the reflexivity constructor.
        // =========================================================
        //
        // DerivedProved directly: the constructor itself witnesses the theorem.
        self.add_definition(SpecDefinition {
            name: "par_refl".to_string(),
            type_src: "forall (e : KExpr), par_reduces e e".to_string(),
            value_src: Some(
                "fun (e : KExpr) => par_reduces.refl e".to_string(),
            ),
            is_axiom: false,
            description: "Reflexivity of par_reduces. Named wrapper over the par_reduces.refl constructor. DerivedProved. Part of #2859 Packet 1.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // par_subsumes_beta — DELETED (owner-approved 2026-07-01)
        // =========================================================
        //
        // The single->single embedding `beta_reduces e e' -> par_reduces e e'`
        // was UNPROVABLE AS STATED (documented Wave 120): the then-widened
        // beta_reduces `let_body` arm secretly bundled TWO reductions, and
        // single-step par_reduces has no prefix/transitivity to bridge the
        // recursor IH (full obstruction analysis in git history; the let-
        // promotion later REPLACED that bundled arm with the kernel-faithful
        // zeta + positional let congruences, but the honest embedding remains
        // the star form below). It sat as a
        // value-less PendingLeaf that lowered to a kernel axiom. The honest,
        // provable form is the star embedding `beta_subsumes_par_star`
        // (DerivedProved, below). DELETED rather than "drained": no proof of
        // this statement exists because the statement is unprovable by
        // construction.

        // =========================================================
        // par_reduces_bd — iota-free parallel reduction (Wave 124, #2859)
        // =========================================================
        //
        // Route B (designs/2026-05-27-church-rosser-full-elimination.md):
        // the confluence skeleton (par_subst → par_strips diamond) is
        // proved over this iota-free sub-relation, isolating the
        // never-inhabited `iota` constructor at exactly one structural
        // seam (`par_strips`) rather than threading it through the
        // substitution lemma `par_subst`. The 8 constructors are the
        // beta/zeta/congruence arms of `par_reduces` with the `iota`
        // constructor dropped — none of which references `iota_reduces`,
        // so the iota wall (Wave 122) does not arise for `par_subst_bd`.
        // `let_` is the parallel zeta on the genuine KExpr.let_ constructor;
        // `let_cong` (trailing) is its positional congruence.
        self.add_inductive(
            r"inductive par_reduces_bd : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_bd e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_bd A A' → par_reduces_bd body body' → par_reduces_bd arg arg' → par_reduces_bd (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_bd f f' → par_reduces_bd a a' → par_reduces_bd (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_bd ty ty' → par_reduces_bd body body' → par_reduces_bd (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_bd dom dom' → par_reduces_bd body body' → par_reduces_bd (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_bd dom dom' → par_reduces_bd body body' → par_reduces_bd (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_bd ty ty' → par_reduces_bd val val' → par_reduces_bd body body' → par_reduces_bd (KExpr.let_ ty val body) (instantiate body' val')
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_bd ty ty' → par_reduces_bd val val' → par_reduces_bd body body' → par_reduces_bd (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_bd sub sub' → par_reduces_bd (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces_bd e e' is iota-free parallel reduction (8 constructors: refl, beta, app, lam, pi, forall_, let_ (the parallel zeta on the genuine KExpr.let_ constructor), let_cong (its positional congruence)). The beta/zeta/congruence fragment of par_reduces with the iota constructor dropped, over which the Tait-Martin-Löf confluence skeleton (par_subst_bd, par_strips_bd) is proved without the iota wall. Part of #2859 Wave 124 (Route B).",
        )?;

        // par_reduces_bd_subsumes_par : par_reduces_bd e e' → par_reduces e e'.
        //
        // The iota-free relation embeds into full par_reduces by mapping
        // each constructor to its identically-shaped par_reduces
        // constructor (no iota arm to handle). DerivedProved by
        // par_reduces_bd.rec; zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_subsumes_par".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces_bd e e' -> par_reduces e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_bd e0 e0') => ",
                    "par_reduces_bd.rec ",
                    "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => par_reduces e e') ",
                    // refl : e
                    "(fun (e : KExpr) => par_reduces.refl e) ",
                    // beta : A A' body body' arg arg', hA hb harg, ihA ihb iharg
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_bd A A') (_hb : par_reduces_bd body body') (_harg : par_reduces_bd arg arg') ",
                    "(ihA : par_reduces A A') (ihb : par_reduces body body') (iharg : par_reduces arg arg') => ",
                    "par_reduces.beta A A' body body' arg arg' ihA ihb iharg) ",
                    // app : f f' a a', hf ha, ihf iha
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : par_reduces_bd f f') (_ha : par_reduces_bd a a') ",
                    "(ihf : par_reduces f f') (iha : par_reduces a a') => ",
                    "par_reduces.app f f' a a' ihf iha) ",
                    // lam : ty ty' body body', hty hb, ihty ihb
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_bd ty ty') (_hb : par_reduces_bd body body') ",
                    "(ihty : par_reduces ty ty') (ihb : par_reduces body body') => ",
                    "par_reduces.lam ty ty' body body' ihty ihb) ",
                    // pi : dom dom' body body', hd hb, ihd ihb
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_bd dom dom') (_hb : par_reduces_bd body body') ",
                    "(ihd : par_reduces dom dom') (ihb : par_reduces body body') => ",
                    "par_reduces.pi dom dom' body body' ihd ihb) ",
                    // forall_ : dom dom' body body', hd hb, ihd ihb
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_bd dom dom') (_hb : par_reduces_bd body body') ",
                    "(ihd : par_reduces dom dom') (ihb : par_reduces body body') => ",
                    "par_reduces.forall_ dom dom' body body' ihd ihb) ",
                    // let_ (zeta) : ty ty' val val' body body', hty hv hb, ihty ihv ihb
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_bd ty ty') (_hv : par_reduces_bd val val') (_hb : par_reduces_bd body body') ",
                    "(ihty : par_reduces ty ty') (ihv : par_reduces val val') (ihb : par_reduces body body') => ",
                    "par_reduces.let_ ty ty' val val' body body' ihty ihv ihb) ",
                    // let_cong : ty ty' val val' body body', hty hv hb, ihty ihv ihb
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_bd ty ty') (_hv : par_reduces_bd val val') (_hb : par_reduces_bd body body') ",
                    "(ihty : par_reduces ty ty') (ihv : par_reduces val val') (ihb : par_reduces body body') => ",
                    "par_reduces.let_cong ty ty' val val' body body' ihty ihv ihb) ",
                    // proj : s i sub sub', h_sub, ih_sub -> par_reduces.proj
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_h_sub : par_reduces_bd sub sub') (ih_sub : par_reduces sub sub') => ",
                    "par_reduces.proj s i sub sub' ih_sub) ",
                    // indices + major
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Iota-free parallel reduction embeds into full par_reduces: ",
                "par_reduces_bd.rec maps each of the 8 constructors to its ",
                "identically-shaped par_reduces constructor. No iota arm. ",
                "Kernel-checked, DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 124 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces".to_string(),
                "par_reduces.refl".to_string(),
                "par_reduces.beta".to_string(),
                "par_reduces.app".to_string(),
                "par_reduces.lam".to_string(),
                "par_reduces.pi".to_string(),
                "par_reduces.forall_".to_string(),
                "par_reduces.let_".to_string(),
                "par_reduces.let_cong".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // beta_subsumes_par_star : par_reduces e e' → beta_reduces_star e e'.
        // =========================================================
        //
        // Registered with its full proof term LATER in this method (Wave
        // 119), after the `beta_reduces_subsumes_star`, `beta_reduces_star_
        // trans`, and the Wave 118 star-congruence helpers it composes are
        // in the environment. The kernel checks declarations in
        // registration order, so the proof term must follow its
        // dependencies. See the `beta_subsumes_par_star` block below the
        // Wave 118 helpers.

        // =========================================================
        // Packet 2 tombstone — par_subst + par_strips DELETED
        // (owner-approved 2026-07-01)
        // =========================================================
        //
        // `par_subst : par_reduces e e' -> par_reduces v v' ->
        //  par_reduces (instantiate e v) (instantiate e' v')` over the
        // iota-ful par_reduces was FALSE AS A SINGLE STEP: `par_reduces.iota`
        // is ATOMIC (it lifts a bare directed `iota_reduces e e'` with NO
        // simultaneous sub-reductions), so with v => v' and v != v' the
        // substituted reduct e'[v] differs from the target e'[v'] and no
        // single par_reduces constructor bridges them (e.g. the reduct of
        // `Nat.rec P z s (succ (bvar 0))` references the substitution point).
        // The iota wall itself IS broken — but only as a 2-step star:
        // the honest, provable forms are ALREADY DerivedProved in-tree:
        //   - `par_subst_bd`   (single-step, iota-free fragment; below)
        //   - `par_subst_c` / `par_subst_full_c` (star, iota-ful;
        //     par_reduces_c.rs)
        // Both false single-step leaves sat as value-less PendingLeaf kernel
        // axioms. DELETED rather than "drained": porting the banked beta-only
        // proof onto these iota-ful single-step names would have proved a
        // DIFFERENT statement (the masquerade the no-fake rule forbids).
        // Full obstruction analyses in git history.

        // =========================================================
        // Wave 126 (Route B) — prerequisite chain for par_subst_bd.
        // =========================================================
        //
        // Dependency-scoping wave. The proof term for `par_subst_bd`
        // decomposes (via par_reduces_bd.rec on the first hypothesis) into a
        // refl arm and six congruence/contraction arms. The refl arm needs the
        // auxiliary `par_subst_refl_bd`, whose bvar-at-depth case needs a lift
        // congruence `par_lift_bd`, whose beta/let contraction arms in turn
        // need a lift/substitution interchange `lift_instantiate_swap`. These
        // three are registered DerivedPending here (statements only, empty
        // axiom_deps, NO faked value_src) in the exact order the kernel must
        // check them, so the following dispatch can land closed proof terms
        // bottom-up without re-deriving the decomposition. Each obligation is
        // stated precisely below.

        // lift_instantiate_swap (Wave 126 obligation #1) is now LANDED
        // DerivedProved in expr_model_lift_instantiate_swap.rs (Wave 129),
        // registered via add_expr_model_subst_lift_gen which loads well before
        // this bundle. Its true gap-form statement (the Wave-126 full-cutoff
        // form was FALSE for 0<d, caught in Wave 127/128) is:
        //   lift_at (instantiate_at body val d) (d+k) a
        //     = instantiate_at (lift_at body (succ(d+k)) a) (lift_at val k a) d
        // proved by KExpr.rec on body (bvar via a 4-leaf triple-Nat.rec convoy
        // delegating to lift_instantiate_swap_bvar; app/lam/pi mirror
        // subst_lift_interchange_gen adapted to the gap-form conclusion). At
        // d=0 (nat_zero_add) it specializes to exactly what par_lift_bd's beta/
        // let_ contraction arms need. No iota arm, no new axiom.

        // par_lift_bd (Wave 126 obligation #2).
        //
        // Statement (lift congruence for the iota-free relation):
        //   forall (v v' : KExpr) (c : Nat) (a : Nat),
        //     par_reduces_bd v v' ->
        //     par_reduces_bd (lift_at v c a) (lift_at v' c a)
        //
        // Proof obligation: par_reduces_bd.rec on the v ⇒ v' derivation.
        //   refl     : par_reduces_bd.refl (lift_at e c a).
        //   app      : par_reduces_bd.app on the lifted IHs (lift_at_app unfold).
        //   lam/pi/forall_ : matching congruence constructor on the lifted IHs;
        //              body IH is taken at cutoff (succ c) (lift_at_lam/pi unfold).
        //   beta     : lift the redex app (lam A body) arg; par_reduces_bd.beta
        //              yields instantiate (lift_at body' (succ c) a) (lift_at arg' c a);
        //              transport to lift_at (instantiate body' arg') c a via
        //              `lift_instantiate_swap` at d=0 (gap k=c, since
        //              Nat.add 0 c = c by nat_zero_add and lift_at arg' (Nat.add 0 c) a
        //              = lift_at arg' c a — the d=0 specialization of the
        //              CORRECTED gap-form statement; see Wave-127 note above).
        //   let_     : same contraction transport as beta — the zeta arm on the
        //              genuine KExpr.let_ constructor has the same instantiate
        //              contractum shape (the lifted source is let_-headed via
        //              the lift_at let_ unfold; ty and val lift at cutoff c,
        //              body at succ c).
        //   let_cong : matching congruence constructor on the lifted IHs
        //              (ty/val at cutoff c, body at succ c) — the trailing
        //              positional let congruence minor.
        // Empty axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_lift_bd".to_string(),
            type_src: concat!(
                "forall (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat), ",
                "par_reduces_bd v v' -> ",
                "par_reduces_bd (lift_at v c a) (lift_at v' c a)"
            )
            .to_string(),
            value_src: Some(par_lift_bd_proof()),
            is_axiom: false,
            description: concat!(
                "Lift congruence for iota-free parallel reduction: v ⇒ v' implies ",
                "lift_at v c a ⇒ lift_at v' c a. Needed for the bvar-at-depth case ",
                "of par_subst_refl_bd (substituted value is lifted by the binder ",
                "depth). DerivedProved: par_reduces_bd.rec on v ⇒ v' with a motive ",
                "universalizing (c, a); congruence arms (incl. the trailing ",
                "let_cong) reassemble the matching constructor on lifted IHs ",
                "(body IH at cutoff succ c), the beta/let_ (zeta) contraction ",
                "arms transport the second index via ",
                "lift_instantiate_swap at d=0 (nat_zero_add) with Eq.subst. ",
                "No iota arm, no new axiom. Part of #2859 Wave 130 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_reduces_bd.beta".to_string(),
                "par_reduces_bd.app".to_string(),
                "par_reduces_bd.lam".to_string(),
                "par_reduces_bd.pi".to_string(),
                "par_reduces_bd.forall_".to_string(),
                "par_reduces_bd.let_".to_string(),
                "par_reduces_bd.let_cong".to_string(),
                "lift_at".to_string(),
                "lift_instantiate_swap".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "nat_zero_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_refl_bd (Wave 126 obligation #3).
        //
        // Statement (the refl arm of par_subst_bd, generalized to arbitrary
        // substitution depth so the binder recursion goes through):
        //   forall (e v v' : KExpr) (d : Nat),
        //     par_reduces_bd v v' ->
        //     par_reduces_bd (instantiate_at e v d) (instantiate_at e v' d)
        //
        // Proof obligation: KExpr.rec on `e`, motive universalizing (v, v', d).
        //   sort/const : par_reduces_bd.refl (instantiate is identity on heads).
        //   bvar i     : triple-Nat.rec convoy on (Nat.sub d i) / (Nat.sub i d):
        //                  i < d : both sides reduce to bvar i -> par_reduces_bd.refl.
        //                  i = d : both sides reduce to lift_at v/v' 0 d ->
        //                          `par_lift_bd v v' 0 d` applied to the hypothesis.
        //                  i > d : both sides reduce to bvar (i-1) -> refl.
        //   app        : par_reduces_bd.app on the two IHs at depth d
        //                (instantiate_at_app unfold).
        //   lam/pi     : matching congruence constructor; ty IH at depth d, body
        //                IH at depth (succ d) (instantiate_at_lam/pi unfold).
        //   let_       : par_reduces_bd.let_cong on the three IHs; ty and val
        //                IHs at depth d, body IH at depth (succ d)
        //                (instantiate_at_let_ unfold) — trailing KExpr.rec minor.
        // par_subst_bd's refl arm then specializes this at d = Nat.zero (since
        // `instantiate e v = instantiate_at e v Nat.zero`). Empty axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_subst_refl_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_bd v v' -> ",
                "par_reduces_bd (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_refl_bd_proof()),
            is_axiom: false,
            description: concat!(
                "Reflexive (skeleton-fixed) substitution congruence for iota-free ",
                "parallel reduction: substituting parallel-reducing values v ⇒ v' ",
                "into a fixed term e at any depth d yields a parallel reduction. ",
                "The refl arm of par_subst_bd. DerivedProved: KExpr.rec on e — ",
                "sort/const by refl, app/lam/pi/let_ congruence via the matching ",
                "constructor on IHs (let_ via par_reduces_bd.let_cong; body IH ",
                "at succ depth), the bvar arm a ",
                "double-Nat.rec convoy on sub(i,d)/sub(d,i) that threads v ⇒ v' ",
                "through par_lift_bd at the i=d position (value lifted by the ",
                "depth) and lands refl on the i<d / i>d positions, transporting ",
                "the indices via instantiate_bvar_at_below/above / ",
                "instantiate_at_bvar_eq_from_zero_witnesses and Eq.subst. ",
                "No iota arm, no new axiom. Part of #2859 Wave 131 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_reduces_bd.app".to_string(),
                "par_reduces_bd.lam".to_string(),
                "par_reduces_bd.pi".to_string(),
                "par_reduces_bd.let_cong".to_string(),
                "par_lift_bd".to_string(),
                "instantiate_at".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_zero_of_sub_pos".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "KExpr.rec".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // par_subst_bd — iota-free parallel substitution (Wave 125, Route B)
        // =========================================================
        //
        // Statement (over the iota-free par_reduces_bd):
        //   forall e e' v v',
        //     par_reduces_bd e e' → par_reduces_bd v v'
        //       → par_reduces_bd (instantiate e v) (instantiate e' v')
        //
        // This is `par_subst` restricted to the beta/zeta/congruence fragment.
        // Crucially, because `par_reduces_bd` has NO iota constructor, the
        // induction on `par_reduces_bd.rec` has only 8 arms and the
        // Wave-122 iota wall does not arise. Every arm is constructively
        // closable with in-tree, fully-kernel-checked infrastructure:
        //
        //   refl    : need par_reduces_bd (instantiate e v) (instantiate e v')
        //             from par_reduces_bd v v'. Proved by the auxiliary
        //             `par_subst_refl_bd` (recursion on the KExpr structure
        //             of e: leaves close by refl, the bvar-at-depth position
        //             threads the v ⇒ v' hypothesis, binders lift one depth).
        //   app     : congruence — recurse under both sides, reassemble via
        //             par_reduces_bd.app.
        //   lam/pi/forall_ : congruence under binder — recurse, lift v one
        //             depth, apply the matching congruence constructor.
        //   beta    : (λA.b) arg ⇒ instantiate b' arg' commutes with the
        //             outer substitution via the in-tree
        //             `subst_lift_interchange_gen` Eq-transport (which is
        //             registered through `add_definition` and therefore fully
        //             kernel-checked — `add_definition_structural` is a mere
        //             documentation alias for `add_definition`, NOT the
        //             kernel-level add_decl_structural that the unchecked-decl
        //             ratchet tracks).
        //   let_    : the zeta contraction on the genuine KExpr.let_
        //             constructor — same instantiate-contractum transport as
        //             beta (the substituted source is let_-headed via the
        //             instantiate_at let_ unfold).
        //   let_cong: congruence under the let binder — recurse (ty/val at
        //             depth d, body at succ d), reassemble via
        //             par_reduces_bd.let_cong.
        //
        // No iota arm ⇒ no NEW infrastructure, no axiom. Once landed
        // (DerivedProved), `par_strips_bd` consumes it for its (beta,beta)
        // case, and the full-`par_reduces` `par_subst`/`par_strips` are
        // recovered by `par_reduces_bd_subsumes_par` plus the iota-seam
        // forwarding handler (Wave 127). See
        // designs/2026-05-27-church-rosser-full-elimination.md.
        //
        // Registered DerivedPending here (statement + plan) ahead of the
        // proof term; the auxiliary `par_subst_refl_bd` lands first. No
        // value faked — do NOT use add_decl_unchecked.
        self.add_definition(SpecDefinition {
            name: "par_subst_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr), ",
                "par_reduces_bd e e' -> par_reduces_bd v v' -> ",
                "par_reduces_bd (instantiate e v) (instantiate e' v')"
            )
            .to_string(),
            value_src: Some(par_subst_bd_proof()),
            is_axiom: false,
            description: concat!(
                "Iota-free parallel substitution commutes with parallel ",
                "reduction: par_reduces_bd e e' and par_reduces_bd v v' imply ",
                "par_reduces_bd (instantiate e v) (instantiate e' v'). The ",
                "Route B replacement for par_subst's blocked iota arm — over ",
                "par_reduces_bd there is NO iota constructor, so the 8-arm ",
                "par_reduces_bd.rec induction closes with in-tree kernel-checked ",
                "infrastructure. DerivedProved: par_reduces_bd.rec on e ⇒ e' with ",
                "a depth-generalized motive (binder arms recurse at succ depth), ",
                "specialized at d=Nat.zero. refl via par_subst_refl_bd; app/lam/ ",
                "pi/forall_/let_cong congruence by the matching constructor on ",
                "IHs; beta/let_ (zeta) contraction transported via ",
                "instantiate_nested_commutes_zero_subst ",
                "(substitution commutes with substitution at depth 0) and Eq.subst. ",
                "No iota arm, no new axiom. Part of #2859 Wave 132 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_reduces_bd.beta".to_string(),
                "par_reduces_bd.app".to_string(),
                "par_reduces_bd.lam".to_string(),
                "par_reduces_bd.pi".to_string(),
                "par_reduces_bd.forall_".to_string(),
                "par_reduces_bd.let_".to_string(),
                "par_reduces_bd.let_cong".to_string(),
                "par_subst_refl_bd".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness : KExpr → KExpr → Type
        //
        // Packaged existential for the single-step diamond conclusion.
        // There is no `Exists` or `Sigma` type in the current spec fragment
        // (foundation_types.rs provides `AndType` only), so the meeting point
        // `exists e3, par_reduces e1 e3 ∧ par_reduces e2 e3` is encoded as
        // an explicit inductive with one constructor.
        //
        //   intro : forall (e3 : KExpr), par_reduces e1 e3 → par_reduces e2 e3
        //           → par_strips_witness e1 e2
        //
        // Packet 3 (par_diamond) and Packet 3 (beta_confluent) both
        // consume the projections via `par_strips_witness.rec`. Downstream
        // consumers that prefer the AndType encoding can wrap via
        // `AndType (par_reduces e1 e3) (par_reduces e2 e3)`, but keeping e3
        // packaged directly with its two witnesses matches the Lean 4
        // metatheory convention (Carneiro 2023 §5.2) and avoids a second
        // layer of eliminator pattern-matching in the diamond proof.
        self.add_inductive(
            r"inductive par_strips_witness : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces e1 e3 → par_reduces e2 e3 → par_strips_witness e1 e2",
            "par_strips_witness e1 e2 packages the single-step diamond conclusion: a common reduct e3 together with par_reduces e1 e3 and par_reduces e2 e3. Encodes the existential meeting point without a Sigma/Exists type (not in current spec fragment). Part of #2859 Packet 2.",
        )?;

        // par_strips — DELETED (owner-approved 2026-07-01). The iota-ful
        // single-step diamond inherited par_subst's atomic-iota falseness
        // through its (beta, beta) case. Honest, provable forms already
        // DerivedProved in-tree: `par_strips_bd` (iota-free single-step,
        // below) and the cd-star join machinery
        // (`par_reduces_cd_star_diamond`, par_reduces_pd.rs / def_eq_joinable
        // path). The `par_strips_witness` inductive above STAYS — it is the
        // packaged-existential vocabulary consumed by the star-level diamonds.

        // =========================================================
        // beta_reduces_subsumes_star — single-step β-reduction embeds into
        // the reflexive-transitive closure.
        // =========================================================
        //
        // Statement:
        //   forall (e e' : KExpr), beta_reduces e e' -> beta_reduces_star e e'.
        //
        // Proof (constructive, DerivedProved): the closed term is the
        // `step` constructor with the tail filled in by `refl`:
        //
        //   fun (e e' : KExpr) (h : beta_reduces e e') =>
        //     beta_reduces_star.step e e' e' h (beta_reduces_star.refl e')
        //
        // No recursion on the input — the witness is built directly from
        // the `beta_reduces_star` constructors. No HelperAxiom use —
        // axiom_deps = {}. DerivedProved.
        //
        // Cited by Packet B as the embedding used in `beta_subsumes_par_star`
        // for the per-step lifting of single-step reductions into stars
        // before composition via `beta_reduces_star_trans`. Provides the
        // base case for both the `beta` and `let_` (zeta) contraction arms
        // of the par_reduces recursor.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_subsumes_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "beta_reduces e e' -> beta_reduces_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : beta_reduces e e') => ",
                    "beta_reduces_star.step e e' e' h ",
                    "(beta_reduces_star.refl e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-step beta_reduces embeds into beta_reduces_star: ",
                "build the witness directly via beta_reduces_star.step with ",
                "the singleton-tail filled by beta_reduces_star.refl. ",
                "DerivedProved with zero axiom_deps. Helper for ",
                "beta_subsumes_par_star's per-step lifting. Part of #2859 ",
                "Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces".to_string(),
                "beta_reduces_star".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // beta_reduces_star_trans — transitivity of the reflexive-transitive
        // closure of beta_reduces.
        // =========================================================
        //
        // Cited in the `beta_subsumes_par_star` design block above as the
        // "helper lemma `beta_reduces_star.trans`" required by Packet B's
        // proof composition. Without it, congruence cases of
        // `beta_subsumes_par_star` cannot lift sub-derivations under each
        // binder position and compose the per-position stars into a single
        // star at the surrounding constructor.
        //
        // Statement:
        //   forall (e1 e2 e3 : KExpr),
        //     beta_reduces_star e1 e2 ->
        //     beta_reduces_star e2 e3 ->
        //     beta_reduces_star e1 e3.
        //
        // Proof sketch: structural induction on the FIRST argument
        // (`beta_reduces_star e1 e2`) using `beta_reduces_star.rec`.
        //
        //   refl : e1 = e2 ⇒ the result is the second argument directly.
        //   step : e1 -β-> e_mid, beta_reduces_star e_mid e2 ⇒ by the IH at
        //          e_mid we obtain `beta_reduces_star e_mid e3`; prefix the
        //          single step e1 -β-> e_mid via `beta_reduces_star.step` to
        //          conclude `beta_reduces_star e1 e3`.
        //
        // This is the standard "left-recursive" definition of multi-step
        // transitivity, mirroring Lean 4's `Relation.ReflTransGen.trans`.
        // No HelperAxiom use — axiom_deps = {}.
        //
        // Proved in Wave 117 of #2859: the closed term is a single
        // `beta_reduces_star.rec` application with the second argument
        // (`beta_reduces_star e2 e3`) captured in the motive as a function
        // result. Inducting on the FIRST star derivation:
        //
        //   motive a b (_ : beta_reduces_star a b)
        //     := beta_reduces_star b e3 -> beta_reduces_star a e3
        //
        //   refl e : the tail star `beta_reduces_star e e3` IS the result.
        //   step e e' e'' hstep htail ih :
        //     given a tail `beta_reduces_star e'' e3`, the IH extends from
        //     e' (yielding `beta_reduces_star e' e3`), then we prefix the
        //     single step `hstep : beta_reduces e e'` via
        //     `beta_reduces_star.step` to conclude `beta_reduces_star e e3`.
        //
        // Applying the recursor to the indices e1 e2 and the major premise
        // h1, then feeding h2, yields `beta_reduces_star e1 e3`. No
        // HelperAxiom use — axiom_deps = {}. DerivedProved.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_trans".to_string(),
            type_src: concat!(
                "forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "beta_reduces_star e1 e2 -> beta_reduces_star e2 e3 -> ",
                "beta_reduces_star e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : beta_reduces_star e1 e2) ",
                    "(h2 : beta_reduces_star e2 e3) => ",
                    "beta_reduces_star.rec ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(_ : beta_reduces_star a b) => ",
                    "beta_reduces_star b e3 -> beta_reduces_star a e3) ",
                    "(fun (e : KExpr) (k : beta_reduces_star e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star e'' e3 -> beta_reduces_star e' e3) ",
                    "(k : beta_reduces_star e'' e3) => ",
                    "beta_reduces_star.step e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of beta_reduces_star (reflexive-transitive ",
                "closure of single-step beta reduction). Proved by ",
                "structural induction on the first argument via ",
                "beta_reduces_star.rec, prefixing each step constructor onto ",
                "the recursively-extended tail. Helper lemma cited by ",
                "beta_subsumes_par_star's congruence composition. Part of ",
                "#2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // beta_reduces_star single-position congruence helpers (Wave 118)
        // =========================================================
        //
        // Each lemma lifts a multi-step reduction in one subterm position
        // into a multi-step reduction of the surrounding constructor, with
        // the sibling positions held fixed. They are the star-level
        // analogues of the `beta_reduces` congruence constructors and are
        // the per-position lifting primitives `beta_subsumes_par_star`
        // composes (via `beta_reduces_star_trans`) to simulate each
        // `par_reduces` constructor by a finite beta sequence.
        //
        // Common proof shape: structural induction on the input star via
        // `beta_reduces_star.rec` with motive
        //   fun (x y : KExpr) (_ : beta_reduces_star x y) =>
        //     beta_reduces_star (C .. x ..) (C .. y ..)
        // (the surrounding constructor C with the moving position
        // substituted). The `refl` arm returns `beta_reduces_star.refl` at
        // the framed shape; the `step` arm prefixes the matching
        // single-step `beta_reduces` congruence constructor onto the IH via
        // `beta_reduces_star.step`. No recursion beyond the single
        // `beta_reduces_star.rec`; zero axiom_deps. DerivedProved.

        // beta_reduces_star_app_left : reduce the head of an application,
        // argument fixed.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_app_left".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (f' : KExpr) (a : KExpr), ",
                "beta_reduces_star f f' -> ",
                "beta_reduces_star (KExpr.app f a) (KExpr.app f' a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(h : beta_reduces_star f f') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.app x a) (KExpr.app y a)) ",
                    "(fun (e : KExpr) => ",
                    "beta_reduces_star.refl (KExpr.app e a)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.app e' a) (KExpr.app e'' a)) => ",
                    "beta_reduces_star.step (KExpr.app e a) (KExpr.app e' a) ",
                    "(KExpr.app e'' a) (beta_reduces.app_left e e' a hstep) ih) ",
                    "f f' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level left congruence over application: lift ",
                "beta_reduces_star in the head into the application, ",
                "holding the argument fixed. Proved by beta_reduces_star.rec ",
                "prefixing beta_reduces.app_left on each step. DerivedProved, ",
                "zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.app_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_proj — star-level congruence into the proj subterm
        // (proj/lit rung; mirrors beta_reduces_star_app_left, prefixing
        // beta_reduces.proj on each step).
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_proj".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), ",
                "beta_reduces_star sub sub' -> ",
                "beta_reduces_star (KExpr.proj s i sub) (KExpr.proj s i sub')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(h : beta_reduces_star sub sub') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) (_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.proj s i x) (KExpr.proj s i y)) ",
                    "(fun (e : KExpr) => beta_reduces_star.refl (KExpr.proj s i e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') (_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.proj s i e') (KExpr.proj s i e'')) => ",
                    "beta_reduces_star.step (KExpr.proj s i e) (KExpr.proj s i e') ",
                    "(KExpr.proj s i e'') (beta_reduces.proj s i e e' hstep) ih) ",
                    "sub sub' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Star-level congruence over proj: lift beta_reduces_star into the proj subterm (proj/lit rung).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.proj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_app_right : reduce the argument, head fixed.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_app_right".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (a' : KExpr), ",
                "beta_reduces_star a a' -> ",
                "beta_reduces_star (KExpr.app f a) (KExpr.app f a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(h : beta_reduces_star a a') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.app f x) (KExpr.app f y)) ",
                    "(fun (e : KExpr) => ",
                    "beta_reduces_star.refl (KExpr.app f e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.app f e') (KExpr.app f e'')) => ",
                    "beta_reduces_star.step (KExpr.app f e) (KExpr.app f e') ",
                    "(KExpr.app f e'') (beta_reduces.app_right f e e' hstep) ih) ",
                    "a a' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level right congruence over application: lift ",
                "beta_reduces_star in the argument into the application, ",
                "holding the head fixed. Proved by beta_reduces_star.rec ",
                "prefixing beta_reduces.app_right on each step. DerivedProved, ",
                "zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.app_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_lam_ty : reduce the binder type of a lambda,
        // body fixed.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_lam_ty".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (ty' : KExpr) (body : KExpr), ",
                "beta_reduces_star ty ty' -> ",
                "beta_reduces_star (KExpr.lam ty body) (KExpr.lam ty' body)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
                    "(h : beta_reduces_star ty ty') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.lam x body) (KExpr.lam y body)) ",
                    "(fun (e : KExpr) => ",
                    "beta_reduces_star.refl (KExpr.lam e body)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.lam e' body) (KExpr.lam e'' body)) => ",
                    "beta_reduces_star.step (KExpr.lam e body) (KExpr.lam e' body) ",
                    "(KExpr.lam e'' body) (beta_reduces.lam_ty e e' body hstep) ih) ",
                    "ty ty' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the lambda binder type. Proved ",
                "by beta_reduces_star.rec prefixing beta_reduces.lam_ty on ",
                "each step. DerivedProved, zero axiom_deps. Part of #2859 ",
                "Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.lam_ty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_lam_body : reduce the lambda body, type fixed.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_lam_body".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (body : KExpr) (body' : KExpr), ",
                "beta_reduces_star body body' -> ",
                "beta_reduces_star (KExpr.lam ty body) (KExpr.lam ty body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(h : beta_reduces_star body body') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.lam ty x) (KExpr.lam ty y)) ",
                    "(fun (e : KExpr) => ",
                    "beta_reduces_star.refl (KExpr.lam ty e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.lam ty e') (KExpr.lam ty e'')) => ",
                    "beta_reduces_star.step (KExpr.lam ty e) (KExpr.lam ty e') ",
                    "(KExpr.lam ty e'') (beta_reduces.lam_body ty e e' hstep) ih) ",
                    "body body' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the lambda body. Proved by ",
                "beta_reduces_star.rec prefixing beta_reduces.lam_body on ",
                "each step. DerivedProved, zero axiom_deps. Part of #2859 ",
                "Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.lam_body".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_pi_dom : reduce the Pi domain, body fixed.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_pi_dom".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (dom' : KExpr) (body : KExpr), ",
                "beta_reduces_star dom dom' -> ",
                "beta_reduces_star (KExpr.pi dom body) (KExpr.pi dom' body)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(h : beta_reduces_star dom dom') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.pi x body) (KExpr.pi y body)) ",
                    "(fun (e : KExpr) => ",
                    "beta_reduces_star.refl (KExpr.pi e body)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.pi e' body) (KExpr.pi e'' body)) => ",
                    "beta_reduces_star.step (KExpr.pi e body) (KExpr.pi e' body) ",
                    "(KExpr.pi e'' body) (beta_reduces.pi_dom e e' body hstep) ih) ",
                    "dom dom' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the Pi domain. Proved by ",
                "beta_reduces_star.rec prefixing beta_reduces.pi_dom on each ",
                "step. DerivedProved, zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.pi_dom".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_pi_cod : reduce the Pi codomain, domain fixed.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_star_pi_cod".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (body : KExpr) (body' : KExpr), ",
                "beta_reduces_star body body' -> ",
                "beta_reduces_star (KExpr.pi dom body) (KExpr.pi dom body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(h : beta_reduces_star body body') => ",
                    "beta_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : beta_reduces_star x y) => ",
                    "beta_reduces_star (KExpr.pi dom x) (KExpr.pi dom y)) ",
                    "(fun (e : KExpr) => ",
                    "beta_reduces_star.refl (KExpr.pi dom e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces e e') ",
                    "(_htail : beta_reduces_star e' e'') ",
                    "(ih : beta_reduces_star (KExpr.pi dom e') (KExpr.pi dom e'')) => ",
                    "beta_reduces_star.step (KExpr.pi dom e) (KExpr.pi dom e') ",
                    "(KExpr.pi dom e'') (beta_reduces.pi_cod dom e e' hstep) ih) ",
                    "body body' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the Pi codomain. Proved by ",
                "beta_reduces_star.rec prefixing beta_reduces.pi_cod on each ",
                "step. DerivedProved, zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_star".to_string(),
                "beta_reduces_star.rec".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces.pi_cod".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_star_let_ty / _let_val / _let_body : the three
        // single-position star congruences over the GENUINE KExpr.let_
        // constructor (let-promotion). Same Wave-118 proof shape, prefixing
        // the matching beta_reduces.let_ty / .let_val / .let_body positional
        // congruence on each step. Consumed by beta_subsumes_par_star's
        // let_ (zeta) and let_cong arms.
        for (name, params, src_lhs, src_rhs, frame, ctor, step_term, what) in [
            (
                "beta_reduces_star_let_ty",
                "(ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr)",
                "ty",
                "ty'",
                "(KExpr.let_ {} val body)",
                "beta_reduces.let_ty",
                "beta_reduces.let_ty e e' val body hstep",
                "let binder type",
            ),
            (
                "beta_reduces_star_let_val",
                "(ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr)",
                "val",
                "val'",
                "(KExpr.let_ ty {} body)",
                "beta_reduces.let_val",
                "beta_reduces.let_val ty e e' body hstep",
                "let value",
            ),
            (
                "beta_reduces_star_let_body",
                "(ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr)",
                "body",
                "body'",
                "(KExpr.let_ ty val {})",
                "beta_reduces.let_body",
                "beta_reduces.let_body ty val e e' hstep",
                "let body",
            ),
        ] {
            let frame_with = |m: &str| frame.replacen("{}", m, 1);
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall {params}, ",
                        "beta_reduces_star {src_lhs} {src_rhs} -> ",
                        "beta_reduces_star {frame_lhs} {frame_rhs}"
                    ),
                    params = params,
                    src_lhs = src_lhs,
                    src_rhs = src_rhs,
                    frame_lhs = frame_with(src_lhs),
                    frame_rhs = frame_with(src_rhs),
                ),
                value_src: Some(format!(
                    concat!(
                        "fun {params} ",
                        "(h : beta_reduces_star {src_lhs} {src_rhs}) => ",
                        "beta_reduces_star.rec ",
                        "(fun (x : KExpr) (y : KExpr) ",
                        "(_ : beta_reduces_star x y) => ",
                        "beta_reduces_star {frame_x} {frame_y}) ",
                        "(fun (e : KExpr) => ",
                        "beta_reduces_star.refl {frame_e}) ",
                        "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                        "(hstep : beta_reduces e e') ",
                        "(_htail : beta_reduces_star e' e'') ",
                        "(ih : beta_reduces_star {frame_ep} {frame_epp}) => ",
                        "beta_reduces_star.step {frame_e} {frame_ep} ",
                        "{frame_epp} ({step_term}) ih) ",
                        "{src_lhs} {src_rhs} h"
                    ),
                    params = params,
                    src_lhs = src_lhs,
                    src_rhs = src_rhs,
                    frame_x = frame_with("x"),
                    frame_y = frame_with("y"),
                    frame_e = frame_with("e"),
                    frame_ep = frame_with("e'"),
                    frame_epp = frame_with("e''"),
                    step_term = step_term,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Star-level congruence over the {what} position of the ",
                        "genuine KExpr.let_ constructor. Proved by ",
                        "beta_reduces_star.rec prefixing {ctor} on each step. ",
                        "DerivedProved, zero axiom_deps. Part of the ",
                        "let-promotion confluence batch (#2859 Packet 2 shape)."
                    ),
                    what = what,
                    ctor = ctor,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "beta_reduces_star".to_string(),
                    "beta_reduces_star.rec".to_string(),
                    "beta_reduces_star.refl".to_string(),
                    "beta_reduces_star.step".to_string(),
                    ctor.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // =========================================================
        // beta_subsumes_par_star : par_reduces e e' → beta_reduces_star e e'
        // (Wave 119)
        // =========================================================
        //
        // The par ⊆ beta* direction of the Tait-Martin-Löf chain. Proved by
        // structural induction on the par_reduces derivation via
        // par_reduces.rec, motive
        //   fun (e e' : KExpr) (_ : par_reduces e e') => beta_reduces_star e e'
        // Each arm simulates a single parallel step by a finite beta
        // sequence, composed via beta_reduces_star_trans and the Wave 118
        // single-position star-congruence helpers:
        //
        //   refl    : beta_reduces_star.refl.
        //   beta    : (λA.body) arg ⇒ instantiate body' arg'. Reduce inside
        //             left-to-right — A↦A' (lam_ty under app_left), body↦body'
        //             (lam_body under app_left), arg↦arg' (app_right) — to
        //             reach (λA'.body') arg', then a single beta_reduces.beta
        //             head contraction (lifted via beta_reduces_subsumes_star).
        //   app     : app_left(ihf) then app_right(iha), composed.
        //   lam     : lam_ty(ihty) then lam_body(ihbody).
        //   pi      : pi_dom(ihdom) then pi_cod(ihbody).
        //   forall_ : same as pi (KExpr.forall_ is a reducible alias of
        //             KExpr.pi, so the pi-shaped helper terms check against the
        //             forall_-shaped goal by definitional unfolding).
        //   let_    : the ZETA arm on the genuine KExpr.let_ constructor
        //             (let-promotion; a let is let_-headed, NOT an app-headed
        //             beta redex). Reduce inside — body↦body' (let_body star),
        //             val↦val' (let_val star) — to reach let_ ty val' body',
        //             then a single beta_reduces.zeta head contraction (lifted
        //             via beta_reduces_subsumes_star). Mirrors the beta arm
        //             with the let_ positional congruences in place of the
        //             app/lam ones (the annotation IH is unused, as there).
        //   iota    : beta_reduces.iota lifted to a single-step star via
        //             beta_reduces_subsumes_star.
        //   let_cong: three-position congruence — ty↦ty' (let_ty star), then
        //             val↦val' (let_val star), then body↦body' (let_body star),
        //             composed via beta_reduces_star_trans.
        //
        // No HelperAxiom use — axiom_deps = {}. DerivedProved.
        self.add_definition(SpecDefinition {
            name: "beta_subsumes_par_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces e e' -> beta_reduces_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces e0 e0') => ",
                    "par_reduces.rec ",
                    "(fun (e : KExpr) (e' : KExpr) (_ : par_reduces e e') => ",
                    "beta_reduces_star e e') ",
                    // refl
                    "(fun (e : KExpr) => beta_reduces_star.refl e) ",
                    // beta : A A' body body' arg arg', subs hA hbody harg, IHs ihA ihbody iharg
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces A A') (_hbody : par_reduces body body') ",
                    "(_harg : par_reduces arg arg') ",
                    "(ihA : beta_reduces_star A A') (ihbody : beta_reduces_star body body') ",
                    "(iharg : beta_reduces_star arg arg') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.app (KExpr.lam A body) arg) ",
                    "(KExpr.app (KExpr.lam A' body') arg') ",
                    "(instantiate body' arg') ",
                    "(beta_reduces_star_trans ",
                    "(KExpr.app (KExpr.lam A body) arg) ",
                    "(KExpr.app (KExpr.lam A' body') arg) ",
                    "(KExpr.app (KExpr.lam A' body') arg') ",
                    "(beta_reduces_star_trans ",
                    "(KExpr.app (KExpr.lam A body) arg) ",
                    "(KExpr.app (KExpr.lam A' body) arg) ",
                    "(KExpr.app (KExpr.lam A' body') arg) ",
                    "(beta_reduces_star_app_left (KExpr.lam A body) (KExpr.lam A' body) arg ",
                    "(beta_reduces_star_lam_ty A A' body ihA)) ",
                    "(beta_reduces_star_app_left (KExpr.lam A' body) (KExpr.lam A' body') arg ",
                    "(beta_reduces_star_lam_body A' body body' ihbody))) ",
                    "(beta_reduces_star_app_right (KExpr.lam A' body') arg arg' iharg)) ",
                    "(beta_reduces_subsumes_star ",
                    "(KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
                    "(beta_reduces.beta A' body' arg'))) ",
                    // app : f f' a a', subs hf ha, IHs ihf iha
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : par_reduces f f') (_ha : par_reduces a a') ",
                    "(ihf : beta_reduces_star f f') (iha : beta_reduces_star a a') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.app f a) (KExpr.app f' a) (KExpr.app f' a') ",
                    "(beta_reduces_star_app_left f f' a ihf) ",
                    "(beta_reduces_star_app_right f' a a' iha)) ",
                    // lam : ty ty' body body', subs, IHs ihty ihbody
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces ty ty') (_hbody : par_reduces body body') ",
                    "(ihty : beta_reduces_star ty ty') (ihbody : beta_reduces_star body body') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.lam ty body) (KExpr.lam ty' body) (KExpr.lam ty' body') ",
                    "(beta_reduces_star_lam_ty ty ty' body ihty) ",
                    "(beta_reduces_star_lam_body ty' body body' ihbody)) ",
                    // pi : dom dom' body body', subs, IHs ihdom ihbody
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hdom : par_reduces dom dom') (_hbody : par_reduces body body') ",
                    "(ihdom : beta_reduces_star dom dom') (ihbody : beta_reduces_star body body') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.pi dom body) (KExpr.pi dom' body) (KExpr.pi dom' body') ",
                    "(beta_reduces_star_pi_dom dom dom' body ihdom) ",
                    "(beta_reduces_star_pi_cod dom' body body' ihbody)) ",
                    // forall_ : dom dom' body body', subs, IHs (alias of pi)
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hdom : par_reduces dom dom') (_hbody : par_reduces body body') ",
                    "(ihdom : beta_reduces_star dom dom') (ihbody : beta_reduces_star body body') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.pi dom body) (KExpr.pi dom' body) (KExpr.pi dom' body') ",
                    "(beta_reduces_star_pi_dom dom dom' body ihdom) ",
                    "(beta_reduces_star_pi_cod dom' body body' ihbody)) ",
                    // let_ (zeta) : ty ty' val val' body body', subs, IHs ihty ihval ihbody
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
                    "(body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces ty ty') (_hval : par_reduces val val') ",
                    "(_hbody : par_reduces body body') ",
                    "(ihty : beta_reduces_star ty ty') (ihval : beta_reduces_star val val') ",
                    "(ihbody : beta_reduces_star body body') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.let_ ty val body) ",
                    "(KExpr.let_ ty val' body') ",
                    "(instantiate body' val') ",
                    "(beta_reduces_star_trans ",
                    "(KExpr.let_ ty val body) ",
                    "(KExpr.let_ ty val body') ",
                    "(KExpr.let_ ty val' body') ",
                    "(beta_reduces_star_let_body ty val body body' ihbody) ",
                    "(beta_reduces_star_let_val ty val val' body' ihval)) ",
                    "(beta_reduces_subsumes_star ",
                    "(KExpr.let_ ty val' body') (instantiate body' val') ",
                    "(beta_reduces.zeta ty val' body'))) ",
                    // iota : e e', sub h (iota_reduces e e')
                    "(fun (e : KExpr) (e' : KExpr) (h : iota_reduces e e') => ",
                    "beta_reduces_subsumes_star e e' (beta_reduces.iota e e' h)) ",
                    // let_cong : ty ty' val val' body body', subs, IHs ihty ihval ihbody
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
                    "(body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces ty ty') (_hval : par_reduces val val') ",
                    "(_hbody : par_reduces body body') ",
                    "(ihty : beta_reduces_star ty ty') (ihval : beta_reduces_star val val') ",
                    "(ihbody : beta_reduces_star body body') => ",
                    "beta_reduces_star_trans ",
                    "(KExpr.let_ ty val body) ",
                    "(KExpr.let_ ty' val body) ",
                    "(KExpr.let_ ty' val' body') ",
                    "(beta_reduces_star_let_ty ty ty' val body ihty) ",
                    "(beta_reduces_star_trans ",
                    "(KExpr.let_ ty' val body) ",
                    "(KExpr.let_ ty' val' body) ",
                    "(KExpr.let_ ty' val' body') ",
                    "(beta_reduces_star_let_val ty' val val' body ihval) ",
                    "(beta_reduces_star_let_body ty' val' body body' ihbody))) ",
                    // proj : s i sub sub', h_sub, ih_sub -> beta_reduces_star_proj
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces sub sub') (ihsub : beta_reduces_star sub sub') => ",
                    "beta_reduces_star_proj s i sub sub' ihsub) ",
                    // indices + major
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Every single-step parallel reduction is simulated by a finite sequence of ",
                "single-step beta reductions. Derived by structural induction on par_reduces.rec ",
                "in canonical left-to-right outermost-first order, composing beta_reduces_star_trans ",
                "and the single-position star-congruence helpers to lift reductions under ",
                "each binder, with one beta_reduces.beta (resp. beta_reduces.zeta) head ",
                "contraction appended for the beta (resp. let_) contraction cases. The forall_ ",
                "arm reuses the pi path through the reducible KExpr.forall_ surface alias; the ",
                "let_ (zeta) and let_cong arms use the genuine-KExpr.let_ positional star ",
                "congruences (let-promotion). Kernel-checked, DerivedProved, ",
                "zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces".to_string(),
                "par_reduces.rec".to_string(),
                "beta_reduces".to_string(),
                "beta_reduces.beta".to_string(),
                "beta_reduces.zeta".to_string(),
                "beta_reduces.iota".to_string(),
                "beta_reduces_star".to_string(),
                "beta_reduces_star.refl".to_string(),
                "beta_reduces_star.step".to_string(),
                "beta_reduces_subsumes_star".to_string(),
                "beta_reduces_star_trans".to_string(),
                "beta_reduces_star_app_left".to_string(),
                "beta_reduces_star_app_right".to_string(),
                "beta_reduces_star_lam_ty".to_string(),
                "beta_reduces_star_lam_body".to_string(),
                "beta_reduces_star_pi_dom".to_string(),
                "beta_reduces_star_pi_cod".to_string(),
                "beta_reduces_star_let_ty".to_string(),
                "beta_reduces_star_let_val".to_string(),
                "beta_reduces_star_let_body".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // par_reduces_star — reflexive-transitive closure of par_reduces
        // (Wave 120)
        // =========================================================
        //
        // The Tait-Martin-Löf argument concludes confluence of beta_reduces
        // at the multi-step level. The two halves of the chain (beta* ⊆ par*
        // and par* ⊆ beta*) are both stated over RT-closures. par_reduces is
        // single-step and reflexive (par_reduces.refl) but not transitive, so
        // we add its RT-closure explicitly, mirroring beta_reduces_star.
        //
        // It is also the correct target for the corrected `par_subsumes_beta`
        // (see the OBSTRUCTION note above): `beta_reduces e e' →
        // par_reduces_star e e'`. (Historically the star target absorbed the
        // pre-promotion bundled `let_body` arm's two reductions; post
        // let-promotion every beta_reduces arm is a single par step or a
        // single-position congruence, and the star target is kept for the
        // congruence lifting.)
        self.add_inductive(
            r"inductive par_reduces_star : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_star e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), par_reduces e e' → par_reduces_star e' e'' → par_reduces_star e e''",
            "par_reduces_star e e'' is the reflexive-transitive closure of par_reduces: either e = e'' (refl) or e parallel-reduces to an intermediate e' that continues to e''. The multi-step level at which the Tait-Martin-Löf confluence conclusion lives. Part of #2859 Packet 2.",
        )?;

        // par_subsumes_par_star : par_reduces e e' → par_reduces_star e e'.
        // Single parallel step embeds into its RT-closure, built directly
        // from the constructors (no recursion). DerivedProved.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_par_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces e e' -> par_reduces_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : par_reduces e e') => ",
                    "par_reduces_star.step e e' e' h (par_reduces_star.refl e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-step par_reduces embeds into par_reduces_star: ",
                "build the witness directly via par_reduces_star.step with the ",
                "singleton tail filled by par_reduces_star.refl. DerivedProved, ",
                "zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces".to_string(),
                "par_reduces_star".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_trans : transitivity of par_reduces_star.
        // Structural induction on the first argument via par_reduces_star.rec,
        // generalizing the motive over the second star and prefixing each step
        // onto the recursively-extended tail (the par-level analogue of
        // beta_reduces_star_trans). DerivedProved.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_trans".to_string(),
            type_src: concat!(
                "forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "par_reduces_star e1 e2 -> par_reduces_star e2 e3 -> ",
                "par_reduces_star e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : par_reduces_star e1 e2) ",
                    "(h2 : par_reduces_star e2 e3) => ",
                    "par_reduces_star.rec ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(_ : par_reduces_star a b) => ",
                    "par_reduces_star b e3 -> par_reduces_star a e3) ",
                    "(fun (e : KExpr) (k : par_reduces_star e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star e'' e3 -> par_reduces_star e' e3) ",
                    "(k : par_reduces_star e'' e3) => ",
                    "par_reduces_star.step e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of par_reduces_star (reflexive-transitive ",
                "closure of par_reduces). Proved by structural induction on ",
                "the first argument via par_reduces_star.rec, prefixing each ",
                "step constructor onto the recursively-extended tail. ",
                "DerivedProved, zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // par_reduces single-side congruence wrappers (Wave 116)
        // =========================================================
        //
        // The `par_subsumes_beta` recursor (Packet B) maps each binary
        // congruence constructor of `beta_reduces` to the matching
        // `par_reduces` constructor with `par_refl` filling the
        // non-reducing side. These three closed-form wrappers package that
        // pattern so the recursor arms reduce to a single named lemma
        // application instead of inlining the `par_refl`-padded
        // constructor each time. Each is a direct constructor application
        // — no recursion — so the kernel type-checks the term at
        // add_decl time with zero axiom dependencies. DerivedProved.

        // par_reduces_app_left : congruence on the head of an application
        // with the argument held fixed (the `app_left` arm of
        // par_subsumes_beta).
        //
        //   fun (f f' a : KExpr) (h : par_reduces f f') =>
        //     par_reduces.app f f' a a h (par_reduces.refl a)
        self.add_definition(SpecDefinition {
            name: "par_reduces_app_left".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (f' : KExpr) (a : KExpr), ",
                "par_reduces f f' -> ",
                "par_reduces (KExpr.app f a) (KExpr.app f' a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(h : par_reduces f f') => ",
                    "par_reduces.app f f' a a h (par_reduces.refl a)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Left congruence of par_reduces over application: reduce the ",
                "head, hold the argument fixed via par_reduces.refl. ",
                "DerivedProved closed term, zero axiom_deps. Wrapper for the ",
                "app_left arm of par_subsumes_beta. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces".to_string(),
                "par_reduces.app".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_app_right : congruence on the argument of an
        // application with the head held fixed (the `app_right` arm).
        //
        //   fun (f a a' : KExpr) (h : par_reduces a a') =>
        //     par_reduces.app f f a a' (par_reduces.refl f) h
        self.add_definition(SpecDefinition {
            name: "par_reduces_app_right".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces a a' -> ",
                "par_reduces (KExpr.app f a) (KExpr.app f a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(h : par_reduces a a') => ",
                    "par_reduces.app f f a a' (par_reduces.refl f) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Right congruence of par_reduces over application: reduce the ",
                "argument, hold the head fixed via par_reduces.refl. ",
                "DerivedProved closed term, zero axiom_deps. Wrapper for the ",
                "app_right arm of par_subsumes_beta. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces".to_string(),
                "par_reduces.app".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_iota_lift : lift an iota_reduces witness into
        // par_reduces (the `iota` arm of par_subsumes_beta).
        //
        //   fun (e e' : KExpr) (h : iota_reduces e e') =>
        //     par_reduces.iota e e' h
        self.add_definition(SpecDefinition {
            name: "par_reduces_iota_lift".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "iota_reduces e e' -> par_reduces e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(h : iota_reduces e e') => ",
                    "par_reduces.iota e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lift a single-step iota_reduces witness into par_reduces via ",
                "the par_reduces.iota constructor. DerivedProved closed term, ",
                "zero axiom_deps. Wrapper for the iota arm of ",
                "par_subsumes_beta. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces".to_string(),
                "par_reduces.iota".to_string(),
                "iota_reduces".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // par_reduces_star single-position congruence helpers (Wave 121)
        // =========================================================
        //
        // The par-level analogues of the Wave 118 beta_reduces_star
        // congruence helpers: lift a multi-step parallel reduction in one
        // subterm position into the surrounding constructor, sibling
        // positions fixed. Common proof shape: induction on the input
        // par_reduces_star via par_reduces_star.rec with motive
        //   fun (x y : KExpr) (_ : par_reduces_star x y) =>
        //     par_reduces_star (C .. x ..) (C .. y ..)
        // refl returns par_reduces_star.refl at the framed shape; step
        // prefixes the matching single-step par_reduces congruence
        // constructor (with par_reduces.refl on the fixed side) via
        // par_reduces_star.step. Zero axiom_deps; DerivedProved. These are
        // the per-position lifting primitives `par_subsumes_beta_star`
        // composes for the congruence arms of beta_reduces.rec.

        // par_reduces_star_app_left : reduce the head, argument fixed.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_app_left".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (f' : KExpr) (a : KExpr), ",
                "par_reduces_star f f' -> ",
                "par_reduces_star (KExpr.app f a) (KExpr.app f' a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(h : par_reduces_star f f') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.app x a) (KExpr.app y a)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.app e a)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.app e' a) (KExpr.app e'' a)) => ",
                    "par_reduces_star.step (KExpr.app e a) (KExpr.app e' a) ",
                    "(KExpr.app e'' a) ",
                    "(par_reduces.app e e' a a hstep (par_reduces.refl a)) ih) ",
                    "f f' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level left congruence over application for par_reduces. ",
                "Proved by par_reduces_star.rec prefixing par_reduces.app (with ",
                "par_reduces.refl on the argument) on each step. DerivedProved, ",
                "zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.app".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_app_right : reduce the argument, head fixed.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_app_right".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_star a a' -> ",
                "par_reduces_star (KExpr.app f a) (KExpr.app f a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(h : par_reduces_star a a') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.app f x) (KExpr.app f y)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.app f e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.app f e') (KExpr.app f e'')) => ",
                    "par_reduces_star.step (KExpr.app f e) (KExpr.app f e') ",
                    "(KExpr.app f e'') ",
                    "(par_reduces.app f f e e' (par_reduces.refl f) hstep) ih) ",
                    "a a' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level right congruence over application for par_reduces. ",
                "Proved by par_reduces_star.rec prefixing par_reduces.app (with ",
                "par_reduces.refl on the head) on each step. DerivedProved, zero ",
                "axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.app".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_lam_ty : reduce the lambda binder type, body fixed.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_lam_ty".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (ty' : KExpr) (body : KExpr), ",
                "par_reduces_star ty ty' -> ",
                "par_reduces_star (KExpr.lam ty body) (KExpr.lam ty' body)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
                    "(h : par_reduces_star ty ty') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.lam x body) (KExpr.lam y body)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.lam e body)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.lam e' body) (KExpr.lam e'' body)) => ",
                    "par_reduces_star.step (KExpr.lam e body) (KExpr.lam e' body) ",
                    "(KExpr.lam e'' body) ",
                    "(par_reduces.lam e e' body body hstep (par_reduces.refl body)) ih) ",
                    "ty ty' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the lambda binder type for ",
                "par_reduces. DerivedProved, zero axiom_deps. Part of #2859 ",
                "Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.lam".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_lam_body : reduce the lambda body, type fixed.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_lam_body".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_star body body' -> ",
                "par_reduces_star (KExpr.lam ty body) (KExpr.lam ty body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(h : par_reduces_star body body') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.lam ty x) (KExpr.lam ty y)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.lam ty e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.lam ty e') (KExpr.lam ty e'')) => ",
                    "par_reduces_star.step (KExpr.lam ty e) (KExpr.lam ty e') ",
                    "(KExpr.lam ty e'') ",
                    "(par_reduces.lam ty ty e e' (par_reduces.refl ty) hstep) ih) ",
                    "body body' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the lambda body for par_reduces. ",
                "DerivedProved, zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.lam".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_pi_dom : reduce the Pi domain, body fixed.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_pi_dom".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (dom' : KExpr) (body : KExpr), ",
                "par_reduces_star dom dom' -> ",
                "par_reduces_star (KExpr.pi dom body) (KExpr.pi dom' body)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(h : par_reduces_star dom dom') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.pi x body) (KExpr.pi y body)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.pi e body)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.pi e' body) (KExpr.pi e'' body)) => ",
                    "par_reduces_star.step (KExpr.pi e body) (KExpr.pi e' body) ",
                    "(KExpr.pi e'' body) ",
                    "(par_reduces.pi e e' body body hstep (par_reduces.refl body)) ih) ",
                    "dom dom' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the Pi domain for par_reduces. ",
                "DerivedProved, zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.pi".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_pi_cod : reduce the Pi codomain, domain fixed.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_pi_cod".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_star body body' -> ",
                "par_reduces_star (KExpr.pi dom body) (KExpr.pi dom body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(h : par_reduces_star body body') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.pi dom x) (KExpr.pi dom y)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.pi dom e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.pi dom e') (KExpr.pi dom e'')) => ",
                    "par_reduces_star.step (KExpr.pi dom e) (KExpr.pi dom e') ",
                    "(KExpr.pi dom e'') ",
                    "(par_reduces.pi dom dom e e' (par_reduces.refl dom) hstep) ih) ",
                    "body body' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the Pi codomain for par_reduces. ",
                "DerivedProved, zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.pi".to_string(),
                "par_reduces.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_star_let_ty / _let_val / _let_body : the three
        // single-position star congruences over the GENUINE KExpr.let_
        // constructor for par_reduces. Same Wave-121 proof shape; the
        // per-step witness is par_reduces.let_cong with par_reduces.refl
        // padding on the two fixed positions (par_reduces has no dedicated
        // single-position let constructors). Consumed by
        // par_subsumes_beta_star's let_ty/let_val/let_body arms.
        for (name, params, src_lhs, src_rhs, frame, step_term, what) in [
            (
                "par_reduces_star_let_ty",
                "(ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr)",
                "ty",
                "ty'",
                "(KExpr.let_ {} val body)",
                concat!(
                    "par_reduces.let_cong e e' val val body body hstep ",
                    "(par_reduces.refl val) (par_reduces.refl body)"
                ),
                "let binder type",
            ),
            (
                "par_reduces_star_let_val",
                "(ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr)",
                "val",
                "val'",
                "(KExpr.let_ ty {} body)",
                concat!(
                    "par_reduces.let_cong ty ty e e' body body ",
                    "(par_reduces.refl ty) hstep (par_reduces.refl body)"
                ),
                "let value",
            ),
            (
                "par_reduces_star_let_body",
                "(ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr)",
                "body",
                "body'",
                "(KExpr.let_ ty val {})",
                concat!(
                    "par_reduces.let_cong ty ty val val e e' ",
                    "(par_reduces.refl ty) (par_reduces.refl val) hstep"
                ),
                "let body",
            ),
        ] {
            let frame_with = |m: &str| frame.replacen("{}", m, 1);
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall {params}, ",
                        "par_reduces_star {src_lhs} {src_rhs} -> ",
                        "par_reduces_star {frame_lhs} {frame_rhs}"
                    ),
                    params = params,
                    src_lhs = src_lhs,
                    src_rhs = src_rhs,
                    frame_lhs = frame_with(src_lhs),
                    frame_rhs = frame_with(src_rhs),
                ),
                value_src: Some(format!(
                    concat!(
                        "fun {params} ",
                        "(h : par_reduces_star {src_lhs} {src_rhs}) => ",
                        "par_reduces_star.rec ",
                        "(fun (x : KExpr) (y : KExpr) ",
                        "(_ : par_reduces_star x y) => ",
                        "par_reduces_star {frame_x} {frame_y}) ",
                        "(fun (e : KExpr) => par_reduces_star.refl {frame_e}) ",
                        "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                        "(hstep : par_reduces e e') ",
                        "(_htail : par_reduces_star e' e'') ",
                        "(ih : par_reduces_star {frame_ep} {frame_epp}) => ",
                        "par_reduces_star.step {frame_e} {frame_ep} ",
                        "{frame_epp} ({step_term}) ih) ",
                        "{src_lhs} {src_rhs} h"
                    ),
                    params = params,
                    src_lhs = src_lhs,
                    src_rhs = src_rhs,
                    frame_x = frame_with("x"),
                    frame_y = frame_with("y"),
                    frame_e = frame_with("e"),
                    frame_ep = frame_with("e'"),
                    frame_epp = frame_with("e''"),
                    step_term = step_term,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Star-level congruence over the {what} position of the ",
                        "genuine KExpr.let_ constructor for par_reduces. Proved ",
                        "by par_reduces_star.rec prefixing par_reduces.let_cong ",
                        "(refl-padded on the fixed positions) on each step. ",
                        "DerivedProved, zero axiom_deps. Part of the ",
                        "let-promotion confluence batch (#2859 Packet 2 shape)."
                    ),
                    what = what,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_star".to_string(),
                    "par_reduces_star.rec".to_string(),
                    "par_reduces_star.refl".to_string(),
                    "par_reduces_star.step".to_string(),
                    "par_reduces.let_cong".to_string(),
                    "par_reduces.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_star_proj : reduce under the projection scrutinee.
        self.add_definition(SpecDefinition {
            name: "par_reduces_star_proj".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), ",
                "par_reduces_star sub sub' -> ",
                "par_reduces_star (KExpr.proj s i sub) (KExpr.proj s i sub')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(h : par_reduces_star sub sub') => ",
                    "par_reduces_star.rec ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(_ : par_reduces_star x y) => ",
                    "par_reduces_star (KExpr.proj s i x) (KExpr.proj s i y)) ",
                    "(fun (e : KExpr) => par_reduces_star.refl (KExpr.proj s i e)) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces e e') ",
                    "(_htail : par_reduces_star e' e'') ",
                    "(ih : par_reduces_star (KExpr.proj s i e') (KExpr.proj s i e'')) => ",
                    "par_reduces_star.step (KExpr.proj s i e) (KExpr.proj s i e') ",
                    "(KExpr.proj s i e'') ",
                    "(par_reduces.proj s i e e' hstep) ih) ",
                    "sub sub' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level congruence over the scrutinee of the KExpr.proj ",
                "constructor for par_reduces. Proved by par_reduces_star.rec ",
                "prefixing par_reduces.proj on each step. DerivedProved, zero ",
                "axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_star".to_string(),
                "par_reduces_star.rec".to_string(),
                "par_reduces_star.refl".to_string(),
                "par_reduces_star.step".to_string(),
                "par_reduces.proj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // par_subsumes_beta_star : beta_reduces e e' → par_reduces_star e e'
        // (Wave 121) — the CORRECTED beta ⊆ par* embedding.
        // =========================================================
        //
        // Replaces the unprovable single→single `par_subsumes_beta` (see the
        // OBSTRUCTION note at its registration). Structural induction on
        // beta_reduces.rec, motive
        //   fun (e e' : KExpr) (_ : beta_reduces e e') => par_reduces_star e e'
        // Each of the 14 beta_reduces constructors maps to a par_reduces_star:
        //
        //   beta              : single par-step (par_reduces.beta with refls)
        //                       embedded via par_subsumes_par_star.
        //   app_left/right    : lift the IH (par_reduces_star) through the
        //                       matching par_reduces_star congruence helper.
        //   lam_ty/body       : par_reduces_star_lam_ty / _lam_body on the IH.
        //   pi_dom/cod        : par_reduces_star_pi_dom / _pi_cod on the IH.
        //   forall_congr_*    : same as pi via the reducible KExpr.forall_
        //                       alias.
        //   zeta              : single par-step (par_reduces.let_ — the
        //                       parallel zeta — with refls) embedded via
        //                       par_subsumes_par_star. (The pre-promotion
        //                       bundled let_body arm needed a two-step
        //                       composition here; the genuine zeta is one
        //                       parallel step.)
        //   let_ty/val/body   : par_reduces_star_let_ty / _let_val / _let_body
        //                       on the IH (the genuine-KExpr.let_ positional
        //                       congruences).
        //   iota              : par_reduces.iota embedded via
        //                       par_subsumes_par_star.
        //
        // Kernel-checked, DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_beta_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "beta_reduces e e' -> par_reduces_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) (h0 : beta_reduces e0 e0') => ",
                    "beta_reduces.rec ",
                    "(fun (e : KExpr) (e' : KExpr) (_ : beta_reduces e e') => ",
                    "par_reduces_star e e') ",
                    // beta : A body arg
                    "(fun (A : KExpr) (body : KExpr) (arg : KExpr) => ",
                    "par_subsumes_par_star ",
                    "(KExpr.app (KExpr.lam A body) arg) (instantiate body arg) ",
                    "(par_reduces.beta A A body body arg arg ",
                    "(par_reduces.refl A) (par_reduces.refl body) (par_reduces.refl arg))) ",
                    // app_left : f f' a, hf, ih : par_reduces_star f f'
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(_hf : beta_reduces f f') (ih : par_reduces_star f f') => ",
                    "par_reduces_star_app_left f f' a ih) ",
                    // app_right : f a a', ha, ih : par_reduces_star a a'
                    "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_ha : beta_reduces a a') (ih : par_reduces_star a a') => ",
                    "par_reduces_star_app_right f a a' ih) ",
                    // lam_ty : ty ty' body, hty, ih
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
                    "(_hty : beta_reduces ty ty') (ih : par_reduces_star ty ty') => ",
                    "par_reduces_star_lam_ty ty ty' body ih) ",
                    // lam_body : ty body body', hb, ih
                    "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hb : beta_reduces body body') (ih : par_reduces_star body body') => ",
                    "par_reduces_star_lam_body ty body body' ih) ",
                    // pi_dom : dom dom' body, hd, ih
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(_hd : beta_reduces dom dom') (ih : par_reduces_star dom dom') => ",
                    "par_reduces_star_pi_dom dom dom' body ih) ",
                    // pi_cod : dom body body', hb, ih
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hb : beta_reduces body body') (ih : par_reduces_star body body') => ",
                    "par_reduces_star_pi_cod dom body body' ih) ",
                    // forall_congr_dom : dom dom' body, hd, ih (alias of pi)
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(_hd : beta_reduces dom dom') (ih : par_reduces_star dom dom') => ",
                    "par_reduces_star_pi_dom dom dom' body ih) ",
                    // forall_congr_cod : dom body body', hb, ih (alias of pi)
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hb : beta_reduces body body') (ih : par_reduces_star body body') => ",
                    "par_reduces_star_pi_cod dom body body' ih) ",
                    // zeta : ty val body — single par-step (parallel zeta with refls)
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) => ",
                    "par_subsumes_par_star ",
                    "(KExpr.let_ ty val body) (instantiate body val) ",
                    "(par_reduces.let_ ty ty val val body body ",
                    "(par_reduces.refl ty) (par_reduces.refl val) (par_reduces.refl body))) ",
                    // let_ty : ty ty' val body, hty, ih
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
                    "(_hty : beta_reduces ty ty') (ih : par_reduces_star ty ty') => ",
                    "par_reduces_star_let_ty ty ty' val body ih) ",
                    // let_val : ty val val' body, hval, ih
                    "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
                    "(_hval : beta_reduces val val') (ih : par_reduces_star val val') => ",
                    "par_reduces_star_let_val ty val val' body ih) ",
                    // let_body : ty val body body', hbody, ih
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hbody : beta_reduces body body') (ih : par_reduces_star body body') => ",
                    "par_reduces_star_let_body ty val body body' ih) ",
                    // iota : e e', h
                    "(fun (e : KExpr) (e' : KExpr) (h : iota_reduces e e') => ",
                    "par_subsumes_par_star e e' (par_reduces.iota e e' h)) ",
                    // proj : s i sub sub', hsub, ih : par_reduces_star sub sub'
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : beta_reduces sub sub') (ih : par_reduces_star sub sub') => ",
                    "par_reduces_star_proj s i sub sub' ih) ",
                    // indices + major
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Every single-step beta reduction embeds into the reflexive-transitive ",
                "closure of parallel reduction (the corrected beta ⊆ par* direction, ",
                "replacing the unprovable single→single par_subsumes_beta). Structural ",
                "induction on beta_reduces.rec: the beta/zeta/iota arms embed a single ",
                "par-step via par_subsumes_par_star (zeta via par_reduces.let_, the ",
                "parallel zeta on the genuine KExpr.let_ constructor); the congruence ",
                "arms lift the IH through the par_reduces_star congruence helpers ",
                "(forall_ via the pi alias, let_ty/let_val/let_body via the ",
                "genuine-let_ positional helpers). Kernel-checked, DerivedProved, ",
                "zero axiom_deps. Part of #2859 Packet 2."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces".to_string(),
                "beta_reduces.rec".to_string(),
                "par_reduces".to_string(),
                "par_reduces.refl".to_string(),
                "par_reduces.beta".to_string(),
                "par_reduces.let_".to_string(),
                "par_reduces.iota".to_string(),
                "par_reduces_star".to_string(),
                "par_subsumes_par_star".to_string(),
                "par_reduces_star_app_left".to_string(),
                "par_reduces_star_app_right".to_string(),
                "par_reduces_star_lam_ty".to_string(),
                "par_reduces_star_lam_body".to_string(),
                "par_reduces_star_pi_dom".to_string(),
                "par_reduces_star_pi_cod".to_string(),
                "par_reduces_star_let_ty".to_string(),
                "par_reduces_star_let_val".to_string(),
                "par_reduces_star_let_body".to_string(),
                "par_reduces_star_proj".to_string(),
                "par_reduces.proj".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 133 (Route B) — iota-free single-step diamond scaffold.
        // =========================================================
        //
        // par_strips_witness_bd : KExpr → KExpr → Type
        //
        // The iota-free analogue of par_strips_witness. Packages the
        // single-step diamond conclusion over the iota-free relation
        // `par_reduces_bd`: a common reduct e3 together with
        // par_reduces_bd e1 e3 and par_reduces_bd e2 e3. Mirrors
        // par_strips_witness (par_reduction.rs:723), swapping
        // par_reduces → par_reduces_bd. Encodes the existential meeting
        // point without a Sigma/Exists type (not in the current spec
        // fragment). Consumed by par_strips_bd (the 64-case diamond) and,
        // via the iota seam (Wave 127 of the plan), by the full par_strips.
        self.add_inductive(
            r"inductive par_strips_witness_bd : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_bd e1 e3 → par_reduces_bd e2 e3 → par_strips_witness_bd e1 e2",
            "par_strips_witness_bd e1 e2 packages the iota-free single-step diamond conclusion: a common reduct e3 together with par_reduces_bd e1 e3 and par_reduces_bd e2 e3. The iota-free analogue of par_strips_witness (Route B). Encodes the existential meeting point without a Sigma/Exists type. Part of #2859 Wave 133.",
        )?;

        // =========================================================
        // Wave 136 (Route B) — par_reduces_bd shape-recovery (inversion).
        // =========================================================
        //
        // The convoy lemmas par_strips_bd's inner case-split needs: from a
        // par_reduces_bd derivation whose SOURCE has a concrete constructor
        // shape, recover which constructor fired and its sub-derivations.
        // Delivered in continuation-passing (motive-eliminator) form so no
        // Sigma/Or carrier is needed. Proved by par_reduces_bd.rec with a
        // source-equation motive; matching arms recover sub-terms by
        // injectivity (app_inj_fst/snd, lam_inj_*, pi_inj_*) and transport
        // sub-derivations with Eq.subst, mismatched arms discharge by
        // no-confusion (lam_ne_app/pi_ne_app/app_ne_lam/pi_ne_lam/app_ne_pi/
        // lam_ne_pi, plus the let-promotion let_ne_app/let_ne_lam/let_ne_pi
        // for the now-genuinely-let_-headed let_/let_cong sources).
        // DerivedProved (full kernel type-check), zero axiom_deps.
        //
        // par_reduces_bd_app_inv : from par_reduces_bd (app f a) t, give either
        //   the congruence case (t = app f' a' with f => f', a => a') or the
        //   contraction case (f = lam A body, t = instantiate body' arg'). The
        //   refl and app constructors fold into the congruence continuation; the
        //   beta constructor folds into the contraction continuation;
        //   lam/pi/forall_ are impossible, and — post let-promotion — so are
        //   let_ (zeta) and let_cong (a let is let_-headed, never app-headed;
        //   discharged by let_ne_app).
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_app_inv".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_bd (KExpr.app f a) t -> ",
                "(forall (f' : KExpr) (a' : KExpr), ",
                "par_reduces_bd f f' -> par_reduces_bd a a' -> C (KExpr.app f' a')) -> ",
                "(forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(arg' : KExpr), Eq KExpr f (KExpr.lam A body) -> ",
                "par_reduces_bd A A' -> par_reduces_bd body body' -> par_reduces_bd a arg' -> ",
                "C (instantiate body' arg')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_app_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for an app-headed iota-free parallel reduction: ",
                "from par_reduces_bd (app f a) t, dispatch to the congruence continuation ",
                "(t = app f' a' with f => f', a => a') or the contraction continuation ",
                "(f = lam A body, t = instantiate body' arg'). refl/app fold into the former, ",
                "beta into the latter; lam/pi/forall_ are discharged by no-confusion, and ",
                "post let-promotion so are the let_-headed let_ (zeta) and let_cong sources ",
                "(let_ne_app). Continuation-passing form (no Sigma/Or carrier). DerivedProved via ",
                "par_reduces_bd.rec with a source-equation motive + app injectivity + Eq.subst. ",
                "Zero axiom_deps. Part of #2859 Wave 136 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "lam_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "let_ne_app".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_lam_inv : from par_reduces_bd (lam ty body) t, recover
        //   t = lam ty' body' with ty => ty', body => body'. refl folds in with
        //   reflexive sub-derivations; every non-lam constructor is impossible
        //   (app-headed beta/app via app_ne_lam, pi-headed pi/forall_ via
        //   pi_ne_lam, let_-headed let_/let_cong via let_ne_lam).
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_lam_inv".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_bd (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "par_reduces_bd ty ty' -> par_reduces_bd body body' -> ",
                "C (KExpr.lam ty' body')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_lam_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a lam-headed iota-free parallel reduction: ",
                "from par_reduces_bd (lam ty body) t, recover t = lam ty' body' with ty => ty' ",
                "and body => body'. refl folds in with reflexive sub-derivations; the lam arm is ",
                "the genuine congruence; all other arms are impossible (app_ne_lam for ",
                "beta/app, pi_ne_lam for pi/forall_, let_ne_lam for the let_-headed ",
                "let_/let_cong). Continuation-passing form. DerivedProved ",
                "via par_reduces_bd.rec with a source-equation motive + lam injectivity + Eq.subst. ",
                "Zero axiom_deps. Part of #2859 Wave 136 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_pi_inv / par_reduces_bd_forall_inv : the two pi-headed
        // inversions. Because KExpr.forall_ is the reducible alias of KExpr.pi,
        // BOTH the pi and forall_ constructor arms are genuine matching cases
        // (their sources are definitionally equal), recovering sub-terms via
        // pi_inj_fst/snd. The app-headed (beta/app) and lam arms are
        // discharged by app_ne_pi / lam_ne_pi; the let_-headed let_/let_cong
        // arms by let_ne_pi (post let-promotion a let is NOT app-headed). The
        // two lemmas differ only in
        // the source head and the reduct head passed to the continuation.
        for (name, head, red_head, label) in [
            ("par_reduces_bd_pi_inv", "KExpr.pi", "KExpr.pi", "pi"),
            (
                "par_reduces_bd_forall_inv",
                "KExpr.forall_",
                "KExpr.forall_",
                "forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (dom : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                        "par_reduces_bd ({head} dom body) t -> ",
                        "(forall (dom' : KExpr) (body' : KExpr), ",
                        "par_reduces_bd dom dom' -> par_reduces_bd body body' -> ",
                        "C ({red_head} dom' body')) -> ",
                        "C t"
                    ),
                    head = head,
                    red_head = red_head,
                ),
                value_src: Some(par_reduces_bd_pi_like_inv_proof(head, red_head)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Shape-recovery (inversion) for a {label}-headed iota-free parallel ",
                        "reduction: from par_reduces_bd ({head} dom body) t, recover ",
                        "t = {red_head} dom' body' with dom => dom' and body => body'. Both the ",
                        "pi and forall_ arms match (forall_ is the reducible pi alias); refl folds ",
                        "in; beta/app are discharged by app_ne_pi, lam by lam_ne_pi, and the ",
                        "let_-headed let_/let_cong by let_ne_pi (let-promotion). ",
                        "Continuation-passing form. DerivedProved via par_reduces_bd.rec with a ",
                        "source-equation motive + pi injectivity + Eq.subst. Zero axiom_deps. ",
                        "Part of #2859 Wave 136 (Route B)."
                    ),
                    label = label,
                    head = head,
                    red_head = red_head,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_bd".to_string(),
                    "par_reduces_bd.rec".to_string(),
                    "par_reduces_bd.refl".to_string(),
                    "pi_inj_fst".to_string(),
                    "pi_inj_snd".to_string(),
                    "app_ne_pi".to_string(),
                    "lam_ne_pi".to_string(),
                    "let_ne_pi".to_string(),
                    "instantiate".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_bd_let_inv : the let_-headed inversion (NEW with the
        // let-promotion — before it a let was app-headed and the app inversion
        // covered it). From par_reduces_bd (KExpr.let_ ty val body) t, dispatch
        // to the congruence continuation (t = let_ ty' val' body' with
        // ty => ty', val => val', body => body'; refl and let_cong fold in) or
        // the ZETA continuation (t = instantiate body' val' with the same
        // three sub-derivations; the let_ constructor). beta/app are
        // app-headed (app_ne_let), lam is lam-headed (lam_ne_let), pi/forall_
        // are pi-headed (pi_ne_let) — all impossible against a let_ source.
        // The matching arms recover sub-terms via let_ injectivity
        // (let_inj_fst/snd/thd) and transport with Eq.subst. This is the
        // convoy lemma par_strips_bd's let_ (zeta) and let_cong outer arms
        // consume.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_let_inv".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (val : KExpr) (body : KExpr) (t : KExpr) ",
                "(C : KExpr -> Type), ",
                "par_reduces_bd (KExpr.let_ ty val body) t -> ",
                "(forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
                "par_reduces_bd ty ty' -> par_reduces_bd val val' -> ",
                "par_reduces_bd body body' -> C (KExpr.let_ ty' val' body')) -> ",
                "(forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
                "par_reduces_bd ty ty' -> par_reduces_bd val val' -> ",
                "par_reduces_bd body body' -> C (instantiate body' val')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_let_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a let_-headed iota-free parallel reduction ",
                "(let-promotion): from par_reduces_bd (KExpr.let_ ty val body) t, dispatch to ",
                "the congruence continuation (t = let_ ty' val' body'; refl/let_cong fold in) ",
                "or the zeta continuation (t = instantiate body' val'; the let_ constructor), ",
                "each carrying ty => ty', val => val', body => body'. beta/app are discharged ",
                "by app_ne_let, lam by lam_ne_let, pi/forall_ by pi_ne_let; matching arms ",
                "recover sub-terms via let_inj_fst/snd/thd + Eq.subst. Continuation-passing ",
                "form (no Sigma/Or carrier). DerivedProved via par_reduces_bd.rec with a ",
                "source-equation motive. Zero axiom_deps. Part of the let-promotion ",
                "confluence batch (#2859 Wave 136 shape)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "let_inj_fst".to_string(),
                "let_inj_snd".to_string(),
                "let_inj_thd".to_string(),
                "app_ne_let".to_string(),
                "lam_ne_let".to_string(),
                "pi_ne_let".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_proj_inv : shape-recovery (inversion) for a proj-headed
        // iota-free parallel reduction (proj/lit fragment rung). proj is a pure
        // single-position congruence, so from par_reduces_bd (proj s i sub) t the
        // only shapes are refl (t = proj s i sub) and proj-cong (t = proj s i
        // sub' with sub => sub'); both feed the single kproj continuation. Every
        // other constructor has an app/lam/pi/let_-headed source, impossible
        // against a proj target — discharged by app_ne_proj / lam_ne_proj /
        // pi_ne_proj / let_ne_proj. The matching proj arm recovers the components
        // via proj_inj_name/idx/sub and transports with Eq.subst. This is the
        // convoy lemma par_strips_bd's proj outer arm consumes.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_proj_inv".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub : KExpr) (t : KExpr) ",
                "(C : KExpr -> Type), ",
                "par_reduces_bd (KExpr.proj s i sub) t -> ",
                "(forall (sub' : KExpr), ",
                "par_reduces_bd sub sub' -> C (KExpr.proj s i sub')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_proj_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Shape-recovery (inversion) for a proj-headed iota-free parallel reduction ",
                "(proj/lit fragment rung): from par_reduces_bd (KExpr.proj s i sub) t, ",
                "dispatch to the single kproj continuation (t = proj s i sub' with ",
                "sub => sub'; refl/proj fold in). beta/app are discharged by app_ne_proj, ",
                "lam by lam_ne_proj, pi/forall_ by pi_ne_proj, let_/let_cong by let_ne_proj; ",
                "the matching proj arm recovers the components via proj_inj_name/idx/sub + ",
                "Eq.subst. Continuation-passing form (no Sigma/Or carrier). DerivedProved via ",
                "par_reduces_bd.rec with a source-equation motive. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "proj_inj_name".to_string(),
                "proj_inj_idx".to_string(),
                "proj_inj_sub".to_string(),
                "app_ne_proj".to_string(),
                "lam_ne_proj".to_string(),
                "pi_ne_proj".to_string(),
                "let_ne_proj".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 137 (Route B) — par_strips_bd assembly support.
        // =========================================================
        //
        // Three closed leaves the full diamond reduces to. See the proof-term
        // function docs at the bottom of this file for the constructions.

        // par_reduces_bd_lam_inv_eq : Eq-DATA lam inversion. Unlike the Wave 136
        // continuation-passing inversion (which hides the reduct shape in the
        // goal), this hands the continuation the reduct equality
        // Eq t (lam ty' body') as data, so two derivations targeting the SAME
        // reduct can both be transported onto it (the cross-arm meet needs this).
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_lam_inv_eq".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_bd (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.lam ty' body') -> ",
                "par_reduces_bd ty ty' -> par_reduces_bd body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_lam_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Eq-data shape recovery for a lam-headed iota-free parallel reduction: from ",
                "par_reduces_bd (lam ty body) t, hand the continuation the reduct equality ",
                "Eq t (lam ty' body') together with ty => ty' and body => body', returning the ",
                "fixed result type C. The motive returns the arrow Eq e (lam ty body) -> Kont e' -> C ",
                "with Kont parameterized by the arm reduct, so the recursor substitutes the genuine ",
                "reduct t. refl folds in; lam is the match (Eq.refl reduct equation); app/pi/let_- ",
                "headed arms discharged by no-confusion (app_ne_lam/pi_ne_lam/let_ne_lam). ",
                "DerivedProved via par_reduces_bd.rec, zero ",
                "axiom_deps. Part of #2859 Wave 137 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_bd_lam_meet : from a diamond on two lambdas,
        // recover the diamond on their bodies. Projects the lam-lam witness to
        // its common reduct g3, Eq-inverts both legs to lam-shapes, identifies
        // the body meet by lam_inj_snd, and meets the bodies there.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_bd_lam_meet".to_string(),
            type_src: concat!(
                "forall (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr), ",
                "par_strips_witness_bd (KExpr.lam t1 b1) (KExpr.lam t2 b2) -> ",
                "par_strips_witness_bd b1 b2"
            )
            .to_string(),
            value_src: Some(par_strips_witness_bd_lam_meet_proof()),
            is_axiom: false,
            description: concat!(
                "Body sub-meet recovery: from a diamond witness on two lambdas ",
                "par_strips_witness_bd (lam t1 b1) (lam t2 b2), recover the diamond on the bodies ",
                "par_strips_witness_bd b1 b2. Projects to the common reduct g3, Eq-inverts both legs ",
                "(par_reduces_bd_lam_inv_eq) to lam shapes, identifies the body meet via lam_inj_snd ",
                "+ Eq.trans, and meets the bodies there. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 137 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_lam_inv_eq".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd.rec".to_string(),
                "lam_inj_snd".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_bd_app_beta : the (app, beta) cross core. First side is the
        // syntactic redex app (lam Af bodyf) a0p; second is the contracted
        // instantiate bodyq argp. Given the body meet wb and the arg meet wa,
        // meet at instantiate b3 a3 (b3 = body meet, a3 = arg meet): first side
        // beta-contracts (par_reduces_bd.beta), second via par_subst_bd. The
        // outer-app cross arm feeds the body meet via par_strips_witness_bd_lam_meet;
        // the symmetric (beta, app) cross arm is the par_strips_witness_bd_symm image.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_app_beta".to_string(),
            type_src: concat!(
                "forall (Af : KExpr) (bodyf : KExpr) (a0p : KExpr) ",
                "(bodyq : KExpr) (argp : KExpr), ",
                "par_strips_witness_bd bodyf bodyq -> ",
                "par_strips_witness_bd a0p argp -> ",
                "par_strips_witness_bd (KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp)"
            )
            .to_string(),
            value_src: Some(par_strips_bd_app_beta_proof()),
            is_axiom: false,
            description: concat!(
                "The (app, beta) cross core for the iota-free single-step diamond: the first ",
                "side is the syntactic redex app (lam Af bodyf) a0p, the second the contracted ",
                "instantiate bodyq argp. Given the body meet and arg meet, meeting point ",
                "instantiate b3 a3; the first side beta-contracts (par_reduces_bd.beta, reflexive ",
                "domain reduct), the second transports through par_subst_bd. DerivedProved, zero ",
                "axiom_deps. Part of #2859 Wave 137 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.beta".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd.rec".to_string(),
                "par_subst_bd".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_bd : forall e e1 e2,
        //   par_reduces_bd e e1 → par_reduces_bd e e2 → par_strips_witness_bd e1 e2
        //
        // The single-step diamond for the iota-free parallel reduction.
        // Given two iota-free parallel reductions e ⇒ e1 and e ⇒ e2 from a
        // common source, they join at a shared reduct e3 with e1 ⇒ e3 and
        // e2 ⇒ e3. This is the Route-B keystone: it discharges the
        // Tait-Martin-Löf single-step diamond entirely over the
        // beta/congruence fragment, with NO iota constructor in scope, so
        // par_subst_bd (Wave 132) is the only non-structural ingredient and
        // the iota wall never arises. The iota seam is handled separately at
        // the full-par_strips level by forwarding the never-inhabited
        // iota_reduces hypothesis (see the design note, Wave 127).
        //
        // Proof shape (64-case nested eliminator): par_reduces_bd.rec on the
        // first derivation e ⇒ e1 with a motive that universalizes the
        // second target and derivation:
        //   motive := fun (e e1 : KExpr) (_ : par_reduces_bd e e1) =>
        //     forall (e2 : KExpr), par_reduces_bd e e2 → par_strips_witness_bd e1 e2
        // Each of the 8 outer arms case-splits the second derivation via a
        // nested par_reduces_bd.rec (motive carrying a source-equation so the
        // matching arm recovers sub-terms by injectivity and mismatched arms
        // discharge by no-confusion — app_inj_fst/snd, lam_inj_*, pi_inj_*,
        // let_inj_*, *_ne_app, *_ne_let). 8×8 = 64 cases:
        //   (refl, _)            : meet at e2 — par_reduces_bd.refl e2 + h2.
        //   (_, refl)            : meet at e1 — symmetric.
        //   congruence diagonal  : (app,app)/(lam,lam)/(pi,pi)/(forall_,forall_)/
        //                          (let_cong,let_cong) — recurse per
        //                          sub-derivation, reassemble via the matching
        //                          constructor.
        //   (beta, beta)         : meet at instantiate (join body) (join arg),
        //                          justified by par_subst_bd on joined reducts.
        //   (let_, let_) [zeta,zeta] : meet at instantiate (join body) (join
        //                          val) via par_subst_bd — the beta-beta
        //                          mechanism on the genuine let_ constructor.
        //   cross (beta,app)/(app,beta) : re-fold the congruent side into the
        //                          redex shape, join via par_subst_bd.
        //   cross (let_,let_cong)/(let_cong,let_) [zeta-vs-congruence] : the
        //                          congruence side catches up by FIRING the
        //                          zeta (par_reduces_bd.let_ on the joined
        //                          val/body), the contracted side transports
        //                          through par_subst_bd; meet at
        //                          instantiate (join body) (join val).
        //
        // Registered DerivedPending here (statement + plan, empty axiom_deps,
        // NO faked value_src) ahead of the proof-term waves. Per the dispatch
        // fallback, the diagonal/symmetric arms land first as helpers, then the
        // cross/contraction arms, each its own wave.
        //
        // STATUS (Wave 135): the congruence-diagonal arms ((app,app)/(lam,lam)/
        // (pi,pi)/(forall_,forall_)) are now discharged as standalone
        // DerivedProved combinators (par_strips_bd_app/_lam/_pi/_forall below),
        // alongside the (refl,_)/(_,refl) helpers (Wave 134) and a witness
        // symmetry combinator (par_strips_witness_bd_symm). These are the closed
        // leaves the diagonal arms reduce to.
        //
        // STATUS (Wave 136): the inner case-split convoy is no longer blocked.
        // The four par_reduces_bd shape-recovery (inversion) lemmas —
        // par_reduces_bd_app_inv / _lam_inv / _pi_inv / _forall_inv (registered
        // ABOVE) — are now DerivedProved (full kernel type-check). Each takes a
        // par_reduces_bd derivation whose source has a concrete constructor
        // shape and dispatches, in continuation-passing form, to the matching
        // congruence/contraction case (recovering sub-derivations by injectivity
        // + Eq.subst) with the impossible arms discharged by no-confusion. They
        // correctly fold in the forall_≡pi alias overlap (a matching pi case);
        // post let-promotion the let_-headed sources get their OWN inversion
        // (par_reduces_bd_let_inv above — congruence + zeta continuations).
        // These are the exact convoy lemmas the inner case-split of
        // par_strips_bd needs.
        //
        // REMAINING for the full par_strips_bd proof term: assemble the outer
        // par_reduces_bd.rec on the FIRST derivation (motive universalizing e2
        // and h2), and in each non-refl arm apply the matching inversion lemma
        // to h2, joining the recovered sub-reducts through the recursor IHs
        // (diamond on sub-derivations) and contracting the (beta,beta)/(beta,
        // app)/(app,beta) and (zeta,zeta)/(zeta,let_cong)/(let_cong,zeta)
        // cross-arms via par_subst_bd. The refl arm is
        // par_strips_bd_refl_left. This assembly is the next dispatch; the
        // inversion lemmas above remove the documented blocker for it.
        // NOTE (Wave 138): `par_strips_bd` is now DerivedProved with a full
        // closed proof term. Because that term consumes the refl/diagonal/symm
        // combinators (par_strips_bd_refl_left, par_strips_bd_app/_lam/_pi/
        // _forall, par_strips_witness_bd_symm) and the Wave 137 cross helpers
        // (par_strips_bd_app_beta, par_strips_witness_bd_lam_meet,
        // par_reduces_bd_lam_inv_eq) — all registered BELOW — and the kernel
        // checks declarations in registration order, the `par_strips_bd`
        // registration is moved to the END of this method (just before Ok(())),
        // after every leaf it depends on. See `par_strips_bd_proof`.

        // =========================================================
        // Wave 134 (Route B) — the two refl meeting-point helpers.
        // =========================================================
        //
        // These discharge the (refl, _) and (_, refl) families of the
        // par_strips_bd diamond as standalone closed terms (no recursion):
        // the meeting point is taken at the non-refl reduct, witnessed by the
        // given derivation on one side and par_reduces_bd.refl on the other.
        //
        // par_strips_bd_refl_left : forall e e2,
        //   par_reduces_bd e e2 -> par_strips_witness_bd e e2
        // (the e1 = e case: meet at e2; left witness = h, right witness = refl).
        // Mirrors the (refl, _) row and serves as the diagonal refl handler.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_refl_left".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e2 : KExpr), ",
                "par_reduces_bd e e2 -> par_strips_witness_bd e e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e2 : KExpr) (h : par_reduces_bd e e2) => ",
                    "par_strips_witness_bd.intro e e2 e2 h (par_reduces_bd.refl e2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (refl, _) meeting-point helper for the iota-free single-step diamond: ",
                "given e => e2, join at e2 with the input on the left and par_reduces_bd.refl ",
                "on the right. Closed term, no recursion. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 134 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_bd_refl_right : forall e e1,
        //   par_reduces_bd e e1 -> par_strips_witness_bd e1 e
        // (the e2 = e case: meet at e1; left witness = refl, right witness = h).
        // Mirrors the (_, refl) column.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_refl_right".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr), ",
                "par_reduces_bd e e1 -> par_strips_witness_bd e1 e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e1 : KExpr) (h : par_reduces_bd e e1) => ",
                    "par_strips_witness_bd.intro e1 e e1 (par_reduces_bd.refl e1) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (_, refl) meeting-point helper for the iota-free single-step diamond: ",
                "given e => e1, join at e1 with par_reduces_bd.refl on the left and the input ",
                "on the right. Closed term, no recursion. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 134 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 135 (Route B) — the four binary congruence combinators
        // for the iota-free single-step diamond, plus witness symmetry.
        // =========================================================
        //
        // These discharge the congruence-diagonal arms of par_strips_bd
        // ((app,app)/(lam,lam)/(pi,pi)/(forall_,forall_)) as standalone
        // closed terms. Each takes the diamond witnesses for the
        // sub-components and reassembles a diamond witness for the compound
        // term: the meeting point is the same constructor applied to the
        // per-component meeting points, and each side's par_reduces_bd is the
        // matching congruence constructor applied to the per-component
        // reductions. Proved by par_strips_witness_bd.rec on each input
        // witness (projecting out the common reduct and the two reductions),
        // with NO recursion on par_reduces_bd. DerivedProved, zero axiom_deps.
        //
        // par_strips_bd_app : forall f1 f2 a1 a2,
        //   par_strips_witness_bd f1 f2 -> par_strips_witness_bd a1 a2 ->
        //   par_strips_witness_bd (KExpr.app f1 a1) (KExpr.app f2 a2)
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_app".to_string(),
            type_src: concat!(
                "forall (f1 : KExpr) (f2 : KExpr) (a1 : KExpr) (a2 : KExpr), ",
                "par_strips_witness_bd f1 f2 -> par_strips_witness_bd a1 a2 -> ",
                "par_strips_witness_bd (KExpr.app f1 a1) (KExpr.app f2 a2)"
            )
            .to_string(),
            value_src: Some(par_strips_bd_app_proof()),
            is_axiom: false,
            description: concat!(
                "The (app, app) congruence combinator for the iota-free single-step diamond: ",
                "from diamond witnesses on the head and argument, build the diamond witness on ",
                "the application. Meeting point KExpr.app f3 a3 with par_reduces_bd.app on each ",
                "side. Closed term via par_strips_witness_bd.rec, no par_reduces_bd recursion. ",
                "DerivedProved, zero axiom_deps. Part of #2859 Wave 135 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.app".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The three binder congruence combinators ((lam,lam)/(pi,pi)/
        // (forall_,forall_)). Each shares the structure of the app combinator:
        // recurse on the type/domain witness for the meeting point t3, nest on
        // the body witness for b3, and reassemble via the matching binder
        // constructor. The diamond witnesses are over plain par_reduces_bd, so
        // no depth bookkeeping is needed: the witness on the body sub-terms
        // already carries the (open) body reductions. Closed terms, no
        // par_reduces_bd recursion. DerivedProved, zero axiom_deps.
        for (name, ctor, label, head) in [
            (
                "par_strips_bd_lam",
                "par_reduces_bd.lam",
                "lam",
                "KExpr.lam",
            ),
            ("par_strips_bd_pi", "par_reduces_bd.pi", "pi", "KExpr.pi"),
            (
                "par_strips_bd_forall",
                "par_reduces_bd.forall_",
                "forall_",
                "KExpr.forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr), ",
                        "par_strips_witness_bd t1 t2 -> par_strips_witness_bd b1 b2 -> ",
                        "par_strips_witness_bd ({head} t1 b1) ({head} t2 b2)"
                    ),
                    head = head,
                ),
                value_src: Some(par_strips_bd_binder_proof(ctor, head)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "The ({label}, {label}) congruence combinator for the iota-free ",
                        "single-step diamond: from diamond witnesses on the type/domain and ",
                        "body, build the diamond witness on the binder. Meeting point ",
                        "{head} t3 b3 with {ctor} on each side. Closed term via ",
                        "par_strips_witness_bd.rec, no par_reduces_bd recursion. DerivedProved, ",
                        "zero axiom_deps. Part of #2859 Wave 135 (Route B)."
                    ),
                    label = label,
                    head = head,
                    ctor = ctor,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_bd".to_string(),
                    ctor.to_string(),
                    "par_strips_witness_bd".to_string(),
                    "par_strips_witness_bd.intro".to_string(),
                    "par_strips_witness_bd.rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_strips_bd_let : the (let_cong, let_cong) congruence combinator
        // (let-promotion) — the three-position analogue of the binder
        // combinators above. From diamond witnesses on the type, value and
        // body, build the diamond witness on the genuine let_ constructor:
        // meeting point KExpr.let_ t3 v3 b3 with par_reduces_bd.let_cong on
        // each side. Closed term via three nested par_strips_witness_bd.rec,
        // no par_reduces_bd recursion. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_let".to_string(),
            type_src: concat!(
                "forall (t1 : KExpr) (t2 : KExpr) (v1 : KExpr) (v2 : KExpr) ",
                "(b1 : KExpr) (b2 : KExpr), ",
                "par_strips_witness_bd t1 t2 -> par_strips_witness_bd v1 v2 -> ",
                "par_strips_witness_bd b1 b2 -> ",
                "par_strips_witness_bd (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)"
            )
            .to_string(),
            value_src: Some(par_strips_bd_let_proof()),
            is_axiom: false,
            description: concat!(
                "The (let_cong, let_cong) congruence combinator for the iota-free ",
                "single-step diamond (let-promotion): from diamond witnesses on the type, ",
                "value and body, build the diamond witness on the genuine KExpr.let_ ",
                "constructor. Meeting point KExpr.let_ t3 v3 b3 with par_reduces_bd.let_cong ",
                "on each side. Closed term via three nested par_strips_witness_bd.rec, no ",
                "par_reduces_bd recursion. DerivedProved, zero axiom_deps. Part of the ",
                "let-promotion confluence batch (#2859 Wave 135 shape)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.let_cong".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_bd_proj : the (proj, proj) congruence combinator for the
        // iota-free single-step diamond (proj/lit fragment rung) — the
        // single-position analogue of the binder combinators. From a diamond
        // witness on the scrutinee, build the diamond witness on the projection:
        // meeting point KExpr.proj s i sub3 with par_reduces_bd.proj on each
        // side. Closed term via par_strips_witness_bd.rec, no par_reduces_bd
        // recursion. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_proj".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr), ",
                "par_strips_witness_bd sub1 sub2 -> ",
                "par_strips_witness_bd (KExpr.proj s i sub1) (KExpr.proj s i sub2)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr) ",
                    "(ws : par_strips_witness_bd sub1 sub2) => ",
                    "@par_strips_witness_bd.rec sub1 sub2 ",
                    "(fun (_ws : par_strips_witness_bd sub1 sub2) => ",
                    "par_strips_witness_bd (KExpr.proj s i sub1) (KExpr.proj s i sub2)) ",
                    "(fun (s3 : KExpr) ",
                    "(ps1 : par_reduces_bd sub1 s3) (ps2 : par_reduces_bd sub2 s3) => ",
                    "par_strips_witness_bd.intro ",
                    "(KExpr.proj s i sub1) (KExpr.proj s i sub2) (KExpr.proj s i s3) ",
                    "(par_reduces_bd.proj s i sub1 s3 ps1) ",
                    "(par_reduces_bd.proj s i sub2 s3 ps2)) ",
                    "ws"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (proj, proj) congruence combinator for the iota-free single-step ",
                "diamond (proj/lit fragment rung): from a diamond witness on the ",
                "scrutinee, build the diamond witness on the projection. Meeting point ",
                "KExpr.proj s i sub3 with par_reduces_bd.proj on each side. Closed term ",
                "via par_strips_witness_bd.rec, no par_reduces_bd recursion. DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.proj".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_bd_symm : forall e1 e2,
        //   par_strips_witness_bd e1 e2 -> par_strips_witness_bd e2 e1
        //
        // Symmetry of the packaged diamond conclusion: swapping the two sources
        // keeps the same meeting point e3, swapping the two witnesses. This is
        // the combinator the full par_strips_bd uses to halve its cross arms:
        // the (beta, app) case is the symmetric image of (app, beta), etc.
        // Closed term via par_strips_witness_bd.rec, no recursion on
        // par_reduces_bd. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_bd_symm".to_string(),
            type_src: concat!(
                "forall (e1 : KExpr) (e2 : KExpr), ",
                "par_strips_witness_bd e1 e2 -> par_strips_witness_bd e2 e1"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) (w : par_strips_witness_bd e1 e2) => ",
                    "@par_strips_witness_bd.rec e1 e2 ",
                    "(fun (_w : par_strips_witness_bd e1 e2) => par_strips_witness_bd e2 e1) ",
                    "(fun (a3 : KExpr) ",
                    "(h1 : par_reduces_bd e1 a3) (h2 : par_reduces_bd e2 a3) => ",
                    "par_strips_witness_bd.intro e2 e1 a3 h2 h1) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Symmetry of the iota-free diamond witness: swap the two sources, keep the ",
                "meeting point, swap the two reductions. Halves the cross arms of the full ",
                "par_strips_bd. Closed term via par_strips_witness_bd.rec, no par_reduces_bd ",
                "recursion. DerivedProved, zero axiom_deps. Part of #2859 Wave 135 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 138 (Route B) — par_strips_bd : the iota-free single-step diamond.
        // =========================================================
        //
        // forall e e1 e2, par_reduces_bd e e1 -> par_reduces_bd e e2 ->
        //   par_strips_witness_bd e1 e2.
        //
        // The last structural lemma before the confluence theorem. Outer
        // par_reduces_bd.rec on the first derivation (motive universalizing the
        // second target/derivation); each non-refl arm inverts the second
        // derivation (Wave 136 shape recovery), joins per-sub-derivation through
        // the recursor IHs, and reassembles:
        //   refl                    → par_strips_bd_refl_left.
        //   (app,app)/binder diags  → par_strips_bd_app/_lam/_pi/_forall.
        //   (let_cong,let_cong)     → par_strips_bd_let.
        //   (beta, beta)            → par_subst_bd on the body/arg sub-meets.
        //   (let_, let_) [zeta]     → par_subst_bd on the body/val sub-meets
        //                             (the beta-beta mechanism on the genuine
        //                             let_ constructor).
        //   (app,beta) / (beta,app) → par_strips_bd_app_beta (the (beta,app)
        //                             direction via par_strips_witness_bd_symm),
        //                             redex-side lambda shape recovered by
        //                             par_reduces_bd_lam_inv_eq.
        //   (let_,let_cong) / (let_cong,let_) → the congruence side catches up
        //                             by firing zeta (par_reduces_bd.let_ on
        //                             the joined val/body), the contracted side
        //                             via par_subst_bd; both let_-headed
        //                             inversions via par_reduces_bd_let_inv.
        // Post let-promotion a let is let_-headed (NOT an app(lam) alias): the
        // let_ arms have their own inversion/joiners, disjoint from the beta
        // ones. DerivedProved (full kernel/spec type-check), zero
        // axiom_deps. With this term the iota-free confluence skeleton is closed;
        // what remains for church_rosser_whnf elimination (#2859) is the iota
        // seam at the full-par_strips level (Wave 127 of the plan) and the
        // multi-step lattice completion (par_reduces_star.diamond /
        // beta_confluent) — par_strips_bd is the keystone they consume.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_bd e e1 -> par_reduces_bd e e2 -> ",
                "par_strips_witness_bd e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_bd_proof()),
            is_axiom: false,
            description: concat!(
                "Single-step diamond for the iota-free par_reduces_bd: two parallel ",
                "reductions from a common source join at a shared reduct. Proved (Route B) ",
                "by an outer par_reduces_bd.rec on the first derivation with each arm inverting ",
                "the second; congruence diagonals via par_strips_bd_app/_lam/_pi/_forall/_let, ",
                "the (beta,beta) and (zeta,zeta) contractions via par_subst_bd on the ",
                "sub-meets, the (app,beta)/(beta,app) cross arms via par_strips_bd_app_beta ",
                "(+ par_strips_witness_bd_symm), and the (zeta,let_cong)/(let_cong,zeta) ",
                "cross arms by firing zeta on the congruence side (par_reduces_bd.let_) ",
                "against par_subst_bd on the contracted side — let_-headed inversions via ",
                "par_reduces_bd_let_inv (let-promotion). The ",
                "iota-free keystone of the Tait-Martin-Lof confluence argument; the iota ",
                "constructor is isolated at the full-par_strips seam (never threaded through ",
                "par_subst). DerivedProved, zero axiom_deps. Part of #2859 Wave 138 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_reduces_bd.beta".to_string(),
                "par_reduces_bd.app".to_string(),
                "par_reduces_bd.lam".to_string(),
                "par_reduces_bd.pi".to_string(),
                "par_reduces_bd.forall_".to_string(),
                "par_reduces_bd.let_".to_string(),
                "par_reduces_bd.let_cong".to_string(),
                "par_reduces_bd.proj".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.intro".to_string(),
                "par_strips_witness_bd_symm".to_string(),
                "par_strips_bd_refl_left".to_string(),
                "par_strips_bd_app".to_string(),
                "par_strips_bd_lam".to_string(),
                "par_strips_bd_pi".to_string(),
                "par_strips_bd_forall".to_string(),
                "par_strips_bd_let".to_string(),
                "par_strips_bd_proj".to_string(),
                "par_strips_bd_app_beta".to_string(),
                "par_strips_witness_bd_lam_meet".to_string(),
                "par_reduces_bd_app_inv".to_string(),
                "par_reduces_bd_lam_inv".to_string(),
                "par_reduces_bd_let_inv".to_string(),
                "par_reduces_bd_pi_inv".to_string(),
                "par_reduces_bd_forall_inv".to_string(),
                "par_reduces_bd_proj_inv".to_string(),
                "par_reduces_bd_lam_inv_eq".to_string(),
                "par_subst_bd".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 140 (Route B) — iota-free MULTI-STEP confluence.
        // =========================================================
        //
        // `par_strips_bd` (Wave 138) closed the single-step diamond over the
        // iota-free relation `par_reduces_bd`. The Tait-Martin-Löf argument
        // lifts that single-step diamond to the reflexive-transitive closure:
        // confluence of `par_reduces_bd_star`. This wave registers, entirely
        // additively (no existing decl or KExpr touched), the iota-free
        // multi-step diamond `par_reduces_bd_star_diamond` and its two
        // load-bearing prerequisites:
        //
        //   * par_reduces_bd_star            — RT-closure of par_reduces_bd
        //                                      (refl/step), plus its single-step
        //                                      embedding and transitivity.
        //   * par_strips_witness_bd_star     — the generalized join witness whose
        //                                      legs are par_reduces_bd_star
        //                                      (multi-step), not single steps.
        //   * par_strips_bd_star_strip       — the STRIP lemma: strip one
        //                                      multi-step leg against one
        //                                      single-step leg, by induction on
        //                                      the par_reduces_bd_star derivation
        //                                      using par_strips_bd at each step.
        //   * par_reduces_bd_star_diamond    — the iota-free multi-step diamond:
        //                                      confluence of par_reduces_bd_star,
        //                                      by induction using the strip lemma.
        //
        // The whole block stays inside the iota-free fragment, so it sidesteps
        // the three orthogonal church_rosser_whnf blockers (untyped-model
        // falsity, the delta embedding, the iota seam) and is unconditionally
        // sound: every term below kernel-checks via add_decl with empty
        // axiom_deps. Part of #2859 (blocker #2 of the corrected order).

        // par_reduces_bd_star — reflexive-transitive closure of par_reduces_bd.
        // Mirrors par_reduces_star (par_reduction.rs:1499) over the iota-free
        // relation: refl is the identity reduction; step prefixes one
        // par_reduces_bd step onto an existing closure tail.
        self.add_inductive(
            r"inductive par_reduces_bd_star : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_bd_star e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), par_reduces_bd e e' → par_reduces_bd_star e' e'' → par_reduces_bd_star e e''",
            "par_reduces_bd_star e e'' is the reflexive-transitive closure of the iota-free parallel reduction par_reduces_bd: either e = e'' (refl) or e parallel-reduces (iota-free) to an intermediate e' that continues to e''. The multi-step level at which the iota-free Tait-Martin-Lof confluence conclusion lives. Part of #2859 Wave 140 (Route B).",
        )?;

        // par_subsumes_bd_star : par_reduces_bd e e' -> par_reduces_bd_star e e'.
        // Single iota-free parallel step embeds into its RT-closure, built
        // directly from the constructors (no recursion). DerivedProved.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_bd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces_bd e e' -> par_reduces_bd_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : par_reduces_bd e e') => ",
                    "par_reduces_bd_star.step e e' e' h (par_reduces_bd_star.refl e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-step iota-free par_reduces_bd embeds into par_reduces_bd_star: ",
                "build the witness directly via par_reduces_bd_star.step with the singleton ",
                "tail filled by par_reduces_bd_star.refl. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 140 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.refl".to_string(),
                "par_reduces_bd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_star_trans : transitivity of par_reduces_bd_star.
        // Structural induction on the first argument via par_reduces_bd_star.rec,
        // generalizing the motive over the second star and prefixing each step
        // onto the recursively-extended tail (the iota-free analogue of
        // par_reduces_star_trans). DerivedProved.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_star_trans".to_string(),
            type_src: concat!(
                "forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "par_reduces_bd_star e1 e2 -> par_reduces_bd_star e2 e3 -> ",
                "par_reduces_bd_star e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : par_reduces_bd_star e1 e2) ",
                    "(h2 : par_reduces_bd_star e2 e3) => ",
                    "par_reduces_bd_star.rec ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(_ : par_reduces_bd_star a b) => ",
                    "par_reduces_bd_star b e3 -> par_reduces_bd_star a e3) ",
                    "(fun (e : KExpr) (k : par_reduces_bd_star e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_bd e e') ",
                    "(_htail : par_reduces_bd_star e' e'') ",
                    "(ih : par_reduces_bd_star e'' e3 -> par_reduces_bd_star e' e3) ",
                    "(k : par_reduces_bd_star e'' e3) => ",
                    "par_reduces_bd_star.step e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of par_reduces_bd_star (reflexive-transitive closure of the ",
                "iota-free par_reduces_bd). Proved by structural induction on the first ",
                "argument via par_reduces_bd_star.rec, prefixing each step constructor onto ",
                "the recursively-extended tail. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 140 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.rec".to_string(),
                "par_reduces_bd_star.refl".to_string(),
                "par_reduces_bd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_bd_star : KExpr -> KExpr -> Type
        //
        // GOAL #1. The generalized join witness with MULTI-STEP legs: packages
        // a common reduct e3 together with par_reduces_bd_star e1 e3 and
        // par_reduces_bd_star e2 e3 (the reflexive-transitive closure, not a
        // single step). The multi-step analogue of par_strips_witness_bd; the
        // conclusion shape of the strip lemma and the multi-step diamond.
        self.add_inductive(
            r"inductive par_strips_witness_bd_star : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_bd_star e1 e3 → par_reduces_bd_star e2 e3 → par_strips_witness_bd_star e1 e2",
            "par_strips_witness_bd_star e1 e2 packages the iota-free multi-step join conclusion: a common reduct e3 together with par_reduces_bd_star e1 e3 and par_reduces_bd_star e2 e3 (reflexive-transitive closure legs, not single steps). The multi-step generalization of par_strips_witness_bd; conclusion of the strip lemma and the multi-step diamond. Part of #2859 Wave 140 (Route B).",
        )?;

        // par_strips_bd_star_strip : forall e e1 e2,
        //   par_reduces_bd_star e e1 -> par_reduces_bd e e2 ->
        //   par_strips_witness_bd_star e1 e2.
        //
        // GOAL #2 (the STRIP lemma). Strip one MULTI-step leg (e ⇒* e1) against
        // one SINGLE-step leg (e ⇒ e2), producing a multi-step join of e1 and
        // e2. By induction on the par_reduces_bd_star derivation e ⇒* e1 with
        // motive generalizing over the single-step target e2:
        //
        //   refl (e1 = e): given e ⇒ e2, meet at e2 — e1 = e ⇒* e2 via
        //     par_subsumes_bd_star, e2 ⇒* e2 via par_reduces_bd_star.refl.
        //   step (e ⇒ e', e' ⇒* e1, IH over e'): given e ⇒ e2, the single-step
        //     diamond par_strips_bd e e' e2 joins e' and e2 at some m (e' ⇒ m,
        //     e2 ⇒ m); the IH applied to e' ⇒ m joins e1 and m at some e3
        //     (e1 ⇒* e3, m ⇒* e3); then e2 ⇒ m ⇒* e3 closes via
        //     par_subsumes_bd_star + par_reduces_bd_star_trans, e1 ⇒* e3 is the
        //     IH's first leg. Meet at e3.
        //
        // The recursion is on par_reduces_bd_star.rec only; the per-step join is
        // the iota-free single-step diamond par_strips_bd (Wave 138). Entirely
        // iota-free: no iota constructor anywhere in the closure. DerivedProved
        // (full kernel/spec type-check), zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_star_strip".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_bd_star e e1 -> par_reduces_bd e e2 -> ",
                "par_strips_witness_bd_star e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_bd_star_strip_proof()),
            is_axiom: false,
            description: concat!(
                "The iota-free STRIP lemma: strip one multi-step leg (par_reduces_bd_star e e1) ",
                "against one single-step leg (par_reduces_bd e e2) into a multi-step join ",
                "par_strips_witness_bd_star e1 e2. Proved (Route B) by induction on the ",
                "par_reduces_bd_star derivation via par_reduces_bd_star.rec, generalizing the ",
                "motive over the single-step target; the refl arm meets at e2, the step arm ",
                "joins via the single-step diamond par_strips_bd then the IH, closing the ",
                "single-step side through par_subsumes_bd_star + par_reduces_bd_star_trans. ",
                "Entirely iota-free. DerivedProved, zero axiom_deps. Part of #2859 Wave 140."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.rec".to_string(),
                "par_reduces_bd_star.refl".to_string(),
                "par_reduces_bd_star.step".to_string(),
                "par_strips_bd".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.rec".to_string(),
                "par_strips_witness_bd_star".to_string(),
                "par_strips_witness_bd_star.intro".to_string(),
                "par_strips_witness_bd_star.rec".to_string(),
                "par_subsumes_bd_star".to_string(),
                "par_reduces_bd_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_star_diamond : forall e e1 e2,
        //   par_reduces_bd_star e e1 -> par_reduces_bd_star e e2 ->
        //   par_strips_witness_bd_star e1 e2.
        //
        // GOAL #3 (the iota-free MULTI-STEP DIAMOND). Confluence of the iota-free
        // RT-closure par_reduces_bd_star, the Tait-Martin-Löf conclusion. By
        // induction on the FIRST derivation e ⇒* e1 with motive generalizing over
        // the second multi-step target e2:
        //
        //   refl (e1 = e): given e ⇒* e2, meet at e2 — e1 = e ⇒* e2 (the given
        //     leg), e2 ⇒* e2 via par_reduces_bd_star.refl.
        //   step (e ⇒ e', e' ⇒* e1, IH over e'): given e ⇒* e2, the STRIP lemma
        //     par_strips_bd_star_strip e e2 e' (stripping the multi-step e ⇒* e2
        //     against the single-step e ⇒ e') joins e2 and e' at some m
        //     (e2 ⇒* m, e' ⇒* m); the IH applied to e' ⇒* m joins e1 and m at
        //     some e3 (e1 ⇒* e3, m ⇒* e3); then e2 ⇒* m ⇒* e3 via
        //     par_reduces_bd_star_trans, and e1 ⇒* e3 is the IH's first leg.
        //     Meet at e3.
        //
        // Uses only par_reduces_bd_star.rec, the strip lemma, transitivity, and
        // witness projection — all iota-free. DerivedProved (full kernel/spec
        // type-check), zero axiom_deps. This is the iota-free fragment of the
        // multi-step confluence that the full church_rosser_whnf elimination
        // (#2859) ultimately rests on; it sidesteps blockers #1/#3/#4 (model
        // falsity, delta, iota seam) by construction.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_star_diamond".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_bd_star e e1 -> par_reduces_bd_star e e2 -> ",
                "par_strips_witness_bd_star e1 e2"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_star_diamond_proof()),
            is_axiom: false,
            description: concat!(
                "The iota-free MULTI-STEP diamond (Tait-Martin-Löf confluence of ",
                "par_reduces_bd_star): two iota-free multi-step reductions from a common source ",
                "join at a shared reduct, packaged as par_strips_witness_bd_star. Proved ",
                "(Route B) by induction on the first derivation via par_reduces_bd_star.rec, ",
                "the refl arm meeting at the second target, the step arm joining via the strip ",
                "lemma par_strips_bd_star_strip then the IH and par_reduces_bd_star_trans. ",
                "Entirely iota-free — sidesteps the untyped-model/delta/iota-seam blockers by ",
                "construction. DerivedProved, zero axiom_deps. Part of #2859 Wave 140 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.rec".to_string(),
                "par_reduces_bd_star.refl".to_string(),
                "par_reduces_bd_star.step".to_string(),
                "par_strips_bd_star_strip".to_string(),
                "par_strips_witness_bd_star".to_string(),
                "par_strips_witness_bd_star.intro".to_string(),
                "par_strips_witness_bd_star.rec".to_string(),
                "par_reduces_bd_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 142 (Route B) — star-level pi inversion (shape
        // preservation): the iota-free join PRESERVES pi-headedness and
        // reduces its components componentwise.
        // =========================================================
        //
        // par_reduces_bd_star_pi_inv is the multi-step lift of the Wave-136
        // single-step inversion par_reduces_bd_pi_inv: from
        // par_reduces_bd_star (pi dom body) w, recover w = pi dom' body' with
        // dom ⇒* dom' and body ⇒* body'. Combined with the Wave-140 multi-step
        // diamond par_reduces_bd_star_diamond, this yields pi INJECTIVITY for the
        // iota-free join (two pis with a common reduct have join-able domains and
        // join-able codomains) — the iota-free analogue of the pi-injectivity that
        // the church_rosser_whnf HelperAxiom stands in for at the DefEq level. It
        // is unconditionally true and fully kernel-checked, so it is a sound,
        // axiom-free advance on the only non-fabricating elimination route (#2859),
        // sidestepping the untyped-model/delta/iota-seam blockers by construction.
        //
        // The star induction's step arm must thread the reduct equation
        // e' = pi A' B' to its inductive hypothesis, which the continuation-passing
        // par_reduces_bd_pi_inv DISCARDS. So we first land the Eq-DATA pi inversion
        // par_reduces_bd_pi_inv_eq (the mechanical pi-dual of the in-tree
        // par_reduces_bd_lam_inv_eq), which hands the reduct equality back as data.

        // par_reduces_bd_pi_inv_eq : Eq-DATA pi inversion. From
        // par_reduces_bd (pi dom body) t, hand the continuation Eq t (pi dom' body')
        // together with dom => dom' and body => body'. The pi and forall_ arms are
        // genuine matches (forall_ is the reducible pi alias); refl folds in;
        // lam discharged by lam_ne_pi; beta/app by app_ne_pi; the let_-headed
        // let_/let_cong arms by let_ne_pi (let-promotion).
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_pi_inv_eq".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_bd (KExpr.pi dom body) t -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.pi dom' body') -> ",
                "par_reduces_bd dom dom' -> par_reduces_bd body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_pi_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Eq-data shape recovery for a pi-headed iota-free parallel reduction: from ",
                "par_reduces_bd (pi dom body) t, hand the continuation the reduct equality ",
                "Eq t (pi dom' body') together with dom => dom' and body => body', returning the ",
                "fixed result type C. The pi-dual of par_reduces_bd_lam_inv_eq: the motive returns ",
                "the arrow Eq e (pi dom body) -> Kont e' -> C with Kont parameterized by the arm ",
                "reduct, so the recursor substitutes the genuine reduct t. The pi and forall_ arms ",
                "match (forall_ is the reducible pi alias, Eq.refl reduct equation); refl folds in; ",
                "lam discharged by lam_ne_pi, beta/app by app_ne_pi, the let_-headed ",
                "let_/let_cong by let_ne_pi (let-promotion). DerivedProved via ",
                "par_reduces_bd.rec, zero axiom_deps. Part of #2859 Wave 142 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "par_reduces_bd.refl".to_string(),
                "pi_inj_fst".to_string(),
                "pi_inj_snd".to_string(),
                "app_ne_pi".to_string(),
                "lam_ne_pi".to_string(),
                "let_ne_pi".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_bd_star_pi_inv : star-level pi inversion. From
        // par_reduces_bd_star (pi dom body) w, recover w = pi dom' body' with
        // dom ⇒* dom' and body ⇒* body'. Induction on the multi-step derivation
        // with an accumulator motive carrying Eq s (pi A B) + the prefixes
        // dom ⇒* A, body ⇒* B; the step arm Eq-inverts each single step via
        // par_reduces_bd_pi_inv_eq and extends the prefixes through
        // par_subsumes_bd_star + par_reduces_bd_star_trans.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_star_pi_inv".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type), ",
                "par_reduces_bd_star (KExpr.pi dom body) w -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "par_reduces_bd_star dom dom' -> par_reduces_bd_star body body' -> ",
                "C (KExpr.pi dom' body')) -> ",
                "C w"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_star_pi_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Star-level (multi-step) pi inversion / shape preservation for the iota-free ",
                "parallel join: from par_reduces_bd_star (pi dom body) w, recover ",
                "w = pi dom' body' with dom ⇒* dom' and body ⇒* body'. The multi-step lift of the ",
                "Wave-136 par_reduces_bd_pi_inv. Proved (Route B) by induction on the star ",
                "derivation via par_reduces_bd_star.rec with an accumulator motive that carries the ",
                "reduct equation Eq s (pi A B) and the accumulated prefixes dom ⇒* A, body ⇒* B; the ",
                "refl arm hands the continuation the prefixes (transporting C (pi A B) onto C s), the ",
                "step arm Eq-inverts each step via par_reduces_bd_pi_inv_eq and extends the prefixes ",
                "via par_subsumes_bd_star + par_reduces_bd_star_trans. Combined with the Wave-140 ",
                "multi-step diamond this gives pi-injectivity for the iota-free join — the iota-free ",
                "analogue of the church_rosser_whnf content. Entirely iota-free: DerivedProved, zero ",
                "axiom_deps. Part of #2859 Wave 142 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.rec".to_string(),
                "par_reduces_bd_star.refl".to_string(),
                "par_reduces_bd_pi_inv_eq".to_string(),
                "par_subsumes_bd_star".to_string(),
                "par_reduces_bd_star_trans".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Wave 143 (Route B) — pi INJECTIVITY for the iota-free join:
        // the capstone the Wave-142 inversion + Wave-140 diamond yield.
        // =========================================================
        //
        // Two pis pi a1 b1 and pi a2 b2 that share a common iota-free reduct
        // (par_strips_witness_bd_star) have JOIN-able domains and JOIN-able
        // codomains. This is the iota-free analogue of the pi-injectivity-for-DefEq
        // that the church_rosser_whnf HelperAxiom stands in for: pi-headed terms
        // can only be DefEq if their components are, and confluence is what
        // licenses that inversion. It is unconditionally true and fully
        // kernel-checked — a sound, axiom-free advance on the only non-fabricating
        // elimination route (#2859). The remaining gap to the FULL HelperAxiom
        // elimination is the iota seam (Route A: replace the iota_reduces axiom
        // with a computational iota_step); these injectivity lemmas are the
        // iota-free payload that route ultimately discharges into.

        // par_reduces_bd_star_pi_inv_eq : the Eq-DATA star pi inversion — the
        // reduct equality is handed back as data (rather than threaded through a
        // KExpr-indexed motive). Derived from par_reduces_bd_star_pi_inv by the
        // motive M(ww) := Eq w ww -> C applied at Eq.refl. This is the form pi
        // injectivity consumes: it needs the equation w = pi dom' body' to align
        // two independent inversions of the SAME reduct.
        self.add_definition(SpecDefinition {
            name: "par_reduces_bd_star_pi_inv_eq".to_string(),
            type_src: concat!(
                "forall (dom : KExpr) (body : KExpr) (w : KExpr) (C : Type), ",
                "par_reduces_bd_star (KExpr.pi dom body) w -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr w (KExpr.pi dom' body') -> ",
                "par_reduces_bd_star dom dom' -> par_reduces_bd_star body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_bd_star_pi_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Eq-data star-level pi inversion: from par_reduces_bd_star (pi dom body) w, hand the ",
                "continuation the reduct equality Eq w (pi dom' body') together with dom ⇒* dom' and ",
                "body ⇒* body', returning the fixed result type C. The reduct-as-data sibling of ",
                "par_reduces_bd_star_pi_inv, derived from it by the motive M(ww) := Eq w ww -> C ",
                "applied at Eq.refl w. This is the form pi-injectivity consumes (two inversions of the ",
                "SAME reduct align via their reduct equations). DerivedProved, zero axiom_deps. Part ",
                "of #2859 Wave 143 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star_pi_inv".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_bd_pi_injectivity_dom / par_bd_pi_injectivity_cod : pi injectivity up
        // to iota-free confluence. From a join witness on pi a1 b1 and pi a2 b2,
        // produce a join witness on the domains (a1, a2) / codomains (b1, b2).
        // Project the shared reduct e3, Eq-invert both legs via
        // par_reduces_bd_star_pi_inv_eq to e3 = pi a1' b1' = pi a2' b2', read off
        // a1' = a2' (resp. b1' = b2') by pi injectivity of the equality, and meet.
        for (name, pi_inj, clhs, crhs, meet1, meet2, leg1, leg2, what) in [
            (
                "par_bd_pi_injectivity_dom",
                "pi_inj_fst",
                "a1",
                "a2",
                "a1'",
                "a2'",
                "hda1",
                "hda2",
                "domains",
            ),
            (
                "par_bd_pi_injectivity_cod",
                "pi_inj_snd",
                "b1",
                "b2",
                "b1'",
                "b2'",
                "hdb1",
                "hdb2",
                "codomains",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr), ",
                        "par_strips_witness_bd_star (KExpr.pi a1 b1) (KExpr.pi a2 b2) -> ",
                        "par_strips_witness_bd_star {clhs} {crhs}"
                    ),
                    clhs = clhs,
                    crhs = crhs,
                ),
                value_src: Some(par_bd_pi_injectivity_proof(
                    clhs, crhs, meet1, meet2, leg1, leg2, pi_inj,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Pi injectivity up to iota-free confluence ({what}): from a shared-reduct ",
                        "join witness on pi a1 b1 and pi a2 b2, produce a join witness on the {what}. ",
                        "Project the common reduct e3, Eq-invert both legs via ",
                        "par_reduces_bd_star_pi_inv_eq (e3 = pi a1' b1' = pi a2' b2'), read off the ",
                        "{what} equality by {pi_inj} of the trans'd reduct equation, transport the ",
                        "second leg onto the meet, and package via par_strips_witness_bd_star.intro. ",
                        "The iota-free analogue of pi-injectivity-for-DefEq (the church_rosser_whnf ",
                        "payload). DerivedProved, zero axiom_deps. Part of #2859 Wave 143 (Route B)."
                    ),
                    what = what,
                    pi_inj = pi_inj,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_bd_star".to_string(),
                    "par_strips_witness_bd_star".to_string(),
                    "par_strips_witness_bd_star.rec".to_string(),
                    "par_strips_witness_bd_star.intro".to_string(),
                    "par_reduces_bd_star_pi_inv_eq".to_string(),
                    pi_inj.to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.substType".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // =========================================================
        // Wave 139 (Route B) — iota seam: lift par_strips_bd to full
        // par_reduces, and discharge the closable iota-headed join cases.
        // =========================================================
        //
        // par_strips_bd (above) closed the single-step diamond for the
        // iota-free fragment. Lifting it to the FULL par_reduces single-step
        // diamond (`par_strips`) requires handling the `iota` constructor in
        // BOTH derivations of `par_strips e e1 e2`. The Wave-127 plan forwards
        // the never-introduced `iota_reduces` hypothesis; concretely, the
        // recursor arms split as follows:
        //
        //   * (refl/beta/app/binder, refl/beta/app/binder)  — both derivations
        //     iota-free: these reduce to `par_strips_bd` via the embedding
        //     `par_strips_bd_to_par` (lifting both legs of the iota-free
        //     witness through `par_reduces_bd_subsumes_par`).
        //   * (iota, refl) / (refl, iota)  — one leg is an iota reduct e ⇒ e',
        //     the other is the identity refl. These JOIN constructively at e'
        //     itself (the iota reduct is its own meeting point, the refl side
        //     reaches it by the forwarded iota witness). Closed below as
        //     `par_strips_iota_left_refl` / `par_strips_iota_right_refl`.
        //   * (iota, beta|app|binder|iota) and symmetric  — joining an OPAQUE
        //     iota reduct with a *structurally distinct* parallel reduction is
        //     NOT derivable from the abstract `iota_reduces` witness: the only
        //     fact it carries is a same-value DefEq (`iota_reduces.mk.h_subst`,
        //     symmetric, undirected), and there is no in-tree
        //     `DefEq -> par_reduces` bridge nor an `iota_deterministic` lemma
        //     (the latter was a forward reference that was never landed; see
        //     designs/2026-05-27-church-rosser-full-elimination.md). These cross
        //     cases are exactly the documented Wave-127 risk point; they remain
        //     the narrowed blocker for assembling the full `par_strips` recursor
        //     term. NO axiom is asserted to cover them.
        //
        // The lemmas below land the closable seam pieces as DerivedProved,
        // fully kernel-checked, zero axiom_deps. They are the constructive
        // building blocks the eventual `par_strips` term consumes for its
        // iota-free and (iota, refl)/(refl, iota) arms.

        // par_strips_witness_bd_subsumes_par : forall e1 e2,
        //   par_strips_witness_bd e1 e2 -> par_strips_witness e1 e2.
        //
        // Embed the iota-free diamond witness into the full one: project the
        // packaged (e3, par_reduces_bd e1 e3, par_reduces_bd e2 e3) via
        // par_strips_witness_bd.rec and lift both legs through
        // par_reduces_bd_subsumes_par, repackaging via par_strips_witness.intro
        // at the same meeting point e3. No recursion on par_reduces_bd, no iota
        // arm. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_bd_subsumes_par".to_string(),
            type_src: concat!(
                "forall (e1 : KExpr) (e2 : KExpr), ",
                "par_strips_witness_bd e1 e2 -> par_strips_witness e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) ",
                    "(w : par_strips_witness_bd e1 e2) => ",
                    "@par_strips_witness_bd.rec e1 e2 ",
                    "(fun (_w : par_strips_witness_bd e1 e2) => par_strips_witness e1 e2) ",
                    "(fun (e3 : KExpr) ",
                    "(h1 : par_reduces_bd e1 e3) (h2 : par_reduces_bd e2 e3) => ",
                    "par_strips_witness.intro e1 e2 e3 ",
                    "(par_reduces_bd_subsumes_par e1 e3 h1) ",
                    "(par_reduces_bd_subsumes_par e2 e3 h2)) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Embed the iota-free diamond witness par_strips_witness_bd into the full ",
                "par_strips_witness: project the common reduct e3 via par_strips_witness_bd.rec ",
                "and lift both legs through par_reduces_bd_subsumes_par, repackaging at the same ",
                "meeting point. Closed term, no par_reduces_bd recursion, no iota arm. ",
                "DerivedProved, zero axiom_deps. Part of #2859 Wave 139 (Route B iota seam)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_subsumes_par".to_string(),
                "par_strips_witness".to_string(),
                "par_strips_witness.intro".to_string(),
                "par_strips_witness_bd".to_string(),
                "par_strips_witness_bd.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_bd_to_par : forall e e1 e2,
        //   par_reduces_bd e e1 -> par_reduces_bd e e2 -> par_strips_witness e1 e2.
        //
        // The iota-free single-step diamond delivered at the FULL par_reduces
        // witness level. Composes par_strips_bd (the iota-free diamond) with
        // the embedding par_strips_witness_bd_subsumes_par. This is exactly the
        // iota-free arm of the eventual par_strips recursor term: whenever both
        // input derivations are built without the iota constructor (i.e. they
        // come from par_reduces_bd), the full diamond reduces to par_strips_bd.
        // DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_bd_to_par".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_bd e e1 -> par_reduces_bd e e2 -> ",
                "par_strips_witness e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : par_reduces_bd e e1) (h2 : par_reduces_bd e e2) => ",
                    "par_strips_witness_bd_subsumes_par e1 e2 ",
                    "(par_strips_bd e e1 e2 h1 h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Iota-free single-step diamond at the full par_reduces witness level: two ",
                "iota-free parallel reductions from a common source join at a shared reduct, ",
                "packaged as par_strips_witness. Composes par_strips_bd with the embedding ",
                "par_strips_witness_bd_subsumes_par. This is the iota-free arm the full ",
                "par_strips recursor term consumes. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 139 (Route B iota seam)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_strips_bd".to_string(),
                "par_strips_witness".to_string(),
                "par_strips_witness_bd_subsumes_par".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_iota_left_refl : forall e e',
        //   iota_reduces e e' -> par_strips_witness e' e.
        //
        // The (iota, refl) join of par_strips: the first derivation is the iota
        // reduct e ⇒ e' (so e1 = e'), the second is the identity (e2 = e). The
        // meeting point is e' itself — the iota reduct reaches it reflexively
        // (par_reduces.refl e'), and the refl side reaches it via the forwarded
        // iota witness (par_reduces.iota e e' h). No fact ABOUT the iota redex
        // is asserted beyond re-wrapping the hypothesis. DerivedProved, zero
        // axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_iota_left_refl".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "iota_reduces e e' -> par_strips_witness e' e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : iota_reduces e e') => ",
                    "par_strips_witness.intro e' e e' ",
                    "(par_reduces.refl e') (par_reduces.iota e e' h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (iota, refl) join of the full single-step diamond: an iota reduct e ⇒ e' ",
                "and the identity reduction e ⇒ e join at e'. The iota side reaches e' ",
                "reflexively; the refl side reaches e' by forwarding the iota witness through ",
                "par_reduces.iota. No fact about the opaque iota redex is asserted beyond ",
                "re-wrapping the hypothesis. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 139 (Route B iota seam)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduces".to_string(),
                "par_reduces".to_string(),
                "par_reduces.refl".to_string(),
                "par_reduces.iota".to_string(),
                "par_strips_witness".to_string(),
                "par_strips_witness.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_iota_right_refl : forall e e',
        //   iota_reduces e e' -> par_strips_witness e e'.
        //
        // The (refl, iota) join — symmetric to par_strips_iota_left_refl. Here
        // the first derivation is the identity (e1 = e) and the second is the
        // iota reduct e ⇒ e' (e2 = e'); the meeting point is again e'. Closed
        // by par_strips_witness.intro with the two witnesses in swapped legs.
        // DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_strips_iota_right_refl".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "iota_reduces e e' -> par_strips_witness e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : iota_reduces e e') => ",
                    "par_strips_witness.intro e e' e' ",
                    "(par_reduces.iota e e' h) (par_reduces.refl e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The (refl, iota) join of the full single-step diamond: the identity reduction ",
                "e ⇒ e and an iota reduct e ⇒ e' join at e'. Symmetric image of ",
                "par_strips_iota_left_refl; the refl side reaches e' by forwarding the iota ",
                "witness, the iota side reflexively. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 139 (Route B iota seam)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduces".to_string(),
                "par_reduces".to_string(),
                "par_reduces.refl".to_string(),
                "par_reduces.iota".to_string(),
                "par_strips_witness".to_string(),
                "par_strips_witness.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_beta_bd_confluence()?;

        Ok(())
    }

    /// Wave 141 (Route B) — the iota-free beta Church-Rosser keystone.
    ///
    /// The classic Tait-Martin-Löf bridge from the parallel-reduction diamond
    /// (`par_reduces_bd_star_diamond`, Wave 140) to beta confluence, restricted
    /// to the IOTA-FREE fragment. Because the full `beta_reduces` relation
    /// carries an `iota` constructor with no image in the iota-free
    /// `par_reduces_bd`, the honest iota-free Church-Rosser theorem is stated
    /// over a NEW iota-free single-step beta relation `beta_reduces_bd` (the
    /// 13 non-iota constructors of `beta_reduces`, incl. the let-promotion
    /// zeta + let_ty/let_val/let_body arms) and its closure
    /// `beta_reduces_bd_star`, NOT over `beta_reduces_star` (which is the full
    /// beta+iota relation blocked by the iota wall). See the design note above
    /// the `beta_reduces_bd` registration for the obstruction analysis.
    ///
    /// Landed here (all DerivedProved, zero axiom_deps, iota-free):
    ///   * `beta_reduces_bd` / `beta_reduces_bd_star` inductives.
    ///   * `beta_reduces_bd_star` congruence + closure helpers
    ///     (subsumes_star, trans, app_left/right, lam_ty/body, pi_dom/cod,
    ///     let_ty/val/body).
    ///   * embedding 1a `beta_subsumes_par_bd_star`
    ///     (`beta_reduces_bd e e' -> par_reduces_bd_star e e'` — single beta →
    ///     par closure; each arm is one par step or one congruence lift, the
    ///     zeta arm a single `par_reduces_bd.let_` step; the closure target is
    ///     kept for uniformity with the full-relation mirror).
    ///   * embedding 1b `par_subsumes_beta_bd_star`
    ///     (`par_reduces_bd e e' -> beta_reduces_bd_star e e'`).
    ///   * closure transports `beta_bd_star_subsumes_par_bd_star` /
    ///     `par_bd_star_subsumes_beta_bd_star` (interconvertible closures).
    ///   * `beta_bd_join_witness` inductive + `beta_bd_confluent` — the
    ///     iota-free Church-Rosser theorem for beta reduction.
    fn add_beta_bd_confluence(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // beta_reduces_bd — iota-free single-step beta reduction.
        // =========================================================
        //
        // OBSTRUCTION ANALYSIS (why this relation must be new). The task's
        // stated embedding `beta_reduces e e' -> par_reduces_bd e e'` is FALSE
        // for TWO independent reasons:
        //
        //   (i) iota. `beta_reduces` (whnf_reduction.rs:139) has 11
        //       constructors, the last of which is
        //         iota : iota_reduces e e' -> beta_reduces e e'
        //       and `par_reduces_bd` (par_reduction.rs:220) is iota-free (7
        //       constructors, no iota). An iota beta-step has no image in
        //       par_reduces_bd. Stating `beta_bd_confluent` over the full
        //       `beta_reduces_star` would therefore be the FULL Church-Rosser
        //       theorem — exactly what the iota wall blocks (Wave 127 STOP).
        //
        //  (ii) [HISTORICAL — pre let-promotion] the then-bundled let_body arm
        //       (`beta_reduces_bd (instantiate body val) body' ->
        //       beta_reduces_bd (let_ ty val body) body'`) packed a zeta
        //       contraction plus a further reduction into one constructor, so
        //       the single→single embedding was FALSE (the documented
        //       obstruction that forced the full-relation `par_subsumes_beta`
        //       to be replaced by `par_subsumes_beta_star`). The let-promotion
        //       REPLACED that bundled arm with the kernel-faithful `zeta` head
        //       contraction plus the three positional `let_ty`/`let_val`/
        //       `let_body` congruences (a let is a GENUINE let_-headed node
        //       now, and the pure zeta must be expressible as one step — the
        //       bundled form could not even fire `let_ ty v b -> instantiate
        //       b v` when the contractum is normal). Embedding 1a stays stated
        //       against the closure `par_reduces_bd_star` for uniformity with
        //       the full-relation mirror.
        //
        // The honest iota-free keystone is stated over this NEW relation:
        // `beta_reduces_bd` is `beta_reduces` with the iota constructor dropped
        // (the 13 beta/zeta/congruence constructors). Confluence of its closure
        // is a genuine, fully-iota-free Church-Rosser theorem, transported
        // through the iota-free parallel-reduction diamond.
        self.add_inductive(
            r"inductive beta_reduces_bd : KExpr → KExpr → Type
| beta : forall (A : KExpr) (body : KExpr) (arg : KExpr), beta_reduces_bd (KExpr.app (KExpr.lam A body) arg) (instantiate body arg)
| app_left : forall (f : KExpr) (f' : KExpr) (a : KExpr), beta_reduces_bd f f' → beta_reduces_bd (KExpr.app f a) (KExpr.app f' a)
| app_right : forall (f : KExpr) (a : KExpr) (a' : KExpr), beta_reduces_bd a a' → beta_reduces_bd (KExpr.app f a) (KExpr.app f a')
| lam_ty : forall (ty : KExpr) (ty' : KExpr) (body : KExpr), beta_reduces_bd ty ty' → beta_reduces_bd (KExpr.lam ty body) (KExpr.lam ty' body)
| lam_body : forall (ty : KExpr) (body : KExpr) (body' : KExpr), beta_reduces_bd body body' → beta_reduces_bd (KExpr.lam ty body) (KExpr.lam ty body')
| pi_dom : forall (dom : KExpr) (dom' : KExpr) (body : KExpr), beta_reduces_bd dom dom' → beta_reduces_bd (KExpr.pi dom body) (KExpr.pi dom' body)
| pi_cod : forall (dom : KExpr) (body : KExpr) (body' : KExpr), beta_reduces_bd body body' → beta_reduces_bd (KExpr.pi dom body) (KExpr.pi dom body')
| forall_congr_dom : forall (dom : KExpr) (dom' : KExpr) (body : KExpr), beta_reduces_bd dom dom' → beta_reduces_bd (KExpr.forall_ dom body) (KExpr.forall_ dom' body)
| forall_congr_cod : forall (dom : KExpr) (body : KExpr) (body' : KExpr), beta_reduces_bd body body' → beta_reduces_bd (KExpr.forall_ dom body) (KExpr.forall_ dom body')
| zeta : forall (ty : KExpr) (val : KExpr) (body : KExpr), beta_reduces_bd (KExpr.let_ ty val body) (instantiate body val)
| let_ty : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr), beta_reduces_bd ty ty' → beta_reduces_bd (KExpr.let_ ty val body) (KExpr.let_ ty' val body)
| let_val : forall (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr), beta_reduces_bd val val' → beta_reduces_bd (KExpr.let_ ty val body) (KExpr.let_ ty val' body)
| let_body : forall (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr), beta_reduces_bd body body' → beta_reduces_bd (KExpr.let_ ty val body) (KExpr.let_ ty val body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), beta_reduces_bd sub sub' → beta_reduces_bd (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "beta_reduces_bd e e' is iota-free single-step beta reduction: the 13 non-iota constructors of beta_reduces (beta head contraction, app/lam/pi/forall_ congruences, zeta head contraction on the genuine KExpr.let_ constructor, let_ty/let_val/let_body positional congruences) with the iota constructor dropped. The iota-free analogue of beta_reduces over which the Tait-Martin-Löf beta Church-Rosser theorem is proved without the iota wall. Part of #2859 Wave 141 (Route B).",
        )?;

        // beta_reduces_bd_star — reflexive-transitive closure of
        // beta_reduces_bd. Mirrors beta_reduces_star over the iota-free
        // relation; the level at which the iota-free beta confluence conclusion
        // lives.
        self.add_inductive(
            r"inductive beta_reduces_bd_star : KExpr → KExpr → Type
| refl : forall (e : KExpr), beta_reduces_bd_star e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), beta_reduces_bd e e' → beta_reduces_bd_star e' e'' → beta_reduces_bd_star e e''",
            "beta_reduces_bd_star e e'' is the reflexive-transitive closure of the iota-free beta reduction beta_reduces_bd: either e = e'' (refl) or e beta-reduces (iota-free) to an intermediate e' that continues to e''. The multi-step level at which iota-free beta confluence lives. Part of #2859 Wave 141 (Route B).",
        )?;

        // beta_subsumes_bd_star : beta_reduces_bd e e' -> beta_reduces_bd_star
        // e e'. Single iota-free beta step embeds into its RT-closure, built
        // directly from the constructors. DerivedProved.
        self.add_definition(SpecDefinition {
            name: "beta_subsumes_bd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "beta_reduces_bd e e' -> beta_reduces_bd_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : beta_reduces_bd e e') => ",
                    "beta_reduces_bd_star.step e e' e' h (beta_reduces_bd_star.refl e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-step iota-free beta reduction embeds into ",
                "beta_reduces_bd_star: build the witness directly via ",
                "beta_reduces_bd_star.step with the singleton tail filled by ",
                "beta_reduces_bd_star.refl. DerivedProved, zero axiom_deps. ",
                "Part of #2859 Wave 141 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd_star".to_string(),
                "beta_reduces_bd_star.refl".to_string(),
                "beta_reduces_bd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_bd_star_trans : transitivity of beta_reduces_bd_star.
        // Structural induction on the first argument via
        // beta_reduces_bd_star.rec (the iota-free analogue of
        // beta_reduces_star_trans). DerivedProved.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_bd_star_trans".to_string(),
            type_src: concat!(
                "forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "beta_reduces_bd_star e1 e2 -> beta_reduces_bd_star e2 e3 -> ",
                "beta_reduces_bd_star e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : beta_reduces_bd_star e1 e2) ",
                    "(h2 : beta_reduces_bd_star e2 e3) => ",
                    "beta_reduces_bd_star.rec ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(_ : beta_reduces_bd_star a b) => ",
                    "beta_reduces_bd_star b e3 -> beta_reduces_bd_star a e3) ",
                    "(fun (e : KExpr) (k : beta_reduces_bd_star e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces_bd e e') ",
                    "(_htail : beta_reduces_bd_star e' e'') ",
                    "(ih : beta_reduces_bd_star e'' e3 -> beta_reduces_bd_star e' e3) ",
                    "(k : beta_reduces_bd_star e'' e3) => ",
                    "beta_reduces_bd_star.step e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of beta_reduces_bd_star (reflexive-transitive ",
                "closure of the iota-free beta_reduces_bd). Proved by structural ",
                "induction on the first argument via beta_reduces_bd_star.rec, ",
                "prefixing each step constructor onto the recursively-extended ",
                "tail. DerivedProved, zero axiom_deps. Part of #2859 Wave 141."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd_star".to_string(),
                "beta_reduces_bd_star.rec".to_string(),
                "beta_reduces_bd_star.refl".to_string(),
                "beta_reduces_bd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_bd_star single-position congruence helpers. Each lifts a
        // multi-step iota-free beta reduction in one subterm position into a
        // multi-step reduction of the surrounding constructor, the iota-free
        // analogues of the Wave-118 beta_reduces_star_* helpers. Common shape:
        // beta_reduces_bd_star.rec with a framed motive; refl returns
        // beta_reduces_bd_star.refl at the framed shape, step prefixes the
        // matching beta_reduces_bd congruence constructor. DerivedProved.
        for spec in bd_star_congruence_specs(BdStarRelation::Beta) {
            self.add_definition(SpecDefinition {
                name: spec.name.to_string(),
                type_src: spec.type_src(),
                value_src: Some(bd_star_congruence_proof(&spec)),
                is_axiom: false,
                description: spec.doc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    spec.relation.star().to_string(),
                    format!("{}.rec", spec.relation.star()),
                    format!("{}.refl", spec.relation.star()),
                    format!("{}.step", spec.relation.star()),
                    spec.ctor.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_bd_star single-position congruence helpers — the iota-free
        // parallel-closure analogues used by embedding 1a's congruence arms.
        // Same shape as the beta-star helpers above, over par_reduces_bd_star.
        // The bi-position par_reduces_bd constructors are refl-padded on the
        // fixed side, so par_reduces_bd.refl is an extra dependency.
        for spec in bd_star_congruence_specs(BdStarRelation::Par) {
            self.add_definition(SpecDefinition {
                name: spec.name.to_string(),
                type_src: spec.type_src(),
                value_src: Some(bd_star_congruence_proof(&spec)),
                is_axiom: false,
                description: spec.doc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    spec.relation.star().to_string(),
                    format!("{}.rec", spec.relation.star()),
                    format!("{}.refl", spec.relation.star()),
                    format!("{}.step", spec.relation.star()),
                    spec.ctor.to_string(),
                    format!("{}.refl", spec.relation.step()),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // =========================================================
        // Embedding 1a — beta_subsumes_par_bd_star :
        //   beta_reduces_bd e e' -> par_reduces_bd_star e e'.
        // =========================================================
        //
        // Every single iota-free beta step is simulated by an iota-free
        // parallel reduction. Mirrors par_subsumes_beta_star
        // — the full-relation beta ⊆ par* embedding —
        // adapted to the iota-free relation: there is NO iota arm, so the 13-arm
        // beta_reduces_bd.rec induction closes entirely with the
        // par_reduces_bd_star congruence/closure machinery. Post let-promotion
        // every arm is a single par step (beta/zeta contractions via
        // par_reduces_bd.beta/.let_ with refls) or a single-position
        // congruence lift; the closure target is kept for uniformity with the
        // full-relation mirror. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "beta_subsumes_par_bd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "beta_reduces_bd e e' -> par_reduces_bd_star e e'"
            )
            .to_string(),
            value_src: Some(beta_subsumes_par_bd_star_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding 1a: every single-step iota-free beta reduction embeds ",
                "into the reflexive-transitive closure of iota-free parallel ",
                "reduction. Structural induction on beta_reduces_bd.rec (13 arms, ",
                "no iota): the beta and zeta arms embed a single par-step via ",
                "par_subsumes_bd_star (zeta via par_reduces_bd.let_, the parallel ",
                "zeta on the genuine KExpr.let_ constructor); the congruence arms ",
                "lift the IH through the par_reduces_bd_star congruence helpers ",
                "(forall_ via par.forall_, let_ty/let_val/let_body via the ",
                "genuine-let_ positional helpers). The mirror of ",
                "par_subsumes_beta_star adapted to the iota-free relation. ",
                "Kernel-checked, DerivedProved, zero axiom_deps. Part of #2859 ",
                "Wave 141 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.rec".to_string(),
                "par_reduces_bd".to_string(),
                "par_reduces_bd.refl".to_string(),
                "par_reduces_bd.beta".to_string(),
                "par_reduces_bd.let_".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_subsumes_bd_star".to_string(),
                "par_reduces_bd_star_app_left".to_string(),
                "par_reduces_bd_star_app_right".to_string(),
                "par_reduces_bd_star_lam_ty".to_string(),
                "par_reduces_bd_star_lam_body".to_string(),
                "par_reduces_bd_star_pi_dom".to_string(),
                "par_reduces_bd_star_pi_cod".to_string(),
                "par_reduces_bd_star_let_ty".to_string(),
                "par_reduces_bd_star_let_val".to_string(),
                "par_reduces_bd_star_let_body".to_string(),
                "par_reduces_bd_star_proj".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Embedding 1b — par_subsumes_beta_bd_star :
        //   par_reduces_bd e e' -> beta_reduces_bd_star e e'.
        // =========================================================
        //
        // Every single iota-free parallel step is simulated by a finite
        // sequence of iota-free beta steps. Mirrors beta_subsumes_par_star,
        // which does this for the full par_reduces,
        // adapted to par_reduces_bd: there is NO iota arm, so the 8-arm
        // par_reduces_bd.rec induction closes entirely with the
        // beta_reduces_bd_star congruence helpers + beta_reduces_bd_star_trans
        // (the let_ zeta arm ends in one beta_reduces_bd.zeta head
        // contraction; let_cong composes the three positional let star
        // congruences).
        // DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_beta_bd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces_bd e e' -> beta_reduces_bd_star e e'"
            )
            .to_string(),
            value_src: Some(par_subsumes_beta_bd_star_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding 1b: every single-step iota-free parallel reduction is ",
                "simulated by a finite sequence of iota-free beta reductions. ",
                "Structural induction on par_reduces_bd.rec (8 arms, no iota) in ",
                "canonical outermost-first order, composing ",
                "beta_reduces_bd_star_trans and the Wave-141 single-position ",
                "congruence helpers to lift reductions under each binder, with one ",
                "beta_reduces_bd.beta (resp. beta_reduces_bd.zeta) head contraction ",
                "appended for the beta (resp. let_) contraction cases; the let_cong ",
                "arm composes the three genuine-let_ positional star congruences. ",
                "The mirror of beta_subsumes_par_star adapted to the ",
                "iota-free relation. Kernel-checked, DerivedProved, zero ",
                "axiom_deps. Part of #2859 Wave 141 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd.rec".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.beta".to_string(),
                "beta_reduces_bd.zeta".to_string(),
                "beta_reduces_bd_star".to_string(),
                "beta_reduces_bd_star.refl".to_string(),
                "beta_reduces_bd_star.step".to_string(),
                "beta_subsumes_bd_star".to_string(),
                "beta_reduces_bd_star_trans".to_string(),
                "beta_reduces_bd_star_app_left".to_string(),
                "beta_reduces_bd_star_app_right".to_string(),
                "beta_reduces_bd_star_lam_ty".to_string(),
                "beta_reduces_bd_star_lam_body".to_string(),
                "beta_reduces_bd_star_pi_dom".to_string(),
                "beta_reduces_bd_star_pi_cod".to_string(),
                "beta_reduces_bd_star_let_ty".to_string(),
                "beta_reduces_bd_star_let_val".to_string(),
                "beta_reduces_bd_star_let_body".to_string(),
                "beta_reduces_bd_star_proj".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Closure transports — the two closures are interconvertible.
        // =========================================================
        //
        // beta_bd_star_subsumes_par_bd_star :
        //   beta_reduces_bd_star e e' -> par_reduces_bd_star e e'.
        // Induction on beta_reduces_bd_star.rec: refl ↦ par_reduces_bd_star.refl;
        // step (e ⇒ e', e' ⇒* e'') ↦ compose the head par-closure
        // (beta_subsumes_par_bd_star of the single beta step) with the IH via
        // par_reduces_bd_star_trans. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "beta_bd_star_subsumes_par_bd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "beta_reduces_bd_star e e' -> par_reduces_bd_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) ",
                    "(h0 : beta_reduces_bd_star e0 e0') => ",
                    "beta_reduces_bd_star.rec ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(_ : beta_reduces_bd_star a b) => par_reduces_bd_star a b) ",
                    "(fun (e : KExpr) => par_reduces_bd_star.refl e) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : beta_reduces_bd e e') ",
                    "(_htail : beta_reduces_bd_star e' e'') ",
                    "(ih : par_reduces_bd_star e' e'') => ",
                    "par_reduces_bd_star_trans e e' e'' ",
                    "(beta_subsumes_par_bd_star e e' hstep) ih) ",
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Closure transport: the iota-free beta closure embeds into the ",
                "iota-free parallel closure. Induction on beta_reduces_bd_star.rec ",
                "composing each head step (embedded via beta_subsumes_par_bd_star) ",
                "with the IH through par_reduces_bd_star_trans. DerivedProved, ",
                "zero axiom_deps. Part of #2859 Wave 141 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd_star".to_string(),
                "beta_reduces_bd_star.rec".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.refl".to_string(),
                "par_reduces_bd_star_trans".to_string(),
                "beta_subsumes_par_bd_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_bd_star_subsumes_beta_bd_star :
        //   par_reduces_bd_star e e' -> beta_reduces_bd_star e e'.
        // Induction on par_reduces_bd_star.rec: refl ↦ beta_reduces_bd_star.refl;
        // step (e ⇒ e', e' ⇒* e'') ↦ the head par step expands to a beta
        // sequence (par_subsumes_beta_bd_star), then beta_reduces_bd_star_trans
        // with the IH. DerivedProved, zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "par_bd_star_subsumes_beta_bd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces_bd_star e e' -> beta_reduces_bd_star e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) ",
                    "(h0 : par_reduces_bd_star e0 e0') => ",
                    "par_reduces_bd_star.rec ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(_ : par_reduces_bd_star a b) => beta_reduces_bd_star a b) ",
                    "(fun (e : KExpr) => beta_reduces_bd_star.refl e) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_bd e e') ",
                    "(_htail : par_reduces_bd_star e' e'') ",
                    "(ih : beta_reduces_bd_star e' e'') => ",
                    "beta_reduces_bd_star_trans e e' e'' ",
                    "(par_subsumes_beta_bd_star e e' hstep) ih) ",
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Closure transport: the iota-free parallel closure embeds into ",
                "the iota-free beta closure. Induction on par_reduces_bd_star.rec ",
                "expanding each head par step into a beta sequence ",
                "(par_subsumes_beta_bd_star) and composing with the IH via ",
                "beta_reduces_bd_star_trans. Together with ",
                "beta_bd_star_subsumes_par_bd_star this makes the two closures ",
                "interconvertible (the closure equivalence of GOAL #1). ",
                "DerivedProved, zero axiom_deps. Part of #2859 Wave 141 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_bd".to_string(),
                "par_reduces_bd_star".to_string(),
                "par_reduces_bd_star.rec".to_string(),
                "beta_reduces_bd_star".to_string(),
                "beta_reduces_bd_star.refl".to_string(),
                "par_subsumes_beta_bd_star".to_string(),
                "beta_reduces_bd_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // beta_bd_join_witness + beta_bd_confluent — GOAL #2.
        // =========================================================
        //
        // beta_bd_join_witness packages the iota-free beta confluence
        // conclusion: a common reduct e3 with beta_reduces_bd_star e1 e3 and
        // beta_reduces_bd_star e2 e3. The iota-free beta analogue of
        // par_strips_witness_bd_star.
        self.add_inductive(
            r"inductive beta_bd_join_witness : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), beta_reduces_bd_star e1 e3 → beta_reduces_bd_star e2 e3 → beta_bd_join_witness e1 e2",
            "beta_bd_join_witness e1 e2 packages the iota-free beta confluence conclusion: a common reduct e3 together with beta_reduces_bd_star e1 e3 and beta_reduces_bd_star e2 e3. The iota-free beta analogue of par_strips_witness_bd_star; the conclusion shape of beta_bd_confluent. Part of #2859 Wave 141 (Route B).",
        )?;

        // beta_bd_confluent : forall e e1 e2,
        //   beta_reduces_bd_star e e1 -> beta_reduces_bd_star e e2 ->
        //   beta_bd_join_witness e1 e2.
        //
        // GOAL #2 — the iota-free Church-Rosser theorem for beta reduction.
        // Transport both legs from beta_reduces_bd_star into par_reduces_bd_star
        // (beta_bd_star_subsumes_par_bd_star), apply the iota-free multi-step
        // diamond par_reduces_bd_star_diamond to obtain a par-closure join
        // witness par_strips_witness_bd_star e1 e2 (common reduct e3 with
        // e1 ⇒* e3 and e2 ⇒* e3 in the parallel closure), then transport each
        // par-closure join leg back into the beta closure
        // (par_bd_star_subsumes_beta_bd_star) and repackage as
        // beta_bd_join_witness at the same meeting point e3. Uses only the
        // closure transports, the parallel diamond, and witness projection — all
        // iota-free. DerivedProved (full kernel/spec type-check), zero
        // axiom_deps. This is the iota-free Church-Rosser theorem; it sidesteps
        // the untyped-model / delta / iota-seam blockers (#2859 blockers
        // #1/#3/#4) by construction.
        self.add_definition(SpecDefinition {
            name: "beta_bd_confluent".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "beta_reduces_bd_star e e1 -> beta_reduces_bd_star e e2 -> ",
                "beta_bd_join_witness e1 e2"
            )
            .to_string(),
            value_src: Some(beta_bd_confluent_proof()),
            is_axiom: false,
            description: concat!(
                "The iota-free Church-Rosser theorem for beta reduction: two ",
                "iota-free multi-step beta reductions from a common source join at ",
                "a shared reduct, packaged as beta_bd_join_witness. Proved (Route ",
                "B) by the Tait-Martin-Löf bridge — transport both legs into the ",
                "iota-free parallel closure (beta_bd_star_subsumes_par_bd_star), ",
                "apply the parallel multi-step diamond par_reduces_bd_star_diamond, ",
                "and transport the join legs back into the beta closure ",
                "(par_bd_star_subsumes_beta_bd_star). Entirely iota-free — ",
                "sidesteps the untyped-model / delta / iota-seam blockers by ",
                "construction. DerivedProved, zero axiom_deps. Part of #2859 ",
                "Wave 141 (Route B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd_star".to_string(),
                "beta_bd_join_witness".to_string(),
                "beta_bd_join_witness.intro".to_string(),
                "beta_bd_star_subsumes_par_bd_star".to_string(),
                "par_bd_star_subsumes_beta_bd_star".to_string(),
                "par_reduces_bd_star_diamond".to_string(),
                "par_strips_witness_bd_star".to_string(),
                "par_strips_witness_bd_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

// =====================================================================
// Wave 135 (Route B) — congruence combinator proof terms.
// =====================================================================

/// Closed proof term for `par_strips_bd_app` (Wave 135, Route B).
///
/// Recurse on the head witness `wf : par_strips_witness_bd f1 f2` to obtain
/// the head meeting point `f3` with `f1 => f3` and `f2 => f3`; then nest the
/// recursion on the argument witness `wa` to obtain `a3` with `a1 => a3` and
/// `a2 => a3`. The compound meeting point is `KExpr.app f3 a3`; each side is
/// `par_reduces_bd.app` of the matching per-component reductions.
fn par_strips_bd_app_proof() -> String {
    // par_strips_witness_bd.rec is invoked in @-form with the two index args
    // (e1, e2) supplied explicitly and a NON-dependent motive (the indices are
    // already fixed by the call, so each minor premise binds only the meeting
    // point e3 and the two reductions, never re-binding the indices). The outer
    // rec eliminates the head witness wf (indices f1, f2) for the head meeting
    // point f3; the nested rec eliminates the argument witness wa (indices a1,
    // a2) for the argument meeting point a3. Both motives return the fixed
    // compound conclusion par_strips_witness_bd (app f1 a1) (app f2 a2).
    //
    // Inner: from pa1 : a1 => a3, pa2 : a2 => a3 (and the head reductions pf1,
    // pf2 captured from the outer minor) join the applications at app f3 a3
    // via par_reduces_bd.app on each side.
    let inner = concat!(
        "(@par_strips_witness_bd.rec a1 a2 ",
        "(fun (_wa : par_strips_witness_bd a1 a2) => ",
        "par_strips_witness_bd (KExpr.app f1 a1) (KExpr.app f2 a2)) ",
        "(fun (a3 : KExpr) ",
        "(pa1 : par_reduces_bd a1 a3) (pa2 : par_reduces_bd a2 a3) => ",
        "par_strips_witness_bd.intro ",
        "(KExpr.app f1 a1) (KExpr.app f2 a2) (KExpr.app f3 a3) ",
        "(par_reduces_bd.app f1 f3 a1 a3 pf1 pa1) ",
        "(par_reduces_bd.app f2 f3 a2 a3 pf2 pa2)) ",
        "wa)"
    );
    let outer = format!(
        concat!(
            "(@par_strips_witness_bd.rec f1 f2 ",
            "(fun (_wf : par_strips_witness_bd f1 f2) => ",
            "par_strips_witness_bd (KExpr.app f1 a1) (KExpr.app f2 a2)) ",
            "(fun (f3 : KExpr) ",
            "(pf1 : par_reduces_bd f1 f3) (pf2 : par_reduces_bd f2 f3) => ",
            "{inner}) ",
            "wf)"
        ),
        inner = inner,
    );
    format!(
        concat!(
            "fun (f1 : KExpr) (f2 : KExpr) (a1 : KExpr) (a2 : KExpr) ",
            "(wf : par_strips_witness_bd f1 f2) (wa : par_strips_witness_bd a1 a2) => ",
            "{outer}"
        ),
        outer = outer,
    )
}

/// Closed proof term for the binder congruence combinators
/// `par_strips_bd_lam` / `par_strips_bd_pi` / `par_strips_bd_forall`
/// (Wave 135, Route B), parametric in the par_reduces_bd binder constructor
/// `ctor` and the KExpr binder head `head`.
///
/// Recurse on the type/domain witness `wt : par_strips_witness_bd t1 t2` to
/// obtain the meeting point `t3` with `t1 => t3` and `t2 => t3`; then nest the
/// recursion on the body witness `wb` to obtain `b3` with `b1 => b3` and
/// `b2 => b3`. The compound meeting point is `head t3 b3`; each side is `ctor`
/// of the matching per-component reductions.
fn par_strips_bd_binder_proof(ctor: &str, head: &str) -> String {
    // Same @-form pattern as par_strips_bd_app: two nested
    // par_strips_witness_bd.rec calls with explicit index args and
    // non-dependent motives. The outer rec eliminates the type/domain witness
    // wt (indices t1, t2) for the meeting point t3; the nested rec eliminates
    // the body witness wb (indices b1, b2) for the body meeting point b3. Both
    // join at head t3 b3 via the binder constructor on each side.
    let inner = format!(
        concat!(
            "(@par_strips_witness_bd.rec b1 b2 ",
            "(fun (_wb : par_strips_witness_bd b1 b2) => ",
            "par_strips_witness_bd ({head} t1 b1) ({head} t2 b2)) ",
            "(fun (b3 : KExpr) ",
            "(pb1 : par_reduces_bd b1 b3) (pb2 : par_reduces_bd b2 b3) => ",
            "par_strips_witness_bd.intro ",
            "({head} t1 b1) ({head} t2 b2) ({head} t3 b3) ",
            "({ctor} t1 t3 b1 b3 pt1 pb1) ",
            "({ctor} t2 t3 b2 b3 pt2 pb2)) ",
            "wb)"
        ),
        head = head,
        ctor = ctor,
    );
    let outer = format!(
        concat!(
            "(@par_strips_witness_bd.rec t1 t2 ",
            "(fun (_wt : par_strips_witness_bd t1 t2) => ",
            "par_strips_witness_bd ({head} t1 b1) ({head} t2 b2)) ",
            "(fun (t3 : KExpr) ",
            "(pt1 : par_reduces_bd t1 t3) (pt2 : par_reduces_bd t2 t3) => ",
            "{inner}) ",
            "wt)"
        ),
        head = head,
        inner = inner,
    );
    format!(
        concat!(
            "fun (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr) ",
            "(wt : par_strips_witness_bd t1 t2) (wb : par_strips_witness_bd b1 b2) => ",
            "{outer}"
        ),
        outer = outer,
    )
}

/// Closed proof term for `par_strips_bd_let` (let-promotion, Wave 135 shape).
///
/// The three-position analogue of `par_strips_bd_binder_proof` for the genuine
/// `KExpr.let_` constructor: recurse on the type witness `wt` for the meeting
/// point `t3`, nest on the value witness `wv` for `v3`, nest on the body
/// witness `wb` for `b3`. The compound meeting point is `KExpr.let_ t3 v3 b3`;
/// each side is `par_reduces_bd.let_cong` of the matching per-component
/// reductions.
fn par_strips_bd_let_proof() -> String {
    // Innermost: body witness wb → b3; assemble the meet at let_ t3 v3 b3.
    let inner = concat!(
        "(@par_strips_witness_bd.rec b1 b2 ",
        "(fun (_wb : par_strips_witness_bd b1 b2) => ",
        "par_strips_witness_bd (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
        "(fun (b3 : KExpr) ",
        "(pb1 : par_reduces_bd b1 b3) (pb2 : par_reduces_bd b2 b3) => ",
        "par_strips_witness_bd.intro ",
        "(KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2) (KExpr.let_ t3 v3 b3) ",
        "(par_reduces_bd.let_cong t1 t3 v1 v3 b1 b3 pt1 pv1 pb1) ",
        "(par_reduces_bd.let_cong t2 t3 v2 v3 b2 b3 pt2 pv2 pb2)) ",
        "wb)"
    );
    // Middle: value witness wv → v3.
    let mid = format!(
        concat!(
            "(@par_strips_witness_bd.rec v1 v2 ",
            "(fun (_wv : par_strips_witness_bd v1 v2) => ",
            "par_strips_witness_bd (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
            "(fun (v3 : KExpr) ",
            "(pv1 : par_reduces_bd v1 v3) (pv2 : par_reduces_bd v2 v3) => ",
            "{inner}) ",
            "wv)"
        ),
        inner = inner,
    );
    // Outer: type witness wt → t3.
    let outer = format!(
        concat!(
            "(@par_strips_witness_bd.rec t1 t2 ",
            "(fun (_wt : par_strips_witness_bd t1 t2) => ",
            "par_strips_witness_bd (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
            "(fun (t3 : KExpr) ",
            "(pt1 : par_reduces_bd t1 t3) (pt2 : par_reduces_bd t2 t3) => ",
            "{mid}) ",
            "wt)"
        ),
        mid = mid,
    );
    format!(
        concat!(
            "fun (t1 : KExpr) (t2 : KExpr) (v1 : KExpr) (v2 : KExpr) ",
            "(b1 : KExpr) (b2 : KExpr) ",
            "(wt : par_strips_witness_bd t1 t2) (wv : par_strips_witness_bd v1 v2) ",
            "(wb : par_strips_witness_bd b1 b2) => ",
            "{outer}"
        ),
        outer = outer,
    )
}

// =====================================================================
// Wave 130 (Route B) — par_lift_bd closed proof term.
// =====================================================================
//
// Target:
//   forall (v v' : KExpr) (c : Nat) (a : Nat),
//     par_reduces_bd v v' -> par_reduces_bd (lift_at v c a) (lift_at v' c a)
//
// Proof: par_reduces_bd.rec on the v ⇒ v' derivation, with the motive
// universalizing (c, a) so binder arms recurse at cutoff (succ c):
//   motive := fun (e e' : KExpr) (_ : par_reduces_bd e e') =>
//     forall (c a : Nat), par_reduces_bd (lift_at e c a) (lift_at e' c a)
//
//   refl     : par_reduces_bd.refl (lift_at e c a).
//   app      : par_reduces_bd.app on lifted IHs; lift_at_app is defeq so the
//              constructor result checks against the goal directly.
//   lam/pi/forall_ : matching congruence constructor; ty/dom IH at cutoff c,
//              body IH at cutoff (succ c). lift_at_lam/pi are defeq;
//              KExpr.forall_ is the reducible pi alias so the pi-shaped term
//              checks against the forall_-shaped goal.
//   beta/let_: lift the redex (defeq through the lift_at app/lam unfold for
//              beta; through the lift_at let_ unfold for the genuine-let_
//              zeta — post let-promotion the lifted source is let_-headed,
//              NOT an app(lam) alias). par_reduces_bd.beta/
//              .let_ yields second index
//                instantiate (lift_at body' (succ c) a) (lift_at arg' c a),
//              which we transport to the goal's
//                lift_at (instantiate body' arg') c a
//              via lift_instantiate_swap at d=0 (Nat.add Nat.zero c rewritten to
//              c by nat_zero_add), using Eq.substType on the par_reduces_bd second
//              index. No iota arm (the iota-free relation has none), no new
//              axiom; Eq.substType is the foundational Eq eliminator (not a
//              domain axiom), so axiom_deps stays empty.
//   let_cong : matching congruence constructor on the lifted IHs (ty/val at
//              cutoff c, body at succ c) — the trailing minor.

/// Closed proof term for `par_lift_bd` (Wave 130, Route B).
fn par_lift_bd_proof() -> String {
    // Motive: universalize the lift parameters (c, a).
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
        "forall (c : Nat) (a : Nat), ",
        "par_reduces_bd (lift_at e c a) (lift_at e' c a))"
    );

    // IH shape for a sub-derivation on `SUB ⇒ SUB'`.
    let ih = "forall (c : Nat) (a : Nat), par_reduces_bd (lift_at SUB c a) (lift_at SUB' c a)";

    // refl arm.
    let refl_arm = concat!(
        "(fun (e : KExpr) (c : Nat) (a : Nat) => ",
        "par_reduces_bd.refl (lift_at e c a))"
    );

    // app arm: lifted IHs through the (defeq) lift_at_app unfold.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_bd f f') (_ha : par_reduces_bd a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) (c : Nat) (a : Nat) => ",
            "par_reduces_bd.app (lift_at f c a) (lift_at f' c a) ",
            "(lift_at a0 c a) (lift_at a0' c a) (ihf c a) (iha c a))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // beta/let_ contraction transport: from
    //   instantiate (lift_at BODYP (succ c) a) (lift_at ARGP c a)
    // to
    //   lift_at (instantiate BODYP ARGP) c a
    // via lift_instantiate_swap BODYP ARGP Nat.zero c a, after rewriting
    // (Nat.add Nat.zero c) to c with nat_zero_add c.
    //
    // swap_raw : Eq KExpr
    //   (lift_at (instantiate_at BODYP ARGP Nat.zero) (Nat.add Nat.zero c) a)
    //   (instantiate_at (lift_at BODYP (Nat.succ (Nat.add Nat.zero c)) a)
    //                   (lift_at ARGP c a) Nat.zero)
    //
    // We build the target equation
    //   eq : Eq KExpr (lift_at (instantiate_at BODYP ARGP Nat.zero) c a)
    //                 (instantiate_at (lift_at BODYP (Nat.succ c) a)
    //                                 (lift_at ARGP c a) Nat.zero)
    // by Eq.trans-chaining congruences on the Nat argument (Eq.cong, NOT
    // Eq.substType — the equation is Prop-valued so the Type-targeting Eq.subst
    // does not apply to the inner rewrite):
    //   cong_lhs : goal_lhs = swap_lhs   (rewrite c -> Nat.add Nat.zero c)
    //   cong_rhs : swap_rhs = goal_rhs   (rewrite Nat.add Nat.zero c -> c)
    // eq := Eq.trans goal_lhs swap_lhs goal_rhs cong_lhs
    //         (Eq.trans swap_lhs swap_rhs goal_rhs swap_raw cong_rhs)
    // The outer Eq.substType on the par_reduces_bd second index is Type-valued
    // (par_reduces_bd : KExpr -> KExpr -> Type), so it applies cleanly.
    //
    // `contract` builds the transport given:
    //   lhs_head  = the (defeq) reduced first index of the lifted redex
    //   ctor_term = the fully-applied constructor term (second index =
    //               instantiate (lift_at BODYP (succ c) a) (lift_at ARGP c a))
    //   bodyp/argp = BODYP, ARGP (the reduced bodies, e.g. body', arg').
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        // goal_lhs = lift_at (instantiate_at BODYP ARGP 0) c a
        let goal_lhs = format!(
            "(lift_at (instantiate_at {bodyp} {argp} Nat.zero) c a)",
            bodyp = bodyp,
            argp = argp,
        );
        // swap_lhs = lift_at (instantiate_at BODYP ARGP 0) (Nat.add Nat.zero c) a
        let swap_lhs = format!(
            "(lift_at (instantiate_at {bodyp} {argp} Nat.zero) (Nat.add Nat.zero c) a)",
            bodyp = bodyp,
            argp = argp,
        );
        // swap_rhs = instantiate_at (lift BODYP (succ (Nat.add Nat.zero c)) a) (lift ARGP c a) 0
        let swap_rhs = format!(
            concat!(
                "(instantiate_at (lift_at {bodyp} (Nat.succ (Nat.add Nat.zero c)) a) ",
                "(lift_at {argp} c a) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        // goal_rhs = ctor second index = instantiate_at (lift BODYP (succ c) a) (lift ARGP c a) 0
        let goal_rhs = format!(
            concat!(
                "(instantiate_at (lift_at {bodyp} (Nat.succ c) a) ",
                "(lift_at {argp} c a) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let swap_raw = format!(
            "(lift_instantiate_swap {bodyp} {argp} Nat.zero c a)",
            bodyp = bodyp,
            argp = argp,
        );
        // cong_lhs : goal_lhs = swap_lhs (rewrite c -> Nat.add Nat.zero c via symm nat_zero_add)
        let cong_lhs = format!(
            concat!(
                "(Eq.cong Nat KExpr ",
                "(fun (n : Nat) => lift_at (instantiate_at {bodyp} {argp} Nat.zero) n a) ",
                "c (Nat.add Nat.zero c) ",
                "(Eq.symm Nat (Nat.add Nat.zero c) c (nat_zero_add c)))"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        // cong_rhs : swap_rhs = goal_rhs (rewrite Nat.add Nat.zero c -> c via nat_zero_add)
        let cong_rhs = format!(
            concat!(
                "(Eq.cong Nat KExpr ",
                "(fun (n : Nat) => instantiate_at (lift_at {bodyp} (Nat.succ n) a) ",
                "(lift_at {argp} c a) Nat.zero) ",
                "(Nat.add Nat.zero c) c (nat_zero_add c))"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        // eq : goal_lhs = goal_rhs
        let eq = format!(
            concat!(
                "(Eq.trans KExpr {goal_lhs} {swap_lhs} {goal_rhs} {cong_lhs} ",
                "(Eq.trans KExpr {swap_lhs} {swap_rhs} {goal_rhs} {swap_raw} {cong_rhs}))"
            ),
            goal_lhs = goal_lhs,
            swap_lhs = swap_lhs,
            swap_rhs = swap_rhs,
            goal_rhs = goal_rhs,
            cong_lhs = cong_lhs,
            cong_rhs = cong_rhs,
            swap_raw = swap_raw,
        );
        // P x := par_reduces_bd lhs_head x.
        let p = format!(
            "(fun (x : KExpr) => par_reduces_bd {lhs_head} x)",
            lhs_head = lhs_head,
        );
        // ctor_term : P goal_rhs ; want P goal_lhs ; transport with Eq.symm eq.
        // Eq.substType KExpr P goal_rhs goal_lhs (Eq.symm eq) ctor_term : P goal_lhs.
        format!(
            concat!(
                "(Eq.substType KExpr {p} {goal_rhs} {goal_lhs} ",
                "(Eq.symm KExpr {goal_lhs} {goal_rhs} {eq}) ",
                "{ctor_term})"
            ),
            p = p,
            goal_rhs = goal_rhs,
            goal_lhs = goal_lhs,
            eq = eq,
            ctor_term = ctor_term,
        )
    };

    // beta arm.
    let beta_lhs_head = concat!(
        "(KExpr.app (KExpr.lam (lift_at A c a) (lift_at body (Nat.succ c) a)) ",
        "(lift_at arg c a))"
    );
    let beta_ctor = concat!(
        "(par_reduces_bd.beta (lift_at A c a) (lift_at A' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(lift_at arg c a) (lift_at arg' c a) ",
        "(ihA c a) (ihbody (Nat.succ c) a) (iharg c a))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_bd A A') (_hbody : par_reduces_bd body body') ",
            "(_harg : par_reduces_bd arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(c : Nat) (a : Nat) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );

    // lam/pi/forall_ congruence arm, parametric in the constructor.
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_bd ty ty') (_hbody : par_reduces_bd body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) (c : Nat) (a : Nat) => ",
                "{ctor} (lift_at ty c a) (lift_at ty' c a) ",
                "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
                "(ihty c a) (ihbody (Nat.succ c) a))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };

    // let_ (zeta) arm — genuine-let_ source (the lifted source is let_-headed
    // through the lift_at let_ unfold; ty/val at cutoff c, body at succ c),
    // beta-shaped contraction transport on the second index.
    let let_lhs_head = concat!(
        "(KExpr.let_ (lift_at ty c a) (lift_at val c a) ",
        "(lift_at body (Nat.succ c) a))"
    );
    let let_ctor = concat!(
        "(par_reduces_bd.let_ (lift_at ty c a) (lift_at ty' c a) ",
        "(lift_at val c a) (lift_at val' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(ihty c a) (ihval c a) (ihbody (Nat.succ c) a))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
            "(_hbody : par_reduces_bd body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );

    // let_cong arm — trailing minor: matching congruence constructor on the
    // lifted IHs (ty/val at cutoff c, body at succ c).
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
            "(_hbody : par_reduces_bd body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) => ",
            "par_reduces_bd.let_cong (lift_at ty c a) (lift_at ty' c a) ",
            "(lift_at val c a) (lift_at val' c a) ",
            "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
            "(ihty c a) (ihval c a) (ihbody (Nat.succ c) a))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );

    // proj arm — proj is a 1-child congruence: lift_at descends through proj,
    // the lifted ihsub reassembles par_reduces_bd.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_bd sub sub') (ihsub : {ih_sub}) ",
            "(c : Nat) (a : Nat) => ",
            "par_reduces_bd.proj s i (lift_at sub c a) (lift_at sub' c a) (ihsub c a))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (v0 : KExpr) (v0' : KExpr) (c0 : Nat) (a0 : Nat) ",
            "(h0 : par_reduces_bd v0 v0') => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "v0 v0' h0 c0 a0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_bd.lam"),
        pi_arm = binder_arm("par_reduces_bd.pi"),
        forall_arm = binder_arm("par_reduces_bd.forall_"),
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

// =====================================================================
// Wave 132 (Route B) — par_subst_bd closed proof term.
// =====================================================================
//
// Target:
//   forall (e e' v v' : KExpr),
//     par_reduces_bd e e' -> par_reduces_bd v v' ->
//     par_reduces_bd (instantiate e v) (instantiate e' v')
//
// Proof: par_reduces_bd.rec on the first hypothesis e ⇒ e', with a
// DEPTH-GENERALIZED motive (so binder arms recurse at succ depth):
//   motive := fun (e e' : KExpr) (_ : par_reduces_bd e e') =>
//     forall (v v' : KExpr) (d : Nat), par_reduces_bd v v' ->
//       par_reduces_bd (instantiate_at e v d) (instantiate_at e' v' d)
// The conclusion is reached by specializing d = Nat.zero (instantiate is the
// instantiate_at _ _ Nat.zero wrapper, so the indices are defeq).
//
//   refl     : par_subst_refl_bd e v v' d h (the same-skeleton congruence,
//              Wave 131).
//   app      : par_reduces_bd.app on the two IHs at depth d.
//   lam/pi/forall_ : matching congruence constructor; ty/dom IH at depth d,
//              body IH at depth (succ d). forall_ reuses the pi shape (alias).
//   beta/let_: contract the redex (the substituted let_ source is let_-headed
//              via the instantiate_at let_ unfold — genuine constructor, not
//              an app(lam) alias). par_reduces_bd.beta/.let_ yields second
//              index instantiate (inst body' v' (succ d)) (inst arg' v' d),
//              which equals the goal's instantiate_at (instantiate body' arg')
//              v' d by instantiate_nested_commutes_zero_subst (subst commutes
//              with subst at depth 0); transport via Eq.substType on the
//              par_reduces_bd second index (Type, so Eq.substType applies).
//   let_cong : matching congruence constructor on the three IHs (ty/val at
//              depth d, body at succ d) — the trailing minor.
// No iota arm (par_reduces_bd has none), no new axiom. Part of #2859 Wave 132.

/// Closed proof term for `par_subst_bd` (Wave 132, Route B).
fn par_subst_bd_proof() -> String {
    // Depth-generalized motive.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_bd v v' -> ",
        "par_reduces_bd (instantiate_at e v d) (instantiate_at e' v' d))"
    );
    // IH shape for a sub-derivation SUB ⇒ SUB'.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_bd v v' -> ",
        "par_reduces_bd (instantiate_at SUB v d) (instantiate_at SUB' v' d)"
    );

    // refl arm: par_subst_refl_bd.
    let refl_arm = concat!(
        "(fun (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(h : par_reduces_bd v v') => par_subst_refl_bd e v v' d h)"
    );

    // app arm.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_bd f f') (_ha : par_reduces_bd a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
            "par_reduces_bd.app ",
            "(instantiate_at f v d) (instantiate_at f' v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v' d) ",
            "(ihf v v' d h) (iha v v' d h))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // lam/pi/forall_ congruence arm, parametric in the constructor.
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_bd ty ty') (_hbody : par_reduces_bd body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
                "{ctor} ",
                "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
                "(ihty v v' d h) (ihbody v v' (Nat.succ d) h))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };

    // beta/let_ contraction transport: from
    //   instantiate (inst BODYP v' (succ d)) (inst ARGP v' d)
    //     = instantiate_at (instantiate_at BODYP v' (Nat.succ d))
    //                      (instantiate_at ARGP v' d) Nat.zero
    // to the goal's
    //   instantiate_at (instantiate BODYP ARGP) v' d
    //     = instantiate_at (instantiate_at BODYP ARGP Nat.zero) v' d
    // via instantiate_nested_commutes_zero_subst BODYP ARGP v' d, whose stated
    // equation is exactly
    //   instantiate_at (instantiate BODYP ARGP) v' d
    //     = instantiate_at (instantiate_at BODYP v' (Nat.succ d))
    //                      (instantiate_at ARGP v' d) Nat.zero.
    //
    // `contract` builds the transport given:
    //   lhs_head  = the (defeq) reduced first index of the substituted redex
    //   ctor_term = the constructor term (second index = instantiate (inst
    //               BODYP v' (succ d)) (inst ARGP v' d))
    //   bodyp/argp = BODYP, ARGP (reduced bodies, e.g. body', arg'/val').
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        // goal_rhs = instantiate_at (instantiate_at BODYP ARGP Nat.zero) v' d
        let goal_rhs = format!(
            "(instantiate_at (instantiate_at {bodyp} {argp} Nat.zero) v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        // ctor_rhs = instantiate_at (instantiate_at BODYP v' (Nat.succ d))
        //                           (instantiate_at ARGP v' d) Nat.zero
        let ctor_rhs = format!(
            concat!(
                "(instantiate_at (instantiate_at {bodyp} v' (Nat.succ d)) ",
                "(instantiate_at {argp} v' d) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        // eq : goal_rhs = ctor_rhs (the nested-commutes lemma).
        let eq = format!(
            "(instantiate_nested_commutes_zero_subst {bodyp} {argp} v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        // P x := par_reduces_bd lhs_head x.
        let p = format!(
            "(fun (x : KExpr) => par_reduces_bd {lhs_head} x)",
            lhs_head = lhs_head,
        );
        // ctor_term : P ctor_rhs ; want P goal_rhs ; transport with Eq.symm eq.
        format!(
            concat!(
                "(Eq.substType KExpr {p} {ctor_rhs} {goal_rhs} ",
                "(Eq.symm KExpr {goal_rhs} {ctor_rhs} {eq}) ",
                "{ctor_term})"
            ),
            p = p,
            ctor_rhs = ctor_rhs,
            goal_rhs = goal_rhs,
            eq = eq,
            ctor_term = ctor_term,
        )
    };

    // beta arm.
    let beta_lhs_head = concat!(
        "(KExpr.app ",
        "(KExpr.lam (instantiate_at A v d) (instantiate_at body v (Nat.succ d))) ",
        "(instantiate_at arg v d))"
    );
    let beta_ctor = concat!(
        "(par_reduces_bd.beta ",
        "(instantiate_at A v d) (instantiate_at A' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(instantiate_at arg v d) (instantiate_at arg' v' d) ",
        "(ihA v v' d h) (ihbody v v' (Nat.succ d) h) (iharg v v' d h))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_bd A A') (_hbody : par_reduces_bd body body') ",
            "(_harg : par_reduces_bd arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );

    // let_ (zeta) arm — genuine-let_ source (the substituted source is
    // let_-headed via the instantiate_at let_ unfold; ty/val at depth d,
    // body at succ d), beta-shaped contraction with arg := val.
    let let_lhs_head = concat!(
        "(KExpr.let_ ",
        "(instantiate_at ty v d) (instantiate_at val v d) ",
        "(instantiate_at body v (Nat.succ d)))"
    );
    let let_ctor = concat!(
        "(par_reduces_bd.let_ ",
        "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
        "(instantiate_at val v d) (instantiate_at val' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(ihty v v' d h) (ihval v v' d h) (ihbody v v' (Nat.succ d) h))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
            "(_hbody : par_reduces_bd body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );

    // let_cong arm — trailing minor: matching congruence constructor on the
    // three IHs (ty/val at depth d, body at succ d).
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
            "(_hbody : par_reduces_bd body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
            "par_reduces_bd.let_cong ",
            "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
            "(instantiate_at val v d) (instantiate_at val' v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
            "(ihty v v' d h) (ihval v v' d h) (ihbody v v' (Nat.succ d) h))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );

    // proj arm — 1-child congruence: substitution descends through proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_bd sub sub') (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
            "par_reduces_bd.proj s i ",
            "(instantiate_at sub v d) (instantiate_at sub' v' d) (ihsub v v' d h))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (e0 : KExpr) (e0' : KExpr) (v0 : KExpr) (v0' : KExpr) ",
            "(h_ee : par_reduces_bd e0 e0') (h_vv : par_reduces_bd v0 v0') => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h_ee v0 v0' Nat.zero h_vv"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_bd.lam"),
        pi_arm = binder_arm("par_reduces_bd.pi"),
        forall_arm = binder_arm("par_reduces_bd.forall_"),
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

// =====================================================================
// Wave 131 (Route B) — par_subst_refl_bd closed proof term.
// =====================================================================
//
// Target:
//   forall (e v v' : KExpr) (d : Nat),
//     par_reduces_bd v v' ->
//     par_reduces_bd (instantiate_at e v d) (instantiate_at e v' d)
//
// Proof: KExpr.rec on e, motive universalizing (v, v', d) and threading the
// hypothesis par_reduces_bd v v':
//   motive := fun (e : KExpr) => forall (v v' : KExpr) (d : Nat),
//     par_reduces_bd v v' ->
//     par_reduces_bd (instantiate_at e v d) (instantiate_at e v' d)
//
//   sort/const : par_reduces_bd.refl (instantiate_at is identity on heads,
//                defeq).
//   bvar i     : double-Nat.rec convoy on (Nat.sub i d) outer / (Nat.sub d i)
//                middle, threading equality witnesses so each region applies
//                the matching unfolder:
//                  i < d  (sub d i = succ): both sides = bvar i  -> refl.
//                  i = d  (both sub = 0)  : both sides = lift_at v/v' 0 d
//                          -> par_lift_bd v v' Nat.zero d h.
//                  i > d  (sub i d = succ): both sides = bvar (i-1) -> refl,
//                          with sub d i = 0 from nat_sub_zero_of_sub_pos.
//                Each leaf produces par_reduces_bd on the reduced forms and
//                transports the two indices back to instantiate_at (bvar i) v/v'
//                d with two Eq.substType (the par_reduces_bd indices are Type, so
//                Eq.substType applies).
//   app        : par_reduces_bd.app on the two IHs at depth d (instantiate_at
//                is defeq on app).
//   lam/pi     : matching congruence constructor; ty IH at depth d, body IH at
//                depth (succ d) (instantiate_at defeq on lam/pi).
//   let_       : par_reduces_bd.let_cong on the three IHs; ty/val IHs at depth
//                d, body IH at depth (succ d) (instantiate_at defeq on the
//                genuine let_ constructor) — the trailing KExpr.rec minor
//                (let-promotion).
// No iota arm (KExpr.rec has 7 arms; the iota-free relation has none), no new
// axiom. Part of #2859 Wave 131 (Route B).

/// Closed proof term for `par_subst_refl_bd` (Wave 131, Route B).
fn par_subst_refl_bd_proof() -> String {
    // Motive over the recursed term e.
    let motive = concat!(
        "(fun (e : KExpr) => forall (v : KExpr) (v' : KExpr) (d : Nat), ",
        "par_reduces_bd v v' -> ",
        "par_reduces_bd (instantiate_at e v d) (instantiate_at e v' d))"
    );
    // IH shape for a sub-term SUB.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_bd v v' -> ",
        "par_reduces_bd (instantiate_at SUB v d) (instantiate_at SUB v' d)"
    );

    // Goal G(i) for the bvar arm.
    let goal_l = "(instantiate_at (KExpr.bvar i) v d)";
    let goal_r = "(instantiate_at (KExpr.bvar i) v' d)";

    // transport: given X X' eqL eqR T, produce
    //   par_reduces_bd (instantiate_at (bvar i) v d) (instantiate_at (bvar i) v' d)
    // from T : par_reduces_bd X X', eqL : goal_l = X, eqR : goal_r = X'.
    let transport = |xl: &str, xr: &str, eql: &str, eqr: &str, t: &str| -> String {
        // inner : par_reduces_bd goal_l X'  (rewrite X -> goal_l on first index)
        let inner = format!(
            concat!(
                "(Eq.substType KExpr (fun (y : KExpr) => par_reduces_bd y {xr}) ",
                "{xl} {goal_l} ",
                "(Eq.symm KExpr {goal_l} {xl} {eql}) {t})"
            ),
            xr = xr,
            xl = xl,
            goal_l = goal_l,
            eql = eql,
            t = t,
        );
        // outer : par_reduces_bd goal_l goal_r (rewrite X' -> goal_r on 2nd index)
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (y : KExpr) => par_reduces_bd {goal_l} y) ",
                "{xr} {goal_r} ",
                "(Eq.symm KExpr {goal_r} {xr} {eqr}) {inner})"
            ),
            goal_l = goal_l,
            xr = xr,
            goal_r = goal_r,
            eqr = eqr,
            inner = inner,
        )
    };

    // LEAF: i = d (h_id : sub i d = 0, h_di0 : sub d i = 0).
    let leaf_eq = {
        let xl = "(lift_at v Nat.zero d)";
        let xr = "(lift_at v' Nat.zero d)";
        let eql = "(instantiate_at_bvar_eq_from_zero_witnesses i d v h_di0 h_id)";
        let eqr = "(instantiate_at_bvar_eq_from_zero_witnesses i d v' h_di0 h_id)";
        let t = "(par_lift_bd v v' Nat.zero d h)";
        transport(xl, xr, eql, eqr, t)
    };

    // LEAF: i < d (h_di : sub d i = succ k2, h_id : sub i d = 0). Both = bvar i.
    let leaf_below = {
        let w_di = "(nat_pos_witness_from_succ_eq (Nat.sub d i) k2 h_di)";
        let xl = "(KExpr.bvar i)";
        let xr = "(KExpr.bvar i)";
        let eql = format!(
            concat!(
                "(Eq.trans KExpr {goal_l} (instantiate_bvar_at i d v) (KExpr.bvar i) ",
                "(instantiate_at_bvar i v d) ",
                "(instantiate_bvar_at_below i d v {w_di}))"
            ),
            goal_l = goal_l,
            w_di = w_di,
        );
        let eqr = format!(
            concat!(
                "(Eq.trans KExpr {goal_r} (instantiate_bvar_at i d v') (KExpr.bvar i) ",
                "(instantiate_at_bvar i v' d) ",
                "(instantiate_bvar_at_below i d v' {w_di}))"
            ),
            goal_r = goal_r,
            w_di = w_di,
        );
        let t = "(par_reduces_bd.refl (KExpr.bvar i))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // LEAF: i > d (h_id : sub i d = succ k4). Both = bvar (i-1).
    let leaf_above = {
        let h_di0 = "(nat_sub_zero_of_sub_pos i d k4 h_id)";
        let w_id = "(nat_pos_witness_from_succ_eq (Nat.sub i d) k4 h_id)";
        let xl = "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))";
        let xr = "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))";
        let eql = format!(
            concat!(
                "(Eq.trans KExpr {goal_l} (instantiate_bvar_at i d v) ",
                "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar i v d) ",
                "(instantiate_bvar_at_above i d v {h_di0} {w_id}))"
            ),
            goal_l = goal_l,
            h_di0 = h_di0,
            w_id = w_id,
        );
        let eqr = format!(
            concat!(
                "(Eq.trans KExpr {goal_r} (instantiate_bvar_at i d v') ",
                "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar i v' d) ",
                "(instantiate_bvar_at_above i d v' {h_di0} {w_id}))"
            ),
            goal_r = goal_r,
            h_di0 = h_di0,
            w_id = w_id,
        );
        let t = "(par_reduces_bd.refl (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // bvar arm: double-Nat.rec convoy.
    let bvar_arm = format!(
        concat!(
            "(fun (i : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
            "(h : par_reduces_bd v v') => ",
            // OUTER Nat.rec on sub(i, d)
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub i d) g -> ",
            "par_reduces_bd {goal_l} {goal_r}) ",
            // OUTER ZERO: sub(i,d) = 0
            "(fun (h_id : Eq Nat (Nat.sub i d) Nat.zero) => ",
            // MIDDLE Nat.rec on sub(d, i)
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub d i) g2 -> ",
            "par_reduces_bd {goal_l} {goal_r}) ",
            // MIDDLE ZERO: sub(d,i) = 0 (i = d)
            "(fun (h_di0 : Eq Nat (Nat.sub d i) Nat.zero) => {leaf_eq}) ",
            // MIDDLE SUCC: sub(d,i) = succ k2 (i < d)
            "(fun (k2 : Nat) ",
            "(_ : Eq Nat (Nat.sub d i) k2 -> par_reduces_bd {goal_l} {goal_r}) ",
            "(h_di : Eq Nat (Nat.sub d i) (Nat.succ k2)) => {leaf_below}) ",
            "(Nat.sub d i) (Eq.refl Nat (Nat.sub d i))) ",
            // OUTER SUCC: sub(i,d) = succ k4 (i > d)
            "(fun (k4 : Nat) ",
            "(_ : Eq Nat (Nat.sub i d) k4 -> par_reduces_bd {goal_l} {goal_r}) ",
            "(h_id : Eq Nat (Nat.sub i d) (Nat.succ k4)) => {leaf_above}) ",
            "(Nat.sub i d) (Eq.refl Nat (Nat.sub i d)))"
        ),
        goal_l = goal_l,
        goal_r = goal_r,
        leaf_eq = leaf_eq,
        leaf_below = leaf_below,
        leaf_above = leaf_above,
    );

    // sort/const arms.
    let sort_arm = concat!(
        "(fun (sv : Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_h : par_reduces_bd v v') => par_reduces_bd.refl (KExpr.sort sv))"
    );
    let const_arm = concat!(
        "(fun (nm : Name) (us : ListType Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_h : par_reduces_bd v v') => par_reduces_bd.refl (KExpr.const nm us))"
    );

    // app arm.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (a0 : KExpr) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
            "par_reduces_bd.app ",
            "(instantiate_at f v d) (instantiate_at f v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0 v' d) ",
            "(ihf v v' d h) (iha v v' d h))"
        ),
        ih_f = ih.replace("SUB", "f"),
        ih_a = ih.replace("SUB", "a0"),
    );

    // lam/pi arm parametric in the constructor.
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
                "{ctor} ",
                "(instantiate_at ty v d) (instantiate_at ty v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
                "(ihty v v' d h) (ihbody v v' (Nat.succ d) h))"
            ),
            ih_ty = ih.replace("SUB", "ty"),
            ih_body = ih.replace("SUB", "body"),
            ctor = ctor,
        )
    };

    // let_ arm — trailing KExpr.rec minor (let-promotion): let_cong on the
    // three IHs; ty/val at depth d, body at succ d.
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
            "par_reduces_bd.let_cong ",
            "(instantiate_at ty v d) (instantiate_at ty v' d) ",
            "(instantiate_at val v d) (instantiate_at val v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
            "(ihty v v' d h) (ihval v v' d h) (ihbody v v' (Nat.succ d) h))"
        ),
        ih_ty = ih.replace("SUB", "ty"),
        ih_val = ih.replace("SUB", "val"),
        ih_body = ih.replace("SUB", "body"),
    );

    // proj arm — 1-child congruence: instantiate_at descends through proj,
    // the substituted ihsub reassembles par_reduces_bd.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_bd v v') => ",
            "par_reduces_bd.proj s i ",
            "(instantiate_at sub v d) (instantiate_at sub v' d) (ihsub v v' d h))"
        ),
        ih_sub = ih.replace("SUB", "sub"),
    );
    // lit arm — leaf: instantiate is identity on lit, so refl.
    let lit_arm = concat!(
        "(fun (m : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_h : par_reduces_bd v v') => par_reduces_bd.refl (KExpr.lit m))"
    );

    format!(
        concat!(
            "fun (e0 : KExpr) => ",
            "KExpr.rec {motive} ",
            "{sort_arm} {bvar_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {const_arm} {let_arm} {proj_arm} {lit_arm} ",
            "e0"
        ),
        motive = motive,
        sort_arm = sort_arm,
        bvar_arm = bvar_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_bd.lam"),
        pi_arm = binder_arm("par_reduces_bd.pi"),
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

// =====================================================================
// Wave 136 (Route B) — par_reduces_bd shape-recovery (inversion) lemmas.
// =====================================================================
//
// These are the convoy lemmas the inner case-split of `par_strips_bd`
// needs: from a `par_reduces_bd` derivation whose SOURCE has a concrete
// constructor shape (`app f a`, `lam ty body`, `pi dom body`,
// `forall_ dom body`), recover — constructively, by `par_reduces_bd.rec`
// with a source-equation motive — exactly which constructor fired and the
// sub-derivations it carries. Mismatched constructor arms are discharged by
// the in-tree no-confusion lemmas (`lam_ne_app`/`pi_ne_app` etc.); matching
// arms recover sub-terms by injectivity (`app_inj_fst/snd`, `lam_inj_*`,
// `pi_inj_*`) and transport the sub-derivations with `Eq.subst`.
//
// The inversion is delivered in continuation-passing (motive-eliminator)
// form — `forall (C : KExpr -> Type), <derivation> -> <case handlers> -> C t`
// — to avoid a `Sigma`/`Or` carrier (neither is in the current spec
// fragment). Each handler concludes `C` of the *concrete* reduct it
// describes, so the matching arm transports `C (app f a)` / `C (lam ...)` to
// `C e'` for the arm's reduct via `Eq.subst` on the recovered source
// equation. No new axiom; `Eq.subst`/`Eq.symm`/`Eq.refl` are the
// foundational `Eq` eliminators, so axiom_deps stays empty.
//
// IMPORTANT defeq note: `KExpr.forall_ d b` is the reducible alias of
// `KExpr.pi d b`, so the `forall_` arm of a `pi`-shaped inversion is a genuine
// matching case (defeq to `pi`). POST LET-PROMOTION `KExpr.let_ t v b` is a
// GENUINE constructor (NOT the old `KExpr.app (KExpr.lam t b) v` alias): the
// `let_` (zeta) and `let_cong` arms of the app/lam/pi-shaped inversions are
// impossible and discharged by the let_ne_app/let_ne_lam/let_ne_pi
// no-confusion lemmas; let_-headed sources get their own inversion
// (`par_reduces_bd_let_inv`) whose matching arms use let_inj_fst/snd/thd.

/// Closed proof term for `par_reduces_bd_app_inv` (Wave 136, Route B).
///
/// From `par_reduces_bd (app f a) t`, dispatch to one of two continuations:
/// the congruence/refl case (`t = app f' a'` with `f => f'`, `a => a'`) or the
/// contraction case (`f = lam A body`, `t = instantiate body' arg'`). The refl
/// and `app` constructors fold into the congruence handler; the `beta`
/// constructor folds into the contraction handler; the `lam`/`pi`/`forall_`
/// arms are impossible and discharged by `lam_ne_app`/`pi_ne_app`, and — post
/// let-promotion — so are the let_-headed `let_` (zeta) and `let_cong` arms
/// (discharged by `let_ne_app`).
fn par_reduces_bd_app_inv_proof() -> String {
    // Motive: carry a source equation so each arm learns its source shape, and
    // conclude C on the arm's reduct e'. The handlers kapp/kbeta are fixed
    // outer parameters in scope.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
        "Eq KExpr e (KExpr.app f a) -> C e')"
    );

    // refl arm: reduct e; goal C e. Build C (app f a) from kapp with refl
    // sub-derivations, then transport along (symm eq) to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.app f a)) => ",
        "Eq.substType KExpr C (KExpr.app f a) e ",
        "(Eq.symm KExpr e (KExpr.app f a) eq) ",
        "(kapp f a (par_reduces_bd.refl f) (par_reduces_bd.refl a)))"
    );

    // beta arm: source app (lam A body) arg, reduct instantiate body' arg'.
    // From eq recover f = lam A body (symm of app_inj_fst) and a = arg
    // (app_inj_snd, used to transport harg to par_reduces_bd a arg').
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(hA : par_reduces_bd A A') (hbody : par_reduces_bd body body') ",
        "(harg : par_reduces_bd arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.app f a) -> C A') ",
        "(_ihbody : Eq KExpr body (KExpr.app f a) -> C body') ",
        "(_iharg : Eq KExpr arg (KExpr.app f a) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A body) arg) (KExpr.app f a)) => ",
        "kbeta A A' body body' arg' ",
        "(Eq.symm KExpr (KExpr.lam A body) f ",
        "(app_inj_fst (KExpr.lam A body) arg f a eq)) ",
        "hA hbody ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x arg') arg a ",
        "(app_inj_snd (KExpr.lam A body) arg f a eq) harg))"
    );

    // app arm: source app g b, reduct app g' b'. Transport hg/hb to f/a.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(hg : par_reduces_bd g g') (hb : par_reduces_bd b b') ",
        "(_ihg : Eq KExpr g (KExpr.app f a) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.app f a) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.app f a)) => ",
        "kapp g' b' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x g') g f ",
        "(app_inj_fst g b f a eq) hg) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b') b a ",
        "(app_inj_snd g b f a eq) hb))"
    );

    // lam arm: impossible — lam ty body /= app f a.
    let lam_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_bd ty ty') (_hbody : par_reduces_bd body body') ",
        "(_ihty : Eq KExpr ty (KExpr.app f a) -> C ty') ",
        "(_ihbody : Eq KExpr body (KExpr.app f a) -> C body') ",
        "(eq : Eq KExpr (KExpr.lam ty body) (KExpr.app f a)) => ",
        "lam_ne_app ty body f a (C (KExpr.lam ty' body')) eq)"
    );

    // pi arm: impossible — pi dom body /= app f a.
    let pi_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_bd dom dom') (_hbody : par_reduces_bd body body') ",
        "(_ihd : Eq KExpr dom (KExpr.app f a) -> C dom') ",
        "(_ihbody : Eq KExpr body (KExpr.app f a) -> C body') ",
        "(eq : Eq KExpr (KExpr.pi dom body) (KExpr.app f a)) => ",
        "pi_ne_app dom body f a (C (KExpr.pi dom' body')) eq)"
    );

    // forall_ arm: impossible — forall_ dom body = pi dom body (alias) /= app.
    let forall_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_bd dom dom') (_hbody : par_reduces_bd body body') ",
        "(_ihd : Eq KExpr dom (KExpr.app f a) -> C dom') ",
        "(_ihbody : Eq KExpr body (KExpr.app f a) -> C body') ",
        "(eq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app f a)) => ",
        "pi_ne_app dom body f a (C (KExpr.forall_ dom' body')) eq)"
    );

    // let_ (zeta) arm: impossible post let-promotion — the source
    // KExpr.let_ ty val body is let_-headed, never app-headed (let_ne_app).
    let let_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
        "(body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
        "(_hbody : par_reduces_bd body body') ",
        "(_ihty : Eq KExpr ty (KExpr.app f a) -> C ty') ",
        "(_ihval : Eq KExpr val (KExpr.app f a) -> C val') ",
        "(_ihbody : Eq KExpr body (KExpr.app f a) -> C body') ",
        "(eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app f a)) => ",
        "let_ne_app ty val body f a (C (instantiate body' val')) eq)"
    );

    // let_cong arm: impossible for the same reason (let_ne_app).
    let let_cong_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
        "(body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
        "(_hbody : par_reduces_bd body body') ",
        "(_ihty : Eq KExpr ty (KExpr.app f a) -> C ty') ",
        "(_ihval : Eq KExpr val (KExpr.app f a) -> C val') ",
        "(_ihbody : Eq KExpr body (KExpr.app f a) -> C body') ",
        "(eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app f a)) => ",
        "let_ne_app ty val body f a (C (KExpr.let_ ty' val' body')) eq)"
    );

    // proj arm: impossible — proj s i sub /= app f a (proj_ne_app).
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_bd sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.app f a) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.app f a)) => ",
        "proj_ne_app s i sub f a (C (KExpr.proj s i sub')) eq)"
    );

    format!(
        concat!(
            "fun (f : KExpr) (a : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_bd (KExpr.app f a) t) ",
            "(kapp : forall (f' : KExpr) (a' : KExpr), ",
            "par_reduces_bd f f' -> par_reduces_bd a a' -> C (KExpr.app f' a')) ",
            "(kbeta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg' : KExpr), Eq KExpr f (KExpr.lam A body) -> ",
            "par_reduces_bd A A' -> par_reduces_bd body body' -> par_reduces_bd a arg' -> ",
            "C (instantiate body' arg')) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.app f a) t h (Eq.refl KExpr (KExpr.app f a))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_bd_lam_inv` (Wave 136, Route B).
///
/// From `par_reduces_bd (lam ty body) t`, recover `t = lam ty' body'` with
/// `ty => ty'` and `body => body'` (refl folds in with reflexive sub-
/// derivations; `lam` is the genuine congruence arm). Every other constructor
/// produces an `app`/`pi`/`let_`-headed source, all impossible against `lam`,
/// and is discharged by `app_ne_lam` (beta/app), `pi_ne_lam` (pi/forall_) or
/// `let_ne_lam` (let_/let_cong, post let-promotion).
fn par_reduces_bd_lam_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
        "Eq KExpr e (KExpr.lam ty body) -> C e')"
    );

    // refl: reduct e; build C (lam ty body), transport to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) => ",
        "Eq.substType KExpr C (KExpr.lam ty body) e ",
        "(Eq.symm KExpr e (KExpr.lam ty body) eq) ",
        "(klam ty body (par_reduces_bd.refl ty) (par_reduces_bd.refl body)))"
    );

    // beta: source app (lam A b0) arg — app /= lam.
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_bd A A') (_hb0 : par_reduces_bd b0 b0') ",
        "(_harg : par_reduces_bd arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.lam ty body) -> C A') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) => ",
        "app_ne_lam (KExpr.lam A b0) arg ty body (C (instantiate b0' arg')) eq)"
    );

    // app: source app g b — app /= lam.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_bd g g') (_hb : par_reduces_bd b b') ",
        "(_ihg : Eq KExpr g (KExpr.lam ty body) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.lam ty body) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) => ",
        "app_ne_lam g b ty body (C (KExpr.app g' b')) eq)"
    );

    // lam: source lam t0 b0 — the matching congruence arm.
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(ht : par_reduces_bd t0 t0') (hb : par_reduces_bd b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) => ",
        "klam t0' b0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x t0') t0 ty ",
        "(lam_inj_fst t0 b0 ty body eq) ht) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
        "(lam_inj_snd t0 b0 ty body eq) hb))"
    );

    // pi: source pi dom b0 — pi /= lam.
    let pi_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_bd dom dom') (_hb0 : par_reduces_bd b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.pi dom' b0')) eq)"
    );

    // forall_: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_bd dom dom') (_hb0 : par_reduces_bd b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.forall_ dom' b0')) eq)"
    );

    // let_ (zeta): source let_ t0 v b0 is let_-headed (genuine constructor,
    // let-promotion) — let_ /= lam via let_ne_lam.
    let let_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
        "(b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
        "(_hb0 : par_reduces_bd b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
        "let_ne_lam t0 v b0 ty body (C (instantiate b0' v')) eq)"
    );

    // let_cong: same let_-headed source — let_ne_lam.
    let let_cong_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
        "(b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
        "(_hb0 : par_reduces_bd b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
        "let_ne_lam t0 v b0 ty body (C (KExpr.let_ t0' v' b0')) eq)"
    );

    // proj: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_bd sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) => ",
        "proj_ne_lam s i sub ty body (C (KExpr.proj s i sub')) eq)"
    );

    format!(
        concat!(
            "fun (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_bd (KExpr.lam ty body) t) ",
            "(klam : forall (ty' : KExpr) (body' : KExpr), ",
            "par_reduces_bd ty ty' -> par_reduces_bd body body' -> ",
            "C (KExpr.lam ty' body')) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for the pi-headed inversions `par_reduces_bd_pi_inv` and
/// `par_reduces_bd_forall_inv` (Wave 136, Route B), parametric in the source
/// binder head `head` (`KExpr.pi` or `KExpr.forall_`) and the reduct head
/// `red_head` used by the continuation `kpi`.
///
/// Because `KExpr.forall_ d b` is the reducible alias of `KExpr.pi d b`, BOTH
/// the `pi` and `forall_` constructor arms are genuine matching cases for a
/// pi-headed source (their sources are definitionally equal). They recover
/// sub-terms via `pi_inj_fst/snd` (the kernel unfolds `forall_` to `pi` so the
/// equation feeds `pi_inj_*` directly) and reassemble via the continuation.
/// `refl` folds in with reflexive sub-derivations; `beta`/`app` are
/// `app`-headed and discharged by `app_ne_pi`; `lam` by `lam_ne_pi`; the
/// let_-headed `let_`/`let_cong` arms by `let_ne_pi` (let-promotion).
fn par_reduces_bd_pi_like_inv_proof(head: &str, red_head: &str) -> String {
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
            "Eq KExpr e ({head} dom body) -> C e')"
        ),
        head = head,
    );

    // refl: reduct e; build C (red_head dom body), transport to C e. Note
    // red_head dom body is defeq to head dom body, so the transport target
    // matches the motive equation's RHS.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e ({head} dom body)) => ",
            "Eq.substType KExpr C ({head} dom body) e ",
            "(Eq.symm KExpr e ({head} dom body) eq) ",
            "(kpi dom body (par_reduces_bd.refl dom) (par_reduces_bd.refl body)))"
        ),
        head = head,
    );

    // beta: source app (lam A b0) arg — app /= pi.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_bd A A') (_hb0 : par_reduces_bd b0 b0') ",
            "(_harg : par_reduces_bd arg arg') ",
            "(_ihA : Eq KExpr A ({head} dom body) -> C A') ",
            "(_ihb0 : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(_iharg : Eq KExpr arg ({head} dom body) -> C arg') ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) ({head} dom body)) => ",
            "app_ne_pi (KExpr.lam A b0) arg dom body (C (instantiate b0' arg')) eq)"
        ),
        head = head,
    );

    // app: source app g b — app /= pi.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_bd g g') (_hb : par_reduces_bd b b') ",
            "(_ihg : Eq KExpr g ({head} dom body) -> C g') ",
            "(_ihb : Eq KExpr b ({head} dom body) -> C b') ",
            "(eq : Eq KExpr (KExpr.app g b) ({head} dom body)) => ",
            "app_ne_pi g b dom body (C (KExpr.app g' b')) eq)"
        ),
        head = head,
    );

    // lam: source lam t0 b0 — lam /= pi.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_bd t0 t0') (_hb : par_reduces_bd b0 b0') ",
            "(_iht : Eq KExpr t0 ({head} dom body) -> C t0') ",
            "(_ihb : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) ({head} dom body)) => ",
            "lam_ne_pi t0 b0 dom body (C (KExpr.lam t0' b0')) eq)"
        ),
        head = head,
    );

    // pi: source pi d0 b0 — matching arm (pi). The eq is
    // Eq (pi d0 b0) (head dom body); when head = forall_ the kernel unfolds it
    // to pi, so pi_inj_fst/snd apply directly.
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_bd d0 d0') (hb : par_reduces_bd b0 b0') ",
            "(_ihd : Eq KExpr d0 ({head} dom body) -> C d0') ",
            "(_ihb : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.pi d0 b0) ({head} dom body)) => ",
            "kpi d0' b0' ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        head = head,
    );

    // forall_: source forall_ d0 b0 = pi d0 b0 (alias) — also a matching arm.
    // The eq Eq (forall_ d0 b0) (head dom body) is defeq to
    // Eq (pi d0 b0) (pi dom body), so pi_inj_fst/snd apply.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_bd d0 d0') (hb : par_reduces_bd b0 b0') ",
            "(_ihd : Eq KExpr d0 ({head} dom body) -> C d0') ",
            "(_ihb : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.forall_ d0 b0) ({head} dom body)) => ",
            "kpi d0' b0' ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        head = head,
    );

    // let_ (zeta): source let_ t0 v b0 is let_-headed (genuine constructor,
    // let-promotion) — let_ /= pi via let_ne_pi (the head-side forall_ alias
    // still unfolds to pi, so let_ne_pi covers both heads).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
            "(_hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 ({head} dom body) -> C t0') ",
            "(_ihv : Eq KExpr v ({head} dom body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) ({head} dom body)) => ",
            "let_ne_pi t0 v b0 dom body (C (instantiate b0' v')) eq)"
        ),
        head = head,
    );

    // let_cong: same let_-headed source — let_ne_pi.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
            "(_hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 ({head} dom body) -> C t0') ",
            "(_ihv : Eq KExpr v ({head} dom body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 ({head} dom body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) ({head} dom body)) => ",
            "let_ne_pi t0 v b0 dom body (C (KExpr.let_ t0' v' b0')) eq)"
        ),
        head = head,
    );

    // proj: source proj s i sub is proj-headed — proj /= pi via proj_ne_pi
    // (the head-side forall_ alias still unfolds to pi, covering both heads).
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_bd sub sub') ",
            "(_ihsub : Eq KExpr sub ({head} dom body) -> C sub') ",
            "(eq : Eq KExpr (KExpr.proj s i sub) ({head} dom body)) => ",
            "proj_ne_pi s i sub dom body (C (KExpr.proj s i sub')) eq)"
        ),
        head = head,
    );

    format!(
        concat!(
            "fun (dom : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_bd ({head} dom body) t) ",
            "(kpi : forall (dom' : KExpr) (body' : KExpr), ",
            "par_reduces_bd dom dom' -> par_reduces_bd body body' -> ",
            "C ({red_head} dom' body')) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "({head} dom body) t h (Eq.refl KExpr ({head} dom body))"
        ),
        head = head,
        red_head = red_head,
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_bd_let_inv` (let-promotion, Wave 136
/// shape).
///
/// From `par_reduces_bd (KExpr.let_ ty val body) t`, dispatch to one of two
/// continuations: the congruence case (`t = let_ ty' val' body'` — refl and
/// `let_cong` fold in) or the ZETA case (`t = instantiate body' val'` — the
/// `let_` constructor), each carrying `ty => ty'`, `val => val'`,
/// `body => body'`. The `beta`/`app` arms are app-headed (app_ne_let), `lam`
/// is lam-headed (lam_ne_let), `pi`/`forall_` are pi-headed (pi_ne_let) — all
/// impossible against the genuinely-let_-headed source. Matching arms recover
/// sub-terms via `let_inj_fst/snd/thd` (ty/val/body projections) and
/// transport the sub-derivations with Eq.subst.
fn par_reduces_bd_let_inv_proof() -> String {
    // Motive: carry a source equation so each arm learns its source shape,
    // concluding C on the arm's reduct e'. The handlers kcong/kzeta are fixed
    // outer parameters in scope.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
        "Eq KExpr e (KExpr.let_ ty val body) -> C e')"
    );

    // refl arm: reduct e; build C (let_ ty val body) from kcong with refl
    // sub-derivations, then transport along (symm eq) to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.let_ ty val body)) => ",
        "Eq.substType KExpr C (KExpr.let_ ty val body) e ",
        "(Eq.symm KExpr e (KExpr.let_ ty val body) eq) ",
        "(kcong ty val body (par_reduces_bd.refl ty) (par_reduces_bd.refl val) ",
        "(par_reduces_bd.refl body)))"
    );

    // beta arm: source app (lam A b0) arg — app-headed, never let_-headed.
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_bd A A') (_hb0 : par_reduces_bd b0 b0') ",
        "(_harg : par_reduces_bd arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.let_ ty val body) -> C A') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(_iharg : Eq KExpr arg (KExpr.let_ ty val body) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.let_ ty val body)) => ",
        "app_ne_let (KExpr.lam A b0) arg ty val body (C (instantiate b0' arg')) eq)"
    );

    // app arm: source app g b — app-headed.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_bd g g') (_hb : par_reduces_bd b b') ",
        "(_ihg : Eq KExpr g (KExpr.let_ ty val body) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.let_ ty val body) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.let_ ty val body)) => ",
        "app_ne_let g b ty val body (C (KExpr.app g' b')) eq)"
    );

    // lam arm: lam-headed.
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_ht : par_reduces_bd t0 t0') (_hb : par_reduces_bd b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.let_ ty val body) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.let_ ty val body)) => ",
        "lam_ne_let t0 b0 ty val body (C (KExpr.lam t0' b0')) eq)"
    );

    // pi arm: pi-headed.
    let pi_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_bd d0 d0') (_hb : par_reduces_bd b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.let_ ty val body) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.let_ ty val body)) => ",
        "pi_ne_let d0 b0 ty val body (C (KExpr.pi d0' b0')) eq)"
    );

    // forall_ arm: forall_ unfolds to pi — pi-headed.
    let forall_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_bd d0 d0') (_hb : par_reduces_bd b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.let_ ty val body) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.let_ ty val body)) => ",
        "pi_ne_let d0 b0 ty val body (C (KExpr.forall_ d0' b0')) eq)"
    );

    // Shared sub-derivation transports for the two matching let_-headed arms:
    // from eq : Eq (let_ t0 v0 b0) (let_ ty val body) recover the component
    // equations and transport each sub-derivation onto the outer components.
    let transported = concat!(
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x t0') t0 ty ",
        "(let_inj_fst t0 v0 b0 ty val body eq) ht0) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x v0') v0 val ",
        "(let_inj_snd t0 v0 b0 ty val body eq) hv0) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
        "(let_inj_thd t0 v0 b0 ty val body eq) hb0)"
    );

    // let_ (zeta) arm: the genuine contraction match — reduct
    // instantiate b0' v0'; conclude via kzeta on the transported sub-derivations.
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v0 : KExpr) (v0' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(ht0 : par_reduces_bd t0 t0') (hv0 : par_reduces_bd v0 v0') ",
            "(hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.let_ ty val body) -> C t0') ",
            "(_ihv0 : Eq KExpr v0 (KExpr.let_ ty val body) -> C v0') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v0 b0) (KExpr.let_ ty val body)) => ",
            "kzeta t0' v0' b0' ",
            "{transported})"
        ),
        transported = transported,
    );

    // let_cong arm: the genuine congruence match — reduct let_ t0' v0' b0';
    // conclude via kcong on the transported sub-derivations.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v0 : KExpr) (v0' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(ht0 : par_reduces_bd t0 t0') (hv0 : par_reduces_bd v0 v0') ",
            "(hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.let_ ty val body) -> C t0') ",
            "(_ihv0 : Eq KExpr v0 (KExpr.let_ ty val body) -> C v0') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.let_ ty val body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v0 b0) (KExpr.let_ ty val body)) => ",
            "kcong t0' v0' b0' ",
            "{transported})"
        ),
        transported = transported,
    );

    // proj arm: source proj s i sub is proj-headed — proj /= let_ via proj_ne_let.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_bd sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.let_ ty val body) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.let_ ty val body)) => ",
        "proj_ne_let s i sub ty val body (C (KExpr.proj s i sub')) eq)"
    );

    format!(
        concat!(
            "fun (ty : KExpr) (val : KExpr) (body : KExpr) (t : KExpr) ",
            "(C : KExpr -> Type) ",
            "(h : par_reduces_bd (KExpr.let_ ty val body) t) ",
            "(kcong : forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
            "par_reduces_bd ty ty' -> par_reduces_bd val val' -> ",
            "par_reduces_bd body body' -> C (KExpr.let_ ty' val' body')) ",
            "(kzeta : forall (ty' : KExpr) (val' : KExpr) (body' : KExpr), ",
            "par_reduces_bd ty ty' -> par_reduces_bd val val' -> ",
            "par_reduces_bd body body' -> C (instantiate body' val')) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.let_ ty val body) t h (Eq.refl KExpr (KExpr.let_ ty val body))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_bd_proj_inv` (proj/lit fragment rung).
///
/// From `par_reduces_bd (KExpr.proj s i sub) t`, dispatch to the single `kproj`
/// continuation. `proj` is a pure single-position congruence, so only `refl`
/// (`t = proj s i sub`) and the `proj` congruence (`t = proj s i sub'` with
/// `sub => sub'`) are non-vacuous; every other constructor has an
/// app/lam/pi/let_-headed source, discharged by `app_ne_proj` / `lam_ne_proj` /
/// `pi_ne_proj` / `let_ne_proj`. The matching `proj` arm recovers the three
/// components via `proj_inj_name`/`proj_inj_idx`/`proj_inj_sub` and transports
/// the sub-derivation and the goal with `Eq.subst`.
fn par_reduces_bd_proj_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
        "Eq KExpr e (KExpr.proj s i sub) -> C e')"
    );

    // refl arm: reduct e; build C (proj s i sub) from kproj with a reflexive
    // scrutinee derivation, then transport along (symm eq) to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.proj s i sub)) => ",
        "Eq.substType KExpr C (KExpr.proj s i sub) e ",
        "(Eq.symm KExpr e (KExpr.proj s i sub) eq) ",
        "(kproj sub (par_reduces_bd.refl sub)))"
    );

    // beta arm: source app (lam A body) arg — app-headed, never proj-headed.
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_bd A A') (_hbody : par_reduces_bd body body') ",
        "(_harg : par_reduces_bd arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.proj s i sub) -> C A') ",
        "(_ihbody : Eq KExpr body (KExpr.proj s i sub) -> C body') ",
        "(_iharg : Eq KExpr arg (KExpr.proj s i sub) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A body) arg) (KExpr.proj s i sub)) => ",
        "app_ne_proj (KExpr.lam A body) arg s i sub (C (instantiate body' arg')) eq)"
    );

    // app arm: source app g b — app-headed.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_bd g g') (_hb : par_reduces_bd b b') ",
        "(_ihg : Eq KExpr g (KExpr.proj s i sub) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.proj s i sub) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.proj s i sub)) => ",
        "app_ne_proj g b s i sub (C (KExpr.app g' b')) eq)"
    );

    // lam arm: lam-headed.
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_ht : par_reduces_bd t0 t0') (_hb : par_reduces_bd b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.proj s i sub) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.proj s i sub)) => ",
        "lam_ne_proj t0 b0 s i sub (C (KExpr.lam t0' b0')) eq)"
    );

    // pi arm: pi-headed.
    let pi_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_bd d0 d0') (_hb : par_reduces_bd b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.proj s i sub) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.proj s i sub)) => ",
        "pi_ne_proj d0 b0 s i sub (C (KExpr.pi d0' b0')) eq)"
    );

    // forall_ arm: forall_ unfolds to pi — pi-headed (pi_ne_proj covers it).
    let forall_arm = concat!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_bd d0 d0') (_hb : par_reduces_bd b0 b0') ",
        "(_ihd : Eq KExpr d0 (KExpr.proj s i sub) -> C d0') ",
        "(_ihb : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.proj s i sub)) => ",
        "pi_ne_proj d0 b0 s i sub (C (KExpr.forall_ d0' b0')) eq)"
    );

    // let_ (zeta) arm: let_-headed.
    let let_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
        "(b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
        "(_hb0 : par_reduces_bd b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.proj s i sub) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.proj s i sub) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.proj s i sub)) => ",
        "let_ne_proj t0 v b0 s i sub (C (instantiate b0' v')) eq)"
    );

    // let_cong arm: same let_-headed source — let_ne_proj.
    let let_cong_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
        "(b0 : KExpr) (b0' : KExpr) ",
        "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
        "(_hb0 : par_reduces_bd b0 b0') ",
        "(_iht0 : Eq KExpr t0 (KExpr.proj s i sub) -> C t0') ",
        "(_ihv : Eq KExpr v (KExpr.proj s i sub) -> C v') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.proj s i sub) -> C b0') ",
        "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.proj s i sub)) => ",
        "let_ne_proj t0 v b0 s i sub (C (KExpr.let_ t0' v' b0')) eq)"
    );

    // proj arm: the genuine match. Source proj s0 i0 sub0, reduct proj s0 i0
    // sub0'. Recover s0=s, i0=i, sub0=sub via proj injectivity, transport the
    // scrutinee derivation onto sub, apply kproj, then transport the resulting
    // C (proj s i sub0') back onto C (proj s0 i0 sub0') along name/idx.
    let proj_arm = concat!(
        "(fun (s0 : Name) (i0 : Nat) (sub0 : KExpr) (sub0' : KExpr) ",
        "(hsub0 : par_reduces_bd sub0 sub0') ",
        "(_ihsub0 : Eq KExpr sub0 (KExpr.proj s i sub) -> C sub0') ",
        "(eq : Eq KExpr (KExpr.proj s0 i0 sub0) (KExpr.proj s i sub)) => ",
        "Eq.substType Nat (fun (x : Nat) => C (KExpr.proj s0 x sub0')) i i0 ",
        "(Eq.symm Nat i0 i (proj_inj_idx s0 i0 sub0 s i sub eq)) ",
        "(Eq.substType Name (fun (x : Name) => C (KExpr.proj x i sub0')) s s0 ",
        "(Eq.symm Name s0 s (proj_inj_name s0 i0 sub0 s i sub eq)) ",
        "(kproj sub0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x sub0') sub0 sub ",
        "(proj_inj_sub s0 i0 sub0 s i sub eq) hsub0))))"
    );

    format!(
        concat!(
            "fun (s : Name) (i : Nat) (sub : KExpr) (t : KExpr) ",
            "(C : KExpr -> Type) ",
            "(h : par_reduces_bd (KExpr.proj s i sub) t) ",
            "(kproj : forall (sub' : KExpr), ",
            "par_reduces_bd sub sub' -> C (KExpr.proj s i sub')) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.proj s i sub) t h (Eq.refl KExpr (KExpr.proj s i sub))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_strips_bd` (Wave 138, Route B) — the iota-free
/// single-step diamond.
///
/// Outer `par_reduces_bd.rec` on the FIRST derivation `h1 : par_reduces_bd e e1`
/// with the motive universalizing the second target/derivation:
///
/// ```text
/// M e e1 _ := forall (e2 : KExpr), par_reduces_bd e e2 -> par_strips_witness_bd e1 e2
/// ```
///
/// Each non-refl outer arm inverts the second derivation `h2` (Wave 136 shape
/// recovery), joining per-sub-derivation via the recursor IHs and reassembling.
/// The refl arm is `par_strips_bd_refl_left`; the (app, app) and binder
/// diagonals use `par_strips_bd_app`/`_lam`/`_pi`/`_forall`; the (beta|let_,
/// beta|let_) cases use `par_subst_bd` on the body/arg sub-meets; the (app,
/// beta) / (beta, app) cross arms use `par_strips_bd_app_beta` (the (beta, app)
/// direction via `par_strips_witness_bd_symm`), with the redex side's lambda
/// shape recovered by `par_reduces_bd_lam_inv_eq`.
///
/// Post let-promotion the let_ outer arms are let_-HEADED (a genuine
/// constructor, not an app(lam) alias): the let_ (zeta) and let_cong outer
/// arms invert their second derivation with `par_reduces_bd_let_inv`. The
/// (zeta,zeta) overlap meets at `instantiate (join body) (join val)` via
/// `par_subst_bd` on both sides (the beta-beta mechanism); the
/// (zeta,let_cong)/(let_cong,zeta) overlaps fire the zeta on the congruence
/// side (`par_reduces_bd.let_` on the joined val/body, refl on the
/// annotation) against `par_subst_bd` on the contracted side; the
/// (let_cong,let_cong) diagonal recurses per component via
/// `par_strips_bd_let`.
fn par_strips_bd_proof() -> String {
    // Outer motive (over the first derivation).
    let motive = concat!(
        "(fun (e : KExpr) (e1 : KExpr) (_h : par_reduces_bd e e1) => ",
        "forall (e2 : KExpr), par_reduces_bd e e2 -> par_strips_witness_bd e1 e2)"
    );
    // IH shape for a sub-derivation SUB ⇒ SUB'.
    let ih = "forall (e2 : KExpr), par_reduces_bd SUB e2 -> par_strips_witness_bd SUB' e2";

    // refl arm: e1 = e, meet at e2 (par_strips_bd_refl_left).
    let refl_arm = concat!(
        "(fun (e : KExpr) (e2 : KExpr) (h2 : par_reduces_bd e e2) => ",
        "par_strips_bd_refl_left e e2 h2)"
    );

    // Shared (beta, beta) joiner, parametric in the four reduct names. Given
    // wb : par_strips_witness_bd LB RB (body sub-meet) and
    // wa : par_strips_witness_bd LA RA (arg sub-meet), project both and meet the
    // contracted terms at instantiate b3 a3 via par_subst_bd on each side:
    //   par_strips_witness_bd (instantiate LB LA) (instantiate RB RA).
    // wb_term / wa_term are the witness terms supplied for the two sub-meets.
    let mk_join =
        |lb: &str, rb: &str, la: &str, ra: &str, wb_term: &str, wa_term: &str| -> String {
            format!(
                concat!(
                    "(@par_strips_witness_bd.rec {lb} {rb} ",
                    "(fun (_wb : par_strips_witness_bd {lb} {rb}) => ",
                    "par_strips_witness_bd (instantiate {lb} {la}) (instantiate {rb} {ra})) ",
                    "(fun (b3 : KExpr) ",
                    "(pb1 : par_reduces_bd {lb} b3) (pb2 : par_reduces_bd {rb} b3) => ",
                    "@par_strips_witness_bd.rec {la} {ra} ",
                    "(fun (_wa : par_strips_witness_bd {la} {ra}) => ",
                    "par_strips_witness_bd (instantiate {lb} {la}) (instantiate {rb} {ra})) ",
                    "(fun (a3 : KExpr) ",
                    "(pa1 : par_reduces_bd {la} a3) (pa2 : par_reduces_bd {ra} a3) => ",
                    "par_strips_witness_bd.intro ",
                    "(instantiate {lb} {la}) (instantiate {rb} {ra}) (instantiate b3 a3) ",
                    "(par_subst_bd {lb} b3 {la} a3 pb1 pa1) ",
                    "(par_subst_bd {rb} b3 {ra} a3 pb2 pa2)) ",
                    "{wa_term}) ",
                    "{wb_term})"
                ),
                lb = lb,
                rb = rb,
                la = la,
                ra = ra,
                wb_term = wb_term,
                wa_term = wa_term,
            )
        };

    // ---- app outer arm ----
    // f f' a0 a0', hf ha, ihf iha. Source app f a0, reduct app f' a0'.
    // Invert h2 : par_reduces_bd (app f a0) e2 via par_reduces_bd_app_inv.
    let app_kapp = concat!(
        "(fun (f2 : KExpr) (a2 : KExpr) ",
        "(hf2 : par_reduces_bd f f2) (ha2 : par_reduces_bd a0 a2) => ",
        "par_strips_bd_app f' f2 a0' a2 (ihf f2 hf2) (iha a2 ha2))"
    );
    // (app, beta) cross: eqf : f = lam A bdy; recover f' = lam Af bodyf, feed
    // body meet (lam_meet on the lam-lam wf') and arg meet (wa) to app_beta,
    // then transport app (lam Af bodyf) a0' back to app f' a0'.
    let app_kbeta_inner = concat!(
        // wf' : par_strips_witness_bd (lam Af bodyf) (lam A' bdy')
        "(par_strips_bd_app_beta Af bodyf a0' bdy' arg' ",
        "(par_strips_witness_bd_lam_meet Af A' bodyf bdy' ",
        "(Eq.substType KExpr ",
        "(fun (x : KExpr) => par_strips_witness_bd x (KExpr.lam A' bdy')) f' (KExpr.lam Af bodyf) eqfp wf) ",
        ") ",
        "wa)"
    );
    let app_kbeta = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (bdy : KExpr) (bdy' : KExpr) (arg' : KExpr) ",
            "(eqf : Eq KExpr f (KExpr.lam A bdy)) ",
            "(hA : par_reduces_bd A A') (hbody : par_reduces_bd bdy bdy') ",
            "(harg : par_reduces_bd a0 arg') => ",
            // hf_lam : par_reduces_bd (lam A bdy) f'
            "(fun (hf_lam : par_reduces_bd (KExpr.lam A bdy) f') ",
            "(wf : par_strips_witness_bd f' (KExpr.lam A' bdy')) ",
            "(wa : par_strips_witness_bd a0' arg') => ",
            "par_reduces_bd_lam_inv_eq A bdy f' ",
            "(par_strips_witness_bd (KExpr.app f' a0') (instantiate bdy' arg')) ",
            "hf_lam ",
            "(fun (Af : KExpr) (bodyf : KExpr) ",
            "(eqfp : Eq KExpr f' (KExpr.lam Af bodyf)) ",
            "(hAf : par_reduces_bd A Af) (hbf : par_reduces_bd bdy bodyf) => ",
            // result : par_strips_witness_bd (app (lam Af bodyf) a0') (instantiate bdy' arg')
            // transport app (lam Af bodyf) a0' -> app f' a0' via symm eqfp.
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_strips_witness_bd (KExpr.app x a0') (instantiate bdy' arg')) ",
            "(KExpr.lam Af bodyf) f' (Eq.symm KExpr f' (KExpr.lam Af bodyf) eqfp) ",
            "{app_kbeta_inner})) ",
            // supply hf_lam, wf, wa:
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x f') f (KExpr.lam A bdy) eqf hf) ",
            "(ihf (KExpr.lam A' bdy') ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x (KExpr.lam A' bdy')) ",
            "(KExpr.lam A bdy) f (Eq.symm KExpr f (KExpr.lam A bdy) eqf) ",
            "(par_reduces_bd.lam A A' bdy bdy' hA hbody))) ",
            "(iha arg' harg))"
        ),
        app_kbeta_inner = app_kbeta_inner,
    );
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(hf : par_reduces_bd f f') (ha : par_reduces_bd a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(e2 : KExpr) (h2 : par_reduces_bd (KExpr.app f a0) e2) => ",
            "par_reduces_bd_app_inv f a0 e2 ",
            "(fun (x : KExpr) => par_strips_witness_bd (KExpr.app f' a0') x) ",
            "h2 {app_kapp} {app_kbeta})"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
        app_kapp = app_kapp,
        app_kbeta = app_kbeta,
    );

    // ---- binder outer arms (lam / pi / forall_) ----
    // ty ty' bdy bdy', hty hbody, ihty ihbody. Source HEAD ty bdy, reduct
    // HEAD ty' bdy'. Invert h2 via INV; single klam case → DIAG combinator.
    let binder_arm = |head: &str, inv: &str, diag: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (bdy : KExpr) (bdy' : KExpr) ",
                "(hty : par_reduces_bd ty ty') (hbody : par_reduces_bd bdy bdy') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(e2 : KExpr) (h2 : par_reduces_bd ({head} ty bdy) e2) => ",
                "{inv} ty bdy e2 ",
                "(fun (x : KExpr) => par_strips_witness_bd ({head} ty' bdy') x) ",
                "h2 ",
                "(fun (ty2 : KExpr) (bdy2 : KExpr) ",
                "(hty2 : par_reduces_bd ty ty2) (hbody2 : par_reduces_bd bdy bdy2) => ",
                "{diag} ty' ty2 bdy' bdy2 (ihty ty2 hty2) (ihbody bdy2 hbody2)))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "bdy'").replace("SUB", "bdy"),
            head = head,
            inv = inv,
            diag = diag,
        )
    };
    let lam_arm = binder_arm("KExpr.lam", "par_reduces_bd_lam_inv", "par_strips_bd_lam");
    let pi_arm = binder_arm("KExpr.pi", "par_reduces_bd_pi_inv", "par_strips_bd_pi");
    let forall_arm = binder_arm(
        "KExpr.forall_",
        "par_reduces_bd_forall_inv",
        "par_strips_bd_forall",
    );

    // ---- beta outer arm (app-headed redex logic) ----
    // The beta arm binds A A' bdy bdy' arg arg' with hA hbody harg, IHs
    // ihA ihbody iharg — only the body/arg sub-derivations and their IHs are
    // used (the binder-type derivation hA plays no role in the reduct
    // instantiate bdy' arg'). Source app (lam A bdy) arg, reduct
    // instantiate bdy' arg'. h2 inverted via par_reduces_bd_app_inv at
    // f := lam A bdy, a := arg.
    //   kbeta inner (beta, beta): meet via beta_beta_join (ibody=ibdy', iarg).
    //   kapp inner  (beta, app):  symm of par_strips_bd_app_beta on the redex
    //     side (g' recovered to a lambda by par_reduces_bd_lam_inv_eq), with
    //     body meet ihbody and arg meet iharg.
    //
    // POST LET-PROMOTION `beta_like_body` serves ONLY the beta arm (a let_ is
    // let_-headed, never this app-headed redex shape; the let_ arms below use
    // par_reduces_bd_let_inv instead). The parametric shape is kept verbatim.
    let beta_like_body = |arg_src: &str, arg_red: &str, iharg: &str, ihbody: &str| -> String {
        let goal_ty = format!(
            "(fun (x : KExpr) => par_strips_witness_bd (instantiate bdy' {arg_red}) x)",
            arg_red = arg_red,
        );
        // inner (beta, beta): inner reduct instantiate ibodyp iarg; meet the
        // outer reduct instantiate bdy' arg_red with it via mk_join. Sub-meets:
        //   wb : par_strips_witness_bd bdy' ibodyp  = ihbody ibodyp (bdy=>ibodyp)
        //        with bdy=>ibodyp from hib : ibody=>ibodyp transported by
        //        lam_inj_snd of (symm eq2) (ibody := bdy).
        //   wa : par_strips_witness_bd arg_red iarg = iharg iarg hia.
        let wb_term = format!(
            concat!(
                "({ihbody} ibodyp ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x ibodyp) ibody bdy ",
                "(lam_inj_snd A2 ibody A bdy ",
                "(Eq.symm KExpr (KExpr.lam A bdy) (KExpr.lam A2 ibody) eq2)) ",
                "hib))"
            ),
            ihbody = ihbody,
        );
        let wa_term = format!("({iharg} iarg hia)", iharg = iharg);
        let kbeta_inner = format!(
            concat!(
                "(fun (A2 : KExpr) (A2p : KExpr) (ibody : KExpr) (ibodyp : KExpr) ",
                "(iarg : KExpr) ",
                "(eq2 : Eq KExpr (KExpr.lam A bdy) (KExpr.lam A2 ibody)) ",
                "(hA2 : par_reduces_bd A2 A2p) (hib : par_reduces_bd ibody ibodyp) ",
                "(hia : par_reduces_bd {arg_src} iarg) => ",
                "{join})"
            ),
            arg_src = arg_src,
            join = mk_join("bdy'", "ibodyp", arg_red, "iarg", &wb_term, &wa_term),
        );
        // inner (beta, app): inner reduct app g' b'. Recover g' = lam Ag bodyg
        // (lam_inv_eq on hg), build app_beta on the redex side, symm, transport.
        let kapp_inner = format!(
            concat!(
                "(fun (g0 : KExpr) (b0 : KExpr) ",
                "(hg : par_reduces_bd (KExpr.lam A bdy) g0) (hb : par_reduces_bd {arg_src} b0) => ",
                "par_reduces_bd_lam_inv_eq A bdy g0 ",
                "(par_strips_witness_bd (instantiate bdy' {arg_red}) (KExpr.app g0 b0)) ",
                "hg ",
                "(fun (Ag : KExpr) (bodyg : KExpr) ",
                "(eqg : Eq KExpr g0 (KExpr.lam Ag bodyg)) ",
                "(hAg : par_reduces_bd A Ag) (hbg : par_reduces_bd bdy bodyg) => ",
                "Eq.substType KExpr ",
                "(fun (x : KExpr) => par_strips_witness_bd (instantiate bdy' {arg_red}) (KExpr.app x b0)) ",
                "(KExpr.lam Ag bodyg) g0 (Eq.symm KExpr g0 (KExpr.lam Ag bodyg) eqg) ",
                "(par_strips_witness_bd_symm ",
                "(KExpr.app (KExpr.lam Ag bodyg) b0) (instantiate bdy' {arg_red}) ",
                "(par_strips_bd_app_beta Ag bodyg b0 bdy' {arg_red} ",
                "(par_strips_witness_bd_symm bdy' bodyg ({ihbody} bodyg hbg)) ",
                "(par_strips_witness_bd_symm {arg_red} b0 ({iharg} b0 hb))))))"
            ),
            arg_src = arg_src,
            arg_red = arg_red,
            ihbody = ihbody,
            iharg = iharg,
        );
        format!(
            concat!(
                "(fun (e2 : KExpr) ",
                "(h2 : par_reduces_bd (KExpr.app (KExpr.lam A bdy) {arg_src}) e2) => ",
                "par_reduces_bd_app_inv (KExpr.lam A bdy) {arg_src} e2 ",
                "{goal_ty} ",
                "h2 {kapp_inner} {kbeta_inner})"
            ),
            arg_src = arg_src,
            goal_ty = goal_ty,
            kapp_inner = kapp_inner,
            kbeta_inner = kbeta_inner,
        )
    };

    // beta arm: A A' bdy bdy' arg arg', hA hbody harg, ihA ihbody iharg.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (bdy : KExpr) (bdy' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(hA : par_reduces_bd A A') (hbody : par_reduces_bd bdy bdy') ",
            "(harg : par_reduces_bd arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) => ",
            "{body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "bdy'").replace("SUB", "bdy"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = beta_like_body("arg", "arg'", "iharg", "ihbody"),
    );

    // ---- let_ (zeta) outer arm ----
    // Source KExpr.let_ A val bdy (genuinely let_-headed, let-promotion),
    // reduct instantiate bdy' valp. Invert h2 via par_reduces_bd_let_inv:
    //   kcong (zeta, let_cong): the congruence side catches up by FIRING the
    //     zeta on the joined val/body (par_reduces_bd.let_, refl annotation);
    //     the contracted side transports through par_subst_bd. Meet at
    //     instantiate b3 v3.
    //   kzeta (zeta, zeta): meet at instantiate b3 v3 via par_subst_bd on
    //     BOTH sides — exactly the (beta, beta) mechanism (mk_join).
    let let_zeta_kcong = concat!(
        "(fun (ty2 : KExpr) (val2 : KExpr) (body2 : KExpr) ",
        "(_ht2 : par_reduces_bd A ty2) (hv2 : par_reduces_bd val val2) ",
        "(hb2 : par_reduces_bd bdy body2) => ",
        "@par_strips_witness_bd.rec bdy' body2 ",
        "(fun (_wb : par_strips_witness_bd bdy' body2) => ",
        "par_strips_witness_bd (instantiate bdy' valp) (KExpr.let_ ty2 val2 body2)) ",
        "(fun (b3 : KExpr) ",
        "(pb1 : par_reduces_bd bdy' b3) (pb2 : par_reduces_bd body2 b3) => ",
        "@par_strips_witness_bd.rec valp val2 ",
        "(fun (_wv : par_strips_witness_bd valp val2) => ",
        "par_strips_witness_bd (instantiate bdy' valp) (KExpr.let_ ty2 val2 body2)) ",
        "(fun (v3 : KExpr) ",
        "(pv1 : par_reduces_bd valp v3) (pv2 : par_reduces_bd val2 v3) => ",
        "par_strips_witness_bd.intro ",
        "(instantiate bdy' valp) (KExpr.let_ ty2 val2 body2) (instantiate b3 v3) ",
        "(par_subst_bd bdy' b3 valp v3 pb1 pv1) ",
        "(par_reduces_bd.let_ ty2 ty2 val2 v3 body2 b3 ",
        "(par_reduces_bd.refl ty2) pv2 pb2)) ",
        "(ihval val2 hv2)) ",
        "(ihbody body2 hb2))"
    );
    let let_zeta_kzeta = format!(
        concat!(
            "(fun (ty2p : KExpr) (val2p : KExpr) (body2p : KExpr) ",
            "(_ht2 : par_reduces_bd A ty2p) (hv2 : par_reduces_bd val val2p) ",
            "(hb2 : par_reduces_bd bdy body2p) => ",
            "{join})"
        ),
        join = mk_join(
            "bdy'",
            "body2p",
            "valp",
            "val2p",
            "(ihbody body2p hb2)",
            "(ihval val2p hv2)",
        ),
    );
    let let_arm = format!(
        concat!(
            "(fun (A : KExpr) (Ap : KExpr) (val : KExpr) (valp : KExpr) ",
            "(bdy : KExpr) (bdy' : KExpr) ",
            "(hty : par_reduces_bd A Ap) (hval : par_reduces_bd val valp) ",
            "(hbody : par_reduces_bd bdy bdy') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(e2 : KExpr) (h2 : par_reduces_bd (KExpr.let_ A val bdy) e2) => ",
            "par_reduces_bd_let_inv A val bdy e2 ",
            "(fun (x : KExpr) => par_strips_witness_bd (instantiate bdy' valp) x) ",
            "h2 {kcong} {kzeta})"
        ),
        ih_ty = ih.replace("SUB'", "Ap").replace("SUB", "A"),
        ih_val = ih.replace("SUB'", "valp").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "bdy'").replace("SUB", "bdy"),
        kcong = let_zeta_kcong,
        kzeta = let_zeta_kzeta,
    );

    // ---- let_cong outer arm ----
    // Source KExpr.let_ A val bdy, reduct KExpr.let_ Ap valp bdy'. Invert h2
    // via par_reduces_bd_let_inv:
    //   kcong (let_cong, let_cong): the congruence diagonal — recurse per
    //     component via the IHs, reassemble with par_strips_bd_let.
    //   kzeta (let_cong, zeta): the congruence side (OUR reduct) catches up by
    //     firing the zeta on the joined val/body; the other, contracted side
    //     transports through par_subst_bd. Meet at instantiate b3 v3.
    let let_cong_kcong = concat!(
        "(fun (ty2 : KExpr) (val2 : KExpr) (body2 : KExpr) ",
        "(ht2 : par_reduces_bd A ty2) (hv2 : par_reduces_bd val val2) ",
        "(hb2 : par_reduces_bd bdy body2) => ",
        "par_strips_bd_let Ap ty2 valp val2 bdy' body2 ",
        "(ihty ty2 ht2) (ihval val2 hv2) (ihbody body2 hb2))"
    );
    let let_cong_kzeta = concat!(
        "(fun (ty2p : KExpr) (val2p : KExpr) (body2p : KExpr) ",
        "(_ht2 : par_reduces_bd A ty2p) (hv2 : par_reduces_bd val val2p) ",
        "(hb2 : par_reduces_bd bdy body2p) => ",
        "@par_strips_witness_bd.rec bdy' body2p ",
        "(fun (_wb : par_strips_witness_bd bdy' body2p) => ",
        "par_strips_witness_bd (KExpr.let_ Ap valp bdy') (instantiate body2p val2p)) ",
        "(fun (b3 : KExpr) ",
        "(pb1 : par_reduces_bd bdy' b3) (pb2 : par_reduces_bd body2p b3) => ",
        "@par_strips_witness_bd.rec valp val2p ",
        "(fun (_wv : par_strips_witness_bd valp val2p) => ",
        "par_strips_witness_bd (KExpr.let_ Ap valp bdy') (instantiate body2p val2p)) ",
        "(fun (v3 : KExpr) ",
        "(pv1 : par_reduces_bd valp v3) (pv2 : par_reduces_bd val2p v3) => ",
        "par_strips_witness_bd.intro ",
        "(KExpr.let_ Ap valp bdy') (instantiate body2p val2p) (instantiate b3 v3) ",
        "(par_reduces_bd.let_ Ap Ap valp v3 bdy' b3 ",
        "(par_reduces_bd.refl Ap) pv1 pb1) ",
        "(par_subst_bd body2p b3 val2p v3 pb2 pv2)) ",
        "(ihval val2p hv2)) ",
        "(ihbody body2p hb2))"
    );
    let let_cong_arm = format!(
        concat!(
            "(fun (A : KExpr) (Ap : KExpr) (val : KExpr) (valp : KExpr) ",
            "(bdy : KExpr) (bdy' : KExpr) ",
            "(hty : par_reduces_bd A Ap) (hval : par_reduces_bd val valp) ",
            "(hbody : par_reduces_bd bdy bdy') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(e2 : KExpr) (h2 : par_reduces_bd (KExpr.let_ A val bdy) e2) => ",
            "par_reduces_bd_let_inv A val bdy e2 ",
            "(fun (x : KExpr) => par_strips_witness_bd (KExpr.let_ Ap valp bdy') x) ",
            "h2 {kcong} {kzeta})"
        ),
        ih_ty = ih.replace("SUB'", "Ap").replace("SUB", "A"),
        ih_val = ih.replace("SUB'", "valp").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "bdy'").replace("SUB", "bdy"),
        kcong = let_cong_kcong,
        kzeta = let_cong_kzeta,
    );

    // ---- proj outer arm (single-position congruence) ----
    // s i sub sub', hsub, ihsub. Source proj s i sub, reduct proj s i sub'.
    // Invert h2 via par_reduces_bd_proj_inv; single kproj case → par_strips_bd_proj.
    let proj_outer_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(hsub : par_reduces_bd sub sub') (ihsub : {ih_sub}) ",
            "(e2 : KExpr) (h2 : par_reduces_bd (KExpr.proj s i sub) e2) => ",
            "par_reduces_bd_proj_inv s i sub e2 ",
            "(fun (x : KExpr) => par_strips_witness_bd (KExpr.proj s i sub') x) ",
            "h2 ",
            "(fun (sub2 : KExpr) (hsub2 : par_reduces_bd sub sub2) => ",
            "par_strips_bd_proj s i sub' sub2 (ihsub sub2 hsub2)))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (e0 : KExpr) (e1_0 : KExpr) (e2_0 : KExpr) ",
            "(h1 : par_reduces_bd e0 e1_0) (h2_0 : par_reduces_bd e0 e2_0) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_outer_arm} ",
            "e0 e1_0 h1 e2_0 h2_0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_outer_arm = proj_outer_arm,
    )
}

// =====================================================================
// Wave 137 (Route B) — par_strips_bd assembly support.
// =====================================================================
//
// The final structural lemma before the confluence theorem is the
// single-step diamond `par_strips_bd`. Its assembly needs three new
// closed terms beyond the Wave 134/135 diagonal/refl combinators and the
// Wave 136 shape-recovery inversions:
//
//   1. par_reduces_bd_lam_inv_eq — an Eq-DATA lam inversion. The Wave 136
//      continuation-passing inversions hide the reduct shape inside the
//      goal, which is lossy when two derivations target the SAME reduct
//      (the cross-arm meet must rewrite both). This variant hands the
//      continuation the reduct equality `Eq t (lam ty' body')` as data,
//      so the meet can transport a second derivation onto the same reduct.
//   2. par_strips_witness_bd_lam_meet — from a diamond on two lambdas,
//      recover the diamond on their bodies (the per-binder sub-meet the
//      beta cross arm contracts through par_subst_bd).
//   3. par_strips_bd_app_beta — the (app, beta) cross combinator: the
//      first side is a syntactic redex `app (lam Af bodyf) a'`, the second
//      the already-contracted `instantiate body' arg'`; they meet at
//      `instantiate b3 a3` (b3 the body meet, a3 the argument meet), the
//      first via par_reduces_bd.beta, the second via par_subst_bd. The
//      symmetric (beta, app) cross arm is recovered by
//      par_strips_witness_bd_symm.
//
// All three are DerivedProved (full kernel/spec type-check), zero
// axiom_deps (Eq.* are the foundational Eq eliminators, not domain
// axioms). They are (with the let-promotion let-inversion/let-diagonal
// leaves) the closed leaves that the 64-case par_strips_bd
// eliminator reduces to.

/// Closed proof term for `par_reduces_bd_lam_inv_eq` (Wave 137, Route B).
///
/// Eq-data lam inversion: from `par_reduces_bd (lam ty body) t`, hand the
/// continuation the reduct equality `Eq t (lam ty' body')` together with the
/// recovered sub-derivations `ty => ty'` and `body => body'`, and return the
/// caller's fixed result type `C`. The motive's result is the arrow
/// `Eq e (lam ty body) -> Kont e' -> C`, where `Kont` is parameterized by the
/// arm reduct `e'`; the recursor substitutes the actual reduct `t` for `e'`,
/// so the user continuation receives the genuine reduct equality. The lam arm
/// passes `Eq.refl` for the reduct equality (reduct = lam t0' b0'); refl folds
/// in (reduct = source); the app/pi/let_-headed arms are discharged by
/// no-confusion (app_ne_lam/pi_ne_lam/let_ne_lam — post let-promotion a let_
/// source is let_-headed, never app-headed).
fn par_reduces_bd_lam_inv_eq_proof() -> String {
    // Kont(R) := forall ty' body', Eq R (lam ty' body') -> (ty=>ty') -> (body=>body') -> C
    let kont = |reduct: &str| -> String {
        format!(
            concat!(
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr {reduct} (KExpr.lam ty' body') -> ",
                "par_reduces_bd ty ty' -> par_reduces_bd body body' -> C)"
            ),
            reduct = reduct,
        )
    };
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
            "Eq KExpr e (KExpr.lam ty body) -> {kont} -> C)"
        ),
        kont = kont("e'"),
    );

    // refl arm: source e, reduct e. k expects Eq e (lam ty' body'); take
    // ty' = ty, body' = body so the equation is exactly eq, sub-derivs refl.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) ",
            "(k : {kont}) => ",
            "k ty body eq (par_reduces_bd.refl ty) (par_reduces_bd.refl body))"
        ),
        kont = kont("e"),
    );

    // lam arm: source lam t0 b0, reduct lam t0' b0' — the genuine match.
    // k receives Eq.refl for the reduct equation and the sub-derivations
    // transported from t0/b0 to ty/body via lam injectivity of eq.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(ht : par_reduces_bd t0 t0') (hb : par_reduces_bd b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) ",
            "(k : {kont_red}) => ",
            "k t0' b0' (Eq.refl KExpr (KExpr.lam t0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x t0') t0 ty ",
            "(lam_inj_fst t0 b0 ty body eq) ht) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
            "(lam_inj_snd t0 b0 ty body eq) hb))"
        ),
        kont_t0 = kont("t0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.lam t0' b0')"),
    );

    // beta arm: source app (lam A b0) arg — app /= lam.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_bd A A') (_hb0 : par_reduces_bd b0 b0') ",
            "(_harg : par_reduces_bd arg arg') ",
            "(_ihA : Eq KExpr A (KExpr.lam ty body) -> {kont_A} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> {kont_arg} -> C) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_lam (KExpr.lam A b0) arg ty body C eq)"
        ),
        kont_A = kont("A'"),
        kont_b0 = kont("b0'"),
        kont_arg = kont("arg'"),
        kont_red = kont("(instantiate b0' arg')"),
    );

    // app arm: source app g b — app /= lam.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_bd g g') (_hb : par_reduces_bd b b') ",
            "(_ihg : Eq KExpr g (KExpr.lam ty body) -> {kont_g} -> C) ",
            "(_ihb : Eq KExpr b (KExpr.lam ty body) -> {kont_b} -> C) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_lam g b ty body C eq)"
        ),
        kont_g = kont("g'"),
        kont_b = kont("b'"),
        kont_red = kont("(KExpr.app g' b')"),
    );

    // pi arm: source pi dom b0 — pi /= lam.
    let pi_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_bd dom dom') (_hb0 : par_reduces_bd b0 b0') ",
            "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> {kont_d} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "pi_ne_lam dom b0 ty body C eq)"
        ),
        kont_d = kont("dom'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.pi dom' b0')"),
    );

    // forall_ arm: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_bd dom dom') (_hb0 : par_reduces_bd b0 b0') ",
            "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> {kont_d} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "pi_ne_lam dom b0 ty body C eq)"
        ),
        kont_d = kont("dom'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.forall_ dom' b0')"),
    );

    // let_ (zeta) arm: source let_ t0 v b0 is let_-headed (genuine
    // constructor, let-promotion) — let_ /= lam via let_ne_lam.
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
            "(_hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_lam t0 v b0 ty body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(instantiate b0' v')"),
    );

    // let_cong arm: same let_-headed source — let_ne_lam.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
            "(_hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_lam t0 v b0 ty body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.let_ t0' v' b0')"),
    );

    // proj arm: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_bd sub sub') ",
            "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> {kont_sub} -> C) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "proj_ne_lam s i sub ty body C eq)"
        ),
        kont_sub = kont("sub'"),
        kont_red = kont("(KExpr.proj s i sub')"),
    );

    format!(
        concat!(
            "fun (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_bd (KExpr.lam ty body) t) ",
            "(klam : {kont_t}) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body)) klam"
        ),
        kont_t = kont("t"),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_strips_witness_bd_lam_meet` (Wave 137, Route B).
///
/// From a diamond witness on two lambdas
/// `par_strips_witness_bd (lam t1 b1) (lam t2 b2)`, recover the diamond on the
/// bodies `par_strips_witness_bd b1 b2`. Project the witness to its common
/// reduct `g3` with `lam t1 b1 => g3` and `lam t2 b2 => g3`; the Eq-data lam
/// inversion of the first gives `eqA : g3 = lam tA bA` (and `b1 => bA`), of the
/// second `eqB : g3 = lam tB bB` (and `b2 => bB`). Then `lam tB bB = lam tA bA`
/// by `Eq.trans (Eq.symm eqB) eqA`, so `bB = bA` by `lam_inj_snd`; transport
/// `b2 => bB` onto `b2 => bA` and meet at `bA`.
fn par_strips_witness_bd_lam_meet_proof() -> String {
    // Inner continuation (after both inversions): build the body meet at bA.
    let inner_k = concat!(
        "(fun (tB : KExpr) (bB : KExpr) ",
        "(eqB : Eq KExpr g3 (KExpr.lam tB bB)) ",
        "(_ht2 : par_reduces_bd t2 tB) (hb2 : par_reduces_bd b2 bB) => ",
        "par_strips_witness_bd.intro b1 b2 bA hb1 ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd b2 x) bB bA ",
        "(lam_inj_snd tB bB tA bA ",
        "(Eq.trans KExpr (KExpr.lam tB bB) g3 (KExpr.lam tA bA) ",
        "(Eq.symm KExpr g3 (KExpr.lam tB bB) eqB) eqA)) ",
        "hb2))"
    );
    // Outer continuation (after inverting p1): invert p2 at the same reduct g3.
    let outer_k = format!(
        concat!(
            "(fun (tA : KExpr) (bA : KExpr) ",
            "(eqA : Eq KExpr g3 (KExpr.lam tA bA)) ",
            "(_ht1 : par_reduces_bd t1 tA) (hb1 : par_reduces_bd b1 bA) => ",
            "par_reduces_bd_lam_inv_eq t2 b2 g3 (par_strips_witness_bd b1 b2) p2 {inner_k})"
        ),
        inner_k = inner_k,
    );
    format!(
        concat!(
            "fun (t1 : KExpr) (t2 : KExpr) (b1 : KExpr) (b2 : KExpr) ",
            "(w : par_strips_witness_bd (KExpr.lam t1 b1) (KExpr.lam t2 b2)) => ",
            "@par_strips_witness_bd.rec (KExpr.lam t1 b1) (KExpr.lam t2 b2) ",
            "(fun (_w : par_strips_witness_bd (KExpr.lam t1 b1) (KExpr.lam t2 b2)) => ",
            "par_strips_witness_bd b1 b2) ",
            "(fun (g3 : KExpr) ",
            "(p1 : par_reduces_bd (KExpr.lam t1 b1) g3) ",
            "(p2 : par_reduces_bd (KExpr.lam t2 b2) g3) => ",
            "par_reduces_bd_lam_inv_eq t1 b1 g3 (par_strips_witness_bd b1 b2) p1 {outer_k}) ",
            "w"
        ),
        outer_k = outer_k,
    )
}

/// Closed proof term for `par_strips_bd_app_beta` (Wave 137, Route B).
///
/// The (app, beta) cross core. The first side is a syntactic redex
/// `app (lam Af bodyf) a0p`; the second side `instantiate bodyq argp` is the
/// already-contracted beta reduct. Given the body diamond `wb :
/// par_strips_witness_bd bodyf bodyq` and the argument diamond `wa :
/// par_strips_witness_bd a0p argp`, project both to their meets `b3`/`a3` and
/// meet at `instantiate b3 a3`: the first side beta-contracts there
/// (`par_reduces_bd.beta`, domain reduct taken reflexively since instantiate
/// drops the lambda annotation), the second via `par_subst_bd` on the body and
/// argument meets. Both cross arms reduce to this core: the outer-app arm feeds
/// the body meet via `par_strips_witness_bd_lam_meet`, the outer-beta arm via
/// the body IH (then `par_strips_witness_bd_symm` for the swapped conclusion).
fn par_strips_bd_app_beta_proof() -> String {
    // After projecting wb to (b3, bodyf => b3, bodyq => b3) and wa to
    // (a3, a0p => a3, argp => a3), assemble the meet at instantiate b3 a3.
    let wa_rec = concat!(
        "(@par_strips_witness_bd.rec a0p argp ",
        "(fun (_wa : par_strips_witness_bd a0p argp) => ",
        "par_strips_witness_bd (KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp)) ",
        "(fun (a3 : KExpr) ",
        "(pa1 : par_reduces_bd a0p a3) (pa2 : par_reduces_bd argp a3) => ",
        "par_strips_witness_bd.intro ",
        "(KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp) ",
        "(instantiate b3 a3) ",
        "(par_reduces_bd.beta Af Af bodyf b3 a0p a3 ",
        "(par_reduces_bd.refl Af) pbf pa1) ",
        "(par_subst_bd bodyq b3 argp a3 pbq pa2)) ",
        "wa)"
    );
    // Project the body meet (b3, bodyf => b3, bodyq => b3), then run wa inside.
    let body_rec = format!(
        concat!(
            "(@par_strips_witness_bd.rec bodyf bodyq ",
            "(fun (_wb : par_strips_witness_bd bodyf bodyq) => ",
            "par_strips_witness_bd (KExpr.app (KExpr.lam Af bodyf) a0p) (instantiate bodyq argp)) ",
            "(fun (b3 : KExpr) ",
            "(pbf : par_reduces_bd bodyf b3) (pbq : par_reduces_bd bodyq b3) => ",
            "{wa_rec}) ",
            "wb)"
        ),
        wa_rec = wa_rec,
    );
    format!(
        concat!(
            "fun (Af : KExpr) (bodyf : KExpr) (a0p : KExpr) ",
            "(bodyq : KExpr) (argp : KExpr) ",
            "(wb : par_strips_witness_bd bodyf bodyq) ",
            "(wa : par_strips_witness_bd a0p argp) => ",
            "{body_rec}"
        ),
        body_rec = body_rec,
    )
}

// =====================================================================
// Wave 140 (Route B) — iota-free multi-step confluence proof terms.
// =====================================================================

/// Closed proof term for the iota-free STRIP lemma `par_strips_bd_star_strip`
/// (Wave 140, Route B).
///
/// `forall e e1 e2, par_reduces_bd_star e e1 -> par_reduces_bd e e2 ->`
/// `par_strips_witness_bd_star e1 e2`.
///
/// Induction on the multi-step derivation `e ⇒* e1` via `par_reduces_bd_star.rec`
/// with the motive generalized over the single-step target. The refl arm meets
/// at `e2`; the step arm joins via the single-step diamond `par_strips_bd`, the
/// inductive hypothesis, then `par_subsumes_bd_star` + `par_reduces_bd_star_trans`
/// to close the single-step side. Every leg is iota-free.
fn par_strips_bd_star_strip_proof() -> String {
    // Outer recursor motive: M a b _ := forall e2, par_reduces_bd a e2 ->
    //   par_strips_witness_bd_star b e2. (Generalizes over the single-step target
    // e2 so the IH can be applied to the per-step diamond's reduct.)
    let motive = concat!(
        "(fun (a : KExpr) (b : KExpr) (_h : par_reduces_bd_star a b) => ",
        "forall (e2 : KExpr), par_reduces_bd a e2 -> par_strips_witness_bd_star b e2)"
    );
    // refl arm (a = b = e): meet at e2 itself. e ⇒* e2 via par_subsumes_bd_star,
    // e2 ⇒* e2 via par_reduces_bd_star.refl.
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (e2 : KExpr) (h2 : par_reduces_bd e e2) => ",
        "par_strips_witness_bd_star.intro e e2 e2 ",
        "(par_subsumes_bd_star e e2 h2) ",
        "(par_reduces_bd_star.refl e2))"
    );
    // step arm: hstep : e ⇒ e', htail : e' ⇒* e'', ih : forall x, e' ⇒ x ->
    //   par_strips_witness_bd_star e'' x. Goal: forall e2, e ⇒ e2 ->
    //   par_strips_witness_bd_star e'' e2.
    //
    // Inner-inner: project ih's witness par_strips_witness_bd_star e'' m for the
    // shared reduct e3 (e'' ⇒* e3, m ⇒* e3), then meet e'' and e2 at e3 — the e2
    // side is e2 ⇒ m ⇒* e3 (par_subsumes_bd_star then par_reduces_bd_star_trans).
    let star_proj = concat!(
        "(@par_strips_witness_bd_star.rec e'' m ",
        "(fun (_w : par_strips_witness_bd_star e'' m) => ",
        "par_strips_witness_bd_star e'' e2) ",
        "(fun (e3 : KExpr) ",
        "(pe2e3 : par_reduces_bd_star e'' e3) (pme3 : par_reduces_bd_star m e3) => ",
        "par_strips_witness_bd_star.intro e'' e2 e3 pe2e3 ",
        "(par_reduces_bd_star_trans e2 m e3 ",
        "(par_subsumes_bd_star e2 m pe2m) pme3)) ",
        "(ih m pe1m))"
    );
    // Inner: project the single-step diamond par_strips_bd e e' e2's witness for
    // its reduct m (e' ⇒ m, e2 ⇒ m), then feed e' ⇒ m into the IH.
    let strips_proj = format!(
        concat!(
            "(@par_strips_witness_bd.rec e' e2 ",
            "(fun (_w : par_strips_witness_bd e' e2) => ",
            "par_strips_witness_bd_star e'' e2) ",
            "(fun (m : KExpr) ",
            "(pe1m : par_reduces_bd e' m) (pe2m : par_reduces_bd e2 m) => ",
            "{star_proj}) ",
            "(par_strips_bd e e' e2 hstep h2))"
        ),
        star_proj = star_proj,
    );
    let step_arm = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
            "(hstep : par_reduces_bd e e') ",
            "(_htail : par_reduces_bd_star e' e'') ",
            "(ih : forall (x : KExpr), par_reduces_bd e' x -> ",
            "par_strips_witness_bd_star e'' x) => ",
            "fun (e2 : KExpr) (h2 : par_reduces_bd e e2) => ",
            "{strips_proj})"
        ),
        strips_proj = strips_proj,
    );
    format!(
        concat!(
            "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(h1 : par_reduces_bd_star e e1) (h2 : par_reduces_bd e e2) => ",
            "par_reduces_bd_star.rec {motive} {refl_arm} {step_arm} ",
            "e e1 h1 e2 h2"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for the iota-free MULTI-STEP diamond
/// `par_reduces_bd_star_diamond` (Wave 140, Route B).
///
/// `forall e e1 e2, par_reduces_bd_star e e1 -> par_reduces_bd_star e e2 ->`
/// `par_strips_witness_bd_star e1 e2`.
///
/// Induction on the first multi-step derivation `e ⇒* e1` via
/// `par_reduces_bd_star.rec` with the motive generalized over the second
/// multi-step target. The refl arm meets at `e2`; the step arm strips the
/// single step `e ⇒ e'` out of the second leg via `par_strips_bd_star_strip`,
/// recurses through the IH, and re-closes with `par_reduces_bd_star_trans`.
fn par_reduces_bd_star_diamond_proof() -> String {
    // Outer recursor motive: M a b _ := forall e2, par_reduces_bd_star a e2 ->
    //   par_strips_witness_bd_star b e2.
    let motive = concat!(
        "(fun (a : KExpr) (b : KExpr) (_h : par_reduces_bd_star a b) => ",
        "forall (e2 : KExpr), par_reduces_bd_star a e2 -> par_strips_witness_bd_star b e2)"
    );
    // refl arm (a = b = e): meet at e2 — e ⇒* e2 is the given leg, e2 ⇒* e2 refl.
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (e2 : KExpr) (h2 : par_reduces_bd_star e e2) => ",
        "par_strips_witness_bd_star.intro e e2 e2 h2 ",
        "(par_reduces_bd_star.refl e2))"
    );
    // step arm: hstep : e ⇒ e', htail : e' ⇒* e'', ih : forall x,
    //   par_reduces_bd_star e' x -> par_strips_witness_bd_star e'' x. Goal: forall
    //   e2, par_reduces_bd_star e e2 -> par_strips_witness_bd_star e'' e2.
    //
    // Strip lemma joins the multi-step e ⇒* e2 against the single step e ⇒ e' at
    // m (e2 ⇒* m, e' ⇒* m); the IH on e' ⇒* m joins e'' and m at e3 (e'' ⇒* e3,
    // m ⇒* e3); e2 ⇒* m ⇒* e3 via transitivity.
    let star_proj = concat!(
        "(@par_strips_witness_bd_star.rec e'' m ",
        "(fun (_w : par_strips_witness_bd_star e'' m) => ",
        "par_strips_witness_bd_star e'' e2) ",
        "(fun (e3 : KExpr) ",
        "(pe2e3 : par_reduces_bd_star e'' e3) (pme3 : par_reduces_bd_star m e3) => ",
        "par_strips_witness_bd_star.intro e'' e2 e3 pe2e3 ",
        "(par_reduces_bd_star_trans e2 m e3 pe2m pme3)) ",
        "(ih m pe1m))"
    );
    let strip_proj = format!(
        concat!(
            "(@par_strips_witness_bd_star.rec e2 e' ",
            "(fun (_w : par_strips_witness_bd_star e2 e') => ",
            "par_strips_witness_bd_star e'' e2) ",
            "(fun (m : KExpr) ",
            "(pe2m : par_reduces_bd_star e2 m) (pe1m : par_reduces_bd_star e' m) => ",
            "{star_proj}) ",
            "(par_strips_bd_star_strip e e2 e' h2 hstep))"
        ),
        star_proj = star_proj,
    );
    let step_arm = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
            "(hstep : par_reduces_bd e e') ",
            "(_htail : par_reduces_bd_star e' e'') ",
            "(ih : forall (x : KExpr), par_reduces_bd_star e' x -> ",
            "par_strips_witness_bd_star e'' x) => ",
            "fun (e2 : KExpr) (h2 : par_reduces_bd_star e e2) => ",
            "{strip_proj})"
        ),
        strip_proj = strip_proj,
    );
    format!(
        concat!(
            "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(h1 : par_reduces_bd_star e e1) (h2 : par_reduces_bd_star e e2) => ",
            "par_reduces_bd_star.rec {motive} {refl_arm} {step_arm} ",
            "e e1 h1 e2 h2"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

// =====================================================================
// Wave 142 (Route B) — star-level pi inversion proof terms.
// =====================================================================

/// Closed proof term for `par_reduces_bd_pi_inv_eq` (Wave 142, Route B).
///
/// Eq-data pi inversion — the pi-headed dual of `par_reduces_bd_lam_inv_eq`.
/// From `par_reduces_bd (pi dom body) t`, hand the continuation the reduct
/// equality `Eq t (pi dom' body')` together with the recovered sub-derivations
/// `dom => dom'` and `body => body'`, and return the caller's fixed result type
/// `C`. The motive's result is the arrow `Eq e (pi dom body) -> Kont e' -> C`,
/// with `Kont` parameterized by the arm reduct `e'`, so the recursor substitutes
/// the genuine reduct `t`. Both the `pi` and `forall_` constructor arms are
/// genuine matches (forall_ is the reducible pi alias) and pass `Eq.refl` at the
/// `pi`-normalized reduct; `refl` folds in; the `lam` arm is discharged by
/// `lam_ne_pi`, the app-headed `beta`/`app` arms by `app_ne_pi`, and the
/// let_-headed `let_`/`let_cong` arms by `let_ne_pi` (let-promotion). This is
/// the reduct-as-DATA inversion that `par_reduces_bd_star_pi_inv` consumes in its
/// step arm (the continuation-passing `par_reduces_bd_pi_inv` hides the reduct,
/// so the star IH cannot be applied through it).
fn par_reduces_bd_pi_inv_eq_proof() -> String {
    // Kont(R) := forall dom' body', Eq R (pi dom' body') -> (dom=>dom') ->
    //   (body=>body') -> C.
    let kont = |reduct: &str| -> String {
        format!(
            concat!(
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr {reduct} (KExpr.pi dom' body') -> ",
                "par_reduces_bd dom dom' -> par_reduces_bd body body' -> C)"
            ),
            reduct = reduct,
        )
    };
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_bd e e') => ",
            "Eq KExpr e (KExpr.pi dom body) -> {kont} -> C)"
        ),
        kont = kont("e'"),
    );

    // refl arm: source e, reduct e. k expects Eq e (pi dom' body'); take
    // dom' = dom, body' = body so the equation is exactly eq, sub-derivs refl.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.pi dom body)) ",
            "(k : {kont}) => ",
            "k dom body eq (par_reduces_bd.refl dom) (par_reduces_bd.refl body))"
        ),
        kont = kont("e"),
    );

    // beta arm: source app (lam A b0) arg — app /= pi.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_bd A A') (_hb0 : par_reduces_bd b0 b0') ",
            "(_harg : par_reduces_bd arg arg') ",
            "(_ihA : Eq KExpr A (KExpr.pi dom body) -> {kont_A} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(_iharg : Eq KExpr arg (KExpr.pi dom body) -> {kont_arg} -> C) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_pi (KExpr.lam A b0) arg dom body C eq)"
        ),
        kont_A = kont("A'"),
        kont_b0 = kont("b0'"),
        kont_arg = kont("arg'"),
        kont_red = kont("(instantiate b0' arg')"),
    );

    // app arm: source app g b — app /= pi.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_bd g g') (_hb : par_reduces_bd b b') ",
            "(_ihg : Eq KExpr g (KExpr.pi dom body) -> {kont_g} -> C) ",
            "(_ihb : Eq KExpr b (KExpr.pi dom body) -> {kont_b} -> C) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_pi g b dom body C eq)"
        ),
        kont_g = kont("g'"),
        kont_b = kont("b'"),
        kont_red = kont("(KExpr.app g' b')"),
    );

    // lam arm: source lam t0 b0 — lam /= pi.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_bd t0 t0') (_hb : par_reduces_bd b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.pi dom body) -> {kont_t0} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "lam_ne_pi t0 b0 dom body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.lam t0' b0')"),
    );

    // pi arm: source pi d0 b0, reduct pi d0' b0' — the genuine match. k receives
    // Eq.refl for the reduct equation and the sub-derivations transported from
    // d0/b0 to dom/body via pi injectivity of eq.
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_bd d0 d0') (hb : par_reduces_bd b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.pi dom body) -> {kont_d} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.pi dom body)) ",
            "(k : {kont_red}) => ",
            "k d0' b0' (Eq.refl KExpr (KExpr.pi d0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        kont_d = kont("d0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.pi d0' b0')"),
    );

    // forall_ arm: source forall_ d0 b0 = pi d0 b0 (alias), reduct forall_ d0' b0'
    // = pi d0' b0' — also a genuine match. The reduct equality is Eq.refl at the
    // pi-normalized reduct (the kernel unfolds forall_ -> pi), and the eq feeds
    // pi_inj_fst/snd directly.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_bd d0 d0') (hb : par_reduces_bd b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.pi dom body) -> {kont_d} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.pi dom body)) ",
            "(k : {kont_red}) => ",
            "k d0' b0' (Eq.refl KExpr (KExpr.pi d0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        kont_d = kont("d0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.forall_ d0' b0')"),
    );

    // let_ (zeta) arm: source let_ t0 v b0 is let_-headed (genuine
    // constructor, let-promotion) — let_ /= pi via let_ne_pi.
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
            "(_hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.pi dom body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.pi dom body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_pi t0 v b0 dom body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(instantiate b0' v')"),
    );

    // let_cong arm: same let_-headed source — let_ne_pi.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_bd t0 t0') (_hv : par_reduces_bd v v') ",
            "(_hb0 : par_reduces_bd b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.pi dom body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.pi dom body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_pi t0 v b0 dom body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.let_ t0' v' b0')"),
    );

    // proj arm: source proj s i sub is proj-headed — proj /= pi via proj_ne_pi.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_bd sub sub') ",
            "(_ihsub : Eq KExpr sub (KExpr.pi dom body) -> {kont_sub} -> C) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "proj_ne_pi s i sub dom body C eq)"
        ),
        kont_sub = kont("sub'"),
        kont_red = kont("(KExpr.proj s i sub')"),
    );

    format!(
        concat!(
            "fun (dom : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_bd (KExpr.pi dom body) t) ",
            "(kpi : {kont_t}) => ",
            "par_reduces_bd.rec {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.pi dom body) t h (Eq.refl KExpr (KExpr.pi dom body)) kpi"
        ),
        kont_t = kont("t"),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for the star-level pi inversion
/// `par_reduces_bd_star_pi_inv` (Wave 142, Route B).
///
/// `forall (dom body w : KExpr) (C : KExpr -> Type),`
/// `par_reduces_bd_star (pi dom body) w ->`
/// `(forall dom' body', par_reduces_bd_star dom dom' ->`
/// `  par_reduces_bd_star body body' -> C (pi dom' body')) -> C w`
///
/// Pi-headedness is preserved under iota-free multi-step parallel reduction, and
/// its components reduce componentwise. Induction on the multi-step derivation
/// `pi dom body ⇒* w` via `par_reduces_bd_star.rec` with an ACCUMULATOR motive
/// that carries, for the current source `s`, the witness `Eq s (pi A B)` plus the
/// accumulated prefixes `dom ⇒* A` and `body ⇒* B`. The refl arm hands the
/// continuation the accumulated prefixes (transporting `C (pi A B)` onto `C s` via
/// `eq.symm`); the step arm transports the single step onto `pi A B`, Eq-inverts
/// it via `par_reduces_bd_pi_inv_eq` to `e' = pi A' B'` with `A => A'`, `B => B'`,
/// extends the prefixes through `par_reduces_bd_star_trans` + `par_subsumes_bd_star`,
/// and recurses via the IH. Entirely iota-free.
fn par_reduces_bd_star_pi_inv_proof() -> String {
    // Accumulator motive: M s r _ := forall A B, Eq s (pi A B) -> dom ⇒* A ->
    //   body ⇒* B -> C r. (The current source s is some pi A B reachable from
    //   pi dom body componentwise; r is the running target.)
    let motive = concat!(
        "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_bd_star s r) => ",
        "forall (A : KExpr) (B : KExpr), Eq KExpr s (KExpr.pi A B) -> ",
        "par_reduces_bd_star dom A -> par_reduces_bd_star body B -> C r)"
    );
    // refl arm (s = r = e): hand kpi the accumulated prefixes at C (pi A B),
    // transported onto C e via eq.symm.
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e (KExpr.pi A B)) ",
        "(hd : par_reduces_bd_star dom A) (hb : par_reduces_bd_star body B) => ",
        "Eq.substType KExpr C (KExpr.pi A B) e ",
        "(Eq.symm KExpr e (KExpr.pi A B) eq) (kpi A B hd hb))"
    );
    // step arm: hstep : e ⇒ e', _htail : e' ⇒* e'', ih : forall A B,
    //   Eq e' (pi A B) -> dom ⇒* A -> body ⇒* B -> C e''. Transport hstep onto
    //   pi A B, Eq-invert via par_reduces_bd_pi_inv_eq to e' = pi A' B' with
    //   A => A', B => B', extend the prefixes, recurse via ih.
    let step_arm = concat!(
        "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
        "(hstep : par_reduces_bd e e') ",
        "(_htail : par_reduces_bd_star e' e'') ",
        "(ih : forall (A : KExpr) (B : KExpr), Eq KExpr e' (KExpr.pi A B) -> ",
        "par_reduces_bd_star dom A -> par_reduces_bd_star body B -> C e'') => ",
        "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e (KExpr.pi A B)) ",
        "(hd : par_reduces_bd_star dom A) (hb : par_reduces_bd_star body B) => ",
        "par_reduces_bd_pi_inv_eq A B e' (C e'') ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd x e') e (KExpr.pi A B) eq hstep) ",
        "(fun (A' : KExpr) (B' : KExpr) (eq' : Eq KExpr e' (KExpr.pi A' B')) ",
        "(hAA' : par_reduces_bd A A') (hBB' : par_reduces_bd B B') => ",
        "ih A' B' eq' ",
        "(par_reduces_bd_star_trans dom A A' hd (par_subsumes_bd_star A A' hAA')) ",
        "(par_reduces_bd_star_trans body B B' hb (par_subsumes_bd_star B B' hBB'))))"
    );
    format!(
        concat!(
            "fun (dom : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_bd_star (KExpr.pi dom body) w) ",
            "(kpi : forall (dom' : KExpr) (body' : KExpr), ",
            "par_reduces_bd_star dom dom' -> par_reduces_bd_star body body' -> ",
            "C (KExpr.pi dom' body')) => ",
            "par_reduces_bd_star.rec {motive} {refl_arm} {step_arm} ",
            "(KExpr.pi dom body) w h ",
            "dom body (Eq.refl KExpr (KExpr.pi dom body)) ",
            "(par_reduces_bd_star.refl dom) (par_reduces_bd_star.refl body)"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

// =====================================================================
// Wave 143 (Route B) — pi injectivity (iota-free join) proof terms.
// =====================================================================

/// Closed proof term for the Eq-data star pi inversion
/// `par_reduces_bd_star_pi_inv_eq` (Wave 143, Route B).
///
/// Derived from the KExpr-indexed `par_reduces_bd_star_pi_inv` by instantiating
/// its motive at `M(ww) := Eq w ww -> C`: the inversion then returns
/// `Eq w w -> C`, which `Eq.refl w` discharges to `C`, and inside the inversion's
/// continuation the reduct equality `Eq w (pi dom' body')` is in scope and handed
/// straight to the caller's continuation `k`. This re-exposes the reduct as DATA
/// (the indexed form hides it in the motive), which pi injectivity needs to align
/// two inversions of the SAME reduct.
fn par_reduces_bd_star_pi_inv_eq_proof() -> String {
    concat!(
        "fun (dom : KExpr) (body : KExpr) (w : KExpr) (C : Type) ",
        "(h : par_reduces_bd_star (KExpr.pi dom body) w) ",
        "(k : forall (dom' : KExpr) (body' : KExpr), ",
        "Eq KExpr w (KExpr.pi dom' body') -> ",
        "par_reduces_bd_star dom dom' -> par_reduces_bd_star body body' -> C) => ",
        "par_reduces_bd_star_pi_inv dom body w ",
        "(fun (ww : KExpr) => Eq KExpr w ww -> C) h ",
        "(fun (dom' : KExpr) (body' : KExpr) ",
        "(hd : par_reduces_bd_star dom dom') (hb : par_reduces_bd_star body body') => ",
        "fun (eqw : Eq KExpr w (KExpr.pi dom' body')) => k dom' body' eqw hd hb) ",
        "(Eq.refl KExpr w)"
    )
    .to_string()
}

/// Closed proof term for the pi-injectivity-up-to-confluence lemmas
/// `par_bd_pi_injectivity_dom` / `par_bd_pi_injectivity_cod` (Wave 143, Route B),
/// parametric in the component projected.
///
/// From a shared-reduct join witness `par_strips_witness_bd_star (pi a1 b1)
/// (pi a2 b2)`, project the common reduct `e3` with `pi a1 b1 ⇒* e3` and
/// `pi a2 b2 ⇒* e3`. Eq-invert both legs (`par_reduces_bd_star_pi_inv_eq`):
/// `eq1 : e3 = pi a1' b1'` with `a1 ⇒* a1'`, `b1 ⇒* b1'`, and `eq2 : e3 =
/// pi a2' b2'` with `a2 ⇒* a2'`, `b2 ⇒* b2'`. Then `pi a1' b1' = pi a2' b2'` by
/// `Eq.trans (Eq.symm eq1) eq2`, so the projected components are equal
/// (`pi_inj_fst` for the domain, `pi_inj_snd` for the codomain); transport the
/// second leg onto the first's meet and package via
/// `par_strips_witness_bd_star.intro`.
///
/// `clhs`/`crhs` are the conclusion's two terms (`a1`/`a2` or `b1`/`b2`),
/// `meet1`/`meet2` the recovered meet points (`a1'`/`a2'` or `b1'`/`b2'`),
/// `leg1`/`leg2` the recovered prefix derivations (`hda1`/`hda2` or
/// `hdb1`/`hdb2`), and `pi_inj` the projection (`pi_inj_fst`/`pi_inj_snd`).
fn par_bd_pi_injectivity_proof(
    clhs: &str,
    crhs: &str,
    meet1: &str,
    meet2: &str,
    leg1: &str,
    leg2: &str,
    pi_inj: &str,
) -> String {
    // Inner continuation (after inverting the second leg p2): identify the meet by
    // pi injectivity of the trans'd reduct equation, transport leg2 onto it, and
    // package the join witness at meet1.
    let inner_k = format!(
        concat!(
            "(fun (a2' : KExpr) (b2' : KExpr) (eq2 : Eq KExpr e3 (KExpr.pi a2' b2')) ",
            "(hda2 : par_reduces_bd_star a2 a2') (hdb2 : par_reduces_bd_star b2 b2') => ",
            "par_strips_witness_bd_star.intro {clhs} {crhs} {meet1} {leg1} ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_bd_star {crhs} x) {meet2} {meet1} ",
            "(Eq.symm KExpr {meet1} {meet2} ",
            "({pi_inj} a1' b1' a2' b2' ",
            "(Eq.trans KExpr (KExpr.pi a1' b1') e3 (KExpr.pi a2' b2') ",
            "(Eq.symm KExpr e3 (KExpr.pi a1' b1') eq1) eq2))) ",
            "{leg2}))"
        ),
        clhs = clhs,
        crhs = crhs,
        meet1 = meet1,
        meet2 = meet2,
        leg1 = leg1,
        leg2 = leg2,
        pi_inj = pi_inj,
    );
    // Outer continuation (after inverting the first leg p1): invert p2 at the
    // same reduct e3.
    let outer_k = format!(
        concat!(
            "(fun (a1' : KExpr) (b1' : KExpr) (eq1 : Eq KExpr e3 (KExpr.pi a1' b1')) ",
            "(hda1 : par_reduces_bd_star a1 a1') (hdb1 : par_reduces_bd_star b1 b1') => ",
            "par_reduces_bd_star_pi_inv_eq a2 b2 e3 ",
            "(par_strips_witness_bd_star {clhs} {crhs}) p2 {inner_k})"
        ),
        clhs = clhs,
        crhs = crhs,
        inner_k = inner_k,
    );
    format!(
        concat!(
            "fun (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr) ",
            "(w : par_strips_witness_bd_star (KExpr.pi a1 b1) (KExpr.pi a2 b2)) => ",
            "@par_strips_witness_bd_star.rec (KExpr.pi a1 b1) (KExpr.pi a2 b2) ",
            "(fun (_w : par_strips_witness_bd_star (KExpr.pi a1 b1) (KExpr.pi a2 b2)) => ",
            "par_strips_witness_bd_star {clhs} {crhs}) ",
            "(fun (e3 : KExpr) ",
            "(p1 : par_reduces_bd_star (KExpr.pi a1 b1) e3) ",
            "(p2 : par_reduces_bd_star (KExpr.pi a2 b2) e3) => ",
            "par_reduces_bd_star_pi_inv_eq a1 b1 e3 ",
            "(par_strips_witness_bd_star {clhs} {crhs}) p1 {outer_k}) ",
            "w"
        ),
        clhs = clhs,
        crhs = crhs,
        outer_k = outer_k,
    )
}

// =====================================================================
// Wave 141 (Route B) — iota-free beta Church-Rosser keystone proof terms.
// =====================================================================

/// Which iota-free reduction relation a `BdStarCongruenceSpec` ranges over.
/// The star-congruence proof shapes share an outer skeleton (recursor +
/// framed motive + step prefixing), but the per-step congruence WITNESS differs:
/// `beta_reduces_bd` has single-position constructors (`app_left`, `lam_ty`, …)
/// while `par_reduces_bd` has only bi-position constructors (`app`, `lam`, `pi`)
/// that must be refl-padded on the fixed side. The spec carries a per-step
/// witness template to absorb that difference.
#[derive(Clone, Copy)]
enum BdStarRelation {
    Par,
    Beta,
}

impl BdStarRelation {
    /// The reflexive-transitive closure inductive name (also the lemma-name
    /// prefix, since each lemma is named `<star>_<suffix>`).
    fn star(self) -> &'static str {
        match self {
            BdStarRelation::Par => "par_reduces_bd_star",
            BdStarRelation::Beta => "beta_reduces_bd_star",
        }
    }

    /// The single-step relation inductive name (the constructor namespace).
    fn step(self) -> &'static str {
        match self {
            BdStarRelation::Par => "par_reduces_bd",
            BdStarRelation::Beta => "beta_reduces_bd",
        }
    }
}

/// One single-position star-congruence helper to generate. `frame` is the
/// surrounding-constructor shape with the moving position written as the `{}`
/// hole (filled with each variable in turn). `src_red` is the source reduction
/// over the moving position. `step_term` is the per-step single-step congruence
/// proof, a template whose `{e}`/`{ep}` holes are the step source/target and
/// which references the bound step witness `hstep`. `ctor` is the single-step
/// constructor used (for dependency tracking).
struct BdStarCongruenceSpec {
    relation: BdStarRelation,
    name: String,
    params: &'static str,
    src_red: &'static str,
    frame: &'static str,
    ctor: String,
    step_term: String,
    doc: String,
}

impl BdStarCongruenceSpec {
    /// The lemma signature. The two frame endpoints are the `src_red` reduced
    /// terms (e.g. `f`, `f'`), NOT the proof-term motive variables `x`/`y`.
    fn type_src(&self) -> String {
        let mut src_parts = self.src_red.split_whitespace();
        let src_lhs = src_parts.next().unwrap_or("");
        let src_rhs = src_parts.next().unwrap_or("");
        let star = self.relation.star();
        format!(
            "forall {params}, {star} {src_red} -> {star} {frame_lhs} {frame_rhs}",
            params = self.params,
            star = star,
            src_red = self.src_red,
            frame_lhs = self.frame.replacen("{}", src_lhs, 1),
            frame_rhs = self.frame.replacen("{}", src_rhs, 1),
        )
    }
}

/// The nine single-position congruence helpers (app_left, app_right, lam_ty,
/// lam_body, pi_dom, pi_cod, let_ty, let_val, let_body) for the given
/// iota-free relation. The forall_
/// congruence reuses the pi helpers because `KExpr.forall_` is the reducible
/// alias of `KExpr.pi` (same convention as `beta_subsumes_par_star`); the
/// three let positions are over the GENUINE `KExpr.let_` constructor
/// (let-promotion).
///
/// The per-step congruence WITNESS differs by relation: `beta_reduces_bd` has a
/// dedicated single-position constructor for each (`app_left`, …, `let_ty`, …);
/// `par_reduces_bd`
/// has only the bi-position `app`/`lam`/`pi` and tri-position `let_cong`, so
/// the fixed siblings are padded with
/// `par_reduces_bd.refl`. `step_term`s below carry `{e}`/`{ep}` holes for the
/// step source/target and reference the bound witness `hstep`.
fn bd_star_congruence_specs(relation: BdStarRelation) -> Vec<BdStarCongruenceSpec> {
    let star = relation.star();
    let step = relation.step();
    let mk = |suffix: &str,
              params: &'static str,
              src_red: &'static str,
              frame: &'static str,
              ctor_suffix: &str,
              step_term: String,
              what: &str| BdStarCongruenceSpec {
        relation,
        name: format!("{star}_{suffix}"),
        params,
        src_red,
        frame,
        ctor: format!("{step}.{ctor_suffix}"),
        step_term,
        doc: format!(
            "Star-level {what} congruence for the iota-free {step}. Proved by \
             {star}.rec prefixing the matching single-step congruence on each step. \
             DerivedProved, zero axiom_deps. Part of #2859 Wave 141 (Route B)."
        ),
    };
    // Per-relation single-step congruence witnesses. `{e}`/`{ep}` = step
    // source/target of the moving position; `hstep : step {e} {ep}`.
    #[allow(clippy::type_complexity)]
    let (app_left, app_right, lam_ty, lam_body, pi_dom, pi_cod, let_ty, let_val, let_body): (
        String,
        String,
        String,
        String,
        String,
        String,
        String,
        String,
        String,
    ) = match relation {
        BdStarRelation::Beta => (
            format!("{step}.app_left {{e}} {{ep}} a hstep"),
            format!("{step}.app_right f {{e}} {{ep}} hstep"),
            format!("{step}.lam_ty {{e}} {{ep}} body hstep"),
            format!("{step}.lam_body ty {{e}} {{ep}} hstep"),
            format!("{step}.pi_dom {{e}} {{ep}} body hstep"),
            format!("{step}.pi_cod dom {{e}} {{ep}} hstep"),
            format!("{step}.let_ty {{e}} {{ep}} val body hstep"),
            format!("{step}.let_val ty {{e}} {{ep}} body hstep"),
            format!("{step}.let_body ty val {{e}} {{ep}} hstep"),
        ),
        BdStarRelation::Par => (
            format!("{step}.app {{e}} {{ep}} a a hstep ({step}.refl a)"),
            format!("{step}.app f f {{e}} {{ep}} ({step}.refl f) hstep"),
            format!("{step}.lam {{e}} {{ep}} body body hstep ({step}.refl body)"),
            format!("{step}.lam ty ty {{e}} {{ep}} ({step}.refl ty) hstep"),
            format!("{step}.pi {{e}} {{ep}} body body hstep ({step}.refl body)"),
            format!("{step}.pi dom dom {{e}} {{ep}} ({step}.refl dom) hstep"),
            format!(
                "{step}.let_cong {{e}} {{ep}} val val body body hstep \
                 ({step}.refl val) ({step}.refl body)"
            ),
            format!(
                "{step}.let_cong ty ty {{e}} {{ep}} body body ({step}.refl ty) \
                 hstep ({step}.refl body)"
            ),
            format!(
                "{step}.let_cong ty ty val val {{e}} {{ep}} ({step}.refl ty) \
                 ({step}.refl val) hstep"
            ),
        ),
    };
    // proj is a single-position congruence for BOTH relations (KExpr.proj has
    // one KExpr sub-position; s/i are fixed), so its per-step witness is
    // identical in shape across Par/Beta: `<step>.proj s i {e} {ep} hstep`.
    let proj_step = format!("{step}.proj s i {{e}} {{ep}} hstep");
    // For Par, the bi/tri-position constructor witnesses each touch the
    // siblings, so the dependency-tracked constructor is
    // `app`/`lam`/`pi`/`let_cong`; for Beta it is the
    // dedicated single-position constructor.
    let cdep = |single: &str, bi: &str| match relation {
        BdStarRelation::Beta => single.to_string(),
        BdStarRelation::Par => bi.to_string(),
    };
    vec![
        mk(
            "app_left",
            "(f : KExpr) (f' : KExpr) (a : KExpr)",
            "f f'",
            "(KExpr.app {} a)",
            &cdep("app_left", "app"),
            app_left,
            "application-head",
        ),
        mk(
            "app_right",
            "(f : KExpr) (a : KExpr) (a' : KExpr)",
            "a a'",
            "(KExpr.app f {})",
            &cdep("app_right", "app"),
            app_right,
            "application-argument",
        ),
        mk(
            "lam_ty",
            "(ty : KExpr) (ty' : KExpr) (body : KExpr)",
            "ty ty'",
            "(KExpr.lam {} body)",
            &cdep("lam_ty", "lam"),
            lam_ty,
            "lambda-binder-type",
        ),
        mk(
            "lam_body",
            "(ty : KExpr) (body : KExpr) (body' : KExpr)",
            "body body'",
            "(KExpr.lam ty {})",
            &cdep("lam_body", "lam"),
            lam_body,
            "lambda-body",
        ),
        mk(
            "pi_dom",
            "(dom : KExpr) (dom' : KExpr) (body : KExpr)",
            "dom dom'",
            "(KExpr.pi {} body)",
            &cdep("pi_dom", "pi"),
            pi_dom,
            "pi-domain",
        ),
        mk(
            "pi_cod",
            "(dom : KExpr) (body : KExpr) (body' : KExpr)",
            "body body'",
            "(KExpr.pi dom {})",
            &cdep("pi_cod", "pi"),
            pi_cod,
            "pi-codomain",
        ),
        mk(
            "let_ty",
            "(ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr)",
            "ty ty'",
            "(KExpr.let_ {} val body)",
            &cdep("let_ty", "let_cong"),
            let_ty,
            "let-binder-type",
        ),
        mk(
            "let_val",
            "(ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr)",
            "val val'",
            "(KExpr.let_ ty {} body)",
            &cdep("let_val", "let_cong"),
            let_val,
            "let-value",
        ),
        mk(
            "let_body",
            "(ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr)",
            "body body'",
            "(KExpr.let_ ty val {})",
            &cdep("let_body", "let_cong"),
            let_body,
            "let-body",
        ),
        mk(
            "proj",
            "(s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr)",
            "sub sub'",
            "(KExpr.proj s i {})",
            &cdep("proj", "proj"),
            proj_step,
            "projection-scrutinee",
        ),
    ]
}

/// Closed proof term for a single-position star-congruence helper. Structural
/// induction on the input star via `<star>.rec` with a framed motive: refl
/// returns `<star>.refl` at the framed shape, step prefixes the matching
/// single-step congruence witness (`step_term`) via `<star>.step`.
fn bd_star_congruence_proof(spec: &BdStarCongruenceSpec) -> String {
    let star = spec.relation.star();
    let step = spec.relation.step();
    // Fill the single `{}` hole of the frame with a given moving-position term.
    let frame_with = |m: &str| spec.frame.replacen("{}", m, 1);
    // The per-step congruence witness with its source/target holes filled.
    let step_term = spec.step_term.replace("{e}", "e").replace("{ep}", "e'");
    // The leading index binders for the recursor application (e.g. "f f'").
    let mut src_parts = spec.src_red.split_whitespace();
    let src_lhs = src_parts.next().unwrap_or("");
    let src_rhs = src_parts.next().unwrap_or("");
    format!(
        concat!(
            "fun {params} (h : {star} {src_red}) => ",
            "{star}.rec ",
            "(fun (x : KExpr) (y : KExpr) (_ : {star} x y) => ",
            "{star} {frame_x} {frame_y}) ",
            "(fun (e : KExpr) => {star}.refl {frame_e}) ",
            "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
            "(hstep : {step} e e') ",
            "(_htail : {star} e' e'') ",
            "(ih : {star} {frame_ep} {frame_epp}) => ",
            "{star}.step {frame_e} {frame_ep} {frame_epp} ",
            "({step_term}) ih) ",
            "{src_lhs} {src_rhs} h"
        ),
        params = spec.params,
        star = star,
        step = step,
        src_red = spec.src_red,
        frame_x = frame_with("x"),
        frame_y = frame_with("y"),
        frame_e = frame_with("e"),
        frame_ep = frame_with("e'"),
        frame_epp = frame_with("e''"),
        step_term = step_term,
        src_lhs = src_lhs,
        src_rhs = src_rhs,
    )
}

/// Closed proof term for embedding 1a `beta_subsumes_par_bd_star`
/// (`beta_reduces_bd e e' -> par_reduces_bd_star e e'`). Structural induction on
/// `beta_reduces_bd.rec` (13 iota-free arms). The mirror of
/// `par_subsumes_beta_star` over the iota-free relation: the beta and zeta arms
/// embed a single par-step via `par_subsumes_bd_star` (zeta via
/// `par_reduces_bd.let_`, the parallel zeta on the genuine KExpr.let_
/// constructor); congruence arms lift the IH
/// through the `par_reduces_bd_star` congruence helpers (forall_ via the pi
/// alias, let_ty/let_val/let_body via the genuine-let_ positional helpers).
fn beta_subsumes_par_bd_star_proof() -> String {
    concat!(
        "fun (e0 : KExpr) (e0' : KExpr) (h0 : beta_reduces_bd e0 e0') => ",
        "beta_reduces_bd.rec ",
        "(fun (e : KExpr) (e' : KExpr) (_ : beta_reduces_bd e e') => ",
        "par_reduces_bd_star e e') ",
        // beta : A body arg
        "(fun (A : KExpr) (body : KExpr) (arg : KExpr) => ",
        "par_subsumes_bd_star ",
        "(KExpr.app (KExpr.lam A body) arg) (instantiate body arg) ",
        "(par_reduces_bd.beta A A body body arg arg ",
        "(par_reduces_bd.refl A) (par_reduces_bd.refl body) ",
        "(par_reduces_bd.refl arg))) ",
        // app_left : f f' a, hf, ih
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
        "(_hf : beta_reduces_bd f f') (ih : par_reduces_bd_star f f') => ",
        "par_reduces_bd_star_app_left f f' a ih) ",
        // app_right : f a a', ha, ih
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_ha : beta_reduces_bd a a') (ih : par_reduces_bd_star a a') => ",
        "par_reduces_bd_star_app_right f a a' ih) ",
        // lam_ty : ty ty' body, hty, ih
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') (ih : par_reduces_bd_star ty ty') => ",
        "par_reduces_bd_star_lam_ty ty ty' body ih) ",
        // lam_body : ty body body', hb, ih
        "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : par_reduces_bd_star body body') => ",
        "par_reduces_bd_star_lam_body ty body body' ih) ",
        // pi_dom : dom dom' body, hd, ih
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') (ih : par_reduces_bd_star dom dom') => ",
        "par_reduces_bd_star_pi_dom dom dom' body ih) ",
        // pi_cod : dom body body', hb, ih
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : par_reduces_bd_star body body') => ",
        "par_reduces_bd_star_pi_cod dom body body' ih) ",
        // forall_congr_dom : dom dom' body, hd, ih (alias of pi)
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') (ih : par_reduces_bd_star dom dom') => ",
        "par_reduces_bd_star_pi_dom dom dom' body ih) ",
        // forall_congr_cod : dom body body', hb, ih (alias of pi)
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : par_reduces_bd_star body body') => ",
        "par_reduces_bd_star_pi_cod dom body body' ih) ",
        // zeta : ty val body — ONE par step (the parallel zeta with refls)
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) => ",
        "par_subsumes_bd_star ",
        "(KExpr.let_ ty val body) (instantiate body val) ",
        "(par_reduces_bd.let_ ty ty val val body body ",
        "(par_reduces_bd.refl ty) (par_reduces_bd.refl val) ",
        "(par_reduces_bd.refl body))) ",
        // let_ty : ty ty' val body, hty, ih
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') (ih : par_reduces_bd_star ty ty') => ",
        "par_reduces_bd_star_let_ty ty ty' val body ih) ",
        // let_val : ty val val' body, hval, ih
        "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
        "(_hval : beta_reduces_bd val val') (ih : par_reduces_bd_star val val') => ",
        "par_reduces_bd_star_let_val ty val val' body ih) ",
        // let_body : ty val body body', hbody, ih
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hbody : beta_reduces_bd body body') ",
        "(ih : par_reduces_bd_star body body') => ",
        "par_reduces_bd_star_let_body ty val body body' ih) ",
        // proj : s i sub sub', hsub, ih
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : beta_reduces_bd sub sub') (ih : par_reduces_bd_star sub sub') => ",
        "par_reduces_bd_star_proj s i sub sub' ih) ",
        // indices + major
        "e0 e0' h0"
    )
    .to_string()
}

/// Closed proof term for embedding 1b `par_subsumes_beta_bd_star`
/// (`par_reduces_bd e e' -> beta_reduces_bd_star e e'`). Structural induction on
/// `par_reduces_bd.rec` (8 iota-free arms). The mirror of `beta_subsumes_par_star`
/// over the iota-free relation: each parallel step is simulated by a finite
/// iota-free beta sequence composed with `beta_reduces_bd_star_trans` and the
/// single-position beta-star congruence helpers, with one `beta_reduces_bd.beta`
/// (resp. `beta_reduces_bd.zeta`) head contraction appended for the beta
/// (resp. let_) contraction cases; the let_cong arm composes the three
/// genuine-let_ positional star congruences.
fn par_subsumes_beta_bd_star_proof() -> String {
    concat!(
        "fun (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_bd e0 e0') => ",
        "par_reduces_bd.rec ",
        "(fun (e : KExpr) (e' : KExpr) (_ : par_reduces_bd e e') => ",
        "beta_reduces_bd_star e e') ",
        // refl
        "(fun (e : KExpr) => beta_reduces_bd_star.refl e) ",
        // beta : A A' body body' arg arg', subs, IHs ihA ihbody iharg
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_bd A A') (_hbody : par_reduces_bd body body') ",
        "(_harg : par_reduces_bd arg arg') ",
        "(ihA : beta_reduces_bd_star A A') ",
        "(ihbody : beta_reduces_bd_star body body') ",
        "(iharg : beta_reduces_bd_star arg arg') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.app (KExpr.lam A body) arg) ",
        "(KExpr.app (KExpr.lam A' body') arg') ",
        "(instantiate body' arg') ",
        "(beta_reduces_bd_star_trans ",
        "(KExpr.app (KExpr.lam A body) arg) ",
        "(KExpr.app (KExpr.lam A' body') arg) ",
        "(KExpr.app (KExpr.lam A' body') arg') ",
        "(beta_reduces_bd_star_trans ",
        "(KExpr.app (KExpr.lam A body) arg) ",
        "(KExpr.app (KExpr.lam A' body) arg) ",
        "(KExpr.app (KExpr.lam A' body') arg) ",
        "(beta_reduces_bd_star_app_left (KExpr.lam A body) (KExpr.lam A' body) arg ",
        "(beta_reduces_bd_star_lam_ty A A' body ihA)) ",
        "(beta_reduces_bd_star_app_left (KExpr.lam A' body) (KExpr.lam A' body') arg ",
        "(beta_reduces_bd_star_lam_body A' body body' ihbody))) ",
        "(beta_reduces_bd_star_app_right (KExpr.lam A' body') arg arg' iharg)) ",
        "(beta_subsumes_bd_star ",
        "(KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
        "(beta_reduces_bd.beta A' body' arg'))) ",
        // app : f f' a a', subs hf ha, IHs ihf iha
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_bd f f') (_ha : par_reduces_bd a a') ",
        "(ihf : beta_reduces_bd_star f f') (iha : beta_reduces_bd_star a a') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.app f a) (KExpr.app f' a) (KExpr.app f' a') ",
        "(beta_reduces_bd_star_app_left f f' a ihf) ",
        "(beta_reduces_bd_star_app_right f' a a' iha)) ",
        // lam : ty ty' body body', subs, IHs ihty ihbody
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_bd ty ty') (_hbody : par_reduces_bd body body') ",
        "(ihty : beta_reduces_bd_star ty ty') ",
        "(ihbody : beta_reduces_bd_star body body') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.lam ty body) (KExpr.lam ty' body) (KExpr.lam ty' body') ",
        "(beta_reduces_bd_star_lam_ty ty ty' body ihty) ",
        "(beta_reduces_bd_star_lam_body ty' body body' ihbody)) ",
        // pi : dom dom' body body', subs, IHs ihdom ihbody
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hdom : par_reduces_bd dom dom') (_hbody : par_reduces_bd body body') ",
        "(ihdom : beta_reduces_bd_star dom dom') ",
        "(ihbody : beta_reduces_bd_star body body') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.pi dom body) (KExpr.pi dom' body) (KExpr.pi dom' body') ",
        "(beta_reduces_bd_star_pi_dom dom dom' body ihdom) ",
        "(beta_reduces_bd_star_pi_cod dom' body body' ihbody)) ",
        // forall_ : dom dom' body body', subs, IHs (alias of pi)
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hdom : par_reduces_bd dom dom') (_hbody : par_reduces_bd body body') ",
        "(ihdom : beta_reduces_bd_star dom dom') ",
        "(ihbody : beta_reduces_bd_star body body') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.pi dom body) (KExpr.pi dom' body) (KExpr.pi dom' body') ",
        "(beta_reduces_bd_star_pi_dom dom dom' body ihdom) ",
        "(beta_reduces_bd_star_pi_cod dom' body body' ihbody)) ",
        // let_ (zeta) : ty ty' val val' body body', subs, IHs ihty ihval ihbody.
        // Post let-promotion the source KExpr.let_ ty val body is a GENUINE
        // let_-headed node: reduce inside via the positional let star
        // congruences (body then val; ty/ty' play no role in the target
        // instantiate body' val', so ihty is unused), then one
        // beta_reduces_bd.zeta head contraction — mirroring the full-relation
        // beta_subsumes_par_star let_ (zeta) arm.
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
        "(body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
        "(_hbody : par_reduces_bd body body') ",
        "(_ihty : beta_reduces_bd_star ty ty') ",
        "(ihval : beta_reduces_bd_star val val') ",
        "(ihbody : beta_reduces_bd_star body body') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.let_ ty val body) ",
        "(KExpr.let_ ty val' body') ",
        "(instantiate body' val') ",
        "(beta_reduces_bd_star_trans ",
        "(KExpr.let_ ty val body) ",
        "(KExpr.let_ ty val body') ",
        "(KExpr.let_ ty val' body') ",
        "(beta_reduces_bd_star_let_body ty val body body' ihbody) ",
        "(beta_reduces_bd_star_let_val ty val val' body' ihval)) ",
        "(beta_subsumes_bd_star ",
        "(KExpr.let_ ty val' body') (instantiate body' val') ",
        "(beta_reduces_bd.zeta ty val' body'))) ",
        // let_cong : ty ty' val val' body body', subs, IHs ihty ihval ihbody —
        // three-position congruence composed via trans (ty, then val, then body).
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
        "(body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_bd ty ty') (_hval : par_reduces_bd val val') ",
        "(_hbody : par_reduces_bd body body') ",
        "(ihty : beta_reduces_bd_star ty ty') ",
        "(ihval : beta_reduces_bd_star val val') ",
        "(ihbody : beta_reduces_bd_star body body') => ",
        "beta_reduces_bd_star_trans ",
        "(KExpr.let_ ty val body) ",
        "(KExpr.let_ ty' val body) ",
        "(KExpr.let_ ty' val' body') ",
        "(beta_reduces_bd_star_let_ty ty ty' val body ihty) ",
        "(beta_reduces_bd_star_trans ",
        "(KExpr.let_ ty' val body) ",
        "(KExpr.let_ ty' val' body) ",
        "(KExpr.let_ ty' val' body') ",
        "(beta_reduces_bd_star_let_val ty' val val' body ihval) ",
        "(beta_reduces_bd_star_let_body ty' val' body body' ihbody))) ",
        // proj : s i sub sub', hsub, ihsub
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_bd sub sub') (ihsub : beta_reduces_bd_star sub sub') => ",
        "beta_reduces_bd_star_proj s i sub sub' ihsub) ",
        // indices + major
        "e0 e0' h0"
    )
    .to_string()
}

/// Closed proof term for `beta_bd_confluent` (the iota-free Church-Rosser
/// theorem). Transport both beta-closure legs into the parallel closure
/// (`beta_bd_star_subsumes_par_bd_star`), apply the parallel multi-step diamond
/// (`par_reduces_bd_star_diamond`) to obtain `par_strips_witness_bd_star e1 e2`,
/// project its common reduct e3, transport each parallel join leg back into the
/// beta closure (`par_bd_star_subsumes_beta_bd_star`), and repackage as
/// `beta_bd_join_witness` at e3.
fn beta_bd_confluent_proof() -> String {
    concat!(
        "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
        "(h1 : beta_reduces_bd_star e e1) (h2 : beta_reduces_bd_star e e2) => ",
        "@par_strips_witness_bd_star.rec e1 e2 ",
        "(fun (_w : par_strips_witness_bd_star e1 e2) => beta_bd_join_witness e1 e2) ",
        "(fun (e3 : KExpr) ",
        "(pe1e3 : par_reduces_bd_star e1 e3) (pe2e3 : par_reduces_bd_star e2 e3) => ",
        "beta_bd_join_witness.intro e1 e2 e3 ",
        "(par_bd_star_subsumes_beta_bd_star e1 e3 pe1e3) ",
        "(par_bd_star_subsumes_beta_bd_star e2 e3 pe2e3)) ",
        "(par_reduces_bd_star_diamond e e1 e2 ",
        "(beta_bd_star_subsumes_par_bd_star e e1 h1) ",
        "(beta_bd_star_subsumes_par_bd_star e e2 h2))"
    )
    .to_string()
}

#[cfg(test)]
#[path = "par_reduction_tests.rs"]
mod par_reduction_tests;
