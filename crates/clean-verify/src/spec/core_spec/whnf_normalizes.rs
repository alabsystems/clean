// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MODEL-side WHNF normalization spec (Front-2 recursive-grounding, T3 BRICK):
//! a well-typed const-free term REDUCES to a normal form.
//!
//! This composes the two landed halves of "recursive whnf reaches a normal
//! form":
//!   * PROGRESS — `whnf_progress_bd` (`whnf_progress.rs`): every const-free
//!     bvar-free `KExpr` exposes a whnf exit (a landed `is_whnf` value, a single
//!     iota-free `beta_reduces_bd` step, or a stuck non-lambda-headed
//!     application `whnf_stuck_head`).
//!   * TERMINATION — `beta_bd_sn_has_type` (`beta_bd_sn.rs`): every well-typed
//!     term is `beta_bd_acc` (accessible under `beta_reduces_bd`, i.e. strongly
//!     normalizing over the iota-free beta relation).
//!
//! The result `whnf_normalizes_bd` is the completion of the exit-shape spec the
//! future literal-whnf verification condition cites: it states that a
//! `has_type`-typable const-free term reduces (via zero-or-more
//! `beta_reduces_bd` steps) to a NORMAL FORM. It is MODEL-side, NOT literal-Rust
//! grounding — no Rust term is walked here; the content is the composition of
//! progress and termination over the abstract `KExpr` model.
//!
//! ## HONESTY: the normal form is WHNF-OR-STUCK, not just `is_whnf`
//!
//! The landed reflexive-transitive closure `whnf_to` (`whnf_reduction.rs`) bakes
//! `is_whnf` into its `refl` base, which does NOT cover the STUCK normal forms
//! (`app (sort 0) (sort 0)` is const-free, bvar-free, not `is_whnf`, and takes
//! no step — the counterexample `whnf_progress_bd` surfaces as its `stuck`
//! shape). T3 therefore builds a stuck-aware closure whose `refl` base is
//! `beta_bd_normal` = `is_whnf` OR `whnf_stuck_head`. This is the FAITHFUL
//! statement, not a weakening: the literal whnf ALSO returns non-WHNF on its
//! typed-stuck / cubical arms by design, so a literal whnf's post-condition must
//! account for stuck applications too. Concluding a bare `is_whnf` normal form
//! here would be a masquerade (false — see the `stuck` counterexample).
//!
//! ## What this brick registers (honest scope)
//!
//! 1. `beta_bd_normal e` — the stuck-aware normal-form predicate:
//!    `whnf (is_whnf e)` or `stuck (whnf_stuck_head e)`.
//! 2. `beta_bd_to e v` — a reflexive-transitive closure of `beta_reduces_bd`
//!    whose `refl` base demands `beta_bd_normal e` (the existing
//!    `beta_reduces_bd_star`, `par_reduction.rs`, has an UNCONDITIONAL `refl`
//!    and so does NOT encode "reaches a normal form" — a fresh stuck-aware
//!    closure is required).
//! 3. `whnf_normalizes_result e` — the existential witness (no Sum/Sigma in the
//!    fragment; the `par_strips` idiom): `intro e v (beta_bd_to e v)`.
//! 4. `const_free_preserved_bd` — a `beta_reduces_bd` step out of a const-free
//!    bvar-free term stays const-free (needed to thread `const_free` through the
//!    accessibility induction; the `beta`/`zeta` contraction arms rewrite
//!    `instantiate body v = body` via `inst_id_of_ceiling_zero`, exactly like
//!    the landed `beta_bd_step_preserves_ceiling_zero`).
//! 5. `whnf_normalizes_prepend` — prepend one `beta_reduces_bd` step in front of
//!    a `whnf_normalizes_result` (the cons of the closure).
//! 6. `whnf_normalizes_bd` — T3:
//!    `forall e T, has_type e T -> const_free e -> whnf_normalizes_result e`.
//!
//! ## Proof structure of T3 (`beta_bd_acc`-induction)
//!
//! `beta_bd_acc.rec` on `beta_bd_sn_has_type e T ht : beta_bd_acc e`, with the
//! measure motive `bvar_ceiling e = 0 -> const_free e -> whnf_normalizes_result
//! e`. At each accessible node the induction supplies a per-reduct recursion
//! `rec_e : forall y, beta_reduces_bd e y -> whnf_normalizes_result y` (built
//! from the `beta_bd_acc` IH, threading `beta_bd_step_preserves_ceiling_zero`
//! for the ceiling and `const_free_preserved_bd` for const-freeness). Then
//! `whnf_progress_bd e (ceiling) (const_free)` is dispatched via
//! `whnf_progress_result.rec` under the motive `(forall y, beta_reduces_bd e y
//! -> whnf_normalizes_result y) -> whnf_normalizes_result e` (the recursion
//! hypothesis is carried IN the motive so the `step` arm keeps the head/reduct
//! connection — no generalization loss):
//!   * `done  (is_whnf e)`   -> `beta_bd_to.refl` over `beta_bd_normal.whnf`;
//!   * `stuck (whnf_stuck_head f)` for `app f a` -> `beta_bd_to.refl` over
//!     `beta_bd_normal.stuck (whnf_stuck_head.app f a)`;
//!   * `step  e ~> e'`       -> `whnf_normalizes_prepend`, recursing on `e'` via
//!     `rec_e e' step`.
//! Zero new axioms; every value kernel-checked at spec build; the computed
//! closure inherits the foundational-only base of `whnf_progress_bd` and the
//! `beta_bd_sn` ladder.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the MODEL-side WHNF normalization (T3) brick: the stuck-aware
    /// closure, the normal-form predicate, the existential witness, the
    /// const-free preservation lemma, and the composition theorem
    /// `whnf_normalizes_bd`.
    ///
    /// Must run after `add_whnf_progress` (`whnf_progress_bd`,
    /// `whnf_progress_result`, `whnf_stuck_head`, `const_free`) and
    /// `add_beta_bd_sn` (`beta_bd_acc`, `beta_bd_sn_has_type`,
    /// `typable_bvar_ceiling_zero`, `beta_bd_step_preserves_ceiling_zero`,
    /// `inst_id_of_ceiling_zero`), and after `add_whnf_reduction` (`is_whnf`),
    /// `add_par_reduction` (`beta_reduces_bd`), the foundation layer
    /// (`AndType`/`Eq.subst`/`Eq.substType`/`Eq.symm`) and the decidable-eq
    /// tower (`nat_add_eq_zero_left/right`). Purely additive; zero new axioms.
    pub(super) fn add_whnf_normalizes(&mut self) -> Result<(), SpecError> {
        self.add_whnf_normalizes_closure()?;
        self.add_whnf_normalizes_const_free_preserved()?;
        self.add_whnf_normalizes_theorem()?;
        Ok(())
    }

    /// The stuck-aware normal-form predicate, the reflexive-transitive closure to
    /// a normal form, and the existential witness inductive.
    fn add_whnf_normalizes_closure(&mut self) -> Result<(), SpecError> {
        // beta_bd_normal e : e is a beta_reduces_bd NORMAL FORM. Faithful to the
        // three exit shapes whnf_progress_bd classifies: a landed is_whnf value
        // (sort/lam/pi/neutral) OR a stuck non-lambda-headed application
        // (whnf_stuck_head — sort/pi/stuck-spine). The narrow landed is_whnf
        // cannot express the stuck forms, so the base of the closure needs both.
        self.add_inductive(
            r"inductive beta_bd_normal : KExpr → Type
| whnf : forall (e : KExpr), is_whnf e → beta_bd_normal e
| stuck : forall (e : KExpr), whnf_stuck_head e → beta_bd_normal e",
            "beta_bd_normal e: e is an iota-free beta (beta_reduces_bd) NORMAL FORM — either a \
             landed is_whnf value (whnf) or a stuck non-lambda-headed application \
             (stuck / whnf_stuck_head). The honest WHNF-OR-STUCK normal-form predicate the \
             literal whnf's post-condition must account for; the narrow landed is_whnf omits the \
             stuck forms. MODEL-side exit shape, not literal-Rust grounding. Part of the WHNF \
             normalization brick (Front-2 recursive grounding, T3).",
        )?;

        // beta_bd_to e v : e reduces to the NORMAL FORM v via zero-or-more
        // beta_reduces_bd steps. Unlike the landed whnf_to (whnf_reduction.rs)
        // whose refl bakes in is_whnf ONLY, this closure's refl base demands
        // beta_bd_normal v (is_whnf OR whnf_stuck_head), so it can terminate on
        // the stuck normal forms. Distinct from beta_reduces_bd_star
        // (par_reduction.rs), whose refl is UNCONDITIONAL and so does not encode
        // "reaches a normal form".
        self.add_inductive(
            r"inductive beta_bd_to : KExpr → KExpr → Type
| refl : forall (e : KExpr), beta_bd_normal e → beta_bd_to e e
| step : forall (e : KExpr) (e' : KExpr) (v : KExpr), beta_reduces_bd e e' → beta_bd_to e' v → beta_bd_to e v",
            "beta_bd_to e v: e reduces to the beta_reduces_bd NORMAL FORM v via zero-or-more \
             iota-free beta steps. The refl base demands beta_bd_normal e (a WHNF-or-stuck normal \
             form), so — unlike the landed whnf_to whose refl bakes in is_whnf only — this closure \
             can terminate on the stuck normal forms whnf_progress_bd surfaces. The stuck-aware \
             reduction-to-normal-form closure. Part of the WHNF normalization brick (Front-2, T3).",
        )?;

        // whnf_normalizes_result e : the existential "e reduces to some normal
        // form". No Sum/Sigma in the fragment; the par_strips single-constructor
        // witness idiom packages the pair (v, beta_bd_to e v).
        self.add_inductive(
            r"inductive whnf_normalizes_result : KExpr → Type
| intro : forall (e : KExpr) (v : KExpr), beta_bd_to e v → whnf_normalizes_result e",
            "whnf_normalizes_result e: the existential witness that e reduces (via beta_reduces_bd) \
             to some normal form v (beta_bd_to e v), packaged without a Sum/Sigma type (not in the \
             fragment) via the single-constructor par_strips idiom. The MODEL-side normalization \
             conclusion the future literal whnf VC cites. Part of the WHNF normalization brick \
             (Front-2, T3).",
        )?;

        Ok(())
    }

    /// `const_free_preserved_bd`: a single iota-free beta step out of a const-free
    /// bvar-free term stays const-free. Mirrors
    /// `beta_bd_step_preserves_ceiling_zero` (the ceiling hypothesis is carried
    /// so the `beta`/`zeta` contraction arms can rewrite `instantiate body v
    /// = body` on the bvar-free body — const-freeness of a substitution reduces
    /// to const-freeness of the fixed body, avoiding a general substitution
    /// lemma).
    fn add_whnf_normalizes_const_free_preserved(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "const_free_preserved_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), beta_reduces_bd e e' -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> const_free e'"
            )
            .to_string(),
            value_src: Some(const_free_preserved_bd_proof()),
            is_axiom: false,
            description: concat!(
                "A single IOTA-FREE beta step (beta_reduces_bd) out of a const-free bvar-free term ",
                "stays const-free: beta_reduces_bd e e' -> bvar_ceiling e = 0 -> const_free e -> ",
                "const_free e'. beta_reduces_bd.rec (13 arms); the beta and zeta contraction ",
                "arms rewrite instantiate body v = body via inst_id_of_ceiling_zero (const-freeness ",
                "of a substitution on a bvar-free body reduces to const-freeness of the fixed ",
                "body, transported with Eq.substType — no general substitution lemma needed), the ",
                "eleven congruence arms (app/lam/pi/forall_ two-position, let_ty/let_val/let_body ",
                "three-position) split the const_free AndType (AndType.left/right), forward ",
                "the changed position through the IH (fed the split bvar-ceiling), and recompose ",
                "(AndType.intro). The ceiling hypothesis is carried solely to reach the contraction ",
                "arms, mirroring beta_bd_step_preserves_ceiling_zero. DerivedProved, zero ",
                "axiom_deps. Part of the WHNF normalization brick (Front-2, T3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.rec".to_string(),
                "bvar_ceiling".to_string(),
                "const_free".to_string(),
                "instantiate".to_string(),
                "inst_id_of_ceiling_zero".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_add_eq_zero_right".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "Nat.add".to_string(),
                "Eq.subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// `whnf_normalizes_prepend` (the closure cons) and `whnf_normalizes_bd`
    /// (T3, the composition theorem).
    fn add_whnf_normalizes_theorem(&mut self) -> Result<(), SpecError> {
        // whnf_normalizes_prepend: cons one beta_reduces_bd step in front of a
        // whnf_normalizes_result. Eliminates the result under a motive carrying
        // the step hypothesis (beta_reduces_bd x idx), so the intro arm keeps the
        // x ~> e' connection needed for beta_bd_to.step.
        self.add_definition(SpecDefinition {
            name: "whnf_normalizes_prepend".to_string(),
            type_src: concat!(
                "forall (x : KExpr) (x' : KExpr), beta_reduces_bd x x' -> ",
                "whnf_normalizes_result x' -> whnf_normalizes_result x"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (x : KExpr) (x' : KExpr) (hstep : beta_reduces_bd x x') ",
                    "(r : whnf_normalizes_result x') => ",
                    // whnf_normalizes_result has a SINGLE ctor (intro) with uniform
                    // index e, so the elaborator promotes e to a recursor PARAMETER
                    // (fixedIndicesToParams): .rec takes the param x' first, a 1-ARY
                    // motive over the major only, and a minor over just the ctor
                    // fields (v, h) — NOT the index-motive shape.
                    "whnf_normalizes_result.rec x' ",
                    "(fun (_ : whnf_normalizes_result x') => ",
                    "beta_reduces_bd x x' -> whnf_normalizes_result x) ",
                    "(fun (v : KExpr) (h : beta_bd_to x' v) ",
                    "(hs : beta_reduces_bd x x') => ",
                    "whnf_normalizes_result.intro x v (beta_bd_to.step x x' v hs h)) ",
                    "r hstep"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Prepend one IOTA-FREE beta step to a normalization witness: beta_reduces_bd x x' ",
                "-> whnf_normalizes_result x' -> whnf_normalizes_result x (the cons of the ",
                "stuck-aware closure beta_bd_to). Eliminates the witness under a motive that ",
                "carries the step hypothesis beta_reduces_bd x idx, so the intro arm keeps the ",
                "x ~> x' connection for beta_bd_to.step. DerivedProved, zero axiom_deps. Part of ",
                "the WHNF normalization brick (Front-2, T3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_normalizes_result".to_string(),
                "whnf_normalizes_result.intro".to_string(),
                "whnf_normalizes_result.rec".to_string(),
                "beta_bd_to".to_string(),
                "beta_bd_to.step".to_string(),
                "beta_reduces_bd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_normalizes_bd — T3: a well-typed const-free term reduces to a
        // WHNF-or-stuck normal form.
        self.add_definition(SpecDefinition {
            name: "whnf_normalizes_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (T : KExpr), has_type e T -> const_free e -> ",
                "whnf_normalizes_result e"
            )
            .to_string(),
            value_src: Some(whnf_normalizes_bd_proof()),
            is_axiom: false,
            description: concat!(
                "MODEL-side WHNF normalization spec (Front-2 recursive-grounding, T3 — the ",
                "completion of the exit-shape spec the future literal whnf VC cites): a well-typed ",
                "(has_type) const-free term reduces via zero-or-more IOTA-FREE beta_reduces_bd ",
                "steps to a NORMAL FORM (whnf_normalizes_result / beta_bd_to). Composes the landed ",
                "PROGRESS half whnf_progress_bd with the landed TERMINATION half ",
                "beta_bd_sn_has_type: beta_bd_acc.rec on the accessibility witness, with the motive ",
                "bvar_ceiling e = 0 -> const_free e -> whnf_normalizes_result e; the ceiling is ",
                "threaded via beta_bd_step_preserves_ceiling_zero and const-freeness via ",
                "const_free_preserved_bd, whnf_progress_bd is dispatched at each node, and the step ",
                "shape recurses through whnf_normalizes_prepend. HONEST: the normal form is ",
                "WHNF-OR-STUCK (beta_bd_normal = is_whnf OR whnf_stuck_head), NOT a bare is_whnf — ",
                "faithful to the literal whnf's typed-stuck arms and to the app (sort 0)(sort 0) ",
                "stuck counterexample; concluding is_whnf here would be FALSE (a masquerade). ",
                "MODEL-side spec, NOT literal-Rust grounding. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "has_type".to_string(),
                "const_free".to_string(),
                "bvar_ceiling".to_string(),
                "whnf_normalizes_result".to_string(),
                "whnf_normalizes_result.intro".to_string(),
                "whnf_normalizes_prepend".to_string(),
                "beta_bd_to".to_string(),
                "beta_bd_to.refl".to_string(),
                "beta_bd_normal".to_string(),
                "beta_bd_normal.whnf".to_string(),
                "beta_bd_normal.stuck".to_string(),
                "beta_bd_acc".to_string(),
                "beta_bd_acc.rec".to_string(),
                "beta_bd_sn_has_type".to_string(),
                "typable_bvar_ceiling_zero".to_string(),
                "beta_bd_step_preserves_ceiling_zero".to_string(),
                "const_free_preserved_bd".to_string(),
                "whnf_progress_bd".to_string(),
                "whnf_progress_result".to_string(),
                "whnf_progress_result.rec".to_string(),
                "is_whnf".to_string(),
                "whnf_stuck_head".to_string(),
                "whnf_stuck_head.app".to_string(),
                "whnf_stuck_head.proj".to_string(),
                "beta_reduces_bd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `const_free_preserved_bd`. `beta_reduces_bd.rec` with
/// motive `bvar_ceiling e = 0 -> const_free e -> const_free e'` (13 arms). The
/// arm order matches the `beta_reduces_bd` constructor order (beta, app_left,
/// app_right, lam_ty, lam_body, pi_dom, pi_cod, forall_congr_dom,
/// forall_congr_cod, zeta, let_ty, let_val, let_body), mirroring
/// `beta_bd_step_preserves_ceiling_zero_proof` with `const_free`/`AndType` in
/// place of `bvar_ceiling`/`Nat.add`.
fn const_free_preserved_bd_proof() -> String {
    concat!(
        "fun (s : KExpr) (t : KExpr) (hst : beta_reduces_bd s t) => ",
        "beta_reduces_bd.rec ",
        "(fun (e : KExpr) (e' : KExpr) (_ : beta_reduces_bd e e') => ",
        "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> const_free e') ",
        // beta A body arg : (app (lam A body) arg) ~> instantiate body arg.
        // Extract const_free body, transport it along body = instantiate body arg.
        "(fun (A : KExpr) (body : KExpr) (arg : KExpr) ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.app (KExpr.lam A body) arg)) Nat.zero) ",
        "(hcf : const_free (KExpr.app (KExpr.lam A body) arg)) => ",
        "(fun (hbody : Eq Nat (bvar_ceiling body) Nat.zero) => ",
        "Eq.substType KExpr (fun (z : KExpr) => const_free z) ",
        "body (instantiate body arg) ",
        "(Eq.symm KExpr (instantiate body arg) body ",
        "(inst_id_of_ceiling_zero body arg hbody)) ",
        "(AndType.right (const_free A) (const_free body) ",
        "(AndType.left (AndType (const_free A) (const_free body)) (const_free arg) hcf))) ",
        "(nat_add_eq_zero_right (bvar_ceiling A) (bvar_ceiling body) ",
        "(nat_add_eq_zero_left (Nat.add (bvar_ceiling A) (bvar_ceiling body)) ",
        "(bvar_ceiling arg) hceil))) ",
        // app_left f f' a : (app f a) ~> (app f' a).
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
        "(_hf : beta_reduces_bd f f') ",
        "(ih : Eq Nat (bvar_ceiling f) Nat.zero -> const_free f -> const_free f') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ",
        "(hcf : const_free (KExpr.app f a)) => ",
        "AndType.intro (const_free f') (const_free a) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hceil) ",
        "(AndType.left (const_free f) (const_free a) hcf)) ",
        "(AndType.right (const_free f) (const_free a) hcf)) ",
        // app_right f a a' : (app f a) ~> (app f a').
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_ha : beta_reduces_bd a a') ",
        "(ih : Eq Nat (bvar_ceiling a) Nat.zero -> const_free a -> const_free a') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ",
        "(hcf : const_free (KExpr.app f a)) => ",
        "AndType.intro (const_free f) (const_free a') ",
        "(AndType.left (const_free f) (const_free a) hcf) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) hceil) ",
        "(AndType.right (const_free f) (const_free a) hcf))) ",
        // lam_ty ty ty' body : (lam ty body) ~> (lam ty' body).
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> const_free ty') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) ",
        "(hcf : const_free (KExpr.lam ty body)) => ",
        "AndType.intro (const_free ty') (const_free body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) (bvar_ceiling body) hceil) ",
        "(AndType.left (const_free ty) (const_free body) hcf)) ",
        "(AndType.right (const_free ty) (const_free body) hcf)) ",
        // lam_body ty body body' : (lam ty body) ~> (lam ty body').
        "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> const_free body') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) ",
        "(hcf : const_free (KExpr.lam ty body)) => ",
        "AndType.intro (const_free ty) (const_free body') ",
        "(AndType.left (const_free ty) (const_free body) hcf) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling ty) (bvar_ceiling body) hceil) ",
        "(AndType.right (const_free ty) (const_free body) hcf))) ",
        // pi_dom dom dom' body : (pi dom body) ~> (pi dom' body).
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> const_free dom -> const_free dom') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.pi dom body)) => ",
        "AndType.intro (const_free dom') (const_free body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) hceil) ",
        "(AndType.left (const_free dom) (const_free body) hcf)) ",
        "(AndType.right (const_free dom) (const_free body) hcf)) ",
        // pi_cod dom body body' : (pi dom body) ~> (pi dom body').
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> const_free body') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.pi dom body)) => ",
        "AndType.intro (const_free dom) (const_free body') ",
        "(AndType.left (const_free dom) (const_free body) hcf) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) hceil) ",
        "(AndType.right (const_free dom) (const_free body) hcf))) ",
        // forall_congr_dom dom dom' body — forall_ is the reducible pi alias.
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> const_free dom -> const_free dom') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.forall_ dom body)) => ",
        "AndType.intro (const_free dom') (const_free body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) hceil) ",
        "(AndType.left (const_free dom) (const_free body) hcf)) ",
        "(AndType.right (const_free dom) (const_free body) hcf)) ",
        // forall_congr_cod dom body body'.
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> const_free body') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) ",
        "(hcf : const_free (KExpr.forall_ dom body)) => ",
        "AndType.intro (const_free dom) (const_free body') ",
        "(AndType.left (const_free dom) (const_free body) hcf) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) hceil) ",
        "(AndType.right (const_free dom) (const_free body) hcf))) ",
        // zeta ty val body — the genuine let_ head contraction: (let_ ty val
        // body) ~> instantiate body val. On the bvar-free body the contractum
        // IS the body (inst_id_of_ceiling_zero); transport its const-freeness.
        // Triple splits: bvar_ceiling (let_ ty val body) = add (ceil ty)
        // (add (ceil val) (ceil body)); const_free (let_ ty val body) =
        // AndType cf_ty (AndType cf_val cf_body).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "(fun (hbody : Eq Nat (bvar_ceiling body) Nat.zero) => ",
        "Eq.substType KExpr (fun (z : KExpr) => const_free z) ",
        "body (instantiate body val) ",
        "(Eq.symm KExpr (instantiate body val) body ",
        "(inst_id_of_ceiling_zero body val hbody)) ",
        "(AndType.right (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf))) ",
        "(nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hceil))) ",
        // let_ty ty ty' val body : (let_ ty val body) ~> (let_ ty' val body).
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> const_free ty') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "AndType.intro (const_free ty') (AndType (const_free val) (const_free body)) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hceil) ",
        "(AndType.left (const_free ty) (AndType (const_free val) (const_free body)) hcf)) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf)) ",
        // let_val ty val val' body : (let_ ty val body) ~> (let_ ty val' body).
        "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
        "(_hv : beta_reduces_bd val val') ",
        "(ih : Eq Nat (bvar_ceiling val) Nat.zero -> const_free val -> const_free val') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "AndType.intro (const_free ty) (AndType (const_free val') (const_free body)) ",
        "(AndType.left (const_free ty) (AndType (const_free val) (const_free body)) hcf) ",
        "(AndType.intro (const_free val') (const_free body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hceil)) ",
        "(AndType.left (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf))) ",
        "(AndType.right (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf)))) ",
        // let_body ty val body body' : (let_ ty val body) ~> (let_ ty val body')
        // — now a PLAIN one-position congruence (the old bundled instantiate
        // premise is gone; zeta carries the contraction).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> const_free body') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(hcf : const_free (KExpr.let_ ty val body)) => ",
        "AndType.intro (const_free ty) (AndType (const_free val) (const_free body')) ",
        "(AndType.left (const_free ty) (AndType (const_free val) (const_free body)) hcf) ",
        "(AndType.intro (const_free val) (const_free body') ",
        "(AndType.left (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf)) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) hceil)) ",
        "(AndType.right (const_free val) (const_free body) ",
        "(AndType.right (const_free ty) (AndType (const_free val) (const_free body)) hcf))))) ",
        // proj ps pidx sub sub' (proj/lit rung): const_free (proj ..) reduces to
        // const_free sub, and bvar_ceiling (proj ..) to bvar_ceiling sub (both defeq),
        // so the IH carries const-freeness straight through the projection.
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : beta_reduces_bd sub sub') ",
        "(ih : Eq Nat (bvar_ceiling sub) Nat.zero -> const_free sub -> const_free sub') ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.proj ps pidx sub)) Nat.zero) ",
        "(hcf : const_free (KExpr.proj ps pidx sub)) => ih hceil hcf) ",
        // indices + major
        "s t hst"
    )
    .to_string()
}

/// Closed proof term for `whnf_normalizes_bd` (T3). `beta_bd_acc.rec` on the
/// accessibility witness, dispatching `whnf_progress_bd` at each node with the
/// recursion hypothesis carried in the `whnf_progress_result.rec` motive.
fn whnf_normalizes_bd_proof() -> String {
    concat!(
        "fun (e0 : KExpr) (T0 : KExpr) (ht : has_type e0 T0) (hcf0 : const_free e0) => ",
        "beta_bd_acc.rec ",
        "(fun (e : KExpr) (_ : beta_bd_acc e) => ",
        "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> whnf_normalizes_result e) ",
        // minor: at an accessible node e, with successor-accessibility h and the
        // per-successor IH ih, build the per-reduct recursion and dispatch
        // whnf_progress_bd.
        "(fun (e : KExpr) ",
        "(_h : forall (e' : KExpr), beta_reduces_bd e e' -> beta_bd_acc e') ",
        "(ih : forall (e' : KExpr), beta_reduces_bd e e' -> ",
        "Eq Nat (bvar_ceiling e') Nat.zero -> const_free e' -> whnf_normalizes_result e') ",
        "(hceil : Eq Nat (bvar_ceiling e) Nat.zero) ",
        "(hcf : const_free e) => ",
        "whnf_progress_result.rec ",
        "(fun (x : KExpr) (_ : whnf_progress_result x) => ",
        "(forall (y : KExpr), beta_reduces_bd x y -> whnf_normalizes_result y) -> ",
        "whnf_normalizes_result x) ",
        // done arm: e is already a normal form (is_whnf).
        "(fun (x : KExpr) (hw : is_whnf x) ",
        "(_rec : forall (y : KExpr), beta_reduces_bd x y -> whnf_normalizes_result y) => ",
        "whnf_normalizes_result.intro x x ",
        "(beta_bd_to.refl x (beta_bd_normal.whnf x hw))) ",
        // step arm: e ~> x'; recurse on x' via the per-reduct recursion, prepend.
        "(fun (x : KExpr) (x' : KExpr) (hs : beta_reduces_bd x x') ",
        "(recx : forall (y : KExpr), beta_reduces_bd x y -> whnf_normalizes_result y) => ",
        "whnf_normalizes_prepend x x' hs (recx x' hs)) ",
        // stuck arm: e = app f a with a stuck head f; app f a is a normal form.
        "(fun (f : KExpr) (a : KExpr) (hsf : whnf_stuck_head f) ",
        "(_rec : forall (y : KExpr), ",
        "beta_reduces_bd (KExpr.app f a) y -> whnf_normalizes_result y) => ",
        "whnf_normalizes_result.intro (KExpr.app f a) (KExpr.app f a) ",
        "(beta_bd_to.refl (KExpr.app f a) ",
        "(beta_bd_normal.stuck (KExpr.app f a) (whnf_stuck_head.app f a hsf)))) ",
        // stuck_proj arm (proj/lit rung): e = proj s i sub with a stuck scrutinee; the
        // projection is a normal form (whnf_stuck_head.proj over the stuck scrutinee).
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (hsp : whnf_stuck_head psub) ",
        "(_rec : forall (y : KExpr), ",
        "beta_reduces_bd (KExpr.proj ps pidx psub) y -> whnf_normalizes_result y) => ",
        "whnf_normalizes_result.intro (KExpr.proj ps pidx psub) (KExpr.proj ps pidx psub) ",
        "(beta_bd_to.refl (KExpr.proj ps pidx psub) ",
        "(beta_bd_normal.stuck (KExpr.proj ps pidx psub) (whnf_stuck_head.proj ps pidx psub hsp)))) ",
        // index + major for whnf_progress_result.rec, then the per-reduct recursion.
        "e (whnf_progress_bd e hceil hcf) ",
        "(fun (y : KExpr) (hsy : beta_reduces_bd e y) => ",
        "ih y hsy ",
        "(beta_bd_step_preserves_ceiling_zero e y hsy hceil) ",
        "(const_free_preserved_bd e y hsy hceil hcf))) ",
        // motive indices + majors for beta_bd_acc.rec
        "e0 (beta_bd_sn_has_type e0 T0 ht) ",
        "(typable_bvar_ceiling_zero e0 T0 ht) hcf0"
    )
    .to_string()
}

#[cfg(test)]
#[path = "whnf_normalizes_tests.rs"]
mod whnf_normalizes_tests;
