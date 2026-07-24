// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-founded accessibility of `KExpr` under the strict-subexpression
//! relation — retirement of the SN-pillar census axiom `infer_terminates`
//! (formerly a `HelperAxiom` in `whnf_lemmas.rs`).
//!
//! ## What is proved (and the honest scope)
//!
//! The census axiom was
//!
//!   `infer_terminates : forall (e : KExpr), terminates_infer e`
//!
//! with `terminates_infer e := infer_acc e` (`whnf_reduction.rs`, reducible
//! alias) and `infer_acc` the accessibility predicate of `e` under the
//! immediate-child relation `subexpr_step`:
//!
//! ```text
//! inductive subexpr_step : KExpr -> KExpr -> Type
//! | app_f    : subexpr_step f  (KExpr.app f a)
//! | app_a    : subexpr_step a  (KExpr.app f a)
//! | lam_ty   : subexpr_step ty (KExpr.lam ty body)
//! | lam_body : subexpr_step body (KExpr.lam ty body)
//! | pi_dom   : subexpr_step ty (KExpr.pi ty body)
//! | pi_cod   : subexpr_step body (KExpr.pi ty body)
//! | let_ty   : subexpr_step ty (KExpr.let_ ty val body)
//! | let_val  : subexpr_step val (KExpr.let_ ty val body)
//! | let_body : subexpr_step body (KExpr.let_ ty val body)
//!
//! inductive infer_acc : KExpr -> Type
//! | intro : (e : KExpr) -> ((e' : KExpr) -> subexpr_step e' e -> infer_acc e')
//!           -> infer_acc e
//! ```
//!
//! `infer_acc e` is inhabited exactly when structural recursion into the
//! immediate subexpressions of `e` is well-founded. It IS — every child is a
//! structurally smaller `KExpr` — so `forall e, infer_acc e` is the standard
//! `Acc subexpr_step` proof, discharged here by structural `KExpr.rec`.
//!
//! ## Proof shape
//!
//! `KExpr.rec` with motive `infer_acc x`. At every node the predecessor
//! obligation `(e' : KExpr) -> subexpr_step e' node -> infer_acc e'` is closed
//! by INVERTING the `subexpr_step` witness. The inversion is factored into the
//! helper `subexpr_step_acc_inv`, whose motive
//! `childAcc parent -> infer_acc child` routes each of the nine `subexpr_step`
//! constructors uniformly: `childAcc p` bundles the accessibility of `p`'s
//! immediate children (an `AndType` at `app`/`lam`/`pi`, a right-nested
//! `AndType (infer_acc ty) (AndType (infer_acc val) (infer_acc body))` at the
//! ternary `let_` node, a trivially-inhabited `ConstFreeUnit` at the
//! `sort`/`bvar`/`const` leaves, mirroring `const_free`), and each minor is a
//! bare `AndType.left`/`AndType.right` projection of the bundle (the `let_val`
//! and `let_body` minors project the inner sub-bundle). The main proof then
//! supplies the bundle per node: the two structural IHs (`AndType.intro`) at a
//! binary node, the nested `AndType.intro` of the three IHs at the `let_` node,
//! `ConstFreeUnit.triv` at a leaf (whose `subexpr_step` predecessor set is
//! empty, so the obligation is vacuous).
//!
//! ## HONESTY (load-bearing)
//!
//! `terminates_infer := infer_acc := Acc(subexpr_step)` models infer's
//! STRUCTURAL recursion into the immediate children of an expression. It is
//! provable and genuine for exactly that. It does NOT model the WHNF reductions
//! that type inference performs on the types it encounters — that termination is
//! the SEPARATE statement `whnf_terminates_well_typed`
//! (`whnf_terminates_well_typed.rs`, proved for the degenerate context-free
//! `has_type` fragment). This lemma is the child-recursion pillar only; it is
//! NOT a claim of full infer-with-reduction termination.
//!
//! ## Ladder (all `DerivedProved`, zero domain axiom_deps)
//!
//!   1. `childAcc` — `KExpr -> Type`; the immediate-children accessibility
//!      bundle (`AndType (infer_acc l) (infer_acc r)` at binary nodes, the
//!      right-nested `AndType (infer_acc ty) (AndType (infer_acc val)
//!      (infer_acc body))` at the ternary `let_` node, `ConstFreeUnit` at
//!      leaves). Recursive `Type`-valued def, same shape as `const_free`.
//!   2. `subexpr_step_acc_inv` — `subexpr_step c p -> childAcc p -> infer_acc c`;
//!      the nine-constructor `subexpr_step.rec` inversion, each minor an
//!      `AndType.left`/`.right` projection of the bundle.
//!   3. `infer_terminates` — `forall e, terminates_infer e`; `KExpr.rec` on the
//!      motive `infer_acc x`, feeding the child-IH bundle (or `ConstFreeUnit.triv`
//!      at a leaf) to `subexpr_step_acc_inv` under each `infer_acc.intro`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the strict-subexpression accessibility ladder and the retired
    /// census axiom `infer_terminates` as a `DerivedProved` theorem.
    ///
    /// Must run AFTER `add_whnf_reduction` (`KExpr` / `subexpr_step` /
    /// `infer_acc` / the reducible `terminates_infer` alias) and
    /// `add_whnf_progress` (`ConstFreeUnit` / `ConstFreeUnit.triv`); `AndType`
    /// and its projectors come from the foundation layer. Purely additive; zero
    /// new axioms — it REMOVES one (the census axiom flips to a theorem).
    pub(super) fn add_infer_terminates_proof(&mut self) -> Result<(), SpecError> {
        self.add_infer_terminates_childacc()?;
        self.add_infer_terminates_step_inv()?;
        self.add_infer_terminates_theorem()?;
        Ok(())
    }

    /// `childAcc p` — the accessibility bundle of `p`'s immediate children:
    /// `AndType (infer_acc l) (infer_acc r)` at an `app`/`lam`/`pi` node, the
    /// right-nested `AndType (infer_acc ty) (AndType (infer_acc val)
    /// (infer_acc body))` at the ternary `let_` node, `ConstFreeUnit` at a
    /// `sort`/`bvar`/`const` leaf (whose child set under `subexpr_step` is
    /// empty). Recursive `Type`-valued def via `KExpr.rec` large elimination,
    /// byte-for-byte the `const_free` idiom; reduces on constructors, so
    /// `childAcc (KExpr.app f a)` is DEFINITIONALLY
    /// `AndType (infer_acc f) (infer_acc a)` and the `subexpr_step.rec` minors
    /// and the per-node bundle applications type-check without an unfolding
    /// lemma. The recursive-argument slots (`cf`/`ca`/`cv`) are ignored —
    /// `childAcc` depends only on the child EXPRESSIONS, not on their
    /// `childAcc` values.
    fn add_infer_terminates_childacc(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def childAcc (p : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) \
             (fun (n : Level) => ConstFreeUnit) (fun (i : Nat) => ConstFreeUnit) \
             (fun (f : KExpr) (a : KExpr) (cf : Type) (ca : Type) => AndType (infer_acc f) (infer_acc a)) \
             (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType (infer_acc ty) (infer_acc b)) \
             (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType (infer_acc ty) (infer_acc b)) \
             (fun (n : Name) (us : ListType Level) => ConstFreeUnit) \
             (fun (ty : KExpr) (v : KExpr) (b : KExpr) (cty : Type) (cv : Type) (cb : Type) => AndType (infer_acc ty) (AndType (infer_acc v) (infer_acc b))) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (csub : Type) => infer_acc sub) \
             (fun (v : Nat) => ConstFreeUnit) p",
            "childAcc p bundles the accessibility of p's immediate subexpressions: \
             AndType (infer_acc l) (infer_acc r) at an app/lam/pi node, the right-nested \
             AndType (infer_acc ty) (AndType (infer_acc val) (infer_acc body)) at the ternary \
             let_ node, ConstFreeUnit at a sort/bvar/const leaf. Recursive Type-valued def \
             (KExpr.rec large elimination, the const_free idiom), reduces on constructors. The \
             motive of the subexpr_step inversion; supplies the per-node child-accessibility \
             payload to subexpr_step_acc_inv. Part of the infer_terminates retirement.",
        )?;
        Ok(())
    }

    /// `subexpr_step_acc_inv` — the nine-constructor `subexpr_step.rec` inversion.
    /// Motive `childAcc pp -> infer_acc cc`; each minor is a bare
    /// `AndType.left`/`AndType.right` projection of the bundle `childAcc parent`
    /// (which reduces to the matching `AndType` of the child witnesses — a plain
    /// binary `AndType` at `app`/`lam`/`pi`, the right-nested ternary bundle at
    /// `let_`, where `let_val`/`let_body` project the inner sub-bundle). No
    /// impossible-constructor discharge is needed: the `childAcc`-keyed motive
    /// makes every one of the nine minors uniformly a projection.
    fn add_infer_terminates_step_inv(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "subexpr_step_acc_inv".to_string(),
            type_src: "forall (c : KExpr) (p : KExpr), subexpr_step c p -> childAcc p -> infer_acc c"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (c : KExpr) (p : KExpr) (h : subexpr_step c p) => ",
                    "subexpr_step.rec ",
                    "(fun (cc : KExpr) (pp : KExpr) (_ : subexpr_step cc pp) => childAcc pp -> infer_acc cc) ",
                    // app_f f a : childAcc (app f a) -> infer_acc f
                    "(fun (f : KExpr) (a : KExpr) (b : childAcc (KExpr.app f a)) => ",
                    "AndType.left (infer_acc f) (infer_acc a) b) ",
                    // app_a f a : childAcc (app f a) -> infer_acc a
                    "(fun (f : KExpr) (a : KExpr) (b : childAcc (KExpr.app f a)) => ",
                    "AndType.right (infer_acc f) (infer_acc a) b) ",
                    // lam_ty ty body : childAcc (lam ty body) -> infer_acc ty
                    "(fun (ty : KExpr) (body : KExpr) (b : childAcc (KExpr.lam ty body)) => ",
                    "AndType.left (infer_acc ty) (infer_acc body) b) ",
                    // lam_body ty body : childAcc (lam ty body) -> infer_acc body
                    "(fun (ty : KExpr) (body : KExpr) (b : childAcc (KExpr.lam ty body)) => ",
                    "AndType.right (infer_acc ty) (infer_acc body) b) ",
                    // pi_dom ty body : childAcc (pi ty body) -> infer_acc ty
                    "(fun (ty : KExpr) (body : KExpr) (b : childAcc (KExpr.pi ty body)) => ",
                    "AndType.left (infer_acc ty) (infer_acc body) b) ",
                    // pi_cod ty body : childAcc (pi ty body) -> infer_acc body
                    "(fun (ty : KExpr) (body : KExpr) (b : childAcc (KExpr.pi ty body)) => ",
                    "AndType.right (infer_acc ty) (infer_acc body) b) ",
                    // let_ty ty val body : childAcc (let_ ty val body) -> infer_acc ty
                    // childAcc (let_ ty val body) reduces to
                    // AndType (infer_acc ty) (AndType (infer_acc val) (infer_acc body)):
                    // ty is the outer AndType.left, val/body are inside the right sub-bundle.
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (b : childAcc (KExpr.let_ ty val body)) => ",
                    "AndType.left (infer_acc ty) (AndType (infer_acc val) (infer_acc body)) b) ",
                    // let_val ty val body : childAcc (let_ ty val body) -> infer_acc val
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (b : childAcc (KExpr.let_ ty val body)) => ",
                    "AndType.left (infer_acc val) (infer_acc body) ",
                    "(AndType.right (infer_acc ty) (AndType (infer_acc val) (infer_acc body)) b)) ",
                    // let_body ty val body : childAcc (let_ ty val body) -> infer_acc body
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (b : childAcc (KExpr.let_ ty val body)) => ",
                    "AndType.right (infer_acc val) (infer_acc body) ",
                    "(AndType.right (infer_acc ty) (AndType (infer_acc val) (infer_acc body)) b)) ",
                    // proj_sub s i sub : childAcc (proj s i sub) reduces to infer_acc sub,
                    // so the bundle b IS the child accessibility (single child).
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (b : childAcc (KExpr.proj s i sub)) => b) ",
                    // child, parent, major
                    "c p h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "subexpr_step inversion into the child-accessibility bundle: ",
                "subexpr_step c p -> childAcc p -> infer_acc c. subexpr_step.rec with motive ",
                "childAcc pp -> infer_acc cc; each of the nine minors (app_f/app_a/lam_ty/lam_body/",
                "pi_dom/pi_cod/let_ty/let_val/let_body) is a bare AndType.left / AndType.right ",
                "projection of childAcc parent (which reduces to AndType (infer_acc l) (infer_acc r) ",
                "on a binary head, and to the right-nested AndType (infer_acc ty) (AndType ",
                "(infer_acc val) (infer_acc body)) on a let_ head — let_val/let_body project the ",
                "inner sub-bundle). The childAcc-keyed motive makes every minor uniform, so no ",
                "impossible-head discharge is needed. DerivedProved, zero axiom_deps. Part of the ",
                "infer_terminates retirement."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "subexpr_step".to_string(),
                "subexpr_step.rec".to_string(),
                "infer_acc".to_string(),
                "childAcc".to_string(),
                "AndType".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// `infer_terminates` — the retired census axiom, now a `DerivedProved`
    /// theorem. `KExpr.rec` on the motive `infer_acc x`: at each node build
    /// `infer_acc.intro node (fun e' h => ...)` where the predecessor function
    /// inverts the `subexpr_step` witness `h` via `subexpr_step_acc_inv`, fed the
    /// child-accessibility bundle — the two structural IHs
    /// (`AndType.intro ih_l ih_r`) at an `app`/`lam`/`pi` node, the nested
    /// `AndType.intro ih_ty (AndType.intro ih_val ih_body)` of the three IHs at
    /// the ternary `let_` node, or `ConstFreeUnit.triv` at a `sort`/`bvar`/`const`
    /// leaf (whose `subexpr_step` predecessor set is empty, so the obligation is
    /// vacuous). The proof term has type `forall e, infer_acc e`, defeq to the
    /// declared `forall e, terminates_infer e` through the reducible
    /// `terminates_infer` alias.
    fn add_infer_terminates_theorem(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "infer_terminates".to_string(),
            type_src: "forall (e : KExpr), terminates_infer e".to_string(),
            value_src: Some(infer_terminates_proof()),
            is_axiom: false,
            description: concat!(
                "Type inference's structural recursion terminates: forall e, terminates_infer e ",
                "(= infer_acc e, accessibility of e under the immediate-child relation subexpr_step). ",
                "RETIRED census axiom (formerly a HelperAxiom in whnf_lemmas.rs), now a genuine ",
                "zero-domain-axiom theorem — the standard well-founded Acc(subexpr_step) proof. ",
                "KExpr.rec on the motive infer_acc x; every node closes its infer_acc.intro ",
                "predecessor obligation by inverting the subexpr_step witness via ",
                "subexpr_step_acc_inv, supplying the child-IH bundle (AndType.intro of the two ",
                "structural IHs) at app/lam/pi, the nested AndType.intro of the three IHs at the ",
                "ternary let_ node, and ConstFreeUnit.triv at the sort/bvar/const leaves ",
                "(whose subexpr_step predecessor set is empty). terminates_infer is a REDUCIBLE ",
                "one-step alias so the infer_acc e proof term concludes terminates_infer e (the ",
                "#464 Opaque-alias-barrier pattern, mirroring terminates_whnf). HONEST SCOPE: ",
                "terminates_infer models infer's STRUCTURAL recursion into immediate children — ",
                "provable and genuine for exactly that — NOT the WHNF reductions infer performs on ",
                "types (that SN is the separate whnf_terminates_well_typed). It is the ",
                "child-recursion pillar, NOT full infer-with-reduction termination, and NOT ",
                "Godel-blocked as the axiom's original phrasing implied. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "terminates_infer".to_string(),
                "infer_acc".to_string(),
                "infer_acc.intro".to_string(),
                "subexpr_step".to_string(),
                "subexpr_step_acc_inv".to_string(),
                "childAcc".to_string(),
                "KExpr".to_string(),
                "KExpr.rec".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "ConstFreeUnit".to_string(),
                "ConstFreeUnit.triv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

/// Closed proof term for `infer_terminates`. `KExpr.rec` (motive
/// `fun x => infer_acc x`, constructor order sort/bvar/app/lam/pi/const/let_);
/// each node emits `infer_acc.intro node (fun e' h => subexpr_step_acc_inv e'
/// node h bundle)` with the bundle = `AndType.intro` of the two structural IHs
/// at a binary node, the nested `AndType.intro ih_ty (AndType.intro ih_v ih_b)`
/// at the ternary `let_` node, `ConstFreeUnit.triv` at a leaf.
fn infer_terminates_proof() -> String {
    concat!(
        "fun (e : KExpr) => ",
        "KExpr.rec ",
        "(fun (x : KExpr) => infer_acc x) ",
        // sort n — leaf: empty predecessor set, bundle = ConstFreeUnit.triv.
        "(fun (n : Level) => ",
        "infer_acc.intro (KExpr.sort n) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.sort n)) => ",
        "subexpr_step_acc_inv e' (KExpr.sort n) h ConstFreeUnit.triv)) ",
        // bvar i — leaf.
        "(fun (i : Nat) => ",
        "infer_acc.intro (KExpr.bvar i) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.bvar i)) => ",
        "subexpr_step_acc_inv e' (KExpr.bvar i) h ConstFreeUnit.triv)) ",
        // app f a — bundle = AndType.intro ih_f ih_a.
        "(fun (f : KExpr) (a : KExpr) (ih_f : infer_acc f) (ih_a : infer_acc a) => ",
        "infer_acc.intro (KExpr.app f a) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.app f a)) => ",
        "subexpr_step_acc_inv e' (KExpr.app f a) h ",
        "(AndType.intro (infer_acc f) (infer_acc a) ih_f ih_a))) ",
        // lam ty body — bundle = AndType.intro ih_ty ih_body.
        "(fun (ty : KExpr) (body : KExpr) (ih_ty : infer_acc ty) (ih_body : infer_acc body) => ",
        "infer_acc.intro (KExpr.lam ty body) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.lam ty body)) => ",
        "subexpr_step_acc_inv e' (KExpr.lam ty body) h ",
        "(AndType.intro (infer_acc ty) (infer_acc body) ih_ty ih_body))) ",
        // pi ty body — symmetric with lam.
        "(fun (ty : KExpr) (body : KExpr) (ih_ty : infer_acc ty) (ih_body : infer_acc body) => ",
        "infer_acc.intro (KExpr.pi ty body) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.pi ty body)) => ",
        "subexpr_step_acc_inv e' (KExpr.pi ty body) h ",
        "(AndType.intro (infer_acc ty) (infer_acc body) ih_ty ih_body))) ",
        // const nm us — leaf.
        "(fun (nm : Name) (us : ListType Level) => ",
        "infer_acc.intro (KExpr.const nm us) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.const nm us)) => ",
        "subexpr_step_acc_inv e' (KExpr.const nm us) h ConstFreeUnit.triv)) ",
        // let_ ty v b — ternary node: bundle = AndType.intro of ih_ty and the
        // nested AndType.intro of ih_v and ih_b (childAcc (let_ ty v b) reduces to
        // AndType (infer_acc ty) (AndType (infer_acc v) (infer_acc b))).
        "(fun (ty : KExpr) (v : KExpr) (b : KExpr) ",
        "(ih_ty : infer_acc ty) (ih_v : infer_acc v) (ih_b : infer_acc b) => ",
        "infer_acc.intro (KExpr.let_ ty v b) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.let_ ty v b)) => ",
        "subexpr_step_acc_inv e' (KExpr.let_ ty v b) h ",
        "(AndType.intro (infer_acc ty) (AndType (infer_acc v) (infer_acc b)) ih_ty ",
        "(AndType.intro (infer_acc v) (infer_acc b) ih_v ih_b)))) ",
        // proj s i sub — single child: childAcc (proj s i sub) reduces to infer_acc sub.
        "(fun (s : Name) (i : Nat) (sub : KExpr) (ih_sub : infer_acc sub) => ",
        "infer_acc.intro (KExpr.proj s i sub) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.proj s i sub)) => ",
        "subexpr_step_acc_inv e' (KExpr.proj s i sub) h ih_sub)) ",
        // lit v — leaf.
        "(fun (v : Nat) => ",
        "infer_acc.intro (KExpr.lit v) ",
        "(fun (e' : KExpr) (h : subexpr_step e' (KExpr.lit v)) => ",
        "subexpr_step_acc_inv e' (KExpr.lit v) h ConstFreeUnit.triv)) ",
        // major
        "e"
    )
    .to_string()
}

#[cfg(test)]
#[path = "infer_terminates_proof_tests.rs"]
mod infer_terminates_proof_tests;
