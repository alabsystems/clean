// Copyright 2026 Andrew Yates.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iota / whnf / infer closedness bundle (census-11 drain, Stage 2B).
//!
//! Ports the PROVED `hiota` closedness lemma from
//! `scratch/hiota-download/project_aristotle/Hiota.lean`
//! (iota-reduction preserves de Bruijn closedness) as explicit Clean
//! `value_src` terms, conditional on the carried recursor-environment closure
//! interfaces `i3 : RecEnvClosed env` / `i4 : RecEnvLiftClosed env`.
//!
//! Stage 2B-i (this function, `add_iota_closedness_bundle`):
//!   * `AllClosed` — the "every element of a list is closed at depth d" family.
//!   * `AllClosed_append`, `list_tail_preserves_closed`,
//!     `apply_spine_preserves_closed`, `kapp_args_closed`,
//!     `list_drop_preserves_closed`, `list_take_preserves_closed`,
//!     `list_head_closed` — the ~8 structural helpers of the Lean proof.
//!   * `kexpr_bvar_inj`, `nat_lt_ne`, `lift_invariant_closed` — the lift-
//!     invariance -> closed bridge (the rhs-closedness step).
//!   * `hiota_generic` — the env-GENERIC `iota_step env e e' -> is_closed_at e d
//!     -> is_closed_at e' d`, proved by inverting `iota_reduct` via the in-tree
//!     CPS inverter `iota_reduct_some_inv` (five opt_bind levels) and composing
//!     `apply_spine_preserves_closed` three times over the reduct segments.
//!   * `hiota` — the PINNED form `iota_reduces e e' -> is_closed_at e d ->
//!     is_closed_at e' d` (carrying `i3 : RecEnvClosed (red_rec the_red_env)` /
//!     `i4 : RecEnvLiftClosed (red_rec the_red_env)`), the literal shape the beta
//!     bundle's iota arm consumes; unwraps `iota_reduces` via
//!     `iota_reduces_to_step` and applies `hiota_generic`.
//!
//! Every term kernel-verifies with an EMPTY (foundational-only) axiom closure:
//! the proofs use only the in-tree iota machinery + Lt/Le arithmetic + the
//! carried i3/i4 closure interfaces (which are TYPE hypotheses, not axioms).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_iota_closedness_bundle(&mut self) -> Result<(), SpecError> {
        // ================================================================
        // AllClosed: every element of a KExpr list is closed at depth d.
        // ================================================================
        self.add_inductive(
            "inductive AllClosed : ListType KExpr -> Nat -> Type\n\
             | nil : forall (d : Nat), AllClosed (ListType.nil KExpr) d\n\
             | cons : forall (x : KExpr) (xs : ListType KExpr) (d : Nat), is_closed_at x d -> AllClosed xs d -> AllClosed (ListType.cons KExpr x xs) d",
            "AllClosed xs d holds if every element of the KExpr list xs is closed at de Bruijn depth d. \
             Structural companion of is_closed_at for application-spine argument lists (the iota reduct \
             is built by apply_spine over kapp_args-derived lists). Part of the census-11 drain (Stage 2B).",
        )?;

        // AllClosed_append: AllClosed is preserved by list_append.
        self.add_definition(SpecDefinition {
            name: "AllClosed_append".to_string(),
            type_src: concat!(
                "forall (xs : ListType KExpr) (ys : ListType KExpr) (d : Nat), ",
                "AllClosed xs d -> AllClosed ys d -> AllClosed (list_append xs ys) d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (xs : ListType KExpr) (ys : ListType KExpr) (d : Nat) ",
                    "(hxs : AllClosed xs d) (hys : AllClosed ys d) => ",
                    "AllClosed.rec ",
                    "(fun (l : ListType KExpr) (n : Nat) (_ : AllClosed l n) => AllClosed ys n -> AllClosed (list_append l ys) n) ",
                    "(fun (d0 : Nat) => fun (hy : AllClosed ys d0) => hy) ",
                    "(fun (x : KExpr) (xs0 : ListType KExpr) (d0 : Nat) (hx : is_closed_at x d0) (hrest : AllClosed xs0 d0) ",
                    "(ih : AllClosed ys d0 -> AllClosed (list_append xs0 ys) d0) => ",
                    "fun (hy : AllClosed ys d0) => AllClosed.cons x (list_append xs0 ys) d0 hx (ih hy)) ",
                    "xs d hxs hys"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "AllClosed is preserved by list_append: AllClosed xs d -> AllClosed ys d -> AllClosed (list_append xs ys) d. DerivedProved via AllClosed.rec (motive carries the ys hypothesis). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "AllClosed.rec".to_string(),
                "AllClosed.cons".to_string(),
                "list_append".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_tail_preserves_closed: AllClosed is preserved by list_tail.
        self.add_definition(SpecDefinition {
            name: "list_tail_preserves_closed".to_string(),
            type_src: concat!(
                "forall (xs : ListType KExpr) (d : Nat), ",
                "AllClosed xs d -> AllClosed (list_tail xs) d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (xs : ListType KExpr) (d : Nat) (h : AllClosed xs d) => ",
                    "AllClosed.rec ",
                    "(fun (l : ListType KExpr) (n : Nat) (_ : AllClosed l n) => AllClosed (list_tail l) n) ",
                    "(fun (d0 : Nat) => AllClosed.nil d0) ",
                    "(fun (x : KExpr) (xs0 : ListType KExpr) (d0 : Nat) (hx : is_closed_at x d0) (hrest : AllClosed xs0 d0) ",
                    "(ih : AllClosed (list_tail xs0) d0) => hrest) ",
                    "xs d h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "AllClosed is preserved by list_tail (list_tail (cons x xs) = xs, list_tail nil = nil). DerivedProved via AllClosed.rec. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "AllClosed.rec".to_string(),
                "AllClosed.nil".to_string(),
                "list_tail".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_drop_preserves_closed: AllClosed is preserved by list_drop n.
        self.add_definition(SpecDefinition {
            name: "list_drop_preserves_closed".to_string(),
            type_src: concat!(
                "forall (n : Nat) (xs : ListType KExpr) (d : Nat), ",
                "AllClosed xs d -> AllClosed (list_drop n xs) d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (xs : ListType KExpr) (d : Nat) (h : AllClosed xs d) => ",
                    "Nat.rec ",
                    "(fun (k : Nat) => forall (l : ListType KExpr), AllClosed l d -> AllClosed (list_drop k l) d) ",
                    "(fun (l : ListType KExpr) (hl : AllClosed l d) => hl) ",
                    "(fun (m : Nat) (ih : forall (l : ListType KExpr), AllClosed l d -> AllClosed (list_drop m l) d) => ",
                    "fun (l : ListType KExpr) (hl : AllClosed l d) => ih (list_tail l) (list_tail_preserves_closed l d hl)) ",
                    "n xs h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "AllClosed is preserved by list_drop n (list_drop (succ m) xs = list_drop m (list_tail xs)). DerivedProved via Nat.rec + list_tail_preserves_closed. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "Nat.rec".to_string(),
                "list_drop".to_string(),
                "list_tail".to_string(),
                "list_tail_preserves_closed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_take_preserves_closed: AllClosed is preserved by list_take n.
        self.add_definition(SpecDefinition {
            name: "list_take_preserves_closed".to_string(),
            type_src: concat!(
                "forall (n : Nat) (xs : ListType KExpr) (d : Nat), ",
                "AllClosed xs d -> AllClosed (list_take n xs) d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (xs : ListType KExpr) (d : Nat) (hxs : AllClosed xs d) => ",
                    "AllClosed.rec ",
                    "(fun (l : ListType KExpr) (nn : Nat) (_ : AllClosed l nn) => forall (k : Nat), AllClosed (list_take k l) nn) ",
                    // nil branch: list_take k nil = nil for all k.
                    "(fun (d0 : Nat) => fun (k : Nat) => ",
                    "Nat.rec (fun (kk : Nat) => AllClosed (list_take kk (ListType.nil KExpr)) d0) ",
                    "(AllClosed.nil d0) ",
                    "(fun (m : Nat) (_ : AllClosed (list_take m (ListType.nil KExpr)) d0) => AllClosed.nil d0) ",
                    "k) ",
                    // cons branch
                    "(fun (x : KExpr) (xs0 : ListType KExpr) (d0 : Nat) (hx : is_closed_at x d0) (hrest : AllClosed xs0 d0) ",
                    "(ih : forall (k : Nat), AllClosed (list_take k xs0) d0) => ",
                    "fun (k : Nat) => ",
                    "Nat.rec (fun (kk : Nat) => AllClosed (list_take kk (ListType.cons KExpr x xs0)) d0) ",
                    "(AllClosed.nil d0) ",
                    "(fun (m : Nat) (_ : AllClosed (list_take m (ListType.cons KExpr x xs0)) d0) => ",
                    "AllClosed.cons x (list_take m xs0) d0 hx (ih m)) ",
                    "k) ",
                    "xs d hxs n"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "AllClosed is preserved by list_take n (list_take 0 xs = nil, list_take (succ m)(cons x xs) = cons x (list_take m xs)). DerivedProved via AllClosed.rec (count generalized) + Nat.rec case-split. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "AllClosed.rec".to_string(),
                "AllClosed.nil".to_string(),
                "AllClosed.cons".to_string(),
                "Nat.rec".to_string(),
                "list_take".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // apply_spine_preserves_closed: a closed head onto closed args is closed.
        self.add_definition(SpecDefinition {
            name: "apply_spine_preserves_closed".to_string(),
            type_src: concat!(
                "forall (args : ListType KExpr) (head : KExpr) (d : Nat), ",
                "AllClosed args d -> is_closed_at head d -> is_closed_at (apply_spine args head) d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (args : ListType KExpr) (head : KExpr) (d : Nat) ",
                    "(hargs : AllClosed args d) (hh : is_closed_at head d) => ",
                    "AllClosed.rec ",
                    "(fun (l : ListType KExpr) (n : Nat) (_ : AllClosed l n) => forall (h0 : KExpr), is_closed_at h0 n -> is_closed_at (apply_spine l h0) n) ",
                    "(fun (d0 : Nat) => fun (h0 : KExpr) (hh0 : is_closed_at h0 d0) => hh0) ",
                    "(fun (x : KExpr) (xs0 : ListType KExpr) (d0 : Nat) (hx : is_closed_at x d0) (hrest : AllClosed xs0 d0) ",
                    "(ih : forall (h0 : KExpr), is_closed_at h0 d0 -> is_closed_at (apply_spine xs0 h0) d0) => ",
                    "fun (h0 : KExpr) (hh0 : is_closed_at h0 d0) => ih (KExpr.app h0 x) (is_closed_at.app h0 x d0 hh0 hx)) ",
                    "args d hargs head hh"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "apply_spine of a closed head onto closed args is closed: AllClosed args d -> is_closed_at head d -> is_closed_at (apply_spine args head) d. DerivedProved via AllClosed.rec (head generalized; apply_spine (cons x rest) h = apply_spine rest (app h x)). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "AllClosed.rec".to_string(),
                "apply_spine".to_string(),
                "is_closed_at.app".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_args_closed: the args of a closed expression are all closed.
        self.add_definition(SpecDefinition {
            name: "kapp_args_closed".to_string(),
            type_src: "forall (e : KExpr) (d : Nat), is_closed_at e d -> AllClosed (kapp_args e) d".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (d : Nat) (hc : is_closed_at e d) => ",
                    "is_closed_at.rec ",
                    "(fun (e0 : KExpr) (D : Nat) (_hc : is_closed_at e0 D) => AllClosed (kapp_args e0) D) ",
                    // sort
                    "(fun (nn : Level) (D : Nat) => AllClosed.nil D) ",
                    // bvar
                    "(fun (i : Nat) (D : Nat) (hlt : Lt i D) => AllClosed.nil D) ",
                    // app
                    "(fun (f : KExpr) (a : KExpr) (D : Nat) (_hf : is_closed_at f D) (ha : is_closed_at a D) ",
                    "(ihf : AllClosed (kapp_args f) D) (_iha : AllClosed (kapp_args a) D) => ",
                    "AllClosed_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)) D ihf ",
                    "(AllClosed.cons a (ListType.nil KExpr) D ha (AllClosed.nil D))) ",
                    // lam
                    "(fun (ty : KExpr) (body : KExpr) (D : Nat) (_hty : is_closed_at ty D) (_hbody : is_closed_at body (Nat.succ D)) ",
                    "(_ihty : AllClosed (kapp_args ty) D) (_ihbody : AllClosed (kapp_args body) (Nat.succ D)) => AllClosed.nil D) ",
                    // pi
                    "(fun (ty : KExpr) (body : KExpr) (D : Nat) (_hty : is_closed_at ty D) (_hbody : is_closed_at body (Nat.succ D)) ",
                    "(_ihty : AllClosed (kapp_args ty) D) (_ihbody : AllClosed (kapp_args body) (Nat.succ D)) => AllClosed.nil D) ",
                    // const
                    "(fun (nm : Name) (us : ListType Level) (D : Nat) => AllClosed.nil D) ",
                    // let_ (a let is its own spine head: kapp_args (let_ ...) = nil)
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (D : Nat) (_hty : is_closed_at ty D) (_hval : is_closed_at val D) (_hbody : is_closed_at body (Nat.succ D)) ",
                    "(_ihty : AllClosed (kapp_args ty) D) (_ihval : AllClosed (kapp_args val) D) (_ihbody : AllClosed (kapp_args body) (Nat.succ D)) => AllClosed.nil D) ",
                    // proj/lit are their own spine heads (kapp_args = nil), like let_/const.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (D : Nat) (_hsub : is_closed_at sub D) (_ihsub : AllClosed (kapp_args sub) D) => AllClosed.nil D) ",
                    "(fun (v : Nat) (D : Nat) => AllClosed.nil D) ",
                    "e d hc"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The args of a closed expression are all closed: is_closed_at e d -> AllClosed (kapp_args e) d. DerivedProved via is_closed_at.rec (app arm uses AllClosed_append; the non-app arms have nil kapp_args). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "AllClosed.nil".to_string(),
                "AllClosed.cons".to_string(),
                "AllClosed_append".to_string(),
                "is_closed_at.rec".to_string(),
                "kapp_args".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_head_closed: the head of an AllClosed list is closed.
        self.add_definition(SpecDefinition {
            name: "list_head_closed".to_string(),
            type_src: concat!(
                "forall (xs : ListType KExpr) (x : KExpr) (d : Nat), ",
                "Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr x) -> ",
                "AllClosed xs d -> is_closed_at x d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (xs : ListType KExpr) (x : KExpr) (d : Nat) ",
                    "(hhd : Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr x)) ",
                    "(hall : AllClosed xs d) => ",
                    "AllClosed.rec ",
                    "(fun (l : ListType KExpr) (n : Nat) (_ : AllClosed l n) => ",
                    "Eq (OptionType KExpr) (list_head l) (OptionType.some KExpr x) -> is_closed_at x n) ",
                    // nil branch: list_head nil = none; none = some x is absurd
                    // (Type-valued discrimination via opt_is_none: is_closed_at is
                    // Type, not Prop, so option_none_ne_some (Prop-only) is unusable).
                    "(fun (d0 : Nat) => fun (hn : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr x)) => ",
                    "Empty.rec (fun (_ : Empty) => is_closed_at x d0) ",
                    "(Eq.substType (OptionType KExpr) (opt_is_none KExpr) (OptionType.none KExpr) (OptionType.some KExpr x) hn Nat.zero)) ",
                    // cons branch: list_head (cons y rest) = some y; some y = some x => y = x.
                    "(fun (y : KExpr) (rest : ListType KExpr) (d0 : Nat) (hy : is_closed_at y d0) (hrest : AllClosed rest d0) ",
                    "(_ih : Eq (OptionType KExpr) (list_head rest) (OptionType.some KExpr x) -> is_closed_at x d0) => ",
                    "fun (hc : Eq (OptionType KExpr) (OptionType.some KExpr y) (OptionType.some KExpr x)) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d0) y x (option_some_inj KExpr y x hc) hy) ",
                    "xs d hall hhd"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The head of an AllClosed list is closed: list_head xs = some x -> AllClosed xs d -> is_closed_at x d. DerivedProved via AllClosed.rec (nil: option_none_ne_some; cons: option_some_inj + Eq.substType). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AllClosed".to_string(),
                "AllClosed.rec".to_string(),
                "list_head".to_string(),
                "opt_is_none".to_string(),
                "Empty.rec".to_string(),
                "option_some_inj".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kexpr_bvar_inj: bvar injectivity via a KExpr.rec index projector.
        self.add_definition(SpecDefinition {
            name: "kexpr_bvar_inj".to_string(),
            type_src: "forall (m : Nat) (n : Nat), Eq KExpr (KExpr.bvar m) (KExpr.bvar n) -> Eq Nat m n".to_string(),
            value_src: Some(
                concat!(
                    "fun (m : Nat) (n : Nat) (h : Eq KExpr (KExpr.bvar m) (KExpr.bvar n)) => ",
                    "Eq.cong KExpr Nat ",
                    "(fun (e0 : KExpr) => KExpr.rec (fun (_ : KExpr) => Nat) ",
                    "(fun (k : Level) => Nat.zero) ",
                    "(fun (i : Nat) => i) ",
                    "(fun (f : KExpr) (a : KExpr) (_ : Nat) (_ : Nat) => Nat.zero) ",
                    "(fun (ty : KExpr) (b : KExpr) (_ : Nat) (_ : Nat) => Nat.zero) ",
                    "(fun (ty : KExpr) (b : KExpr) (_ : Nat) (_ : Nat) => Nat.zero) ",
                    "(fun (nm : Name) (us : ListType Level) => Nat.zero) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) (_ : Nat) => Nat.zero) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Nat) => Nat.zero) ",
                    "(fun (_ : Nat) => Nat.zero) ",
                    "e0) ",
                    "(KExpr.bvar m) (KExpr.bvar n) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "bvar injectivity: bvar m = bvar n -> m = n. DerivedProved via Eq.cong through a KExpr.rec index projector (bvar i -> i, else 0). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_lt_ne: Lt a b and Eq a b are incompatible.
        self.add_definition(SpecDefinition {
            name: "nat_lt_ne".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a b -> Eq Nat a b -> Empty".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (hlt : Lt a b) => ",
                    "Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => Eq Nat x y -> Empty) ",
                    "(fun (nn : Nat) => fun (heq : Eq Nat Nat.zero (Nat.succ nn)) => nat_zero_ne_succ nn Empty heq) ",
                    "(fun (nn : Nat) (mm : Nat) (_hlt : Lt nn mm) (ih : Eq Nat nn mm -> Empty) => ",
                    "fun (heq : Eq Nat (Nat.succ nn) (Nat.succ mm)) => ih (nat_succ_inj nn mm heq)) ",
                    "a b hlt"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Lt a b and Eq Nat a b are incompatible: Lt a b -> Eq Nat a b -> Empty. DerivedProved via Lt.rec (zero_lt_succ: nat_zero_ne_succ; succ_lt_succ: nat_succ_inj + IH). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt.rec".to_string(),
                "nat_zero_ne_succ".to_string(),
                "nat_succ_inj".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_invariant_closed: if lifting by a positive amount is a no-op then
        // the expression is closed at the cutoff.
        self.add_definition(SpecDefinition {
            name: "lift_invariant_closed".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (c : Nat) (a : Nat), ",
                "Eq KExpr (lift_at e c (Nat.succ a)) e -> is_closed_at e c"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (c : Nat) (a : Nat) (h : Eq KExpr (lift_at e c (Nat.succ a)) e) => ",
                    "KExpr.rec ",
                    "(fun (e0 : KExpr) => forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at e0 c0 (Nat.succ a0)) e0 -> is_closed_at e0 c0) ",
                    // sort
                    "(fun (nn : Level) => fun (c0 : Nat) (a0 : Nat) (_h : Eq KExpr (lift_at (KExpr.sort nn) c0 (Nat.succ a0)) (KExpr.sort nn)) => is_closed_at.sort nn c0) ",
                    // bvar
                    "(fun (i : Nat) => fun (c0 : Nat) (a0 : Nat) (hb : Eq KExpr (lift_at (KExpr.bvar i) c0 (Nat.succ a0)) (KExpr.bvar i)) => ",
                    "NatLtLeDichotomy.rec i c0 ",
                    "(fun (_dch : NatLtLeDichotomy i c0) => is_closed_at (KExpr.bvar i) c0) ",
                    "(fun (hic : Lt i c0) => is_closed_at.bvar i c0 hic) ",
                    "(fun (hci : Le c0 i) => ",
                    "Empty.rec (fun (_ : Empty) => is_closed_at (KExpr.bvar i) c0) ",
                    "(nat_lt_ne i (Nat.add i (Nat.succ a0)) ",
                    "(Eq.substType Nat (fun (z : Nat) => Lt i z) (Nat.add (Nat.succ i) a0) (Nat.succ (Nat.add i a0)) (nat_succ_add i a0) ",
                    "(lt_add_weaken_right i (Nat.succ i) a0 (lt_succ_self i))) ",
                    "(Eq.symm Nat (Nat.add i (Nat.succ a0)) i ",
                    "(kexpr_bvar_inj (Nat.add i (Nat.succ a0)) i ",
                    "(Eq.trans KExpr (KExpr.bvar (Nat.add i (Nat.succ a0))) (lift_at (KExpr.bvar i) c0 (Nat.succ a0)) (KExpr.bvar i) ",
                    "(Eq.symm KExpr (lift_at (KExpr.bvar i) c0 (Nat.succ a0)) (KExpr.bvar (Nat.add i (Nat.succ a0))) ",
                    "(lift_at_bvar_geq i c0 (Nat.succ a0) (le_sub_zero c0 i hci))) ",
                    "hb))))) ",
                    "(nat_lt_le_dichotomy i c0)) ",
                    // app
                    "(fun (f : KExpr) (a2 : KExpr) (ihf : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at f c0 (Nat.succ a0)) f -> is_closed_at f c0) ",
                    "(iha : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at a2 c0 (Nat.succ a0)) a2 -> is_closed_at a2 c0) => ",
                    "fun (c0 : Nat) (a0 : Nat) (happ : Eq KExpr (lift_at (KExpr.app f a2) c0 (Nat.succ a0)) (KExpr.app f a2)) => ",
                    "is_closed_at.app f a2 c0 ",
                    "(ihf c0 a0 (app_inj_fst (lift_at f c0 (Nat.succ a0)) (lift_at a2 c0 (Nat.succ a0)) f a2 happ)) ",
                    "(iha c0 a0 (app_inj_snd (lift_at f c0 (Nat.succ a0)) (lift_at a2 c0 (Nat.succ a0)) f a2 happ))) ",
                    // lam
                    "(fun (ty : KExpr) (body : KExpr) (ihty : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at ty c0 (Nat.succ a0)) ty -> is_closed_at ty c0) ",
                    "(ihbody : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at body c0 (Nat.succ a0)) body -> is_closed_at body c0) => ",
                    "fun (c0 : Nat) (a0 : Nat) (hlam : Eq KExpr (lift_at (KExpr.lam ty body) c0 (Nat.succ a0)) (KExpr.lam ty body)) => ",
                    "is_closed_at.lam ty body c0 ",
                    "(ihty c0 a0 (lam_inj_fst (lift_at ty c0 (Nat.succ a0)) (lift_at body (Nat.succ c0) (Nat.succ a0)) ty body hlam)) ",
                    "(ihbody (Nat.succ c0) a0 (lam_inj_snd (lift_at ty c0 (Nat.succ a0)) (lift_at body (Nat.succ c0) (Nat.succ a0)) ty body hlam))) ",
                    // pi
                    "(fun (ty : KExpr) (body : KExpr) (ihty : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at ty c0 (Nat.succ a0)) ty -> is_closed_at ty c0) ",
                    "(ihbody : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at body c0 (Nat.succ a0)) body -> is_closed_at body c0) => ",
                    "fun (c0 : Nat) (a0 : Nat) (hpi : Eq KExpr (lift_at (KExpr.pi ty body) c0 (Nat.succ a0)) (KExpr.pi ty body)) => ",
                    "is_closed_at.pi ty body c0 ",
                    "(ihty c0 a0 (pi_inj_fst (lift_at ty c0 (Nat.succ a0)) (lift_at body (Nat.succ c0) (Nat.succ a0)) ty body hpi)) ",
                    "(ihbody (Nat.succ c0) a0 (pi_inj_snd (lift_at ty c0 (Nat.succ a0)) (lift_at body (Nat.succ c0) (Nat.succ a0)) ty body hpi))) ",
                    // const
                    "(fun (nm : Name) (us : ListType Level) => fun (c0 : Nat) (a0 : Nat) (_h : Eq KExpr (lift_at (KExpr.const nm us) c0 (Nat.succ a0)) (KExpr.const nm us)) => is_closed_at.const nm us c0) ",
                    // let_ (ty/val at cutoff, body at succ cutoff; field sub-equations
                    // via inline KExpr.rec projector injectivity, the lam_inj technique)
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(ihty : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at ty c0 (Nat.succ a0)) ty -> is_closed_at ty c0) ",
                    "(ihval : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at val c0 (Nat.succ a0)) val -> is_closed_at val c0) ",
                    "(ihbody : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at body c0 (Nat.succ a0)) body -> is_closed_at body c0) => ",
                    "fun (c0 : Nat) (a0 : Nat) (hlet : Eq KExpr (lift_at (KExpr.let_ ty val body) c0 (Nat.succ a0)) (KExpr.let_ ty val body)) => ",
                    "is_closed_at.let_ ty val body c0 ",
                    "(ihty c0 a0 (Eq.cong KExpr KExpr ",
                    "(fun (e0 : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => ty) (fun (_ : Nat) => ty) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => ty) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => ty) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => ty) ",
                    "(fun (_ : Name) (_ : ListType Level) => ty) ",
                    "(fun (t : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => ty) ",
                    "(fun (_ : Nat) => ty) ",
                    "e0) ",
                    "(lift_at (KExpr.let_ ty val body) c0 (Nat.succ a0)) (KExpr.let_ ty val body) hlet)) ",
                    "(ihval c0 a0 (Eq.cong KExpr KExpr ",
                    "(fun (e0 : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => val) (fun (_ : Nat) => val) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => val) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => val) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => val) ",
                    "(fun (_ : Name) (_ : ListType Level) => val) ",
                    "(fun (_ : KExpr) (v : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => v) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => val) ",
                    "(fun (_ : Nat) => val) ",
                    "e0) ",
                    "(lift_at (KExpr.let_ ty val body) c0 (Nat.succ a0)) (KExpr.let_ ty val body) hlet)) ",
                    "(ihbody (Nat.succ c0) a0 (Eq.cong KExpr KExpr ",
                    "(fun (e0 : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => body) (fun (_ : Nat) => body) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => body) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => body) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => body) ",
                    "(fun (_ : Name) (_ : ListType Level) => body) ",
                    "(fun (_ : KExpr) (_ : KExpr) (bb : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => bb) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => body) ",
                    "(fun (_ : Nat) => body) ",
                    "e0) ",
                    "(lift_at (KExpr.let_ ty val body) c0 (Nat.succ a0)) (KExpr.let_ ty val body) hlet))) ",
                    // proj: extract the sub-field equation via the inline projector, recurse.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ihsub : forall (c0 : Nat) (a0 : Nat), Eq KExpr (lift_at sub c0 (Nat.succ a0)) sub -> is_closed_at sub c0) => ",
                    "fun (c0 : Nat) (a0 : Nat) (hproj : Eq KExpr (lift_at (KExpr.proj s i sub) c0 (Nat.succ a0)) (KExpr.proj s i sub)) => ",
                    "is_closed_at.proj s i sub c0 ",
                    "(ihsub c0 a0 (Eq.cong KExpr KExpr ",
                    "(fun (e0 : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => sub) (fun (_ : Nat) => sub) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => sub) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => sub) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => sub) ",
                    "(fun (_ : Name) (_ : ListType Level) => sub) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => sub) ",
                    "(fun (_ : Name) (_ : Nat) (psub : KExpr) (_ : KExpr) => psub) ",
                    "(fun (_ : Nat) => sub) ",
                    "e0) ",
                    "(lift_at (KExpr.proj s i sub) c0 (Nat.succ a0)) (KExpr.proj s i sub) hproj))) ",
                    // lit: literals carry no bvars, so unconditionally closed.
                    "(fun (v : Nat) => fun (c0 : Nat) (a0 : Nat) (_hlit : Eq KExpr (lift_at (KExpr.lit v) c0 (Nat.succ a0)) (KExpr.lit v)) => is_closed_at.lit v c0) ",
                    "e c a h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Lift-invariance -> closed: lift_at e c (succ a) = e -> is_closed_at e c. DerivedProved via KExpr.rec; bvar arm decides i<c (closed) vs c<=i (contradiction: lift shifts to i + succ a /= i via kexpr_bvar_inj + nat_lt_ne); app/lam/pi use the injectivity lemmas + IHs; let_ uses inline KExpr.rec field-projector injectivity (Eq.cong), ty/val at the cutoff, body at succ cutoff. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "is_closed_at.sort".to_string(),
                "is_closed_at.bvar".to_string(),
                "is_closed_at.app".to_string(),
                "is_closed_at.lam".to_string(),
                "is_closed_at.pi".to_string(),
                "is_closed_at.const".to_string(),
                "is_closed_at.let_".to_string(),
                "is_closed_at.proj".to_string(),
                "is_closed_at.lit".to_string(),
                "NatLtLeDichotomy.rec".to_string(),
                "nat_lt_le_dichotomy".to_string(),
                "lift_at_bvar_geq".to_string(),
                "le_sub_zero".to_string(),
                "kexpr_bvar_inj".to_string(),
                "nat_lt_ne".to_string(),
                "nat_succ_add".to_string(),
                "lt_add_weaken_right".to_string(),
                "lt_succ_self".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "pi_inj_fst".to_string(),
                "pi_inj_snd".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // Type-valued CPS inverters. The in-tree opt_bind_some_inv /
        // iota_reduct_some_inv conclude in `C : Prop` (they discriminate none
        // vs some via option_none_ne_some, whose R is a Prop). hiota_generic must
        // conclude in `is_closed_at e' d`, which is Type-valued, so it needs the
        // Type-valued mirrors below (none-vs-some discriminated via opt_is_none +
        // Empty.rec, the Type-valued no-confusion).
        // ================================================================

        // opt_bind_some_inv_T: Type-valued CPS inversion of opt_bind.
        self.add_definition(SpecDefinition {
            name: "opt_bind_some_inv_T".to_string(),
            type_src: concat!(
                "forall (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type), ",
                "Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r) -> ",
                "(forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type) ",
                    "(h : Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r)) ",
                    "(k : forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) => ",
                    "OptionType.rec a ",
                    "(fun (o0 : OptionType a) => ",
                    "Eq (OptionType b) (opt_bind a b o0 f) (OptionType.some b r) -> ",
                    "(forall (w : a), Eq (OptionType a) o0 (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> C) ",
                    "(fun (h0 : Eq (OptionType b) (opt_bind a b (OptionType.none a) f) (OptionType.some b r)) ",
                    "(k0 : forall (w : a), Eq (OptionType a) (OptionType.none a) (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType (OptionType b) (opt_is_none b) (OptionType.none b) (OptionType.some b r) h0 Nat.zero)) ",
                    "(fun (w : a) ",
                    "(h0 : Eq (OptionType b) (opt_bind a b (OptionType.some a w) f) (OptionType.some b r)) ",
                    "(k0 : forall (w0 : a), Eq (OptionType a) (OptionType.some a w) (OptionType.some a w0) -> ",
                    "Eq (OptionType b) (f w0) (OptionType.some b r) -> C) => ",
                    "k0 w (Eq.refl (OptionType a) (OptionType.some a w)) h0) ",
                    "o h k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Type-valued CPS inversion of opt_bind: opt_bind o f = some r yields a witness w with o = some w and f w = some r, delivered to a Type-valued continuation. The Type mirror of opt_bind_some_inv (none branch discriminated via opt_is_none + Empty.rec instead of the Prop-only option_none_ne_some). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "OptionType.rec".to_string(),
                "opt_is_none".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_reduct_some_inv_T: Type-valued mirror of iota_reduct_some_inv
        // (five nested opt_bind_some_inv_T). Recovers the five intermediate
        // witnesses + lookup equations + reduct equation, delivered to a
        // Type-valued continuation.
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let extras = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
            let fields = "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))";
            let prefix = format!("(list_take {prefix_n} (kapp_args e))");
            let reduct = format!(
                "(apply_spine {extras} (apply_spine {fields} (apply_spine {prefix} (recrule_rhs rule))))"
            );

            let l6 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct})");
            let l5 = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {l6})"
            );
            let l4 = format!(
                "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {l5})"
            );
            let l3 = format!("(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e))) {l4})");
            let l2 = format!(
                "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {l3})"
            );

            let kont = format!(
                "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> \
                 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                 Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major) -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 C)"
            );

            let value = format!(
                "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Type) \
                 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')) \
                 (k : {kont}) => \
                 opt_bind_some_inv_T Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
                 (fun (recname : Name) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h1r : Eq (OptionType KExpr) ({l2} recname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_T RecMeta KExpr (recmeta_for env recname) {l3} e' C h1r \
                 (fun (meta : RecMeta) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h2r : Eq (OptionType KExpr) ({l3} meta) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_T KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e))) {l4} e' C h2r \
                 (fun (major : KExpr) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
                 (h3r : Eq (OptionType KExpr) ({l4} major) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_T Name KExpr (kexpr_const_name (kapp_fn major)) {l5} e' C h3r \
                 (fun (cname : Name) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h4r : Eq (OptionType KExpr) ({l5} cname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_T RecRule KExpr (recrule_for env recname cname) {l6} e' C h4r \
                 (fun (rule : RecRule) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) ({l6} rule) (OptionType.some KExpr e')) => \
                 k recname meta major cname rule h1 h2 h3 h4 h5 h5r))))))"
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_some_inv_T".to_string(),
                type_src: format!(
                    "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Type), \
                     Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e') -> {kont} -> C"
                ),
                value_src: Some(value),
                is_axiom: false,
                description: "Type-valued mirror of iota_reduct_some_inv: from iota_reduct env e = some e', recover the recursor name, metadata, major premise, constructor name and rule with each lookup equation and the reduct equation, delivered to a Type-valued continuation. Five nested opt_bind_some_inv_T. DerivedProved, zero axiom_deps.".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "opt_bind_some_inv_T".to_string(),
                    "kexpr_const_name".to_string(),
                    "recmeta_for".to_string(),
                    "recrule_for".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // ================================================================
        // hiota_generic: the env-generic iota-closedness preservation, via the
        // Type-valued CPS inverter iota_reduct_some_inv_T (five opt_bind levels).
        // ================================================================
        {
            // The arithmetic + reduct sub-terms of iota_reduct (verbatim from its
            // def / from iota_reduct_some_inv's kont), so the continuation binder
            // types and the reduct match the inverter's output exactly.
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let extras = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
            let fields = "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))";
            let prefix = format!("(list_take {prefix_n} (kapp_args e))");
            let reduct = format!(
                "(apply_spine {extras} (apply_spine {fields} (apply_spine {prefix} (recrule_rhs rule))))"
            );

            // The continuation delivered to iota_reduct_some_inv.
            let kont_body = format!(
                "fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e')) => \
                 Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d) {reduct} e' \
                 (option_some_inj KExpr {reduct} e' h5r) \
                 (apply_spine_preserves_closed {extras} (apply_spine {fields} (apply_spine {prefix} (recrule_rhs rule))) d \
                 (list_drop_preserves_closed (Nat.succ {major_idx}) (kapp_args e) d (kapp_args_closed e d hc)) \
                 (apply_spine_preserves_closed {fields} (apply_spine {prefix} (recrule_rhs rule)) d \
                 (list_drop_preserves_closed (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major) d \
                 (kapp_args_closed major d \
                 (list_head_closed (list_drop {major_idx} (kapp_args e)) major d h3 \
                 (list_drop_preserves_closed {major_idx} (kapp_args e) d (kapp_args_closed e d hc))))) \
                 (apply_spine_preserves_closed {prefix} (recrule_rhs rule) d \
                 (list_take_preserves_closed {prefix_n} (kapp_args e) d (kapp_args_closed e d hc)) \
                 (lift_invariant_closed (recrule_rhs rule) d Nat.zero \
                 (recenv_lift_closed_rhs env recname cname rule d (Nat.succ Nat.zero) i4 h5)))))"
            );

            let value = format!(
                "fun (env : RecEnv) (i3 : RecEnvClosed env) (i4 : RecEnvLiftClosed env) \
                 (e : KExpr) (e' : KExpr) (d : Nat) (hstep : iota_step env e e') (hc : is_closed_at e d) => \
                 iota_reduct_some_inv_T env e e' (is_closed_at e' d) hstep ({kont_body})"
            );

            self.add_definition(SpecDefinition {
                name: "hiota_generic".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (i3 : RecEnvClosed env) (i4 : RecEnvLiftClosed env) ",
                    "(e : KExpr) (e' : KExpr) (d : Nat), ",
                    "iota_step env e e' -> is_closed_at e d -> is_closed_at e' d"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "Env-generic iota-reduction preserves closedness: iota_step env e e' -> is_closed_at e d ",
                    "-> is_closed_at e' d, conditional on the carried closure interfaces i3 : RecEnvClosed env ",
                    "(unused here, threaded for parity) and i4 : RecEnvLiftClosed env (the rule-rhs is lift-",
                    "invariant hence closed). DerivedProved by inverting iota_reduct via iota_reduct_some_inv ",
                    "(five opt_bind levels), then composing apply_spine_preserves_closed three times over the ",
                    "extras/fields/prefix segments (each closed by list_{drop,take}_preserves_closed + ",
                    "kapp_args_closed), with the rhs closed via lift_invariant_closed on recenv_lift_closed_rhs. ",
                    "i3/i4 are TYPE hypotheses, not axioms. Zero axiom_deps. Stage 2B-i."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_step".to_string(),
                    "iota_reduct_some_inv_T".to_string(),
                    "RecEnvClosed".to_string(),
                    "RecEnvLiftClosed".to_string(),
                    "recenv_lift_closed_rhs".to_string(),
                    "kapp_args_closed".to_string(),
                    "list_drop_preserves_closed".to_string(),
                    "list_take_preserves_closed".to_string(),
                    "list_head_closed".to_string(),
                    "apply_spine_preserves_closed".to_string(),
                    "lift_invariant_closed".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.substType".to_string(),
                    "is_closed_at".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // ================================================================
        // hiota: the PINNED form the beta bundle consumes. Unwraps iota_reduces
        // to its iota_step (red_rec the_red_env) witness and applies hiota_generic,
        // carrying i3/i4 for red_rec the_red_env.
        // ================================================================
        self.add_definition(SpecDefinition {
            name: "hiota".to_string(),
            type_src: concat!(
                "forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                "(e : KExpr) (e' : KExpr) (d : Nat), ",
                "iota_reduces e e' -> is_closed_at e d -> is_closed_at e' d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                    "(e : KExpr) (e' : KExpr) (d : Nat) (w : iota_reduces e e') (hc : is_closed_at e d) => ",
                    "hiota_generic (red_rec the_red_env) i3 i4 e e' d (iota_reduces_to_step e e' w) hc"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pinned iota-closedness (the literal shape the beta bundle's iota arm consumes): ",
                "iota_reduces e e' -> is_closed_at e d -> is_closed_at e' d, carrying i3 : RecEnvClosed ",
                "(red_rec the_red_env) / i4 : RecEnvLiftClosed (red_rec the_red_env) as TYPE hypotheses. ",
                "DerivedProved: unwraps iota_reduces to its iota_step (red_rec the_red_env) witness via ",
                "iota_reduces_to_step and applies hiota_generic. Zero axiom_deps. Stage 2B-i."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hiota_generic".to_string(),
                "iota_reduces".to_string(),
                "iota_reduces_to_step".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
                "is_closed_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // Stage 2B-ii: whnf / infer closedness preservation.
        // ================================================================

        // IsConst: KExpr.rec discriminator, inhabited (by Nat) iff e is a const,
        // Empty otherwise — the witness that makes const_untypable go through.
        self.add_recursive_def(
            r"def IsConst (e : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (n : Level) => Empty) (fun (i : Nat) => Empty) (fun (f : KExpr) (a : KExpr) (_ : Type) (_ : Type) => Empty) (fun (ty : KExpr) (b : KExpr) (_ : Type) (_ : Type) => Empty) (fun (ty : KExpr) (b : KExpr) (_ : Type) (_ : Type) => Empty) (fun (nm : Name) (us : ListType Level) => Nat) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (s : Name) (i : Nat) (sub : KExpr) (_ : Type) => Empty) (fun (v : Nat) => Empty) e",
            "IsConst e is inhabited (by Nat.zero) exactly when e is a const, and Empty otherwise. \
             KExpr.rec discriminator used to prove const_untypable (the context-free Typing judgment \
             has no const rule). Stage 2B-ii.",
        )?;

        // const_subject_untypable: a const-headed term is untypable in the
        // context-free Typing judgment (no const/var rule; conv passes the IH).
        self.add_definition(SpecDefinition {
            name: "const_subject_untypable".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), Typing e T -> IsConst e -> Empty".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (T : KExpr) (h : Typing e T) => ",
                    "Typing.rec ",
                    "(fun (e0 : KExpr) (T0 : KExpr) (_ : Typing e0 T0) => IsConst e0 -> Empty) ",
                    "(fun (n : Level) => fun (hc : IsConst (KExpr.sort n)) => hc) ",
                    "(fun (A : KExpr) (B : KExpr) (n : Level) (m : Level) (_hA : Typing A (KExpr.sort n)) (_hB : Typing B (KExpr.sort m)) ",
                    "(_ihA : IsConst A -> Empty) (_ihB : IsConst B -> Empty) => fun (hc : IsConst (KExpr.pi A B)) => hc) ",
                    "(fun (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) (_hA : Typing A (KExpr.sort u)) (_hb : Typing b B) ",
                    "(_ihA : IsConst A -> Empty) (_ihb : IsConst b -> Empty) => fun (hc : IsConst (KExpr.lam A b)) => hc) ",
                    "(fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (_hf : Typing f (KExpr.pi A B)) (_ha : Typing a A) ",
                    "(_ihf : IsConst f -> Empty) (_iha : IsConst a -> Empty) => fun (hc : IsConst (KExpr.app f a)) => hc) ",
                    "(fun (e0 : KExpr) (A : KExpr) (B : KExpr) (_he : Typing e0 A) (_eq : DefEq A B) ",
                    "(ihe : IsConst e0 -> Empty) => fun (hc : IsConst e0) => ihe hc) ",
                    "e T h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "A const-headed term is untypable: Typing e T -> IsConst e -> Empty. DerivedProved via Typing.rec — sort/pi/lam/app subjects are not const (IsConst reduces to Empty), and conv forwards the subject IH. The context-free Typing judgment has no const/var rule. Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "IsConst".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // const_untypable: from has_type (const n us) T, conclude anything.
        self.add_definition(SpecDefinition {
            name: "const_untypable".to_string(),
            type_src: "forall (n : Name) (us : ListType Level) (T : KExpr) (C : Type), has_type (KExpr.const n us) T -> C".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Name) (us : ListType Level) (T : KExpr) (C : Type) (h : has_type (KExpr.const n us) T) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(const_subject_untypable (KExpr.const n us) T h Nat.zero)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "has_type (const n us) T is uninhabited: has_type (const n us) T -> C for any C. DerivedProved via const_subject_untypable at the IsConst (const n us) = Nat witness (Nat.zero) + Empty.rec. Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "const_subject_untypable".to_string(),
                "has_type".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_reduct_some_inv_T: Type-valued CPS inversion of delta_reduct's
        // 2-level opt_bind chain (the delta mirror of iota_reduct_some_inv_T).
        {
            let reduct = "(apply_spine (kapp_args e) val)";
            let l3 = format!("(fun (val : KExpr) => OptionType.some KExpr {reduct})");
            let l2 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) {l3})");
            let kont = format!(
                "(forall (dname : Name) (val : KExpr), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) -> \
                 Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 C)"
            );
            let value = format!(
                "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Type) \
                 (h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) \
                 (k : {kont}) => \
                 opt_bind_some_inv_T Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
                 (fun (dname : Name) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) \
                 (h1r : Eq (OptionType KExpr) ({l2} dname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_T KExpr KExpr (defval_for env dname) {l3} e' C h1r \
                 (fun (val : KExpr) \
                 (h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) ({l3} val) (OptionType.some KExpr e')) => \
                 k dname val h1 h2 h2r))"
            );
            self.add_definition(SpecDefinition {
                name: "delta_reduct_some_inv_T".to_string(),
                type_src: format!(
                    "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Type), \
                     Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e') -> {kont} -> C"
                ),
                value_src: Some(value),
                is_axiom: false,
                description: "Type-valued mirror of delta_reduct_some_inv: from delta_reduct env e = some e', recover the definition name and value with each lookup equation and the reduct equation, delivered to a Type-valued continuation. Two nested opt_bind_some_inv_T. DerivedProved, zero axiom_deps. Stage 2B-ii.".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_reduct".to_string(),
                    "opt_bind_some_inv_T".to_string(),
                    "kexpr_const_name".to_string(),
                    "defval_for".to_string(),
                    "apply_spine".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // hdelta_generic: env-generic delta-reduction preserves closedness.
        self.add_definition(SpecDefinition {
            name: "hdelta_generic".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (i5 : DefEnvClosed env) (i6 : DefEnvLiftClosed env) ",
                "(e : KExpr) (e' : KExpr) (d : Nat), ",
                "delta_step env e e' -> is_closed_at e d -> is_closed_at e' d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (i5 : DefEnvClosed env) (i6 : DefEnvLiftClosed env) ",
                    "(e : KExpr) (e' : KExpr) (d : Nat) (hstep : delta_step env e e') (hc : is_closed_at e d) => ",
                    "delta_reduct_some_inv_T env e e' (is_closed_at e' d) hstep ",
                    "(fun (dname : Name) (val : KExpr) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) ",
                    "(h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) ",
                    "(h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d) (apply_spine (kapp_args e) val) e' ",
                    "(option_some_inj KExpr (apply_spine (kapp_args e) val) e' h2r) ",
                    "(apply_spine_preserves_closed (kapp_args e) val d (kapp_args_closed e d hc) ",
                    "(lift_invariant_closed val d Nat.zero ",
                    "(defenv_lift_closed_val env dname val d (Nat.succ Nat.zero) i6 h2))))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Env-generic delta-reduction preserves closedness: delta_step env e e' -> is_closed_at e d -> is_closed_at e' d, conditional on i6 : DefEnvLiftClosed env (the def value is lift-invariant hence closed; i5 carried for parity). DerivedProved by inverting delta_reduct via delta_reduct_some_inv_T, then apply_spine_preserves_closed over the (closed) spine args and the (closed) def value. i5/i6 are TYPE hypotheses, not axioms. Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_step".to_string(),
                "delta_reduct_some_inv_T".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "defenv_lift_closed_val".to_string(),
                "kapp_args_closed".to_string(),
                "apply_spine_preserves_closed".to_string(),
                "lift_invariant_closed".to_string(),
                "option_some_inj".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // hdelta: pinned delta-closedness (the whnf bundle's delta arm consumes it).
        self.add_definition(SpecDefinition {
            name: "hdelta".to_string(),
            type_src: concat!(
                "forall (i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                "(e : KExpr) (e' : KExpr) (d : Nat), ",
                "delta_reduces e e' -> is_closed_at e d -> is_closed_at e' d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                    "(e : KExpr) (e' : KExpr) (d : Nat) (w : delta_reduces e e') (hc : is_closed_at e d) => ",
                    "hdelta_generic (red_def the_red_env) i5 i6 e e' d (delta_reduces_to_step e e' w) hc"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Pinned delta-closedness: delta_reduces e e' -> is_closed_at e d -> is_closed_at e' d, carrying i5/i6 for red_def the_red_env as TYPE hypotheses. DerivedProved: unwraps delta_reduces via delta_reduces_to_step and applies hdelta_generic. Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hdelta_generic".to_string(),
                "delta_reduces".to_string(),
                "delta_reduces_to_step".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_step_preserves_closed: a single whnf_step (beta or delta) preserves
        // closedness (beta via beta_reduces_preserves_closed + hiota; delta via hdelta).
        self.add_definition(SpecDefinition {
            name: "whnf_step_preserves_closed".to_string(),
            type_src: concat!(
                "forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                "(e : KExpr) (e' : KExpr), whnf_step e e' -> forall (d : Nat), is_closed_at e d -> is_closed_at e' d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                    "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                    "(e : KExpr) (e' : KExpr) (hs : whnf_step e e') => ",
                    // whnf_step promotes e/e' to inductive PARAMETERS (uniform ctor
                    // conclusions): they are passed explicitly BEFORE the motive, the
                    // motive ranges over the major premise only, and the beta/delta
                    // arms bind just the reduction witness.
                    "whnf_step.rec e e' ",
                    "(fun (_ : whnf_step e e') => forall (d : Nat), is_closed_at e d -> is_closed_at e' d) ",
                    "(fun (hb : beta_reduces e e') => fun (d : Nat) (hc : is_closed_at e d) => ",
                    "beta_reduces_preserves_closed (hiota i3 i4) e e' hb d hc) ",
                    "(fun (hdel : delta_reduces e e') => fun (d : Nat) (hc : is_closed_at e d) => ",
                    "hdelta i5 i6 e e' d hdel hc) ",
                    "hs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "A single whnf_step preserves closedness: whnf_step e e' -> is_closed_at e d -> is_closed_at e' d. DerivedProved via whnf_step.rec — beta arm uses beta_reduces_preserves_closed at the pinned hiota (i3/i4); delta arm uses hdelta (i5/i6). Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "beta_reduces_preserves_closed".to_string(),
                "hiota".to_string(),
                "hdelta".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_preserves_closed: the kernel WHNF loop preserves closedness.
        self.add_definition(SpecDefinition {
            name: "whnf_preserves_closed".to_string(),
            type_src: concat!(
                "forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                "(st : KernelState) (e : KExpr) (w : KExpr), ",
                "KernelWhnfAccepts st e w -> forall (d : Nat), is_closed_at e d -> is_closed_at w d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                    "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                    "(st : KernelState) (e : KExpr) (w : KExpr) (hacc : KernelWhnfAccepts st e w) => ",
                    "KernelWhnfAccepts.rec st ",
                    "(fun (e0 : KExpr) (w0 : KExpr) (_ : KernelWhnfAccepts st e0 w0) => forall (d : Nat), is_closed_at e0 d -> is_closed_at w0 d) ",
                    "(fun (e0 : KExpr) (hw : is_whnf e0) => fun (d : Nat) (hc : is_closed_at e0 d) => hc) ",
                    "(fun (e0 : KExpr) (e0' : KExpr) (v : KExpr) (hstep : whnf_step e0 e0') (hrec : KernelWhnfAccepts st e0' v) ",
                    "(ih : forall (d : Nat), is_closed_at e0' d -> is_closed_at v d) => ",
                    "fun (d : Nat) (hc : is_closed_at e0 d) => ih d (whnf_step_preserves_closed i3 i4 i5 i6 e0 e0' hstep d hc)) ",
                    "e w hacc"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The kernel WHNF loop preserves closedness: KernelWhnfAccepts st e w -> is_closed_at e d -> is_closed_at w d. DerivedProved via KernelWhnfAccepts.rec (refl: identity; step: whnf_step_preserves_closed then IH), carrying i3..i6. Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelWhnfAccepts.rec".to_string(),
                "whnf_step_preserves_closed".to_string(),
                "is_whnf".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // infer_preserves_closed: the kernel infer loop preserves closedness
        // (depth-generalized). Threads henv/hctx for the const arm (const_untypable).
        self.add_definition(SpecDefinition {
            name: "infer_preserves_closed".to_string(),
            type_src: concat!(
                "forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                "(st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                "KernelInferAccepts st e T -> forall (d : Nat), is_closed_at e d -> is_closed_at T d"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                    "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                    "(st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hinfer : KernelInferAccepts st e T) => ",
                    "KernelInferAccepts.rec st ",
                    "(fun (x : KExpr) (y : KExpr) (_ : KernelInferAccepts st x y) => forall (d : Nat), is_closed_at x d -> is_closed_at y d) ",
                    // sort
                    "(fun (l : Level) (T2 : KExpr) (heq : Eq KExpr (KExpr.sort (Level.succ l)) T2) => ",
                    "fun (d : Nat) (_hc : is_closed_at (KExpr.sort l) d) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d) (KExpr.sort (Level.succ l)) T2 heq ",
                    "(is_closed_at.sort (Level.succ l) d)) ",
                    // const
                    "(fun (n : Name) (us : ListType Level) (T2 : KExpr) ",
                    "(hpr : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st (KExpr.const n us) -> has_type (KExpr.const n us) T2) => ",
                    "fun (d : Nat) (_hc : is_closed_at (KExpr.const n us) d) => ",
                    "const_untypable n us T2 (is_closed_at T2 d) (hpr henv hctx (is_closed_at.const n us Nat.zero))) ",
                    // app
                    "(fun (f : KExpr) (a : KExpr) (T2 : KExpr) (Rf : KExpr) (Ra : KExpr) ",
                    "(hf : KernelInferAccepts st f Rf) (ha : KernelInferAccepts st a Ra) ",
                    "(hwit : AppInferWitness st Rf Ra a T2) ",
                    "(hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st (KExpr.app f a) -> KernelInputAdmissible st Rf) ",
                    "(ihf : forall (d : Nat), is_closed_at f d -> is_closed_at Rf d) ",
                    "(iha : forall (d : Nat), is_closed_at a d -> is_closed_at Ra d) => ",
                    "fun (d : Nat) (hc : is_closed_at (KExpr.app f a) d) => ",
                    "AppInferWitness.rec st Rf Ra a T2 ",
                    "(fun (_w : AppInferWitness st Rf Ra a T2) => is_closed_at T2 d) ",
                    "(fun (dom : KExpr) (cod : KExpr) (hwhnf : KernelWhnfAccepts st Rf (KExpr.pi dom cod)) ",
                    "(hdefeq : KernelDefEqAccepts st Ra dom) (hresult : Eq KExpr (instantiate cod a) T2) ",
                    "(hchkadm : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st a -> KernelBinaryInputAdmissible st Ra dom) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d) (instantiate cod a) T2 hresult ",
                    "(instantiate_preserves_closed cod a d Nat.zero ",
                    "(is_closed_at_pi_body dom cod d ",
                    "(whnf_preserves_closed i3 i4 i5 i6 st Rf (KExpr.pi dom cod) hwhnf d (ihf d (is_closed_at_app_fun f a d hc)))) ",
                    "(is_closed_at_app_arg f a d hc))) ",
                    "hwit) ",
                    // lam
                    "(fun (A : KExpr) (body : KExpr) (T2 : KExpr) (bt : KExpr) ",
                    "(hbody : KernelInferAccepts st body bt) (hwit : LamInferWitness A body bt T2) ",
                    "(ihbody : forall (d : Nat), is_closed_at body d -> is_closed_at bt d) => ",
                    "fun (d : Nat) (hc : is_closed_at (KExpr.lam A body) d) => ",
                    "LamInferWitness.rec A body bt T2 ",
                    "(fun (_w : LamInferWitness A body bt T2) => is_closed_at T2 d) ",
                    "(fun (dl : Level) (hdom : Typing A (KExpr.sort dl)) (hbodyty : Typing body bt) (hresult : Eq KExpr (KExpr.pi A bt) T2) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d) (KExpr.pi A bt) T2 hresult ",
                    "(is_closed_at.pi A bt d (is_closed_at_lam_type A body d hc) (ihbody (Nat.succ d) (is_closed_at_lam_body A body d hc)))) ",
                    "hwit) ",
                    // pi
                    "(fun (A : KExpr) (B : KExpr) (T2 : KExpr) (hwit : PiInferWitness A B T2) => ",
                    "fun (d : Nat) (_hc : is_closed_at (KExpr.pi A B) d) => ",
                    "PiInferWitness.rec A B T2 ",
                    "(fun (_w : PiInferWitness A B T2) => is_closed_at T2 d) ",
                    "(fun (dom : Level) (cod : Level) (hdom : Typing A (KExpr.sort dom)) (hcod : Typing B (KExpr.sort cod)) ",
                    "(hresult : Eq KExpr (KExpr.sort (Level.imax dom cod)) T2) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => is_closed_at z d) (KExpr.sort (Level.imax dom cod)) T2 hresult ",
                    "(is_closed_at.sort (Level.imax dom cod) d)) ",
                    "hwit) ",
                    "e T hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The kernel infer loop preserves closedness (depth-generalized): KernelInferAccepts st e T -> is_closed_at e d -> is_closed_at T d. DerivedProved via KernelInferAccepts.rec: sort/pi conclude in a sort (always closed); const is untypable (const_untypable, using the threaded state-validity guards); lam is structural (T = pi A bt, closed via the body IH at succ d); app uses whnf_preserves_closed (Rf whnf-reduces to pi dom cod) + is_closed_at_pi_body + instantiate_preserves_closed (M3) on T = instantiate cod a. Carries i3..i6 as TYPE hypotheses. Zero axiom_deps. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferAccepts.rec".to_string(),
                "AppInferWitness.rec".to_string(),
                "LamInferWitness.rec".to_string(),
                "PiInferWitness.rec".to_string(),
                "const_untypable".to_string(),
                "whnf_preserves_closed".to_string(),
                "instantiate_preserves_closed".to_string(),
                "is_closed_at_pi_body".to_string(),
                "is_closed_at_app_fun".to_string(),
                "is_closed_at_app_arg".to_string(),
                "is_closed_at_lam_type".to_string(),
                "is_closed_at_lam_body".to_string(),
                "is_closed_at.sort".to_string(),
                "is_closed_at.pi".to_string(),
                "is_closed_at.const".to_string(),
                "instantiate".to_string(),
                "imax_nat".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // infer_result_self_admissible: an inferred type of a closed input is
        // itself closed, so the (T, T) pair is binary-admissible.
        self.add_definition(SpecDefinition {
            name: "infer_result_self_admissible".to_string(),
            type_src: concat!(
                "forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                "(st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                "KernelInferAccepts st e T -> KernelInputAdmissible st e -> KernelBinaryInputAdmissible st T T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                    "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                    "(st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hinfer : KernelInferAccepts st e T) (hadm : KernelInputAdmissible st e) => ",
                    "AndType.intro (KernelInputAdmissible st T) (KernelInputAdmissible st T) ",
                    "(infer_preserves_closed i3 i4 i5 i6 st e T henv hctx hinfer Nat.zero hadm) ",
                    "(infer_preserves_closed i3 i4 i5 i6 st e T henv hctx hinfer Nat.zero hadm)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The inferred type of a closed input is itself closed, so (T, T) is binary-admissible: KernelInferAccepts st e T -> KernelInputAdmissible st e -> KernelBinaryInputAdmissible st T T. DerivedProved from infer_preserves_closed at depth 0 (KernelInputAdmissible = is_closed; KernelBinaryInputAdmissible = AndType is_closed is_closed). Carries i3..i6 as TYPE hypotheses. Zero axiom_deps. The guard supplied to tc_infer_soundness's KernelCheckAccepts.mk. Stage 2B-ii.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "infer_preserves_closed".to_string(),
                "AndType.intro".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelBinaryInputAdmissible".to_string(),
                "KernelInferAccepts".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
