// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment E (#2859 computational-iota/delta track): substitution-commutation
//! substrate for `iota_reduct`.
//!
//! The goal of E is to close `par_subst`'s iota arm (the Wave-122 wall) by showing
//! the computational reduct commutes with `instantiate_at` ON THE REDEX BRANCH —
//! sound because a genuine iota redex is `const`-recursor-headed applied to a
//! `const`-constructor-headed major (both fixed by `instantiate_at_const`), so the
//! `kapp_fn`-vs-`instantiate_at` non-commutation (which only bites bvar-headed
//! spines) does not apply. The opaque `RecRule.rhs` rides through as
//! `instantiate_at rhs v d` uniformly on both sides — never unfolded.
//!
//! This module runs AFTER `add_whnf_lemmas` (it consumes `instantiate_at_app` /
//! `instantiate_at_const`) and uses the iota_step substrate (`apply_spine`,
//! `kapp_args`, the C.4–C.6 unfolds). First, the unconditional spine-commutation
//! `instantiate_at_apply_spine` (the load-bearing lemma every later E step
//! consumes), built per the adversarially-verified design workflow. See
//! `designs/2026-06-14-computational-iota-delta-track.md` (Increment E).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_iota_subst(&mut self) -> Result<(), SpecError> {
        // list_map: pointwise image of a KExpr list under f. The substrate has no
        // map; the substitution-commutation needs "map (instantiate_at . v d)".
        self.add_recursive_def(
            r"def list_map (f : KExpr → KExpr) (xs : ListType KExpr) : ListType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) (ListType.nil KExpr) (fun (x : KExpr) (rest : ListType KExpr) (ih : ListType KExpr) => ListType.cons KExpr (f x) ih) xs",
            "Pointwise image of a KExpr list under f. Part of #2859 (Increment E).",
        )?;

        let unfold = |name: &str, type_src: &str, value_src: &str, desc: &str| SpecDefinition {
            name: name.to_string(),
            type_src: type_src.to_string(),
            value_src: Some(value_src.to_string()),
            is_axiom: false,
            description: desc.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        };

        // list_map f [] = []
        self.add_definition(unfold(
            "list_map_nil",
            "forall (f : KExpr -> KExpr), Eq (ListType KExpr) (list_map f (ListType.nil KExpr)) (ListType.nil KExpr)",
            "fun (f : KExpr -> KExpr) => Eq.refl (ListType KExpr) (ListType.nil KExpr)",
            "Unfolding: list_map f [] = []. DerivedProved. Part of #2859 (Increment E).",
        ))?;

        // list_map f (x :: rest) = (f x) :: (list_map f rest)
        self.add_definition(unfold(
            "list_map_cons",
            "forall (f : KExpr -> KExpr) (x : KExpr) (rest : ListType KExpr), Eq (ListType KExpr) (list_map f (ListType.cons KExpr x rest)) (ListType.cons KExpr (f x) (list_map f rest))",
            "fun (f : KExpr -> KExpr) (x : KExpr) (rest : ListType KExpr) => Eq.refl (ListType KExpr) (ListType.cons KExpr (f x) (list_map f rest))",
            "Unfolding: list_map f (x :: rest) = (f x) :: list_map f rest. DerivedProved. Part of #2859 (Increment E).",
        ))?;

        // instantiate_at_apply_spine: instantiate_at distributes through the
        // application spine — the load-bearing UNCONDITIONAL commutation (no
        // const-head guard; pure structural distribution over app). By ListType.rec
        // on args, chained through apply_spine_cons + instantiate_at_app +
        // list_map_cons + the head IH. f := (fun a => instantiate_at a v d).
        let f = "(fun (a : KExpr) => instantiate_at a v d)";
        self.add_definition(SpecDefinition {
            name: "instantiate_at_apply_spine".to_string(),
            type_src: format!(
                concat!(
                    "forall (args : ListType KExpr) (head : KExpr) (v : KExpr) (d : Nat), ",
                    "Eq KExpr (instantiate_at (apply_spine args head) v d) ",
                    "(apply_spine (list_map {f} args) (instantiate_at head v d))"
                ),
                f = f,
            ),
            value_src: Some(format!(
                concat!(
                    "fun (args : ListType KExpr) (head : KExpr) (v : KExpr) (d : Nat) => ",
                    "ListType.rec KExpr ",
                    "(fun (args0 : ListType KExpr) => forall (head0 : KExpr), ",
                    "Eq KExpr (instantiate_at (apply_spine args0 head0) v d) ",
                    "(apply_spine (list_map {f} args0) (instantiate_at head0 v d))) ",
                    // nil case
                    "(fun (head0 : KExpr) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (apply_spine (ListType.nil KExpr) head0) v d) ",
                    "(instantiate_at head0 v d) ",
                    "(apply_spine (list_map {f} (ListType.nil KExpr)) (instantiate_at head0 v d)) ",
                    "(Eq.cong KExpr KExpr (fun (X : KExpr) => instantiate_at X v d) ",
                    "(apply_spine (ListType.nil KExpr) head0) head0 (apply_spine_nil head0)) ",
                    "(Eq.symm KExpr ",
                    "(apply_spine (list_map {f} (ListType.nil KExpr)) (instantiate_at head0 v d)) ",
                    "(instantiate_at head0 v d) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (list_map {f} (ListType.nil KExpr)) (instantiate_at head0 v d)) ",
                    "(apply_spine (ListType.nil KExpr) (instantiate_at head0 v d)) ",
                    "(instantiate_at head0 v d) ",
                    "(Eq.cong (ListType KExpr) KExpr ",
                    "(fun (L : ListType KExpr) => apply_spine L (instantiate_at head0 v d)) ",
                    "(list_map {f} (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil {f})) ",
                    "(apply_spine_nil (instantiate_at head0 v d))))) ",
                    // cons case
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(ih : forall (head0 : KExpr), ",
                    "Eq KExpr (instantiate_at (apply_spine rest head0) v d) ",
                    "(apply_spine (list_map {f} rest) (instantiate_at head0 v d))) => ",
                    "fun (head0 : KExpr) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (apply_spine (ListType.cons KExpr x rest) head0) v d) ",
                    "(apply_spine (list_map {f} rest) (KExpr.app (instantiate_at head0 v d) (instantiate_at x v d))) ",
                    "(apply_spine (list_map {f} (ListType.cons KExpr x rest)) (instantiate_at head0 v d)) ",
                    // leg1
                    "(Eq.trans KExpr ",
                    "(instantiate_at (apply_spine (ListType.cons KExpr x rest) head0) v d) ",
                    "(apply_spine (list_map {f} rest) (instantiate_at (KExpr.app head0 x) v d)) ",
                    "(apply_spine (list_map {f} rest) (KExpr.app (instantiate_at head0 v d) (instantiate_at x v d))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (apply_spine (ListType.cons KExpr x rest) head0) v d) ",
                    "(instantiate_at (apply_spine rest (KExpr.app head0 x)) v d) ",
                    "(apply_spine (list_map {f} rest) (instantiate_at (KExpr.app head0 x) v d)) ",
                    "(Eq.cong KExpr KExpr (fun (X : KExpr) => instantiate_at X v d) ",
                    "(apply_spine (ListType.cons KExpr x rest) head0) (apply_spine rest (KExpr.app head0 x)) ",
                    "(apply_spine_cons x rest head0)) ",
                    "(ih (KExpr.app head0 x))) ",
                    "(Eq.cong KExpr KExpr (fun (Y : KExpr) => apply_spine (list_map {f} rest) Y) ",
                    "(instantiate_at (KExpr.app head0 x) v d) ",
                    "(KExpr.app (instantiate_at head0 v d) (instantiate_at x v d)) ",
                    "(instantiate_at_app head0 x v d))) ",
                    // leg2 (symm of RHS forward chain)
                    "(Eq.symm KExpr ",
                    "(apply_spine (list_map {f} (ListType.cons KExpr x rest)) (instantiate_at head0 v d)) ",
                    "(apply_spine (list_map {f} rest) (KExpr.app (instantiate_at head0 v d) (instantiate_at x v d))) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (list_map {f} (ListType.cons KExpr x rest)) (instantiate_at head0 v d)) ",
                    "(apply_spine (ListType.cons KExpr (instantiate_at x v d) (list_map {f} rest)) (instantiate_at head0 v d)) ",
                    "(apply_spine (list_map {f} rest) (KExpr.app (instantiate_at head0 v d) (instantiate_at x v d))) ",
                    "(Eq.cong (ListType KExpr) KExpr ",
                    "(fun (L : ListType KExpr) => apply_spine L (instantiate_at head0 v d)) ",
                    "(list_map {f} (ListType.cons KExpr x rest)) ",
                    "(ListType.cons KExpr (instantiate_at x v d) (list_map {f} rest)) ",
                    "(list_map_cons {f} x rest)) ",
                    "(apply_spine_cons (instantiate_at x v d) (list_map {f} rest) (instantiate_at head0 v d))))) ",
                    "args head"
                ),
                f = f,
            )),
            is_axiom: false,
            description: concat!(
                "instantiate_at (apply_spine args head) v d = apply_spine (list_map (instantiate_at . v d) ",
                "args) (instantiate_at head v d): instantiate_at distributes through the application ",
                "spine. UNCONDITIONAL (no const-head guard). By ListType.rec on args through ",
                "apply_spine_cons + instantiate_at_app + list_map_cons + the head IH. The load-bearing ",
                "spine-commutation every later E step consumes. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "apply_spine".to_string(),
                "list_map".to_string(),
                "ListType.rec".to_string(),
                "apply_spine_nil".to_string(),
                "apply_spine_cons".to_string(),
                "list_map_nil".to_string(),
                "list_map_cons".to_string(),
                "instantiate_at_app".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ===============================================================
        // E wall — opt_bind chain inversion (no Sigma/Exists in the fragment,
        // so CPS witness-passing). E-core inverts the 5-level iota_reduct opt_bind
        // chain to recover the const-head witnesses; each level uses this.
        // ===============================================================

        // opt_is_none: large-elimination discriminator (none -> Nat, some -> Empty),
        // registered as a def (mirror of kexpr_not_pi, expr_model_discrimination_pi.rs:47).
        self.add_recursive_def(
            r"def opt_is_none (b : Type) (o : OptionType b) : Type := OptionType.rec b (fun (_ : OptionType b) => Type) Nat (fun (_ : b) => Empty) o",
            "Discriminator: opt_is_none none = Nat, opt_is_none (some _) = Empty. Part of #2859 (Increment E).",
        )?;

        // option_none_ne_some: none /= some (no-confusion), via opt_is_none
        // (mirror of sort_ne_pi, expr_model_discrimination_pi.rs:75).
        self.add_definition(SpecDefinition {
            name: "option_none_ne_some".to_string(),
            type_src: concat!(
                "forall (b : Type) (r : b) (R : Prop), ",
                "Eq (OptionType b) (OptionType.none b) (OptionType.some b r) -> R"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : Type) (r : b) (R : Prop) ",
                    "(h : Eq (OptionType b) (OptionType.none b) (OptionType.some b r)) => ",
                    "Empty.rec (fun (_ : Empty) => R) ",
                    "(Eq.substType (OptionType b) (opt_is_none b) ",
                    "(OptionType.none b) (OptionType.some b r) h Nat.zero)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "OptionType no-confusion: none /= some. Empty discriminator (none -> Nat inhabited ",
                "by zero, some -> Empty) transported along the false equation. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_is_none".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // opt_bind_some_inv: CPS inversion of opt_bind. From opt_bind o f = some r,
        // recover the witness a with o = some a and f a = some r, delivered to a
        // continuation (no Sigma/Exists). By cases on o: none -> opt_bind = none =
        // some r is absurd (option_none_ne_some); some a -> opt_bind = f a.
        self.add_definition(SpecDefinition {
            name: "opt_bind_some_inv".to_string(),
            type_src: concat!(
                "forall (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Prop), ",
                "Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r) -> ",
                "(forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Prop) ",
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
                    "option_none_ne_some b r C h0) ",
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
            description: concat!(
                "CPS inversion of opt_bind: opt_bind o f = some r yields a witness w with o = some w ",
                "and f w = some r, delivered to a continuation (the fragment has no Sigma/Exists). By ",
                "OptionType.rec on o — none is absurd (opt_bind = none = some r via option_none_ne_some), ",
                "some w reduces opt_bind to f w. The per-level inversion the 5-level iota_reduct chain ",
                "needs (Increment E). DerivedProved, zero axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "OptionType.rec".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ===============================================================
        // E substrate — list_map commutations (list_map distributes over the
        // list ops iota_reduct uses: append, length, ...). All unconditional.
        // ===============================================================

        // opt_map: image of an OptionType KExpr under f (none -> none, some x -> some (f x)).
        self.add_recursive_def(
            r"def opt_map (f : KExpr → KExpr) (o : OptionType KExpr) : OptionType KExpr := OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (OptionType.none KExpr) (fun (x : KExpr) => OptionType.some KExpr (f x)) o",
            "Map over an OptionType KExpr: none -> none, some x -> some (f x). Part of #2859 (Increment E).",
        )?;

        // list_length [] = 0
        self.add_definition(unfold(
            "list_length_nil",
            "Eq Nat (list_length (ListType.nil KExpr)) Nat.zero",
            "Eq.refl Nat Nat.zero",
            "Unfolding: list_length [] = 0. DerivedProved. Part of #2859 (Increment E).",
        ))?;

        // list_map f (list_append xs ys) = list_append (list_map f xs) (list_map f ys).
        self.add_definition(SpecDefinition {
            name: "list_map_append".to_string(),
            type_src: concat!(
                "forall (f : KExpr -> KExpr) (xs : ListType KExpr) (ys : ListType KExpr), ",
                "Eq (ListType KExpr) (list_map f (list_append xs ys)) ",
                "(list_append (list_map f xs) (list_map f ys))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr -> KExpr) (xs : ListType KExpr) (ys : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs0 : ListType KExpr) => Eq (ListType KExpr) ",
                    "(list_map f (list_append xs0 ys)) (list_append (list_map f xs0) (list_map f ys))) ",
                    // nil
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map f (list_append (ListType.nil KExpr) ys)) ",
                    "(list_map f ys) ",
                    "(list_append (list_map f (ListType.nil KExpr)) (list_map f ys)) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_append (ListType.nil KExpr) ys) ys (list_append_nil ys)) ",
                    "(Eq.symm (ListType KExpr) ",
                    "(list_append (list_map f (ListType.nil KExpr)) (list_map f ys)) (list_map f ys) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_append (list_map f (ListType.nil KExpr)) (list_map f ys)) ",
                    "(list_append (ListType.nil KExpr) (list_map f ys)) ",
                    "(list_map f ys) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                    "(fun (L : ListType KExpr) => list_append L (list_map f ys)) ",
                    "(list_map f (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil f)) ",
                    "(list_append_nil (list_map f ys))))) ",
                    // cons
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(ih : Eq (ListType KExpr) (list_map f (list_append rest ys)) ",
                    "(list_append (list_map f rest) (list_map f ys))) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_map f (list_append (ListType.cons KExpr x rest) ys)) ",
                    "(ListType.cons KExpr (f x) (list_append (list_map f rest) (list_map f ys))) ",
                    "(list_append (list_map f (ListType.cons KExpr x rest)) (list_map f ys)) ",
                    // leg1: lhs -> cons (f x) (append (map f rest) (map f ys))
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map f (list_append (ListType.cons KExpr x rest) ys)) ",
                    "(ListType.cons KExpr (f x) (list_map f (list_append rest ys))) ",
                    "(ListType.cons KExpr (f x) (list_append (list_map f rest) (list_map f ys))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map f (list_append (ListType.cons KExpr x rest) ys)) ",
                    "(list_map f (ListType.cons KExpr x (list_append rest ys))) ",
                    "(ListType.cons KExpr (f x) (list_map f (list_append rest ys))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_append (ListType.cons KExpr x rest) ys) ",
                    "(ListType.cons KExpr x (list_append rest ys)) (list_append_cons x rest ys)) ",
                    "(list_map_cons f x (list_append rest ys))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                    "(fun (L : ListType KExpr) => ListType.cons KExpr (f x) L) ",
                    "(list_map f (list_append rest ys)) ",
                    "(list_append (list_map f rest) (list_map f ys)) ih)) ",
                    // leg2: cons (f x) (...) -> rhs (symm)
                    "(Eq.symm (ListType KExpr) ",
                    "(list_append (list_map f (ListType.cons KExpr x rest)) (list_map f ys)) ",
                    "(ListType.cons KExpr (f x) (list_append (list_map f rest) (list_map f ys))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_append (list_map f (ListType.cons KExpr x rest)) (list_map f ys)) ",
                    "(list_append (ListType.cons KExpr (f x) (list_map f rest)) (list_map f ys)) ",
                    "(ListType.cons KExpr (f x) (list_append (list_map f rest) (list_map f ys))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                    "(fun (L : ListType KExpr) => list_append L (list_map f ys)) ",
                    "(list_map f (ListType.cons KExpr x rest)) ",
                    "(ListType.cons KExpr (f x) (list_map f rest)) (list_map_cons f x rest)) ",
                    "(list_append_cons (f x) (list_map f rest) (list_map f ys))))) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "list_map distributes over list_append. By ListType.rec on xs through the ",
                "list_map/list_append unfolds. DerivedProved, zero axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_map".to_string(),
                "list_append".to_string(),
                "ListType.rec".to_string(),
                "list_map_nil".to_string(),
                "list_map_cons".to_string(),
                "list_append_nil".to_string(),
                "list_append_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_length (list_map f xs) = list_length xs (length preserved — load-bearing
        // for the field-offset arithmetic in iota_reduct).
        self.add_definition(SpecDefinition {
            name: "list_map_length".to_string(),
            type_src: concat!(
                "forall (f : KExpr -> KExpr) (xs : ListType KExpr), ",
                "Eq Nat (list_length (list_map f xs)) (list_length xs)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr -> KExpr) (xs : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs0 : ListType KExpr) => Eq Nat (list_length (list_map f xs0)) (list_length xs0)) ",
                    // nil
                    "(Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) ",
                    "(list_map f (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil f)) ",
                    // cons
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(ih : Eq Nat (list_length (list_map f rest)) (list_length rest)) => ",
                    "Eq.trans Nat ",
                    "(list_length (list_map f (ListType.cons KExpr x rest))) ",
                    "(Nat.succ (list_length (list_map f rest))) ",
                    "(list_length (ListType.cons KExpr x rest)) ",
                    "(Eq.trans Nat ",
                    "(list_length (list_map f (ListType.cons KExpr x rest))) ",
                    "(list_length (ListType.cons KExpr (f x) (list_map f rest))) ",
                    "(Nat.succ (list_length (list_map f rest))) ",
                    "(Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) ",
                    "(list_map f (ListType.cons KExpr x rest)) ",
                    "(ListType.cons KExpr (f x) (list_map f rest)) (list_map_cons f x rest)) ",
                    "(list_length_cons (f x) (list_map f rest))) ",
                    "(Eq.trans Nat ",
                    "(Nat.succ (list_length (list_map f rest))) ",
                    "(Nat.succ (list_length rest)) ",
                    "(list_length (ListType.cons KExpr x rest)) ",
                    "(Eq.cong Nat Nat (fun (n : Nat) => Nat.succ n) ",
                    "(list_length (list_map f rest)) (list_length rest) ih) ",
                    "(Eq.symm Nat (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) ",
                    "(list_length_cons x rest)))) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "list_map preserves list_length. By ListType.rec on xs. Load-bearing for the ",
                "field-offset arithmetic in iota_reduct (offsets match under instantiate_at). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_map".to_string(),
                "list_length".to_string(),
                "ListType.rec".to_string(),
                "list_map_nil".to_string(),
                "list_map_cons".to_string(),
                "list_length_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // More unfolds (Eq.refl) needed by the remaining list_map commutations.
        self.add_definition(unfold(
            "list_tail_nil",
            "Eq (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr)",
            "Eq.refl (ListType KExpr) (ListType.nil KExpr)",
            "Unfolding: list_tail [] = []. DerivedProved. Part of #2859 (Increment E).",
        ))?;
        self.add_definition(unfold(
            "list_head_nil",
            "Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.none KExpr)",
            "Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "Unfolding: list_head [] = none. DerivedProved. Part of #2859 (Increment E).",
        ))?;
        self.add_definition(unfold(
            "opt_map_none",
            "forall (f : KExpr -> KExpr), Eq (OptionType KExpr) (opt_map f (OptionType.none KExpr)) (OptionType.none KExpr)",
            "fun (f : KExpr -> KExpr) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "Unfolding: opt_map f none = none. DerivedProved. Part of #2859 (Increment E).",
        ))?;
        self.add_definition(unfold(
            "opt_map_some",
            "forall (f : KExpr -> KExpr) (x : KExpr), Eq (OptionType KExpr) (opt_map f (OptionType.some KExpr x)) (OptionType.some KExpr (f x))",
            "fun (f : KExpr -> KExpr) (x : KExpr) => Eq.refl (OptionType KExpr) (OptionType.some KExpr (f x))",
            "Unfolding: opt_map f (some x) = some (f x). DerivedProved. Part of #2859 (Increment E).",
        ))?;

        // list_tail (list_map f xs) = list_map f (list_tail xs). ListType.rec cases on xs.
        self.add_definition(SpecDefinition {
            name: "list_map_tail".to_string(),
            type_src: concat!(
                "forall (f : KExpr -> KExpr) (xs : ListType KExpr), ",
                "Eq (ListType KExpr) (list_tail (list_map f xs)) (list_map f (list_tail xs))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr -> KExpr) (xs : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs0 : ListType KExpr) => Eq (ListType KExpr) ",
                    "(list_tail (list_map f xs0)) (list_map f (list_tail xs0))) ",
                    // nil
                    "(Eq.trans (ListType KExpr) ",
                    "(list_tail (list_map f (ListType.nil KExpr))) ",
                    "(ListType.nil KExpr) ",
                    "(list_map f (list_tail (ListType.nil KExpr))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_tail (list_map f (ListType.nil KExpr))) ",
                    "(list_tail (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_tail L) ",
                    "(list_map f (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil f)) ",
                    "list_tail_nil) ",
                    "(Eq.symm (ListType KExpr) ",
                    "(list_map f (list_tail (ListType.nil KExpr))) (ListType.nil KExpr) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map f (list_tail (ListType.nil KExpr))) ",
                    "(list_map f (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(list_map_nil f)))) ",
                    // cons
                    "(fun (x : KExpr) (rest : ListType KExpr) (_ih : Eq (ListType KExpr) ",
                    "(list_tail (list_map f rest)) (list_map f (list_tail rest))) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_tail (list_map f (ListType.cons KExpr x rest))) ",
                    "(list_map f rest) ",
                    "(list_map f (list_tail (ListType.cons KExpr x rest))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_tail (list_map f (ListType.cons KExpr x rest))) ",
                    "(list_tail (ListType.cons KExpr (f x) (list_map f rest))) ",
                    "(list_map f rest) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_tail L) ",
                    "(list_map f (ListType.cons KExpr x rest)) ",
                    "(ListType.cons KExpr (f x) (list_map f rest)) (list_map_cons f x rest)) ",
                    "(list_tail_cons (f x) (list_map f rest))) ",
                    "(Eq.symm (ListType KExpr) ",
                    "(list_map f (list_tail (ListType.cons KExpr x rest))) (list_map f rest) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_tail (ListType.cons KExpr x rest)) rest (list_tail_cons x rest)))) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "list_map commutes with list_tail. By ListType.rec cases on xs. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_map".to_string(),
                "list_tail".to_string(),
                "ListType.rec".to_string(),
                "list_map_nil".to_string(),
                "list_map_cons".to_string(),
                "list_tail_nil".to_string(),
                "list_tail_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_head (list_map f xs) = opt_map f (list_head xs). ListType.rec cases.
        self.add_definition(SpecDefinition {
            name: "list_map_head".to_string(),
            type_src: concat!(
                "forall (f : KExpr -> KExpr) (xs : ListType KExpr), ",
                "Eq (OptionType KExpr) (list_head (list_map f xs)) (opt_map f (list_head xs))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr -> KExpr) (xs : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs0 : ListType KExpr) => Eq (OptionType KExpr) ",
                    "(list_head (list_map f xs0)) (opt_map f (list_head xs0))) ",
                    // nil
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_map f (ListType.nil KExpr))) ",
                    "(OptionType.none KExpr) ",
                    "(opt_map f (list_head (ListType.nil KExpr))) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_map f (ListType.nil KExpr))) ",
                    "(list_head (ListType.nil KExpr)) ",
                    "(OptionType.none KExpr) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_map f (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil f)) ",
                    "list_head_nil) ",
                    "(Eq.symm (OptionType KExpr) ",
                    "(opt_map f (list_head (ListType.nil KExpr))) (OptionType.none KExpr) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(opt_map f (list_head (ListType.nil KExpr))) ",
                    "(opt_map f (OptionType.none KExpr)) ",
                    "(OptionType.none KExpr) ",
                    "(Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (O : OptionType KExpr) => opt_map f O) ",
                    "(list_head (ListType.nil KExpr)) (OptionType.none KExpr) list_head_nil) ",
                    "(opt_map_none f)))) ",
                    // cons
                    "(fun (x : KExpr) (rest : ListType KExpr) (_ih : Eq (OptionType KExpr) ",
                    "(list_head (list_map f rest)) (opt_map f (list_head rest))) => ",
                    "Eq.trans (OptionType KExpr) ",
                    "(list_head (list_map f (ListType.cons KExpr x rest))) ",
                    "(OptionType.some KExpr (f x)) ",
                    "(opt_map f (list_head (ListType.cons KExpr x rest))) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_map f (ListType.cons KExpr x rest))) ",
                    "(list_head (ListType.cons KExpr (f x) (list_map f rest))) ",
                    "(OptionType.some KExpr (f x)) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_map f (ListType.cons KExpr x rest)) ",
                    "(ListType.cons KExpr (f x) (list_map f rest)) (list_map_cons f x rest)) ",
                    "(list_head_cons (f x) (list_map f rest))) ",
                    "(Eq.symm (OptionType KExpr) ",
                    "(opt_map f (list_head (ListType.cons KExpr x rest))) (OptionType.some KExpr (f x)) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(opt_map f (list_head (ListType.cons KExpr x rest))) ",
                    "(opt_map f (OptionType.some KExpr x)) ",
                    "(OptionType.some KExpr (f x)) ",
                    "(Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (O : OptionType KExpr) => opt_map f O) ",
                    "(list_head (ListType.cons KExpr x rest)) (OptionType.some KExpr x) (list_head_cons x rest)) ",
                    "(opt_map_some f x)))) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "list_map commutes with list_head (via opt_map). ListType.rec cases. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_map".to_string(),
                "list_head".to_string(),
                "opt_map".to_string(),
                "ListType.rec".to_string(),
                "list_map_nil".to_string(),
                "list_map_cons".to_string(),
                "list_head_nil".to_string(),
                "list_head_cons".to_string(),
                "opt_map_none".to_string(),
                "opt_map_some".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_drop n (list_map f xs) = list_map f (list_drop n xs). Nat.rec on n
        // (motive generalizes xs), succ case via list_drop_succ + list_map_tail + IH.
        self.add_definition(SpecDefinition {
            name: "list_map_drop".to_string(),
            type_src: concat!(
                "forall (f : KExpr -> KExpr) (n : Nat) (xs : ListType KExpr), ",
                "Eq (ListType KExpr) (list_drop n (list_map f xs)) (list_map f (list_drop n xs))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr -> KExpr) (n : Nat) (xs : ListType KExpr) => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (xs0 : ListType KExpr), Eq (ListType KExpr) ",
                    "(list_drop n0 (list_map f xs0)) (list_map f (list_drop n0 xs0))) ",
                    // zero
                    "(fun (xs0 : ListType KExpr) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_drop Nat.zero (list_map f xs0)) (list_map f xs0) (list_map f (list_drop Nat.zero xs0)) ",
                    "(list_drop_zero (list_map f xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_map f (list_drop Nat.zero xs0)) (list_map f xs0) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_drop Nat.zero xs0) xs0 (list_drop_zero xs0)))) ",
                    // succ
                    "(fun (m : Nat) (ih : forall (xs0 : ListType KExpr), Eq (ListType KExpr) ",
                    "(list_drop m (list_map f xs0)) (list_map f (list_drop m xs0))) => ",
                    "fun (xs0 : ListType KExpr) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (list_map f xs0)) ",
                    "(list_map f (list_drop m (list_tail xs0))) ",
                    "(list_map f (list_drop (Nat.succ m) xs0)) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (list_map f xs0)) ",
                    "(list_drop m (list_tail (list_map f xs0))) ",
                    "(list_map f (list_drop m (list_tail xs0))) ",
                    "(list_drop_succ m (list_map f xs0)) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop m (list_tail (list_map f xs0))) ",
                    "(list_drop m (list_map f (list_tail xs0))) ",
                    "(list_map f (list_drop m (list_tail xs0))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                    "(list_tail (list_map f xs0)) (list_map f (list_tail xs0)) (list_map_tail f xs0)) ",
                    "(ih (list_tail xs0)))) ",
                    "(Eq.symm (ListType KExpr) ",
                    "(list_map f (list_drop (Nat.succ m) xs0)) (list_map f (list_drop m (list_tail xs0))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_drop (Nat.succ m) xs0) (list_drop m (list_tail xs0)) (list_drop_succ m xs0)))) ",
                    "n xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "list_map commutes with list_drop. Nat.rec on n (motive generalizes xs), succ case via list_drop_succ + list_map_tail + IH. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_map".to_string(),
                "list_drop".to_string(),
                "list_tail".to_string(),
                "Nat.rec".to_string(),
                "list_drop_zero".to_string(),
                "list_drop_succ".to_string(),
                "list_map_tail".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_take unfolds (Eq.refl).
        self.add_definition(unfold(
            "list_take_zero",
            "forall (xs : ListType KExpr), Eq (ListType KExpr) (list_take Nat.zero xs) (ListType.nil KExpr)",
            "fun (xs : ListType KExpr) => Eq.refl (ListType KExpr) (ListType.nil KExpr)",
            "Unfolding: list_take 0 xs = []. DerivedProved. Part of #2859 (Increment E).",
        ))?;
        self.add_definition(unfold(
            "list_take_succ_nil",
            "forall (m : Nat), Eq (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr)",
            "fun (m : Nat) => Eq.refl (ListType KExpr) (ListType.nil KExpr)",
            "Unfolding: list_take (succ m) [] = []. DerivedProved. Part of #2859 (Increment E).",
        ))?;
        self.add_definition(unfold(
            "list_take_succ_cons",
            "forall (m : Nat) (x : KExpr) (rest : ListType KExpr), Eq (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x rest)) (ListType.cons KExpr x (list_take m rest))",
            "fun (m : Nat) (x : KExpr) (rest : ListType KExpr) => Eq.refl (ListType KExpr) (ListType.cons KExpr x (list_take m rest))",
            "Unfolding: list_take (succ m) (x :: rest) = x :: list_take m rest. DerivedProved. Part of #2859 (Increment E).",
        ))?;

        // list_take n (list_map f xs) = list_map f (list_take n xs). Nat.rec on n
        // (motive generalizes xs); succ arm case-splits xs via ListType.rec, using
        // the OUTER Nat.rec IH at rest (no inner induction).
        self.add_definition(SpecDefinition {
            name: "list_map_take".to_string(),
            type_src: concat!(
                "forall (f : KExpr -> KExpr) (n : Nat) (xs : ListType KExpr), ",
                "Eq (ListType KExpr) (list_take n (list_map f xs)) (list_map f (list_take n xs))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr -> KExpr) (n : Nat) (xs : ListType KExpr) => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (xs0 : ListType KExpr), Eq (ListType KExpr) ",
                    "(list_take n0 (list_map f xs0)) (list_map f (list_take n0 xs0))) ",
                    // zero: both sides -> nil
                    "(fun (xs0 : ListType KExpr) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_take Nat.zero (list_map f xs0)) (ListType.nil KExpr) (list_map f (list_take Nat.zero xs0)) ",
                    "(list_take_zero (list_map f xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_map f (list_take Nat.zero xs0)) (ListType.nil KExpr) ",
                    "(Eq.trans (ListType KExpr) (list_map f (list_take Nat.zero xs0)) (list_map f (ListType.nil KExpr)) (ListType.nil KExpr) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_take Nat.zero xs0) (ListType.nil KExpr) (list_take_zero xs0)) (list_map_nil f)))) ",
                    // succ: case on xs via ListType.rec, using outer ih
                    "(fun (m : Nat) (ih : forall (xs0 : ListType KExpr), Eq (ListType KExpr) ",
                    "(list_take m (list_map f xs0)) (list_map f (list_take m xs0))) => ",
                    "fun (xs0 : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f xs1)) (list_map f (list_take (Nat.succ m) xs1))) ",
                    // inner nil
                    "(Eq.trans (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f (ListType.nil KExpr))) (ListType.nil KExpr) ",
                    "(list_map f (list_take (Nat.succ m) (ListType.nil KExpr))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f (ListType.nil KExpr))) ",
                    "(list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take (Nat.succ m) L) ",
                    "(list_map f (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil f)) ",
                    "(list_take_succ_nil m)) ",
                    "(Eq.symm (ListType KExpr) (list_map f (list_take (Nat.succ m) (ListType.nil KExpr))) (ListType.nil KExpr) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map f (list_take (Nat.succ m) (ListType.nil KExpr))) (list_map f (ListType.nil KExpr)) (ListType.nil KExpr) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) (list_map_nil f)))) ",
                    // inner cons (outer ih at rest)
                    "(fun (x : KExpr) (rest : ListType KExpr) (_ihinner : Eq (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f rest)) (list_map f (list_take (Nat.succ m) rest))) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f (ListType.cons KExpr x rest))) ",
                    "(ListType.cons KExpr (f x) (list_map f (list_take m rest))) ",
                    "(list_map f (list_take (Nat.succ m) (ListType.cons KExpr x rest))) ",
                    // lhs -> meet
                    "(Eq.trans (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f (ListType.cons KExpr x rest))) ",
                    "(ListType.cons KExpr (f x) (list_take m (list_map f rest))) ",
                    "(ListType.cons KExpr (f x) (list_map f (list_take m rest))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_map f (ListType.cons KExpr x rest))) ",
                    "(list_take (Nat.succ m) (ListType.cons KExpr (f x) (list_map f rest))) ",
                    "(ListType.cons KExpr (f x) (list_take m (list_map f rest))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take (Nat.succ m) L) ",
                    "(list_map f (ListType.cons KExpr x rest)) (ListType.cons KExpr (f x) (list_map f rest)) (list_map_cons f x rest)) ",
                    "(list_take_succ_cons m (f x) (list_map f rest))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => ListType.cons KExpr (f x) L) ",
                    "(list_take m (list_map f rest)) (list_map f (list_take m rest)) (ih rest))) ",
                    // meet -> rhs (symm)
                    "(Eq.symm (ListType KExpr) ",
                    "(list_map f (list_take (Nat.succ m) (ListType.cons KExpr x rest))) ",
                    "(ListType.cons KExpr (f x) (list_map f (list_take m rest))) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map f (list_take (Nat.succ m) (ListType.cons KExpr x rest))) ",
                    "(list_map f (ListType.cons KExpr x (list_take m rest))) ",
                    "(ListType.cons KExpr (f x) (list_map f (list_take m rest))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map f L) ",
                    "(list_take (Nat.succ m) (ListType.cons KExpr x rest)) (ListType.cons KExpr x (list_take m rest)) ",
                    "(list_take_succ_cons m x rest)) ",
                    "(list_map_cons f x (list_take m rest))))) ",
                    "xs0) ",
                    "n xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "list_map commutes with list_take. Nat.rec on n (motive generalizes xs); succ arm case-splits xs via ListType.rec using the outer Nat.rec IH at rest. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_map".to_string(),
                "list_take".to_string(),
                "Nat.rec".to_string(),
                "ListType.rec".to_string(),
                "list_take_zero".to_string(),
                "list_take_succ_nil".to_string(),
                "list_take_succ_cons".to_string(),
                "list_map_nil".to_string(),
                "list_map_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
