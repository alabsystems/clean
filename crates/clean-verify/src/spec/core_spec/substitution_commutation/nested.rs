// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nested substitution commutation: bvar case helpers.
//!
//! This module derives the per-case helper lemmas that feed into
//! `instantiate_at_nested_commutes_bvar`. The bvar theorem is the critical
//! base case of the structural induction that proves
//!   inst(inst(body, arg, sd), w, sd+od)
//!     = inst(inst(body, w, succ(sd+od)), inst(arg, w, od), sd)
//!
//! Cases on `i` vs `subst_depth`:
//!   - **below** (i < sd): both sides reduce to `bvar i`
//!   - **equal** (i = sd): both sides now reduce to explicit lifted forms; the
//!     remaining gap is the substitution/lift interchange bridge between them
//!   - **above** (i > sd): three sub-cases on gap vs outer_depth; sub-cases 1,3
//!     are pure bvar reductions, sub-case 2 (gap = od) uses inst_overlift_cancel

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_nested_commutation_bvar_helpers(&mut self) -> Result<(), SpecError> {
        // ── Below case: i < subst_depth ──
        //
        // When i < subst_depth (witnessed by `Nat.sub subst_depth i` being positive),
        // both sides of the nested commutation equation reduce to `KExpr.bvar i`:
        //
        // LHS: inst(inst(bvar i, arg, sd), w, sd+od)
        //    = inst(bvar i, w, sd+od)   [below: sd - i > 0]
        //    = bvar i                    [below: (sd+od) - i > 0, via nat_sub_pos_add_right]
        //
        // RHS: inst(inst(bvar i, w, succ(sd+od)), inst(arg,w,od), sd)
        //    = inst(bvar i, inst(arg,w,od), sd)  [below: succ(sd+od) - i > 0, via nat_sub_pos_succ]
        //    = bvar i                             [below: sd - i > 0]
        //
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_below".to_string(),
            type_src: concat!(
                "forall (i : Nat) (arg : KExpr) (w : KExpr) (subst_depth : Nat) (outer_depth : Nat), ",
                "Eq Nat (Nat.sub subst_depth i) ",
                "(Nat.succ (Nat.sub (Nat.sub subst_depth i) (Nat.succ Nat.zero))) -> ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                "(Nat.add subst_depth outer_depth)) ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                "(instantiate_at arg w outer_depth) subst_depth)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (arg : KExpr) (w : KExpr) ",
                    "(subst_depth : Nat) (outer_depth : Nat) ",
                    "(h : Eq Nat (Nat.sub subst_depth i) ",
                    "(Nat.succ (Nat.sub (Nat.sub subst_depth i) (Nat.succ Nat.zero)))) => ",
                    // Outer Eq.trans: LHS = bvar i = RHS
                    "Eq.trans KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    // ── LHS → bvar i ──
                    "(Eq.trans KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (KExpr.bvar i) w (Nat.add subst_depth outer_depth)) ",
                    "(KExpr.bvar i) ",
                    // inner: inst(bvar i, arg, sd) = bvar i
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w (Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (KExpr.bvar i) arg subst_depth) ",
                    "(KExpr.bvar i) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) arg subst_depth) ",
                    "(instantiate_bvar_at i subst_depth arg) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at_bvar i arg subst_depth) ",
                    "(instantiate_bvar_at_below i subst_depth arg h))) ",
                    // outer: inst(bvar i, w, sd+od) = bvar i
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) w (Nat.add subst_depth outer_depth)) ",
                    "(instantiate_bvar_at i (Nat.add subst_depth outer_depth) w) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at_bvar i w (Nat.add subst_depth outer_depth)) ",
                    "(instantiate_bvar_at_below i (Nat.add subst_depth outer_depth) w ",
                    "(nat_sub_pos_add_right subst_depth outer_depth i h)))) ",
                    // ── RHS → bvar i (Eq.symm) ──
                    "(Eq.symm KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(KExpr.bvar i) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(instantiate_at (KExpr.bvar i) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(KExpr.bvar i) ",
                    // inner: inst(bvar i, w, succ(sd+od)) = bvar i
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(KExpr.bvar i) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_bvar_at i (Nat.succ (Nat.add subst_depth outer_depth)) w) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at_bvar i w (Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_bvar_at_below i ",
                    "(Nat.succ (Nat.add subst_depth outer_depth)) w ",
                    "(nat_sub_pos_succ (Nat.add subst_depth outer_depth) i ",
                    "(nat_sub_pos_add_right subst_depth outer_depth i h))))) ",
                    // outer: inst(bvar i, inst(arg,w,od), sd) = bvar i
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(instantiate_bvar_at i subst_depth ",
                    "(instantiate_at arg w outer_depth)) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at_bvar i (instantiate_at arg w outer_depth) subst_depth) ",
                    "(instantiate_bvar_at_below i subst_depth ",
                    "(instantiate_at arg w outer_depth) h))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Below case (i < subst_depth) of nested substitution commutation on bvars. Both sides reduce to bvar i via instantiate_bvar_at_below, with positivity witnesses propagated by nat_sub_pos_add_right and nat_sub_pos_succ. DerivedProved. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "nat_sub_pos_add_right".to_string(),
                "nat_sub_pos_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Equal case, lhs reduction: i = subst_depth ──
        //
        // The inner substitution hits the equality branch directly:
        //
        // inst(bvar i, arg, sd) = lift_at arg 0 sd
        //
        // so the full lhs becomes the explicit substitution/lift-interchange
        // shape that remains to be bridged.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_equal_lhs".to_string(),
            type_src: concat!(
                "forall (i : Nat) (arg : KExpr) (w : KExpr) ",
                "(subst_depth : Nat) (outer_depth : Nat), ",
                "Eq Nat (Nat.sub subst_depth i) Nat.zero -> ",
                "Eq Nat (Nat.sub i subst_depth) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                "(Nat.add subst_depth outer_depth)) ",
                "(instantiate_at (lift_at arg Nat.zero subst_depth) w ",
                "(Nat.add subst_depth outer_depth))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (arg : KExpr) (w : KExpr) ",
                    "(subst_depth : Nat) (outer_depth : Nat) ",
                    "(h_outer : Eq Nat (Nat.sub subst_depth i) Nat.zero) ",
                    "(h_inner : Eq Nat (Nat.sub i subst_depth) Nat.zero) => ",
                    "Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w (Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (KExpr.bvar i) arg subst_depth) ",
                    "(lift_at arg Nat.zero subst_depth) ",
                    "(instantiate_at_bvar_eq_from_zero_witnesses i subst_depth arg ",
                    "h_outer h_inner)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Equal case lhs reduction for nested substitution commutation on bvars. When i = subst_depth, the inner substitution becomes lift_at arg 0 subst_depth, isolating the remaining substitution/lift interchange frontier. DerivedProved. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Equal case, rhs reduction: i = subst_depth ──
        //
        // The inner `w` substitution is strictly below `succ (sd + od)`, so it
        // collapses back to `bvar i`; the outer substitution then hits the
        // equality branch and yields the lifted instantiated argument.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_equal_rhs".to_string(),
            type_src: concat!(
                "forall (i : Nat) (arg : KExpr) (w : KExpr) ",
                "(subst_depth : Nat) (outer_depth : Nat), ",
                "Eq Nat (Nat.sub subst_depth i) Nat.zero -> ",
                "Eq Nat (Nat.sub i subst_depth) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                "(instantiate_at arg w outer_depth) subst_depth) ",
                "(lift_at (instantiate_at arg w outer_depth) Nat.zero subst_depth)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (arg : KExpr) (w : KExpr) ",
                    "(subst_depth : Nat) (outer_depth : Nat) ",
                    "(h_outer : Eq Nat (Nat.sub subst_depth i) Nat.zero) ",
                    "(h_inner : Eq Nat (Nat.sub i subst_depth) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(instantiate_at (KExpr.bvar i) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(lift_at (instantiate_at arg w outer_depth) Nat.zero subst_depth) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(KExpr.bvar i) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_bvar_at i (Nat.succ (Nat.add subst_depth outer_depth)) w) ",
                    "(KExpr.bvar i) ",
                    "(instantiate_at_bvar i w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_bvar_at_below i ",
                    "(Nat.succ (Nat.add subst_depth outer_depth)) w ",
                    "(nat_sub_pos_witness i (Nat.add subst_depth outer_depth) ",
                    "(nat_sub_zero_add_right i subst_depth outer_depth h_inner))))) ",
                    "(instantiate_at_bvar_eq_from_zero_witnesses i subst_depth ",
                    "(instantiate_at arg w outer_depth) h_outer h_inner)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Equal case rhs reduction for nested substitution commutation on bvars. When i = subst_depth, the rhs normalizes to lift_at (instantiate_at arg w outer_depth) 0 subst_depth, making the remaining equal-case obligation an explicit substitution/lift interchange theorem. DerivedProved. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "nat_sub_pos_witness".to_string(),
                "nat_sub_zero_add_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Above case: i > subst_depth ──
        //
        // When i > subst_depth (witnessed by `Nat.sub subst_depth i` being zero
        // and `Nat.sub i subst_depth` being `Nat.succ gap`), the proof splits
        // into three sub-cases on `gap` vs `outer_depth`:
        //
        //   Sub-case 1 (gap < od): both sides reduce to `bvar(sd + gap)`.
        //     LHS: inst(bvar(i-1), w, sd+od) = bvar(sd+gap) [below: sd+od > sd+gap].
        //     RHS: inst(bvar i, w, succ(sd+od)) = bvar i [below: i < succ(sd+od)],
        //          then inst(bvar i, inst(arg,w,od), sd) = bvar(i-1) = bvar(sd+gap).
        //
        //   Sub-case 2 (gap = od): both sides reduce to `lift_at(w, 0, sd+od)`.
        //     LHS: inst(bvar(sd+od), w, sd+od) = lift_at(w, 0, sd+od) [equal].
        //     RHS: inst(bvar i, w, succ(sd+od)) = lift_at(w, 0, succ(sd+od)) [equal],
        //          then inst_overlift_cancel strips one lift unit.
        //
        //   Sub-case 3 (gap > od): both sides reduce to `bvar(sd + gap - 1)`.
        //     LHS: inst(bvar(sd+gap), w, sd+od) = bvar(sd+gap-1) [above].
        //     RHS: inst(bvar i, w, succ(sd+od)) = bvar(sd+gap) [above: i > succ(sd+od)],
        //          then inst(bvar(sd+gap), inst(arg,w,od), sd) = bvar(sd+gap-1) [above].
        //
        // All three sub-cases are now fully constructive:
        //   - gap < od: instantiate_bvar_at_below / _above (pure bvar)
        //   - gap = od: instantiate_at_bvar_eq_from_zero_witnesses +
        //     inst_overlift_cancel (DerivedProved, axiom_deps = {})
        //   - gap > od: instantiate_bvar_at_above on both sides (pure bvar)
        //
        // Two Nat scaffolding lemmas (nat_sub_add_right_cancel,
        // nat_sub_pos_minuend) are registered first, then the three branch
        // helpers, then the master `_above` assembled via a double Nat.rec
        // convoy on `sub gap od` / `sub od gap`.
        //
        // Part of #464.
        self.add_nested_above_arith_scaffolding()?;
        self.add_nested_above_branch_lt()?;
        self.add_nested_above_branch_eq()?;
        self.add_nested_above_branch_gt()?;

        self.add_definition(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_above".to_string(),
            type_src: nested_above_goal_type(),
            value_src: Some(nested_above_master_proof()),
            is_axiom: false,
            description: concat!(
                "Above case (i > subst_depth) of nested substitution commutation on bvars. ",
                "Three sub-cases on gap vs outer_depth: gap < od (pure bvar), ",
                "gap = od (inst_overlift_cancel), gap > od (pure bvar). ",
                "DerivedProved via a double Nat.rec convoy on sub(gap,od)/sub(od,gap) ",
                "dispatching to the three branch helpers. Formerly a HelperAxiom. ",
                "Part of #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.refl".to_string(),
                "Nat.rec".to_string(),
                "instantiate_at_nested_commutes_bvar_above_lt".to_string(),
                "instantiate_at_nested_commutes_bvar_above_eq".to_string(),
                "instantiate_at_nested_commutes_bvar_above_gt".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Two pure-Nat scaffolding lemmas used by the above-case branch helpers:
    /// exact right-addend subtraction cancellation, and minuend-positivity from
    /// a positive subtraction witness.
    fn add_nested_above_arith_scaffolding(&mut self) -> Result<(), SpecError> {
        // nat_sub_add_right_cancel: (a + c) - (b + c) = a - b (exact).
        //
        // Nat.add recurses on its second argument, so add x (succ c) reduces to
        // succ (add x c) definitionally, and nat_sub_succ_succ peels both
        // shared succ-heads. Nat.rec on the shared right offset c.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_add_right_cancel".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (c : Nat), ",
                "Eq Nat (Nat.sub (Nat.add a c) (Nat.add b c)) (Nat.sub a b)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) => ",
                    "Nat.rec ",
                    "(fun (k : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.add a k) (Nat.add b k)) (Nat.sub a b)) ",
                    "(Eq.refl Nat (Nat.sub a b)) ",
                    "(fun (k : Nat) ",
                    "(ih : Eq Nat (Nat.sub (Nat.add a k) (Nat.add b k)) (Nat.sub a b)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.add a (Nat.succ k)) (Nat.add b (Nat.succ k))) ",
                    "(Nat.sub (Nat.add a k) (Nat.add b k)) ",
                    "(Nat.sub a b) ",
                    "(nat_sub_succ_succ (Nat.add a k) (Nat.add b k)) ",
                    "ih) ",
                    "c",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Exact right-addend subtraction cancellation: (a+c)-(b+c) = a-b. DerivedProved via Nat.rec on the shared right offset + nat_sub_succ_succ. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_pos_minuend: a - b = succ k -> a = succ (a - 1).
        //
        // A positive subtraction forces the minuend to be positive. Nat.rec on
        // a: at zero, sub 0 b = 0 contradicts succ k (nat_zero_ne_succ); at
        // succ a', sub (succ a') 1 = a', so succ (a - 1) = succ a' = a.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_minuend".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub a b) (Nat.succ k) -> ",
                "Eq Nat a (Nat.succ (Nat.sub a (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (k : Nat) => ",
                    "Nat.rec ",
                    "(fun (m : Nat) => ",
                    "Eq Nat (Nat.sub m b) (Nat.succ k) -> ",
                    "Eq Nat m (Nat.succ (Nat.sub m (Nat.succ Nat.zero)))) ",
                    // Zero branch: sub 0 b = 0 contradicts succ k. Transport the
                    // false equation 0 = succ k into the goal shape via Eq.cong on
                    // a Nat.rec whose zero/succ values are the goal's LHS/RHS.
                    "(fun (h0 : Eq Nat (Nat.sub Nat.zero b) (Nat.succ k)) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.succ (Nat.sub Nat.zero (Nat.succ Nat.zero))) n) ",
                    "Nat.zero (Nat.succ k) ",
                    "(Eq.trans Nat Nat.zero (Nat.sub Nat.zero b) (Nat.succ k) ",
                    "(Eq.symm Nat (Nat.sub Nat.zero b) Nat.zero (nat_sub_zero_left b)) ",
                    "h0)) ",
                    "(fun (m : Nat) ",
                    "(_ : Eq Nat (Nat.sub m b) (Nat.succ k) -> ",
                    "Eq Nat m (Nat.succ (Nat.sub m (Nat.succ Nat.zero)))) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ m) b) (Nat.succ k)) => ",
                    "Eq.cong Nat Nat Nat.succ ",
                    "m ",
                    "(Nat.sub (Nat.succ m) (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.succ m) (Nat.succ Nat.zero)) ",
                    "m ",
                    "(nat_sub_succ_one m))) ",
                    "a",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "If a - b = succ k then a = succ (a - 1) (positive minuend). DerivedProved via Nat.rec on a: the zero branch transports the false 0 = succ k through Eq.cong, the succ branch uses nat_sub_succ_one. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// gap < od sub-case: both sides reduce to `bvar (i - 1)`.
    fn add_nested_above_branch_lt(&mut self) -> Result<(), SpecError> {
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_above_lt".to_string(),
            type_src: nested_above_lt_type(),
            value_src: Some(nested_above_lt_proof()),
            is_axiom: false,
            description: "Above case, gap < od sub-branch of nested substitution commutation on bvars. Both sides reduce to bvar(i-1). DerivedProved. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(nested_above_branch_deps()),
            axiom_deps: HashSet::new(),
        })
    }

    /// gap = od sub-case: both sides reduce to `lift_at(w, 0, sd + od)`.
    fn add_nested_above_branch_eq(&mut self) -> Result<(), SpecError> {
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_above_eq".to_string(),
            type_src: nested_above_eq_type(),
            value_src: Some(nested_above_eq_proof()),
            is_axiom: false,
            description: "Above case, gap = od sub-branch of nested substitution commutation on bvars. Both sides reduce to lift_at(w, 0, sd+od); the RHS unit-lift is stripped by inst_overlift_cancel. DerivedProved. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(nested_above_eq_deps()),
            axiom_deps: HashSet::new(),
        })
    }

    /// gap > od sub-case: both sides reduce to `bvar ((i - 1) - 1)`.
    fn add_nested_above_branch_gt(&mut self) -> Result<(), SpecError> {
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_above_gt".to_string(),
            type_src: nested_above_gt_type(),
            value_src: Some(nested_above_gt_proof()),
            is_axiom: false,
            description: "Above case, gap > od sub-branch of nested substitution commutation on bvars. Both sides reduce to bvar((i-1)-1). DerivedProved. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(nested_above_gt_deps()),
            axiom_deps: HashSet::new(),
        })
    }
}

// ════════════════════════════════════════════════════════════════════════
// Proof-term builders for the above-case branches.
//
// Binder convention inside these terms: i, arg, w, sd, od, gap.
// The goal uses subst_depth := sd, outer_depth := od.
//
// Shared abbreviations:
//   D   = Nat.add sd od                  (LHS outer depth)
//   SD1 = Nat.succ (Nat.add sd od)       (RHS inner depth)
//   X   = Nat.sub i (Nat.succ Nat.zero)  (i - 1)
//   AGS = Nat.add gap sd                 (= i - 1, propositionally)
// ════════════════════════════════════════════════════════════════════════

/// `Nat.add sd od`.
const D: &str = "(Nat.add sd od)";
/// `Nat.succ (Nat.add sd od)`.
const SD1: &str = "(Nat.succ (Nat.add sd od))";
/// `Nat.sub i 1`.
const X: &str = "(Nat.sub i (Nat.succ Nat.zero))";

/// LHS of the master equation, with branch binder names (i, arg, w, sd, od).
fn lhs() -> String {
    format!("(instantiate_at (instantiate_at (KExpr.bvar i) arg sd) w {D})")
}

/// RHS of the master equation, with branch binder names.
fn rhs() -> String {
    format!(
        "(instantiate_at (instantiate_at (KExpr.bvar i) w {SD1}) \
         (instantiate_at arg w od) sd)"
    )
}

/// Goal type of the master `_above` (full subst_depth/outer_depth names).
fn nested_above_goal_type() -> String {
    concat!(
        "forall (i : Nat) (arg : KExpr) (w : KExpr) ",
        "(subst_depth : Nat) (outer_depth : Nat), ",
        "Eq Nat (Nat.sub subst_depth i) Nat.zero -> ",
        "forall (gap : Nat), ",
        "Eq Nat (Nat.sub i subst_depth) (Nat.succ gap) -> ",
        "Eq KExpr ",
        "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
        "(Nat.add subst_depth outer_depth)) ",
        "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
        "(Nat.succ (Nat.add subst_depth outer_depth))) ",
        "(instantiate_at arg w outer_depth) subst_depth)",
    )
    .to_string()
}

/// `Eq Nat i (Nat.add (Nat.succ gap) sd)` — from the two entry witnesses.
const H_I: &str = "(nat_sub_zero_succ_gap_to_add i sd gap h_outer h_gap)";

/// `Eq Nat (Nat.sub i 1) (Nat.add gap sd)`.
fn h_im1() -> String {
    format!(
        "(Eq.trans Nat {X} (Nat.sub (Nat.add (Nat.succ gap) sd) (Nat.succ Nat.zero)) \
         (Nat.add gap sd) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) \
         i (Nat.add (Nat.succ gap) sd) {H_I}) \
         (Eq.trans Nat (Nat.sub (Nat.add (Nat.succ gap) sd) (Nat.succ Nat.zero)) \
         (Nat.add (Nat.sub (Nat.succ gap) (Nat.succ Nat.zero)) sd) (Nat.add gap sd) \
         (nat_pred_add_right (Nat.succ gap) sd Nat.zero gap \
         (nat_sub_zero_right (Nat.succ gap))) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.add x sd) \
         (Nat.sub (Nat.succ gap) (Nat.succ Nat.zero)) gap (nat_sub_succ_one gap))))"
    )
}

/// `Eq Nat (Nat.succ (Nat.add sd od)) (Nat.add (Nat.succ od) sd)`.
const H_MIN: &str = concat!(
    "(Eq.trans Nat (Nat.succ (Nat.add sd od)) (Nat.succ (Nat.add od sd)) ",
    "(Nat.add (Nat.succ od) sd) ",
    "(Eq.cong Nat Nat Nat.succ (Nat.add sd od) (Nat.add od sd) ",
    "(nat_add_comm sd od)) ",
    "(Eq.symm Nat (Nat.add (Nat.succ od) sd) (Nat.succ (Nat.add od sd)) ",
    "(nat_succ_add od sd)))",
);

/// `PL1 : Eq KExpr (inst(bvar i, arg, sd)) (bvar (i - 1))`.
fn pl1() -> String {
    format!(
        "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) arg sd) \
         (instantiate_bvar_at i sd arg) (KExpr.bvar {X}) \
         (instantiate_at_bvar i arg sd) \
         (instantiate_bvar_at_above i sd arg h_outer \
         (nat_pos_witness_from_succ_eq (Nat.sub i sd) gap h_gap)))"
    )
}

/// `PR2 : Eq KExpr (inst(bvar i, inst(arg,w,od), sd)) (bvar (i - 1))`.
fn pr2() -> String {
    format!(
        "(Eq.trans KExpr \
         (instantiate_at (KExpr.bvar i) (instantiate_at arg w od) sd) \
         (instantiate_bvar_at i sd (instantiate_at arg w od)) (KExpr.bvar {X}) \
         (instantiate_at_bvar i (instantiate_at arg w od) sd) \
         (instantiate_bvar_at_above i sd (instantiate_at arg w od) h_outer \
         (nat_pos_witness_from_succ_eq (Nat.sub i sd) gap h_gap)))"
    )
}

/// `h_Lsub : Eq Nat (Nat.sub D (i - 1)) (Nat.sub od gap)`.
fn h_lsub() -> String {
    format!(
        "(Eq.trans Nat (Nat.sub {D} {X}) (Nat.sub {D} (Nat.add gap sd)) \
         (Nat.sub od gap) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub {D} x) {X} (Nat.add gap sd) {him1}) \
         (Eq.trans Nat (Nat.sub {D} (Nat.add gap sd)) \
         (Nat.sub (Nat.add od sd) (Nat.add gap sd)) (Nat.sub od gap) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x (Nat.add gap sd)) \
         {D} (Nat.add od sd) (nat_add_comm sd od)) \
         (nat_sub_add_right_cancel od gap sd)))",
        him1 = h_im1()
    )
}

/// `h_R1sub : Eq Nat (Nat.sub SD1 i) (Nat.sub od gap)`.
fn h_r1sub() -> String {
    format!(
        "(Eq.trans Nat (Nat.sub {SD1} i) \
         (Nat.sub (Nat.add (Nat.succ od) sd) (Nat.add (Nat.succ gap) sd)) \
         (Nat.sub od gap) \
         (Eq.trans Nat (Nat.sub {SD1} i) \
         (Nat.sub (Nat.add (Nat.succ od) sd) i) \
         (Nat.sub (Nat.add (Nat.succ od) sd) (Nat.add (Nat.succ gap) sd)) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x i) {SD1} \
         (Nat.add (Nat.succ od) sd) {H_MIN}) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub (Nat.add (Nat.succ od) sd) x) \
         i (Nat.add (Nat.succ gap) sd) {H_I})) \
         (Eq.trans Nat \
         (Nat.sub (Nat.add (Nat.succ od) sd) (Nat.add (Nat.succ gap) sd)) \
         (Nat.sub (Nat.succ od) (Nat.succ gap)) (Nat.sub od gap) \
         (nat_sub_add_right_cancel (Nat.succ od) (Nat.succ gap) sd) \
         (nat_sub_succ_succ od gap)))"
    )
}

/// `h_Linner : Eq Nat (Nat.sub (i - 1) D) (Nat.sub gap od)`.
fn h_linner() -> String {
    format!(
        "(Eq.trans Nat (Nat.sub {X} {D}) (Nat.sub (Nat.add gap sd) {D}) \
         (Nat.sub gap od) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x {D}) {X} (Nat.add gap sd) {him1}) \
         (Eq.trans Nat (Nat.sub (Nat.add gap sd) {D}) \
         (Nat.sub (Nat.add gap sd) (Nat.add od sd)) (Nat.sub gap od) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub (Nat.add gap sd) x) \
         {D} (Nat.add od sd) (nat_add_comm sd od)) \
         (nat_sub_add_right_cancel gap od sd)))",
        him1 = h_im1()
    )
}

/// `h_R1inner : Eq Nat (Nat.sub i SD1) (Nat.sub gap od)`.
fn h_r1inner() -> String {
    format!(
        "(Eq.trans Nat (Nat.sub i {SD1}) \
         (Nat.sub (Nat.add (Nat.succ gap) sd) {SD1}) (Nat.sub gap od) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x {SD1}) i \
         (Nat.add (Nat.succ gap) sd) {H_I}) \
         (Eq.trans Nat (Nat.sub (Nat.add (Nat.succ gap) sd) {SD1}) \
         (Nat.sub (Nat.add (Nat.succ gap) sd) (Nat.add (Nat.succ od) sd)) \
         (Nat.sub gap od) \
         (Eq.cong Nat Nat (fun (x : Nat) => Nat.sub (Nat.add (Nat.succ gap) sd) x) \
         {SD1} (Nat.add (Nat.succ od) sd) {H_MIN}) \
         (Eq.trans Nat \
         (Nat.sub (Nat.add (Nat.succ gap) sd) (Nat.add (Nat.succ od) sd)) \
         (Nat.sub (Nat.succ gap) (Nat.succ od)) (Nat.sub gap od) \
         (nat_sub_add_right_cancel (Nat.succ gap) (Nat.succ od) sd) \
         (nat_sub_succ_succ gap od))))"
    )
}

// ── Branch types ──

/// Common prefix of every branch type (binders + the two entry witnesses).
const BRANCH_PREFIX: &str = concat!(
    "forall (i : Nat) (arg : KExpr) (w : KExpr) (sd : Nat) (od : Nat) ",
    "(gap : Nat) (k : Nat), ",
    "Eq Nat (Nat.sub sd i) Nat.zero -> ",
    "Eq Nat (Nat.sub i sd) (Nat.succ gap) -> ",
);

fn nested_above_lt_type() -> String {
    format!(
        "{BRANCH_PREFIX}Eq Nat (Nat.sub od gap) (Nat.succ k) -> Eq KExpr {l} {r}",
        l = lhs(),
        r = rhs()
    )
}

fn nested_above_gt_type() -> String {
    format!(
        "{BRANCH_PREFIX}Eq Nat (Nat.sub gap od) (Nat.succ k) -> Eq KExpr {l} {r}",
        l = lhs(),
        r = rhs()
    )
}

fn nested_above_eq_type() -> String {
    format!(
        concat!(
            "forall (i : Nat) (arg : KExpr) (w : KExpr) (sd : Nat) (od : Nat) ",
            "(gap : Nat), ",
            "Eq Nat (Nat.sub sd i) Nat.zero -> ",
            "Eq Nat (Nat.sub i sd) (Nat.succ gap) -> ",
            "Eq Nat (Nat.sub od gap) Nat.zero -> ",
            "Eq Nat (Nat.sub gap od) Nat.zero -> ",
            "Eq KExpr {l} {r}",
        ),
        l = lhs(),
        r = rhs()
    )
}

// ── Branch proofs ──

/// gap < od: LHS = bvar(i-1) (below); RHS reduces bvar i (below) then to
/// bvar(i-1) (above). Both sides equal bvar(i-1).
fn nested_above_lt_proof() -> String {
    let x = X;
    // W_L : sub D (i-1) is positive (= sub od gap = S k).
    let w_l = format!(
        "(nat_pos_witness_from_succ_eq (Nat.sub {D} {x}) \
         (Nat.sub (Nat.sub od gap) (Nat.succ Nat.zero)) \
         (Eq.trans Nat (Nat.sub {D} {x}) (Nat.sub od gap) \
         (Nat.succ (Nat.sub (Nat.sub od gap) (Nat.succ Nat.zero))) \
         {hlsub} \
         (nat_pos_witness_from_succ_eq (Nat.sub od gap) k h_lt)))",
        hlsub = h_lsub()
    );
    // W_R1 : sub SD1 i is positive (= sub od gap = S k).
    let w_r1 = format!(
        "(nat_pos_witness_from_succ_eq (Nat.sub {SD1} i) \
         (Nat.sub (Nat.sub od gap) (Nat.succ Nat.zero)) \
         (Eq.trans Nat (Nat.sub {SD1} i) (Nat.sub od gap) \
         (Nat.succ (Nat.sub (Nat.sub od gap) (Nat.succ Nat.zero))) \
         {hr1sub} \
         (nat_pos_witness_from_succ_eq (Nat.sub od gap) k h_lt)))",
        hr1sub = h_r1sub()
    );
    // LHS -> bvar(i-1).
    let lhs_to_x = format!(
        "(Eq.trans KExpr {l} (instantiate_at (KExpr.bvar {x}) w {D}) (KExpr.bvar {x}) \
         (Eq.cong KExpr KExpr (fun (e : KExpr) => instantiate_at e w {D}) \
         (instantiate_at (KExpr.bvar i) arg sd) (KExpr.bvar {x}) {pl1}) \
         (Eq.trans KExpr (instantiate_at (KExpr.bvar {x}) w {D}) \
         (instantiate_bvar_at {x} {D} w) (KExpr.bvar {x}) \
         (instantiate_at_bvar {x} w {D}) \
         (instantiate_bvar_at_below {x} {D} w {w_l})))",
        l = lhs(),
        pl1 = pl1()
    );
    // R1 : inst(bvar i, w, SD1) = bvar i.
    let r1 = format!(
        "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) w {SD1}) \
         (instantiate_bvar_at i {SD1} w) (KExpr.bvar i) \
         (instantiate_at_bvar i w {SD1}) \
         (instantiate_bvar_at_below i {SD1} w {w_r1}))"
    );
    // RHS -> bvar(i-1).
    let rhs_to_x = format!(
        "(Eq.trans KExpr {r} \
         (instantiate_at (KExpr.bvar i) (instantiate_at arg w od) sd) (KExpr.bvar {x}) \
         (Eq.cong KExpr KExpr \
         (fun (e : KExpr) => instantiate_at e (instantiate_at arg w od) sd) \
         (instantiate_at (KExpr.bvar i) w {SD1}) (KExpr.bvar i) {r1}) \
         {pr2})",
        r = rhs(),
        pr2 = pr2()
    );
    format!(
        "fun (i : Nat) (arg : KExpr) (w : KExpr) (sd : Nat) (od : Nat) (gap : Nat) \
         (k : Nat) (h_outer : Eq Nat (Nat.sub sd i) Nat.zero) \
         (h_gap : Eq Nat (Nat.sub i sd) (Nat.succ gap)) \
         (h_lt : Eq Nat (Nat.sub od gap) (Nat.succ k)) => \
         Eq.trans KExpr {l} (KExpr.bvar {x}) {r} {lhs_to_x} \
         (Eq.symm KExpr {r} (KExpr.bvar {x}) {rhs_to_x})",
        l = lhs(),
        r = rhs()
    )
}

/// gap = od: LHS = lift(w,0,D) (equal); RHS reduces bvar i to lift(w,0,SD1)
/// (equal) then strips one lift via inst_overlift_cancel to lift(w,0,D).
fn nested_above_eq_proof() -> String {
    let x = X;
    let lift_d = format!("(lift_at w Nat.zero {D})");
    let lift_sd1 = format!("(lift_at w Nat.zero {SD1})");
    // h_outer_zero : sub D (i-1) = 0.
    let h_outer_zero = format!(
        "(Eq.trans Nat (Nat.sub {D} {x}) (Nat.sub od gap) Nat.zero {hlsub} h_od_gap)",
        hlsub = h_lsub()
    );
    // h_inner_zero : sub (i-1) D = 0.
    let h_inner_zero = format!(
        "(Eq.trans Nat (Nat.sub {x} {D}) (Nat.sub gap od) Nat.zero {hlinner} h_gap_od)",
        hlinner = h_linner()
    );
    // h_R1_outer_zero : sub SD1 i = 0.
    let h_r1_outer_zero = format!(
        "(Eq.trans Nat (Nat.sub {SD1} i) (Nat.sub od gap) Nat.zero {hr1sub} h_od_gap)",
        hr1sub = h_r1sub()
    );
    // h_R1_inner_zero : sub i SD1 = 0.
    let h_r1_inner_zero = format!(
        "(Eq.trans Nat (Nat.sub i {SD1}) (Nat.sub gap od) Nat.zero {hr1inner} h_gap_od)",
        hr1inner = h_r1inner()
    );
    // sub sd D = 0 (the inst_overlift_cancel precondition).
    let h_sd_le_d = "(nat_sub_zero_add_right sd sd od (nat_sub_self sd))".to_string();
    // LHS -> lift(w,0,D).
    let lhs_to_lift = format!(
        "(Eq.trans KExpr {l} (instantiate_at (KExpr.bvar {x}) w {D}) {lift_d} \
         (Eq.cong KExpr KExpr (fun (e : KExpr) => instantiate_at e w {D}) \
         (instantiate_at (KExpr.bvar i) arg sd) (KExpr.bvar {x}) {pl1}) \
         (instantiate_at_bvar_eq_from_zero_witnesses {x} {D} w {h_outer_zero} {h_inner_zero}))",
        l = lhs(),
        pl1 = pl1()
    );
    // R1 : inst(bvar i, w, SD1) = lift(w,0,SD1).
    let r1 = format!(
        "(instantiate_at_bvar_eq_from_zero_witnesses i {SD1} w \
         {h_r1_outer_zero} {h_r1_inner_zero})"
    );
    // RHS -> lift(w,0,D).
    let rhs_to_lift = format!(
        "(Eq.trans KExpr {r} \
         (instantiate_at {lift_sd1} (instantiate_at arg w od) sd) {lift_d} \
         (Eq.cong KExpr KExpr \
         (fun (e : KExpr) => instantiate_at e (instantiate_at arg w od) sd) \
         (instantiate_at (KExpr.bvar i) w {SD1}) {lift_sd1} {r1}) \
         (inst_overlift_cancel w (instantiate_at arg w od) {D} sd {h_sd_le_d}))",
        r = rhs()
    );
    format!(
        "fun (i : Nat) (arg : KExpr) (w : KExpr) (sd : Nat) (od : Nat) (gap : Nat) \
         (h_outer : Eq Nat (Nat.sub sd i) Nat.zero) \
         (h_gap : Eq Nat (Nat.sub i sd) (Nat.succ gap)) \
         (h_od_gap : Eq Nat (Nat.sub od gap) Nat.zero) \
         (h_gap_od : Eq Nat (Nat.sub gap od) Nat.zero) => \
         Eq.trans KExpr {l} {lift_d} {r} {lhs_to_lift} \
         (Eq.symm KExpr {r} {lift_d} {rhs_to_lift})",
        l = lhs(),
        r = rhs()
    )
}

/// gap > od: LHS = bvar((i-1)-1) (above); RHS reduces bvar i to bvar(i-1)
/// (above) then to bvar((i-1)-1) (above). Both sides equal bvar((i-1)-1).
fn nested_above_gt_proof() -> String {
    let x = X;
    // Y = (i-1)-1.
    let y = format!("(Nat.sub {x} (Nat.succ Nat.zero))");
    // h_od_gap : sub od gap = 0 (from sub gap od positive).
    let h_od_gap = "(nat_sub_zero_of_sub_pos gap od k h_gt)".to_string();
    // ── LHS: inst(bvar(i-1), w, D) = bvar((i-1)-1) (above) ──
    // h_L_outer_zero : sub D (i-1) = 0.
    let h_l_outer_zero = format!(
        "(Eq.trans Nat (Nat.sub {D} {x}) (Nat.sub od gap) Nat.zero {hlsub} {h_od_gap})",
        hlsub = h_lsub()
    );
    // h_L_inner_pos : sub (i-1) D positive.
    let h_l_inner_pos = format!(
        "(nat_pos_witness_from_succ_eq (Nat.sub {x} {D}) \
         (Nat.sub (Nat.sub gap od) (Nat.succ Nat.zero)) \
         (Eq.trans Nat (Nat.sub {x} {D}) (Nat.sub gap od) \
         (Nat.succ (Nat.sub (Nat.sub gap od) (Nat.succ Nat.zero))) \
         {hlinner} \
         (nat_pos_witness_from_succ_eq (Nat.sub gap od) k h_gt)))",
        hlinner = h_linner()
    );
    // LHS -> bvar(Y).
    let lhs_to_y = format!(
        "(Eq.trans KExpr {l} (instantiate_at (KExpr.bvar {x}) w {D}) (KExpr.bvar {y}) \
         (Eq.cong KExpr KExpr (fun (e : KExpr) => instantiate_at e w {D}) \
         (instantiate_at (KExpr.bvar i) arg sd) (KExpr.bvar {x}) {pl1}) \
         (Eq.trans KExpr (instantiate_at (KExpr.bvar {x}) w {D}) \
         (instantiate_bvar_at {x} {D} w) (KExpr.bvar {y}) \
         (instantiate_at_bvar {x} w {D}) \
         (instantiate_bvar_at_above {x} {D} w {h_l_outer_zero} {h_l_inner_pos})))",
        l = lhs(),
        pl1 = pl1()
    );
    // ── RHS R1: inst(bvar i, w, SD1) = bvar(i-1) (above) ──
    // h_R1_outer_zero : sub SD1 i = 0.
    let h_r1_outer_zero = format!(
        "(Eq.trans Nat (Nat.sub {SD1} i) (Nat.sub od gap) Nat.zero {hr1sub} {h_od_gap})",
        hr1sub = h_r1sub()
    );
    // h_R1_inner_pos : sub i SD1 positive.
    let h_r1_inner_pos = format!(
        "(nat_pos_witness_from_succ_eq (Nat.sub i {SD1}) \
         (Nat.sub (Nat.sub gap od) (Nat.succ Nat.zero)) \
         (Eq.trans Nat (Nat.sub i {SD1}) (Nat.sub gap od) \
         (Nat.succ (Nat.sub (Nat.sub gap od) (Nat.succ Nat.zero))) \
         {hr1inner} \
         (nat_pos_witness_from_succ_eq (Nat.sub gap od) k h_gt)))",
        hr1inner = h_r1inner()
    );
    let r1 = format!(
        "(Eq.trans KExpr (instantiate_at (KExpr.bvar i) w {SD1}) \
         (instantiate_bvar_at i {SD1} w) (KExpr.bvar {x}) \
         (instantiate_at_bvar i w {SD1}) \
         (instantiate_bvar_at_above i {SD1} w {h_r1_outer_zero} {h_r1_inner_pos}))"
    );
    // ── RHS R2: inst(bvar(i-1), inst(arg,w,od), sd) = bvar((i-1)-1) (above) ──
    // h_R2_outer_zero : sub sd (i-1) = 0.
    let h_r2_outer_zero = format!(
        "(Eq.trans Nat (Nat.sub sd {x}) (Nat.sub sd (Nat.add gap sd)) Nat.zero \
         (Eq.cong Nat Nat (fun (e : Nat) => Nat.sub sd e) {x} (Nat.add gap sd) {him1}) \
         (Eq.trans Nat (Nat.sub sd (Nat.add gap sd)) (Nat.sub sd (Nat.add sd gap)) \
         Nat.zero \
         (Eq.cong Nat Nat (fun (e : Nat) => Nat.sub sd e) \
         (Nat.add gap sd) (Nat.add sd gap) (nat_add_comm gap sd)) \
         (nat_sub_zero_add_right sd sd gap (nat_sub_self sd))))",
        him1 = h_im1()
    );
    // h_R2_inner : sub (i-1) sd = gap.
    let h_r2_inner_sub = format!(
        "(Eq.trans Nat (Nat.sub {x} sd) (Nat.sub (Nat.add gap sd) sd) gap \
         (Eq.cong Nat Nat (fun (e : Nat) => Nat.sub e sd) {x} (Nat.add gap sd) {him1}) \
         (Eq.trans Nat (Nat.sub (Nat.add gap sd) sd) \
         (Nat.sub (Nat.add gap sd) (Nat.add Nat.zero sd)) gap \
         (Eq.cong Nat Nat (fun (e : Nat) => Nat.sub (Nat.add gap sd) e) \
         sd (Nat.add Nat.zero sd) \
         (Eq.symm Nat (Nat.add Nat.zero sd) sd (nat_zero_add sd))) \
         (Eq.trans Nat (Nat.sub (Nat.add gap sd) (Nat.add Nat.zero sd)) \
         (Nat.sub gap Nat.zero) gap \
         (nat_sub_add_right_cancel gap Nat.zero sd) \
         (nat_sub_zero_right gap))))",
        him1 = h_im1()
    );
    // h_R2_inner_pos : sub (i-1) sd positive (= gap, gap positive from gap>od).
    let h_r2_inner_pos = format!(
        "(nat_pos_witness_from_succ_eq (Nat.sub {x} sd) \
         (Nat.sub gap (Nat.succ Nat.zero)) \
         (Eq.trans Nat (Nat.sub {x} sd) gap \
         (Nat.succ (Nat.sub gap (Nat.succ Nat.zero))) \
         {h_r2_inner_sub} \
         (nat_sub_pos_minuend gap od k h_gt)))"
    );
    // R2 : inst(bvar(i-1), inst(arg,w,od), sd) = bvar(Y).
    let r2 = format!(
        "(Eq.trans KExpr \
         (instantiate_at (KExpr.bvar {x}) (instantiate_at arg w od) sd) \
         (instantiate_bvar_at {x} sd (instantiate_at arg w od)) (KExpr.bvar {y}) \
         (instantiate_at_bvar {x} (instantiate_at arg w od) sd) \
         (instantiate_bvar_at_above {x} sd (instantiate_at arg w od) \
         {h_r2_outer_zero} {h_r2_inner_pos}))"
    );
    // RHS -> bvar(Y).
    let rhs_to_y = format!(
        "(Eq.trans KExpr {r} \
         (instantiate_at (KExpr.bvar {x}) (instantiate_at arg w od) sd) (KExpr.bvar {y}) \
         (Eq.cong KExpr KExpr \
         (fun (e : KExpr) => instantiate_at e (instantiate_at arg w od) sd) \
         (instantiate_at (KExpr.bvar i) w {SD1}) (KExpr.bvar {x}) {r1}) \
         {r2})",
        r = rhs()
    );
    format!(
        "fun (i : Nat) (arg : KExpr) (w : KExpr) (sd : Nat) (od : Nat) (gap : Nat) \
         (k : Nat) (h_outer : Eq Nat (Nat.sub sd i) Nat.zero) \
         (h_gap : Eq Nat (Nat.sub i sd) (Nat.succ gap)) \
         (h_gt : Eq Nat (Nat.sub gap od) (Nat.succ k)) => \
         Eq.trans KExpr {l} (KExpr.bvar {y}) {r} {lhs_to_y} \
         (Eq.symm KExpr {r} (KExpr.bvar {y}) {rhs_to_y})",
        l = lhs(),
        r = rhs()
    )
}

/// Master `_above`: double Nat.rec convoy on sub(gap,od) then sub(od,gap)
/// dispatching to the gt / eq / lt branch helpers.
fn nested_above_master_proof() -> String {
    let goal = "Eq KExpr \
         (instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w \
         (Nat.add subst_depth outer_depth)) \
         (instantiate_at (instantiate_at (KExpr.bvar i) w \
         (Nat.succ (Nat.add subst_depth outer_depth))) \
         (instantiate_at arg w outer_depth) subst_depth)"
        .to_string();
    format!(
        "fun (i : Nat) (arg : KExpr) (w : KExpr) (subst_depth : Nat) \
         (outer_depth : Nat) (h_outer : Eq Nat (Nat.sub subst_depth i) Nat.zero) \
         (gap : Nat) (h_gap : Eq Nat (Nat.sub i subst_depth) (Nat.succ gap)) => \
         Nat.rec \
         (fun (g : Nat) => Eq Nat (Nat.sub gap outer_depth) g -> {goal}) \
         (fun (h_gap_od : Eq Nat (Nat.sub gap outer_depth) Nat.zero) => \
         Nat.rec \
         (fun (g2 : Nat) => Eq Nat (Nat.sub outer_depth gap) g2 -> {goal}) \
         (fun (h_od_gap : Eq Nat (Nat.sub outer_depth gap) Nat.zero) => \
         instantiate_at_nested_commutes_bvar_above_eq i arg w subst_depth outer_depth \
         gap h_outer h_gap h_od_gap h_gap_od) \
         (fun (k2 : Nat) \
         (_ : Eq Nat (Nat.sub outer_depth gap) k2 -> {goal}) \
         (h_lt : Eq Nat (Nat.sub outer_depth gap) (Nat.succ k2)) => \
         instantiate_at_nested_commutes_bvar_above_lt i arg w subst_depth outer_depth \
         gap k2 h_outer h_gap h_lt) \
         (Nat.sub outer_depth gap) (Eq.refl Nat (Nat.sub outer_depth gap))) \
         (fun (k : Nat) \
         (_ : Eq Nat (Nat.sub gap outer_depth) k -> {goal}) \
         (h_gt : Eq Nat (Nat.sub gap outer_depth) (Nat.succ k)) => \
         instantiate_at_nested_commutes_bvar_above_gt i arg w subst_depth outer_depth \
         gap k h_outer h_gap h_gt) \
         (Nat.sub gap outer_depth) (Eq.refl Nat (Nat.sub gap outer_depth))"
    )
}

// ── Dependency sets ──

fn nested_above_branch_deps() -> HashSet<String> {
    HashSet::from([
        "Eq.cong".to_string(),
        "Eq.symm".to_string(),
        "Eq.trans".to_string(),
        "instantiate_at_bvar".to_string(),
        "instantiate_bvar_at_above".to_string(),
        "instantiate_bvar_at_below".to_string(),
        "nat_add_comm".to_string(),
        "nat_pos_witness_from_succ_eq".to_string(),
        "nat_pred_add_right".to_string(),
        "nat_sub_add_right_cancel".to_string(),
        "nat_sub_succ_one".to_string(),
        "nat_sub_succ_succ".to_string(),
        "nat_sub_zero_right".to_string(),
        "nat_sub_zero_succ_gap_to_add".to_string(),
        "nat_succ_add".to_string(),
    ])
}

fn nested_above_eq_deps() -> HashSet<String> {
    let mut deps = nested_above_branch_deps();
    deps.insert("instantiate_at_bvar_eq_from_zero_witnesses".to_string());
    deps.insert("inst_overlift_cancel".to_string());
    deps.insert("nat_sub_self".to_string());
    deps.insert("nat_sub_zero_add_right".to_string());
    deps
}

fn nested_above_gt_deps() -> HashSet<String> {
    let mut deps = nested_above_branch_deps();
    deps.insert("nat_sub_pos_minuend".to_string());
    deps.insert("nat_sub_zero_of_sub_pos".to_string());
    deps.insert("nat_sub_zero_add_right".to_string());
    deps.insert("nat_sub_self".to_string());
    deps.insert("nat_zero_add".to_string());
    deps
}

#[cfg(test)]
mod tests {
    use crate::spec::ProofStatus;
    use crate::test_utils::run_with_stack;
    use crate::Specification;

    fn build_substitution_spec_with_stack() -> Specification {
        run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution/WHNF test spec should build")
        })
    }

    #[test]
    fn test_nested_commutes_bvar_above_is_derived_proved() {
        let spec = build_substitution_spec_with_stack();

        // The above case and all three of its sub-branches are now genuine
        // kernel-checked DerivedProved theorems with empty axiom_deps.
        for name in [
            "instantiate_at_nested_commutes_bvar_above",
            "instantiate_at_nested_commutes_bvar_above_lt",
            "instantiate_at_nested_commutes_bvar_above_eq",
            "instantiate_at_nested_commutes_bvar_above_gt",
            "nat_sub_add_right_cancel",
            "nat_sub_pos_minuend",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should exist"));
            assert!(!def.is_axiom, "{name} should no longer be a helper axiom");
            assert!(
                def.value_src.is_some(),
                "{name} should have an explicit kernel-checked proof term"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be fully constructive"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should have no remaining axiom deps: {:?}",
                def.axiom_deps
            );
        }
    }

    #[test]
    fn test_nested_commutes_bvar_equal_reductions_are_constructive() {
        let spec = build_substitution_spec_with_stack();

        for name in [
            "instantiate_at_nested_commutes_bvar_equal_lhs",
            "instantiate_at_nested_commutes_bvar_equal_rhs",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should exist"));
            assert!(
                def.value_src.is_some(),
                "{name} should have an explicit proof term"
            );
            assert!(!def.is_axiom, "{name} should not be a helper axiom");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be fully constructive"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should not retain helper blockers: {:?}",
                def.axiom_deps
            );
        }
    }

    #[test]
    fn test_subst_lift_interchange_is_fully_derived() {
        let spec = build_substitution_spec_with_stack();

        let def = spec
            .definitions()
            .get("subst_lift_interchange")
            .expect("subst_lift_interchange should exist");
        assert!(
            !def.is_axiom,
            "subst_lift_interchange should stay derived, not regress to a helper axiom"
        );
        assert!(
            def.value_src.is_some(),
            "subst_lift_interchange should keep its bridge proof term"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "subst_lift_interchange should be fully DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "subst_lift_interchange should have no remaining axiom deps (bvar_gen is DerivedProved): {:?}",
            def.axiom_deps
        );
    }

    #[test]
    fn test_nested_commutes_bvar_equal_bridge_is_constructive() {
        let spec = build_substitution_spec_with_stack();

        let def = spec
            .definitions()
            .get("instantiate_at_nested_commutes_bvar_equal")
            .expect("equal bridge should exist");
        assert!(
            def.value_src.is_some(),
            "equal bridge should have an explicit proof term"
        );
        assert!(!def.is_axiom, "equal bridge should not be an axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "equal bridge should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "equal bridge should have no remaining helper blockers (interchange chain is DerivedProved): {:?}",
            def.axiom_deps
        );
    }
}
