// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The completeness recursion's **leaf steps** — heads with no components.
//!
//! ```text
//! def_eq_complete_leaf_sort :
//!   whnf_fuel_red the_red_env n a = some (sort u1)
//!     -> whnf_fuel_red the_red_env n b = some (sort u2)
//!     -> Eq Level u1 u2
//!     -> DefEqFuelAccepts a b
//! ```
//!
//! and likewise for `lit` (a `Nat` payload) and `const` (a `Name` and a
//! universe-argument list).
//!
//! ## Why these take payload equalities rather than deriving them
//!
//! At `sort`, `lit` and `const` there is nothing to recurse into: the grid
//! compares payloads *syntactically*, so completeness at these heads needs the
//! payloads to actually agree. The agreement is real — both normal forms reduce
//! to a common `w`, and each is rigid, so the star inversions force `w` to be
//! that very term on both sides, hence the two are equal — but that derivation
//! belongs at the capstone's call site, where `w` and the two legs are in scope.
//!
//! Passing the payload equality in keeps these steps at the same level of
//! abstraction as their recursive siblings in `defeq_complete_steps.rs`: whnf
//! legs plus per-component facts in, one acceptance out. It also means the
//! capstone reads uniformly across all eight leaves.
//!
//! ## No fuel collapse needed
//!
//! Unlike the recursive steps, there are no component acceptances carrying their
//! own hidden fuels — so the legs' `n` is already the only fuel, and the result
//! sits at `n + 1`. That asymmetry is why these are a separate module rather
//! than more rows in the step table.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(head, payload binders on the left, payload binders on the right, the
/// applied forms, the payload equality binders, the transport chain, the intro
/// rule application)`.
struct Leaf {
    head: &'static str,
    /// Binders for both payloads, left then right.
    binders: &'static str,
    left: &'static str,
    right: &'static str,
    /// Equality hypotheses relating right payload to left.
    eqs: &'static str,
    /// Transport `hb` from the right form to the left form.
    transport: &'static str,
    /// The grid introduction rule, applied at the LEFT form's payload.
    intro: &'static str,
}

const LEAVES: [Leaf; 4] = [
    Leaf {
        head: "sort",
        binders: "(u1 : Level) (u2 : Level)",
        left: "(KExpr.sort u1)",
        right: "(KExpr.sort u2)",
        eqs: "(hu : Eq Level u1 u2)",
        transport: "Eq.substType Level \
                    (fun (z : Level) => Eq (OptionType KExpr) \
                    (whnf_fuel_red the_red_env n b) (OptionType.some KExpr (KExpr.sort z))) \
                    u2 u1 (Eq.symm Level u1 u2 hu) hb",
        intro: "def_eq_struct_intro_sort (def_eq_fuel the_red_env n) u1",
    },
    Leaf {
        head: "lit",
        binders: "(v1 : Nat) (v2 : Nat)",
        left: "(KExpr.lit v1)",
        right: "(KExpr.lit v2)",
        eqs: "(hv : Eq Nat v1 v2)",
        transport: "Eq.substType Nat \
                    (fun (z : Nat) => Eq (OptionType KExpr) \
                    (whnf_fuel_red the_red_env n b) (OptionType.some KExpr (KExpr.lit z))) \
                    v2 v1 (Eq.symm Nat v1 v2 hv) hb",
        intro: "def_eq_struct_intro_lit (def_eq_fuel the_red_env n) v1",
    },
    Leaf {
        head: "bvar",
        binders: "(i1 : Nat) (i2 : Nat)",
        left: "(KExpr.bvar i1)",
        right: "(KExpr.bvar i2)",
        eqs: "(hi : Eq Nat i1 i2)",
        transport: "Eq.substType Nat \
                    (fun (z : Nat) => Eq (OptionType KExpr) \
                    (whnf_fuel_red the_red_env n b) (OptionType.some KExpr (KExpr.bvar z))) \
                    i2 i1 (Eq.symm Nat i1 i2 hi) hb",
        intro: "def_eq_struct_intro_bvar (def_eq_fuel the_red_env n) i1",
    },
    Leaf {
        head: "const",
        binders: "(cn1 : Name) (cus1 : ListType Level) (cn2 : Name) (cus2 : ListType Level)",
        left: "(KExpr.const cn1 cus1)",
        right: "(KExpr.const cn2 cus2)",
        eqs: "(hcn : Eq Name cn1 cn2) (hcus : Eq (ListType Level) cus1 cus2)",
        // Two payloads, so two nested transports: the universe list first, then
        // the name.
        transport: "Eq.substType Name \
                    (fun (z : Name) => Eq (OptionType KExpr) \
                    (whnf_fuel_red the_red_env n b) \
                    (OptionType.some KExpr (KExpr.const z cus1))) \
                    cn2 cn1 (Eq.symm Name cn1 cn2 hcn) \
                    (Eq.substType (ListType Level) \
                    (fun (z : ListType Level) => Eq (OptionType KExpr) \
                    (whnf_fuel_red the_red_env n b) \
                    (OptionType.some KExpr (KExpr.const cn2 z))) \
                    cus2 cus1 (Eq.symm (ListType Level) cus1 cus2 hcus) hb)",
        intro: "def_eq_struct_intro_const (def_eq_fuel the_red_env n) cn1 cus1",
    },
];

impl Specification {
    /// The leaf steps of the completeness recursion.
    pub(super) fn add_defeq_complete_leaves(&mut self) -> Result<(), SpecError> {
        for (src, desc) in Self::complete_leaf_decls() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }

    /// Generated so the shape tests read the proof terms, not this file's prose.
    ///
    /// `pub(super)` because `defeq_fuel_wh3_mono` retargets these same sources
    /// onto the three-way algorithm. Sharing the generator rather than copying
    /// the table is deliberate: the two families cannot drift apart, and a fix to
    /// a leaf's transport lands in both.
    pub(super) fn complete_leaf_decls() -> Vec<(String, String)> {
        LEAVES
            .iter()
            .map(|lf| {
                let src = format!(
                    "def def_eq_complete_leaf_{head} (n : Nat) (a : KExpr) (b : KExpr) \
                     {binders} \
                     (ha : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
                     (OptionType.some KExpr {left})) \
                     (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n b) \
                     (OptionType.some KExpr {right})) \
                     {eqs} : DefEqFuelAccepts a b := \
                     DefEqFuelAccepts.mk a b (Nat.succ n) \
                     (def_eq_fuel_of_struct n a b {left} {left} ha \
                     ({transport}) ({intro}))",
                    head = lf.head,
                    binders = lf.binders,
                    left = lf.left,
                    right = lf.right,
                    eqs = lf.eqs,
                    transport = lf.transport,
                    intro = lf.intro,
                );
                let desc = format!(
                    "def_eq_complete_leaf_{head}: the completeness recursion's {head} LEAF — a \
                     head with nothing to recurse into. The grid compares {head} payloads \
                     SYNTACTICALLY, so completeness here needs them to agree; the equality is \
                     taken as a hypothesis rather than derived, because deriving it needs the \
                     common reduct and both legs, which are in scope at the capstone's call site \
                     and not here. That also keeps these steps at the same abstraction as their \
                     recursive siblings, so the capstone reads uniformly across all eight leaves. \
                     \
                     No fuel collapse is needed, unlike the recursive steps: with no component \
                     acceptances there are no hidden fuels, so the legs' n is the only one and the \
                     result sits at n + 1. That asymmetry is why these are a separate module \
                     rather than more rows in the step table. DerivedProved, zero axiom_deps.",
                    head = lf.head,
                );
                (src, desc)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms() -> Vec<String> {
        Specification::complete_leaf_decls()
            .into_iter()
            .map(|(src, _)| src)
            .collect()
    }

    /// One leaf per component-free head — `sort`, `lit`, `const` and `bvar`.
    /// `pi`/`lam`/`app`/`proj` are recursive and live in the step module;
    /// `let_` cannot be a whnf at all. `bvar` joined when `nf_head` gained its
    /// arm: a bound variable carries a payload but no components, so it is a
    /// leaf in exactly the sense `lit` is.
    #[test]
    fn test_one_leaf_per_component_free_head() {
        assert_eq!(LEAVES.len(), 4);
        let heads: Vec<&str> = LEAVES.iter().map(|l| l.head).collect();
        for h in ["sort", "lit", "const", "bvar"] {
            assert!(heads.contains(&h), "missing leaf for {h}");
        }
        for recursive in ["pi", "lam", "app", "proj"] {
            assert!(
                !heads.contains(&recursive),
                "{recursive} has components and belongs in the step module"
            );
        }
    }

    /// Each leaf must sit at `n + 1` and use the legs' own fuel — no pairing, no
    /// raising. Importing the recursive steps' arithmetic here would be
    /// unnecessary complexity that could hide a real mismatch.
    #[test]
    fn test_leaves_need_no_fuel_collapse() {
        for (lf, src) in LEAVES.iter().zip(terms()) {
            assert!(
                src.contains("DefEqFuelAccepts.mk a b (Nat.succ n)"),
                "{}: the result must sit at n + 1, the legs' own fuel",
                lf.head
            );
            for absent in [
                "Nat.add",
                "def_eq_fuel_accepts_pair",
                "def_eq_fuel_le",
                "whnf_fuel_red_le",
            ] {
                assert!(
                    !src.contains(absent),
                    "{}: no fuel collapse is needed at a component-free head, so {absent} must \
                     not appear",
                    lf.head
                );
            }
        }
    }

    /// The payload equality must actually be USED — transported into the second
    /// leg. A leaf that ignored it would be claiming completeness at
    /// syntactically distinct payloads, which is false.
    #[test]
    fn test_payload_equality_is_transported_into_the_second_leg() {
        for (lf, src) in LEAVES.iter().zip(terms()) {
            let substs = src.matches("Eq.substType").count();
            let eq_count = lf.eqs.matches(" : Eq ").count();
            assert_eq!(
                substs, eq_count,
                "{}: one transport per payload equality ({eq_count} expected)",
                lf.head
            );
            assert_eq!(
                src.matches("Eq.symm").count(),
                eq_count,
                "{}: each transport goes from the RIGHT payload to the left, so each needs a symm",
                lf.head
            );
            // Both grid arguments are the LEFT form: that is what the transport buys.
            assert!(
                src.contains(&format!("{left} {left} ha", left = lf.left)),
                "{}: after transport both sides of the grid are the left form",
                lf.head
            );
        }
    }

    #[test]
    fn test_leaf_terms_parens_balanced() {
        for (lf, src) in LEAVES.iter().zip(terms()) {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "{}: close paren before its open", lf.head);
            }
            assert_eq!(depth, 0, "{}: unbalanced parens", lf.head);
        }
    }
}
