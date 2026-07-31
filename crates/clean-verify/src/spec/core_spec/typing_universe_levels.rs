// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closed Nat-level universe helpers for the core Typing rules.

#[cfg(test)]
#[path = "typing_universe_levels_tests.rs"]
mod typing_universe_levels_tests;

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_typing_universe_levels(&mut self) -> Result<(), SpecError> {
        // imax_nat n m = 0 when m = 0 (Prop/impredicative case),
        // otherwise max(n, m). This is the closed Nat shadow of the
        // production Level::imax contract used by #2870.
        self.add_definition_reducible(SpecDefinition {
            name: "imax_nat".to_string(),
            type_src: "Nat -> Nat -> Nat".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (m : Nat) => ",
                    "Nat.rec (fun (_ : Nat) => Nat) ",
                    "Nat.zero ",
                    "(fun (m' : Nat) (_ : Nat) => ",
                    "Nat.add n (Nat.sub (Nat.succ m') n)) ",
                    "m"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Impredicative max for Nat-indexed universe levels: ",
                "imax_nat n 0 = 0, imax_nat n (succ m') = max(n, succ m'). ",
                "Numeric shadow of production Level::imax. Part of #2870."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Nat.add".to_string(),
                "Nat.sub".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "sort_universe_consistency".to_string(),
            type_src: concat!(
                "forall (n : Level) (m : Level), ",
                "Eq KExpr (KExpr.sort n) (KExpr.sort m) -> Eq Level n m"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Level) (m : Level) ",
                    "(h : Eq KExpr (KExpr.sort n) (KExpr.sort m)) => ",
                    "Eq.cong KExpr Level ",
                    "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Level) ",
                    "(fun (k : Level) => k) ",
                    "(fun (_ : Nat) => n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => n) ",
                    "(fun (_ : Name) (_ : ListType Level) => n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) (_ : Level) => n) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Level) => n) ",
                    "(fun (_ : Nat) => n) ",
                    "e) ",
                    "(KExpr.sort n) (KExpr.sort m) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Sort universe consistency: equality between Sort constructors ",
                "forces equality of their Nat universe indices. ",
                "Constructive via Eq.cong + inline KExpr.rec sort projection."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
