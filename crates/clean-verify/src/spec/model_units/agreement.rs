// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The foundation-agreement unit, checked against the MODEL's own foundation.
//!
//! `crates/clean-verify/spec/foundation_agreement.clean` supplies nineteen witnesses for the
//! equations of the six declarations the model shares with any ambient Clean
//! environment — `Nat`, `Nat.add`, `Nat.pred`, `Nat.sub`, `Eq`, `Empty` — each
//! using direct terms, constructors, reflexivity, or recursors,
//! and also covers the ambient `Bool`. It exists
//! because a `clean { }` island registers into the compiler PRELUDE's
//! environment, which owns those six names: the island cannot re-declare them
//! (an identical inductive re-add registers nothing; a conflicting declaration
//! is refused), so agreement is
//! the only honest thing to check about them.
//!
//! # What this module adds
//!
//! With island checking enabled and a compatible compiler, the supplied witness
//! terms are checked over the PRELUDE. This module checks the other environment:
//! it registers the SAME FILE into the model's own foundation (`CoreSpecBundle::ModelUnits`,
//! i.e. the spec's private `Nat`/`Eq`/`Empty`, built on an EMPTY environment)
//! through the SAME `register_unit_declaration` path the units use, and requires
//! every witness to elaborate.
//!
//! Successful checks in both environments establish the supplied, reviewed
//! witnesses, not general model/prelude equivalence or protection against every
//! future weakening of their statements. These model-side tests alone do not
//! establish that the compiler-side island check passed.
//!
//! The eight negative controls below are the same invalid witness terms that
//! `scripts/model_islands.py --verify` checks against the prelude; each must also
//! be refused over the model's foundation. Some state true equations with an
//! invalid reflexivity proof, rather than false propositions. These controls do
//! not themselves prevent weakening a positive witness. The separate statement
//! contract below protects `fa_nat_add_succ`; the other eighteen witness types
//! are not covered by that contract.

use std::path::PathBuf;

use clean_kernel::{Name, TypeChecker};

use super::{declarations_of_source, unit_declarations, LiteralKind, ModelUnit, ModelUnitSource};
use crate::spec::{SpecError, Specification};
use crate::test_utils::run_with_stack;

/// The agreement unit, now a model unit of this crate.
pub(crate) fn agreement_unit_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("spec/foundation_agreement.clean")
}

pub(crate) const AGREEMENT_UNIT_LABEL: &str = "foundation_agreement.clean";

/// Reviewed statement, deliberately independent of the loaded witness text.
/// This pins only fa_nat_add_succ; it is not full model/prelude equivalence.
const NAT_ADD_SUCC_STATEMENT: &str =
    "forall (n : Nat) (m : Nat), @Eq Nat (Nat.add n (Nat.succ m)) (Nat.succ (Nat.add n m))";

fn check_statement_contract(spec: &Specification, name: &str) -> Result<(), SpecError> {
    // The target is explicit so a uniquely named, well-typed weakening control
    // can be checked against this contract without shadowing the live witness.
    let root = clean_parser::parse_name(name)
        .map_err(|error| SpecError::ParseError(format!("agreement statement target: {error}")))?
        .qualify_under(&clean_parser::SurfaceName::default())
        .into_name();
    let constant = spec
        .env()
        .get_const(&root)
        .ok_or_else(|| SpecError::TypeError(format!("agreement statement root missing: {name}")))?;
    let expected = spec.elaborate_source(
        NAT_ADD_SUCC_STATEMENT,
        "reviewed fa_nat_add_succ statement contract",
    )?;
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let _ = checker.infer_type(&expected).map_err(|error| {
        SpecError::TypeError(format!(
            "agreement statement contract is not well-typed: {error:?}"
        ))
    })?;
    if !checker.is_def_eq(&constant.type_, &expected) {
        return Err(SpecError::TypeError(format!(
            "agreement statement contract mismatch: {name}"
        )));
    }
    Ok(())
}

/// The committed declaration census the island gate accounts against.
pub(crate) fn declaration_census_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/model_unit_declarations.json")
}

/// Register controls into a fresh model-units specification. The agreement
/// unit is already live there; a contract target must name the new control.
fn register_over_the_model(
    text: &str,
    contract_target: Option<&str>,
) -> Result<Vec<Name>, SpecError> {
    let decls = declarations_of_source(AGREEMENT_UNIT_LABEL, text)?;
    let mut spec = Specification::new_model_units_spec(ModelUnitSource::CleanFiles)?;
    let mut names = Vec::with_capacity(decls.len());
    for decl in &decls {
        spec.register_unit_declaration(decl.kind, &decl.source, &decl.description)?;
        names.push(
            decl.name
                .qualify_under(&clean_parser::SurfaceName::default())
                .into_name(),
        );
    }
    if let Some(target) = contract_target {
        let target_name = clean_parser::parse_name(target)
            .map_err(|error| SpecError::ParseError(format!("agreement statement target: {error}")))?
            .qualify_under(&clean_parser::SurfaceName::default())
            .into_name();
        if !names.contains(&target_name) {
            return Err(SpecError::TypeError(format!(
                "agreement statement control target was not registered: {target}"
            )));
        }
        check_statement_contract(&spec, target)?;
    }
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The census declares source spellings, not legacy displayed kernel names.
    fn census_name(value: &serde_json::Value) -> Name {
        let source = value.as_str().expect("a census name is a string");
        clean_parser::parse_name(source)
            .unwrap_or_else(|error| panic!("census source name {source:?} does not parse: {error}"))
            .qualify_under(&clean_parser::SurfaceName::default())
            .into_name()
    }

    fn owned_name(name: &Name, declared: &std::collections::BTreeSet<Name>) -> bool {
        use clean_kernel::name::NameInner;
        let mut current = name;
        loop {
            if declared.contains(current) {
                return true;
            }
            match current.inner() {
                NameInner::Anon => return false,
                NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent.as_ref(),
            }
        }
    }

    #[test]
    fn census_source_names_and_owned_prefixes_preserve_quoted_components() {
        let nested = census_name(&serde_json::json!("A.B"));
        let atomic = census_name(&serde_json::json!("«A.B»"));
        assert_eq!(nested, Name::anon().str("A").str("B"));
        assert_eq!(atomic, Name::anon().str("A.B"));
        assert_ne!(nested, atomic);
        let declared = std::collections::BTreeSet::from([nested.clone()]);
        assert!(owned_name(&nested.clone().str("rec"), &declared));
        assert!(!owned_name(&atomic.clone().str("rec"), &declared));
        assert_eq!(census_name(&serde_json::json!("_root_.A.B")), nested);
        assert_eq!(
            census_name(&serde_json::json!("«_root_».A.B")),
            Name::anon().str("_root_").str("A").str("B")
        );
    }

    /// The eight invalid terms `scripts/model_islands.py --verify` requires the
    /// island to refuse. Each must be refused over the model's foundation too,
    /// or the witnesses pin nothing.
    const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
        (
            "add_recurses_left",
            "/-- control -/\ndef bad_add (n : Nat) : @Eq Nat (Nat.add Nat.zero n) n := @Eq.refl Nat n",
            "Nat.add must recurse on its RIGHT argument",
        ),
        (
            "pred_zero_wrong",
            "/-- control -/\ndef bad_pred : @Eq Nat (Nat.pred Nat.zero) (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
            "Nat.pred Nat.zero must be Nat.zero",
        ),
        (
            "sub_drops_pred",
            "/-- control -/\ndef bad_sub (a : Nat) (b : Nat) : @Eq Nat (Nat.sub a (Nat.succ b)) (Nat.sub a b) := @Eq.refl Nat (Nat.sub a b)",
            "Nat.sub must peel the right operand THROUGH pred",
        ),
        (
            "succ_wrong_arity",
            "/-- control -/\ndef bad_succ : Nat -> Nat -> Nat := Nat.succ",
            "Nat.succ must be unary",
        ),
        (
            "nat_rec_three_minors",
            "/-- control -/\ndef bad_nat_rec (C : Nat -> Type) (z : C Nat.zero) (s : (n : Nat) -> C n -> C (Nat.succ n)) (x : C Nat.zero) (n : Nat) : C n := @Nat.rec C z s x n",
            "Nat.rec takes one minor premise per constructor",
        ),
        (
            "bool_rec_three_minors",
            "/-- control -/\ndef bad_bool_rec (C : Bool -> Type) (f : C Bool.false) (t : C Bool.true) (x : C Bool.false) (b : Bool) : C b := @Bool.rec C f t x b",
            "Bool.rec takes one minor premise per constructor",
        ),
        (
            "empty_wrong_sort",
            "/-- control -/\ndef bad_empty_sort : Prop := Empty",
            "Empty must live at the model's sort",
        ),
        (
            "empty_has_ctor",
            "/-- control -/\ndef bad_empty : Empty := Empty.mk",
            "Empty must have no constructors",
        ),
    ];

    fn unit_text() -> String {
        let path = agreement_unit_path();
        std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "the foundation-agreement unit must be readable at {} ({e}). It is loaded as a \
                 `clean mod` island by crates/clean-kernel/src/model_islands.rs, so if it moved, \
                 that module and scripts/model_islands.py moved with it and this path is stale.",
                path.display()
            )
        })
    }

    /// THE TEST THIS MODULE EXISTS FOR: the agreement equations hold over the
    /// MODEL's own foundation, not merely over whatever ambient environment an
    /// island happens to supply.
    ///
    /// Since the unit is registered by the model-units bundle itself, this is
    /// proof BY CONSTRUCTION: the prefix cannot build unless every equation
    /// elaborates over the spec's private `Nat`/`Eq`/`Empty`/`Bool`. The
    /// assertions below pin that the witnesses the island gate names are the ones
    /// that got registered, so the two sides cannot drift apart silently.
    #[test]
    fn agreement_equations_hold_over_the_model_foundation() {
        let spec = run_with_stack(|| {
            let spec = Specification::new_model_units_spec(ModelUnitSource::CleanFiles)
                .unwrap_or_else(|e| {
                    panic!(
                    "the model-units prefix does NOT build with the agreement unit registered: \
                     {e}\n\nEvery equation in {} is supposed to be a defining equation of the \
                     model's own Nat/Nat.add/Nat.pred/Nat.sub/Eq/Empty/Bool, so it must elaborate \
                     using its actual term (constructor, reflexivity, or elimination). A failure \
                     means that term did not check over the model. Inspect the witness and \
                     diagnostic; do not weaken this test.",
                    AGREEMENT_UNIT_LABEL
                )
                });
            check_statement_contract(&spec, "fa_nat_add_succ")
                .expect("the live witness retains its reviewed statement");
            spec
        });
        for required in [
            "fa_nat_zero",
            "fa_nat_succ",
            "fa_nat_add_zero",
            "fa_nat_add_succ",
            "fa_nat_pred_zero",
            "fa_nat_pred_succ",
            "fa_nat_sub_zero",
            "fa_nat_sub_succ",
            "fa_nat_rec",
            "fa_eq_refl",
            "fa_eq_rec",
            "fa_bool_true",
            "fa_bool_false",
            "fa_bool_rec",
            "fa_empty_elim",
            "fa_nat_sort",
            "fa_bool_sort",
            "fa_empty_sort",
            "fa_eq_is_prop",
        ] {
            assert!(
                spec.definitions().contains_key(required),
                "{required} is named by scripts/model_islands.py's agreement cover map but the \
                 model-units spec does not register it; the two must move together"
            );
            spec.verify_definition(required).unwrap_or_else(|error| {
                panic!("live agreement witness {required} must recheck: {error}")
            });
        }
    }

    /// The same eight invalid-term controls the island gate runs. If one of these
    /// ELABORATES over the model's foundation, the witnesses do not pin the
    /// model's arithmetic and the agreement is decoration on both sides.
    #[test]
    fn false_equations_are_refused_over_the_model_foundation() {
        for (label, source, why) in NEGATIVE_CONTROLS {
            let body = (*source).to_string();
            let outcome = run_with_stack(move || register_over_the_model(&body, None));
            assert!(
                outcome.is_err(),
                "negative control {label} ELABORATED over the model's own foundation, but {why}. \
                 The agreement witnesses therefore pin nothing: they cannot tell a foundation that \
                 matches the model from one that does not."
            );
        }
    }

    /// These uniquely named replacements still elaborate. Their
    /// refusal must therefore come from the reviewed statement contract, not
    /// parsing, an unknown identifier, or the replacement proof body.
    #[test]
    fn agreement_add_succ_statement_cannot_be_weakened() {
        let controls = [
            (
                "vacuous_data",
                "agreement_control_add_succ_data",
                "/-- statement-weakening control -/\ndef agreement_control_add_succ_data : Nat := Nat.zero",
            ),
            (
                "vacuous_proposition",
                "agreement_control_add_succ_reflexive",
                "/-- statement-weakening control -/\ndef agreement_control_add_succ_reflexive (n : Nat) (m : Nat) : @Eq Nat n n := @Eq.refl Nat n",
            ),
        ];
        let mut accepted = Vec::new();
        for (label, target, source) in controls {
            let text = source.to_string();
            match run_with_stack(move || register_over_the_model(&text, Some(target))) {
                Ok(names) => accepted.push((label, names)),
                Err(SpecError::TypeError(message))
                    if message == format!("agreement statement contract mismatch: {target}") => {}
                Err(other) => panic!(
                    "{label}: only the registered statement mismatch is a valid refusal; got {other:?}"
                ),
            }
        }
        assert!(
            accepted.is_empty(),
            "well-typed replacements weakened the required witness statement: {accepted:?}"
        );
    }

    /// The island gate (`scripts/model_islands.py`) accounts every model
    /// declaration against `data/model_unit_declarations.json`. That census must
    /// be what the REAL Clean parser reads out of the units — the production
    /// loader's own `declarations_of_source`, reached here through
    /// `unit_declarations` — or a declaration the parser accepts and the census
    /// omits would be invisible to the accounting, and "nothing unaccounted"
    /// would read green while being false.
    #[test]
    fn the_declaration_census_is_what_the_clean_parser_reads() {
        let path = declaration_census_path();
        let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "the declaration census must be readable at {} ({e})",
                path.display()
            )
        });
        let doc: serde_json::Value =
            serde_json::from_str(&raw).expect("the declaration census is valid JSON");
        let units = doc["units"]
            .as_object()
            .expect("the census carries a `units` object");

        let mut total = 0usize;
        for unit in ModelUnit::ALL {
            let file = unit.file_name();
            let key = file
                .strip_suffix(".clean")
                .expect("every unit file name ends in .clean");
            let committed: Vec<Name> = units
                .get(key)
                .unwrap_or_else(|| {
                    panic!(
                        "the census has no entry for model unit {key:?}; it is minted from                          crates/clean-verify/spec/*.clean and must cover every unit"
                    )
                })
                .as_array()
                .expect("a census entry is an array of declaration names")
                .iter()
                .map(census_name)
                .collect();

            let parsed: Vec<Name> = unit_declarations(*unit)
                .unwrap_or_else(|e| panic!("model unit {key} must parse: {e}"))
                .into_iter()
                .map(|d| {
                    d.name
                        .qualify_under(&clean_parser::SurfaceName::default())
                        .into_name()
                })
                .collect();

            assert_eq!(
                committed, parsed,
                "data/model_unit_declarations.json disagrees with the Clean parser for {key}.                  The census is what scripts/model_islands.py accounts against, so a name the                  parser reads and the census omits is a model declaration NOTHING checks —                  re-mint the census and read the diff."
            );
            total += parsed.len();
        }

        let claimed = doc["count"].as_u64().expect("the census carries a `count`") as usize;
        assert_eq!(
            claimed, total,
            "the census `count` field disagrees with its own entries"
        );
        assert_eq!(
            units.len(),
            ModelUnit::ALL.len(),
            "the census covers {} unit(s) but there are {} model units",
            units.len(),
            ModelUnit::ALL.len()
        );
    }

    /// The model's AMBIENT INTERFACE: every constant the model's own declarations
    /// reference that no model unit declares. Those names are supplied by
    /// whichever environment the model is elaborated in — the spec's foundation
    /// here, the compiler prelude in an island — so each one needs an agreement
    /// witness for exactly the reason a prelude-owned declaration does.
    ///
    /// Derived from the KERNEL, not from the text: the elaborated type and value
    /// of every census declaration are walked for their constant references, and
    /// everything the model itself declares (including the constructors and
    /// recursors the kernel generates from its inductives) is subtracted. A
    /// text scan could not do this — it cannot tell a binder from a constant.
    #[test]
    fn the_ambient_interface_is_what_the_census_records() {
        let path = declaration_census_path();
        let raw = std::fs::read_to_string(&path).expect("the census is readable");
        let doc: serde_json::Value = serde_json::from_str(&raw).expect("the census is valid JSON");
        let census_entries: Vec<(String, Name)> = doc["units"]
            .as_object()
            .expect("units object")
            .values()
            .flat_map(|v| v.as_array().expect("array").iter())
            .map(|v| (v.as_str().expect("string").to_owned(), census_name(v)))
            .collect();
        let census_names: std::collections::BTreeSet<Name> = census_entries
            .iter()
            .map(|(_, name)| name.clone())
            .collect();

        let spec = run_with_stack(|| {
            Specification::new_model_units_spec(ModelUnitSource::CleanFiles)
                .expect("the model-units prefix builds")
        });

        // Everything the model brings into the environment: its declarations plus
        // whatever the kernel generated from them (constructors, recursors, and
        // the noConfusion family), recognised by exact component prefix.

        let mut ambient: std::collections::BTreeSet<Name> = std::collections::BTreeSet::new();
        for (source_name, decl_name) in &census_entries {
            // Preserve the existing model's legacy record-presence assertion
            // using the census's actual text, never a formatted kernel name.
            // Unsupported spellings in that legacy record API fail this test;
            // this adapter does not claim to migrate Specification's schema.
            let Some(def) = spec.definitions().get(source_name) else {
                panic!("census declaration {decl_name} is not registered in the model-units spec");
            };
            let constant = spec.env().get_const(decl_name).unwrap_or_else(|| {
                panic!("exact census declaration {decl_name} is absent from the kernel")
            });
            assert_eq!(def.elaborated_type.as_ref(), Some(&constant.type_));
            assert_eq!(def.elaborated_value.as_ref(), constant.value.as_ref());
            for expr in [def.elaborated_type.as_ref(), def.elaborated_value.as_ref()]
                .into_iter()
                .flatten()
            {
                for c in expr.collect_constants() {
                    if !owned_name(&c, &census_names) {
                        ambient.insert(c);
                    }
                }
            }
        }

        let recorded: std::collections::BTreeSet<Name> = doc["ambient"]
            .as_array()
            .unwrap_or_else(|| {
                panic!(
                    "the census records no `ambient` list. Measured now, the model's ambient                      interface is: {ambient:?}"
                )
            })
            .iter()
            .map(census_name)
            .collect();

        assert_eq!(
            recorded, ambient,
            "the census's `ambient` list disagrees with what the kernel says the model references.              Every ambient name must carry an agreement witness, because it is supplied by the              environment rather than by the model — so a name appearing here and not in              scripts/model_islands.py's AMBIENT_AGREED is a dependency on the ambient environment              that NOTHING checks."
        );
    }

    /// The unit must hold only the forms the loader registers, so the island and
    /// this test see the same declarations.
    #[test]
    fn agreement_unit_holds_only_defs() {
        let text = unit_text();
        let decls = declarations_of_source(AGREEMENT_UNIT_LABEL, &text)
            .expect("the agreement unit parses as a Clean file");
        for decl in &decls {
            assert_eq!(
                decl.kind,
                LiteralKind::RecursiveDef,
                "{} is a {:?}; the agreement unit states equations and must hold `def`s only",
                decl.name,
                decl.kind
            );
            assert!(
                !decl.description.trim().is_empty(),
                "{} has no `/-- ... -/` doc comment; the loader requires one on every declaration",
                decl.name
            );
        }
    }
}
