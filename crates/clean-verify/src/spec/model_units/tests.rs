// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The W1 fidelity oracle: a `.clean` model unit and its retained literal must
//! elaborate to IDENTICAL kernel terms — or the move changed the model.
//!
//! Two specifications are built over the same six-stage prefix
//! (`CoreSpecBundle::ModelUnits`): one reads every unit from its `.clean`
//! file, the other from `retained_literals.rs`. The comparator then walks both
//! kernel environments constant by constant and both `SpecDefinition` tables
//! field by field, and computes each moved declaration's axiom closure in each.
//! Any difference is a red test that names the constant and the field.
//!
//! The oracle is itself checked: a planted one-token edit in a term, a planted
//! edit in a description, a missing doc comment and an unsupported declaration
//! form each have an arm below that must go red.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::OnceLock;

use clean_kernel::{ConstantKind, Environment, Name};

use super::{
    declarations_of_source, retained_literals, unit_declarations, LiteralKind, ModelUnit,
    ModelUnitSource,
};
use crate::axiom_ratchet::live_env_axioms;
use crate::spec::Specification;
use crate::test_utils::run_with_stack;

// ---------------------------------------------------------------------------
// Comparator
// ---------------------------------------------------------------------------

/// Every way two specifications built over the same prefix can differ, one
/// line per difference, empty when they are identical.
fn fidelity_differences(a: &Specification, b: &Specification) -> Vec<String> {
    let mut diffs = Vec::new();
    compare_constants(a.env(), b.env(), &mut diffs);
    compare_inductives_and_recursors(a.env(), b.env(), &mut diffs);
    compare_definitions(a, b, &mut diffs);
    diffs
}

fn compare_constants(a: &Environment, b: &Environment, diffs: &mut Vec<String>) {
    let ca: BTreeMap<Name, _> = a.constants().map(|c| (c.name.clone(), c)).collect();
    let cb: BTreeMap<Name, _> = b.constants().map(|c| (c.name.clone(), c)).collect();
    for name in ca.keys().chain(cb.keys()).collect::<BTreeSet<_>>() {
        match (ca.get(name), cb.get(name)) {
            (Some(x), Some(y)) => {
                if x.level_params != y.level_params {
                    diffs.push(format!("constant {name}: level_params differ"));
                }
                if x.type_ != y.type_ {
                    diffs.push(format!("constant {name}: type differs"));
                }
                if x.value != y.value {
                    diffs.push(format!("constant {name}: value differs"));
                }
                if x.is_reducible != y.is_reducible || x.reducibility != y.reducibility {
                    diffs.push(format!("constant {name}: reducibility differs"));
                }
                if x.kind != y.kind {
                    diffs.push(format!(
                        "constant {name}: kind differs ({:?} vs {:?})",
                        x.kind, y.kind
                    ));
                }
            }
            (Some(_), None) => diffs.push(format!("constant {name}: only in the file build")),
            (None, Some(_)) => diffs.push(format!("constant {name}: only in the literal build")),
            (None, None) => unreachable!(),
        }
    }
}

fn compare_inductives_and_recursors(a: &Environment, b: &Environment, diffs: &mut Vec<String>) {
    let names: BTreeSet<Name> = a
        .constants()
        .chain(b.constants())
        .map(|c| c.name.clone())
        .collect();
    for name in &names {
        match (a.get_inductive(name), b.get_inductive(name)) {
            (Some(x), Some(y)) => {
                let same = x.name == y.name
                    && x.level_params == y.level_params
                    && x.type_ == y.type_
                    && x.num_params == y.num_params
                    && x.num_indices == y.num_indices
                    && x.all_names == y.all_names
                    && x.constructor_names == y.constructor_names
                    && x.is_recursive == y.is_recursive
                    && x.is_reflexive == y.is_reflexive
                    && x.is_large_elim == y.is_large_elim
                    && x.is_nested == y.is_nested;
                if !same {
                    diffs.push(format!("inductive {name}: metadata differs"));
                }
            }
            (Some(_), None) | (None, Some(_)) => {
                diffs.push(format!("inductive {name}: present in only one build"));
            }
            (None, None) => {}
        }
        match (a.get_recursor(name), b.get_recursor(name)) {
            (Some(x), Some(y)) => {
                let same = x.name == y.name
                    && x.arg_order == y.arg_order
                    && x.level_params == y.level_params
                    && x.type_ == y.type_
                    && x.inductive_name == y.inductive_name
                    && x.num_params == y.num_params
                    && x.num_indices == y.num_indices
                    && x.num_motives == y.num_motives
                    && x.num_minors == y.num_minors
                    && x.is_k == y.is_k
                    && x.rules.len() == y.rules.len()
                    && x.rules.iter().zip(&y.rules).all(|(r, s)| {
                        r.constructor_name == s.constructor_name
                            && r.num_fields == s.num_fields
                            && r.recursive_fields == s.recursive_fields
                            && r.rhs == s.rhs
                    });
                if !same {
                    diffs.push(format!("recursor {name}: metadata or rules differ"));
                }
            }
            (Some(_), None) | (None, Some(_)) => {
                diffs.push(format!("recursor {name}: present in only one build"));
            }
            (None, None) => {}
        }
    }
}

fn compare_definitions(a: &Specification, b: &Specification, diffs: &mut Vec<String>) {
    // SpecDefinition remains a legacy string-keyed record API. Compare those
    // records verbatim; do not reinterpret their display keys as kernel names.
    // The kernel environment comparator above separately uses exact Name keys.
    let da = a.definitions();
    let db = b.definitions();
    let keys: BTreeSet<&String> = da.keys().chain(db.keys()).collect();
    for name in keys {
        match (da.get(name), db.get(name)) {
            (Some(x), Some(y)) => {
                let mut field = |label: &str, same: bool| {
                    if !same {
                        diffs.push(format!("definition {name}: {label} differs"));
                    }
                };
                field("name", x.name == y.name);
                field("type_src", x.type_src == y.type_src);
                field("value_src", x.value_src == y.value_src);
                field("is_axiom", x.is_axiom == y.is_axiom);
                field("description", x.description == y.description);
                field("category", x.category == y.category);
                field("proof_status", x.proof_status == y.proof_status);
                field("elaborated_type", x.elaborated_type == y.elaborated_type);
                field("elaborated_value", x.elaborated_value == y.elaborated_value);
                field("dependencies", x.dependencies == y.dependencies);
                field("axiom_deps", x.axiom_deps == y.axiom_deps);
            }
            (Some(_), None) => diffs.push(format!("definition {name}: only in the file build")),
            (None, Some(_)) => diffs.push(format!("definition {name}: only in the literal build")),
            (None, None) => unreachable!(),
        }
    }
}

/// The set of kernel AXIOMS (value-less constants) reachable from a constant
/// through its type, its value and — for a recursor — every rule's rhs.
fn axiom_closure(env: &Environment, root: &Name) -> BTreeSet<Name> {
    let mut seen: BTreeSet<Name> = BTreeSet::new();
    let mut stack = vec![root.clone()];
    let mut axioms = BTreeSet::new();
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.kind == ConstantKind::Axiom {
            axioms.insert(name.clone());
        }
        let mut next = info.type_.collect_constants();
        if let Some(v) = &info.value {
            v.collect_constants_into(&mut next);
        }
        if let Some(rec) = env.get_recursor(&name) {
            for rule in &rec.rules {
                rule.rhs.collect_constants_into(&mut next);
            }
        }
        stack.extend(next);
    }
    axioms
}

/// Every name a unit registers directly, plus the `.rec` of each inductive.
fn moved_names(unit: ModelUnit) -> Vec<Name> {
    moved_declaration_names(&unit_declarations(unit).expect("unit parses"))
}

fn moved_declaration_names(decls: &[super::UnitDeclaration]) -> Vec<Name> {
    let mut names = Vec::new();
    for decl in decls {
        // Units have no namespace commands, but an actual unescaped _root_
        // header qualifier is still resolved by registration. Quoted _root_
        // remains an ordinary component, as does an atomic quoted dotted name.
        let owner = decl
            .name
            .qualify_under(&clean_parser::SurfaceName::default())
            .into_name();
        names.push(owner.clone());
        if decl.kind == LiteralKind::Inductive {
            names.push(owner.str("rec"));
        }
    }
    names
}

// ---------------------------------------------------------------------------
// Builders (once per process; every arm clones)
// ---------------------------------------------------------------------------

fn build(source: ModelUnitSource) -> Specification {
    run_with_stack(move || {
        Specification::new_model_units_spec(source).expect("model-unit prefix builds")
    })
}

fn literal_build() -> &'static Specification {
    static LITERAL: OnceLock<Specification> = OnceLock::new();
    LITERAL.get_or_init(|| build(ModelUnitSource::RetainedLiterals))
}

fn file_build() -> &'static Specification {
    static FILE: OnceLock<Specification> = OnceLock::new();
    FILE.get_or_init(|| build(ModelUnitSource::CleanFiles))
}

fn planted(unit: ModelUnit, edit: impl FnOnce(&str) -> String) -> ModelUnitSource {
    let original = unit.embedded_source();
    let edited = edit(original);
    assert_ne!(
        edited, original,
        "the planted edit must change the unit text"
    );
    let mut map = HashMap::new();
    map.insert(unit, edited);
    ModelUnitSource::Planted(map)
}

fn replace_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(
        text.matches(from).count(),
        1,
        "planted edit anchor {from:?} must occur exactly once"
    );
    text.replacen(from, to, 1)
}

// ---------------------------------------------------------------------------
// Static shape: the units are real Clean files, on disk and embedded alike
// ---------------------------------------------------------------------------

#[test]
fn every_unit_is_a_real_clean_file_and_the_embedded_copy_matches_disk() {
    for unit in ModelUnit::ALL {
        // A unit BORN as a file has no pre-move Rust literal, so this oracle --
        // which exists to prove the W1 MOVE changed nothing -- has nothing to
        // compare it against. Skipping it deliberately keeps the oracle saying
        // exactly what it can support; `register_model_unit` registers such a
        // unit from the file on both sides so the two environments still match.
        let Some(_) = retained_literals::of(*unit) else {
            assert!(
                retained_literals::BORN_AS_FILE.contains(unit),
                "{} has no retained literal but is not declared born-as-file. An empty or absent \
                 literal table for a unit W1 MOVED would make this oracle compare the file build \
                 against itself and still print green.",
                unit.file_name()
            );
            continue;
        };
        let path = format!("{}/spec/{}", env!("CARGO_MANIFEST_DIR"), unit.file_name());
        let on_disk = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        assert_eq!(
            on_disk,
            unit.embedded_source(),
            "{path} differs from the copy embedded at build time — rebuild"
        );
        let whole_file = clean_parser::parse_file(unit.embedded_source()).unwrap_or_else(|e| {
            panic!("{}: does not parse as a Clean file: {e}", unit.file_name())
        });
        let chunks = unit_declarations(*unit).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(
            whole_file.len(),
            chunks.len(),
            "{}: parse_file sees {} declarations but the loader read {}",
            unit.file_name(),
            whole_file.len(),
            chunks.len()
        );
        assert!(!chunks.is_empty(), "{}: empty unit", unit.file_name());
    }
}

#[test]
fn every_unit_declaration_is_textually_the_retained_literal() {
    // Cheap pre-check, so a whitespace or doc-comment drift is reported by
    // declaration name before any elaboration runs.
    for unit in ModelUnit::ALL {
        // A unit BORN as a file has no pre-move Rust literal, so this oracle --
        // which exists to prove the W1 MOVE changed nothing -- has nothing to
        // compare it against. Skipping it deliberately keeps the oracle saying
        // exactly what it can support; `register_model_unit` registers such a
        // unit from the file on both sides so the two environments still match.
        let Some(_) = retained_literals::of(*unit) else {
            assert!(
                retained_literals::BORN_AS_FILE.contains(unit),
                "{} has no retained literal but is not declared born-as-file. An empty or absent \
                 literal table for a unit W1 MOVED would make this oracle compare the file build \
                 against itself and still print green.",
                unit.file_name()
            );
            continue;
        };
        let decls = unit_declarations(*unit).unwrap_or_else(|e| panic!("{e}"));
        let lits = retained_literals::of(*unit).expect("guarded above");
        assert_eq!(
            decls.len(),
            lits.len(),
            "{}: {} declarations in the file, {} retained literals",
            unit.file_name(),
            decls.len(),
            lits.len()
        );
        for (decl, lit) in decls.iter().zip(lits) {
            assert_eq!(
                decl.kind,
                lit.kind,
                "{}: {}: kind",
                unit.file_name(),
                decl.name
            );
            assert_eq!(
                decl.source,
                lit.source,
                "{}: {}: declaration text differs from the retained literal",
                unit.file_name(),
                decl.name
            );
            assert_eq!(
                decl.description,
                lit.description,
                "{}: {}: doc comment differs from the retained description",
                unit.file_name(),
                decl.name
            );
        }
    }
}

// ---------------------------------------------------------------------------
// THE ORACLE
// ---------------------------------------------------------------------------

#[test]
fn oracle_file_and_literal_builds_are_identical_kernel_environments() {
    let diffs = fidelity_differences(file_build(), literal_build());
    assert!(
        diffs.is_empty(),
        "the .clean units and the retained literals elaborate differently:\n  {}",
        diffs.join("\n  ")
    );
}

#[test]
fn oracle_every_moved_declaration_has_the_same_axiom_closure() {
    let file = file_build();
    let literal = literal_build();
    let mut checked = 0usize;
    for unit in ModelUnit::ALL {
        // A unit BORN as a file has no pre-move Rust literal, so this oracle --
        // which exists to prove the W1 MOVE changed nothing -- has nothing to
        // compare it against. Skipping it deliberately keeps the oracle saying
        // exactly what it can support; `register_model_unit` registers such a
        // unit from the file on both sides so the two environments still match.
        let Some(_) = retained_literals::of(*unit) else {
            assert!(
                retained_literals::BORN_AS_FILE.contains(unit),
                "{} has no retained literal but is not declared born-as-file. An empty or absent \
                 literal table for a unit W1 MOVED would make this oracle compare the file build \
                 against itself and still print green.",
                unit.file_name()
            );
            continue;
        };
        for name in moved_names(*unit) {
            assert!(
                file.env().get_const(&name).is_some(),
                "{}: `{name}` is not in the kernel environment after registration",
                unit.file_name()
            );
            let from_file = axiom_closure(file.env(), &name);
            let from_literal = axiom_closure(literal.env(), &name);
            assert_eq!(
                from_file,
                from_literal,
                "{}: axiom closure of `{name}` differs between file and literal",
                unit.file_name()
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 24,
        "expected at least 24 moved names, checked {checked}"
    );
    // The whole-prefix kernel axiom census agrees too (the same census the
    // 11-axiom ratchet in tests/axiom_ratchet.rs pins over the full spec).
    let census = |spec: &Specification| -> BTreeSet<String> {
        live_env_axioms(spec).into_iter().map(|a| a.name).collect()
    };
    assert_eq!(census(file), census(literal));
    let exact_census = |spec: &Specification| -> BTreeSet<Name> {
        spec.env()
            .constants()
            .filter(|constant| constant.kind == ConstantKind::Axiom)
            .map(|constant| constant.name.clone())
            .collect()
    };
    assert_eq!(exact_census(file), exact_census(literal));
}

// ---------------------------------------------------------------------------
// The oracle can say no
// ---------------------------------------------------------------------------

#[test]
fn oracle_goes_red_on_a_planted_one_token_term_edit() {
    // `lift` swaps two Nat arguments: still well-typed, still elaborates, and
    // a DIFFERENT function. The comparator must name it.
    let source = planted(ModelUnit::ExprModelCore, |t| {
        replace_once(t, "lift_at e Nat.zero amount", "lift_at e amount Nat.zero")
    });
    let mutant = build(source);
    let diffs = fidelity_differences(&mutant, literal_build());
    assert!(
        diffs
            .iter()
            .any(|d| d.starts_with("constant lift:") && d.contains("value")),
        "planted term edit not detected; differences: {diffs:?}"
    );
}

#[test]
fn oracle_goes_red_on_a_planted_description_edit() {
    let source = planted(ModelUnit::FoundationEq, |t| {
        replace_once(t, "provably equal.", "provably equal!")
    });
    let mutant = build(source);
    let diffs = fidelity_differences(&mutant, literal_build());
    assert_eq!(
        diffs,
        vec!["definition Eq: description differs".to_string()],
        "a description edit must be the ONLY difference, and must be reported"
    );
}

#[test]
fn a_declaration_without_a_doc_comment_is_refused_with_the_fix() {
    let source = planted(ModelUnit::FoundationProd, |t| {
        replace_once(
            t,
            "/-- Product type: ProdType α β is a pair of α and β. -/\n",
            "",
        )
    });
    let err = run_with_stack(move || Specification::new_model_units_spec(source).err())
        .expect("a unit declaration without a doc comment must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("ProdType") && msg.contains("has no doc comment"),
        "{msg}"
    );
    assert!(
        msg.contains("Fix:"),
        "the refusal must carry the fix: {msg}"
    );
}

#[test]
fn an_unsupported_declaration_form_is_refused_with_options() {
    let err = declarations_of_source(
        "probe.clean",
        "/-- a theorem is not a model unit form -/\ntheorem t : Nat := Nat.zero\n",
    )
    .expect_err("theorem must be refused");
    let msg = err.to_string();
    assert!(msg.contains("theorem"), "{msg}");
    assert!(
        msg.contains("Options:"),
        "the refusal must carry options: {msg}"
    );
}

#[test]
fn model_unit_header_and_recursor_identities_preserve_display_twins() {
    let text = "/-- nested -/\ninductive A.B : Type\n\
                /-- atomic -/\ninductive «A.B» : Type\n\
                /-- rooted -/\ninductive _root_.A.B : Type\n\
                /-- literal root -/\ninductive «_root_».A.B : Type\n";
    let decls = declarations_of_source("typed-headers.clean", text).expect("typed headers parse");
    assert_eq!(decls.len(), 4);
    let nested = Name::anon().str("A").str("B");
    let atomic = Name::anon().str("A.B");
    let literal_root = Name::anon().str("_root_").str("A").str("B");
    assert_eq!(decls[0].name.name(), &nested);
    assert_eq!(decls[1].name.name(), &atomic);
    assert_ne!(decls[0].name, decls[1].name);
    assert!(!decls[2].name.same_syntax(&decls[3].name));
    assert_eq!(
        moved_declaration_names(&decls),
        vec![
            nested.clone(),
            nested.clone().str("rec"),
            atomic.clone(),
            atomic.str("rec"),
            nested.clone(),
            nested.str("rec"),
            literal_root.clone(),
            literal_root.str("rec"),
        ]
    );
    assert!(decls[1].source.starts_with("inductive «A.B»"));
    assert!(decls[3].source.starts_with("inductive «_root_».A.B"));
}

#[test]
fn kernel_fidelity_and_axiom_keys_do_not_collapse_display_twins() {
    use clean_kernel::{Declaration, Expr};
    let nested = Name::anon().str("A").str("B");
    let atomic = Name::anon().str("A.B");
    assert_eq!(
        nested.to_string(),
        atomic.to_string(),
        "the display collision is real"
    );
    assert_ne!(nested, atomic);
    let mut left = Environment::new();
    let mut right = Environment::new();
    for (env, name) in [(&mut left, nested.clone()), (&mut right, atomic.clone())] {
        env.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("checked axiom fixture");
    }
    let mut diffs = Vec::new();
    compare_constants(&left, &right, &mut diffs);
    assert_eq!(
        diffs.len(),
        2,
        "both exact one-sided declarations must remain visible"
    );
    assert!(diffs
        .iter()
        .any(|diff| diff.ends_with("only in the file build")));
    assert!(diffs
        .iter()
        .any(|diff| diff.ends_with("only in the literal build")));
    assert_eq!(axiom_closure(&left, &nested), BTreeSet::from([nested]));
    assert_eq!(axiom_closure(&right, &atomic), BTreeSet::from([atomic]));
}
