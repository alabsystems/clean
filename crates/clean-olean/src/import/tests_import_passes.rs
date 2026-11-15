// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! P1_IMPORT (2026-09-26): the per-module import passes that used to cost the
//! WHOLE environment — the large-elimination staging clone and the projection
//! field-table scan — now cost what the module adds. These pin, through the
//! production per-module loader, that what they decide did not change:
//!
//! * a module WITH inductives decides large elimination with its own family
//!   resident (a constructor field typed by a sibling inductive of the same
//!   module only gets large elimination if the sibling was resident);
//! * a module WITHOUT inductives leaves every earlier verdict alone;
//! * a structure whose projections arrive over two modules still gets its
//!   field table, and only once the set is complete;
//! * on the real `Init.Prelude`, every imported inductive's flag agrees with
//!   Lean's own decision (a large-eliminating recursor carries one more
//!   universe parameter than its inductive), the `Prod` field table is
//!   registered, and `instInhabitedNat` is still an instance.

use super::{load_module_with_deps, load_parsed_module, load_parsed_module_at_index};
use crate::expr::{ParsedBinderInfo, ParsedExpr};
use crate::level::ParsedLevel;
use crate::module::{
    ConstantKind, ConstructorValData, InductiveValData, ParsedConstant, ParsedExtension,
    ParsedModule,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

fn prop() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Zero)
}

fn type0() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)))
}

fn cnst(name: &str) -> ParsedExpr {
    ParsedExpr::Const(name.into(), Vec::new())
}

fn pi(binder: &str, dom: ParsedExpr, body: ParsedExpr) -> ParsedExpr {
    ParsedExpr::ForallE(
        binder.into(),
        Box::new(dom),
        Box::new(body),
        ParsedBinderInfo::Default,
    )
}

fn constant(name: &str, kind: ConstantKind, ty: ParsedExpr) -> ParsedConstant {
    ParsedConstant {
        name: name.into(),
        kind,
        level_params: Vec::new(),
        type_: Some(ty),
        value: None,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
        definition_safety: None,
        quot_kind: None,
    }
}

/// A single-constructor inductive `name : ty` with `num_params` parameters
/// and constructor `name.<ctor> : ctor_ty` carrying `num_fields` fields.
fn family(
    name: &str,
    ty: ParsedExpr,
    num_params: u32,
    ctor: &str,
    ctor_ty: ParsedExpr,
    num_fields: u32,
) -> [ParsedConstant; 2] {
    let ctor_name = format!("{name}.{ctor}");
    let mut ind = constant(name, ConstantKind::Inductive, ty);
    ind.inductive_val = Some(InductiveValData {
        num_params,
        num_indices: 0,
        all: vec![name.into()],
        ctors: vec![ctor_name.clone()],
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
        is_nested: false,
    });
    let mut c = constant(&ctor_name, ConstantKind::Constructor, ctor_ty);
    c.constructor_val = Some(ConstructorValData {
        induct: name.into(),
        cidx: 0,
        num_params,
        num_fields,
        is_unsafe: false,
    });
    [ind, c]
}

fn module(constants: Vec<ParsedConstant>, with_extension_rows: bool) -> ParsedModule {
    ParsedModule {
        const_names: constants.iter().map(|c| c.name.clone()).collect(),
        constants,
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        // Any extension row makes the loader run its extension passes, the
        // projection field-table recovery among them.
        entries: if with_extension_rows {
            vec![ParsedExtension {
                extension_name: "P1Import.testExtension".into(),
                entries: Vec::new(),
                undecoded_entries: 0,
            }]
        } else {
            Vec::new()
        },
        clean_payload: None,
    }
}

fn large_elim(env: &Environment, name: &str) -> bool {
    env.get_inductive(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be a resident inductive"))
        .is_large_elim
}

/// `P0 : Prop | mk`, `Q : Prop | intro (h : P0)`, `W (α : Type) : Prop |
/// intro (v : α)`. Lean: `P0.rec` and `Q.rec` eliminate into any `Sort`,
/// `W.rec` only into `Prop`.
fn family_module() -> ParsedModule {
    let mut cs = Vec::new();
    cs.extend(family(
        "P1Import.P0",
        prop(),
        0,
        "mk",
        cnst("P1Import.P0"),
        0,
    ));
    cs.extend(family(
        "P1Import.Q",
        prop(),
        0,
        "intro",
        pi("h", cnst("P1Import.P0"), cnst("P1Import.Q")),
        1,
    ));
    cs.extend(family(
        "P1Import.W",
        pi("α", type0(), prop()),
        1,
        "intro",
        pi(
            "α",
            type0(),
            pi(
                "v",
                ParsedExpr::BVar(0),
                ParsedExpr::App(Box::new(cnst("P1Import.W")), Box::new(ParsedExpr::BVar(1))),
            ),
        ),
        1,
    ));
    module(cs, false)
}

#[test]
fn test_import_passes_module_with_inductives_decides_with_own_family_resident() {
    let mut env = Environment::new();
    load_parsed_module(&mut env, &family_module(), Some("P1Import.Families".into()))
        .expect("family module loads");
    assert!(
        large_elim(&env, "P1Import.P0"),
        "no fields: large elimination"
    );
    assert!(
        large_elim(&env, "P1Import.Q"),
        "the field's type is a SIBLING inductive in Prop: large elimination is only \
         reached when that sibling was resident during the decision"
    );
    assert!(
        !large_elim(&env, "P1Import.W"),
        "a Type-valued field that is not an index: Prop-only elimination"
    );
}

#[test]
fn test_import_passes_module_without_inductives_leaves_verdicts_alone() {
    let mut env = Environment::new();
    load_parsed_module(&mut env, &family_module(), Some("P1Import.Families".into()))
        .expect("family module loads");
    let before: Vec<(String, bool)> = ["P1Import.P0", "P1Import.Q", "P1Import.W"]
        .iter()
        .map(|n| ((*n).to_string(), large_elim(&env, n)))
        .collect();
    let plain = module(
        vec![constant(
            "P1Import.someAxiom",
            ConstantKind::Axiom,
            cnst("P1Import.P0"),
        )],
        true,
    );
    let summary = load_parsed_module(&mut env, &plain, Some("P1Import.Plain".into()))
        .expect("plain module loads");
    assert_eq!(summary.added_constants, 1);
    let after: Vec<(String, bool)> = before
        .iter()
        .map(|(n, _)| (n.clone(), large_elim(&env, n)))
        .collect();
    assert_eq!(before, after);
}

/// A `λ (self : S). self.<idx>` projection-function body.
fn projection(struct_name: &str, field: &str, idx: u32) -> ParsedConstant {
    let mut c = constant(
        &format!("{struct_name}.{field}"),
        ConstantKind::Definition,
        pi("self", cnst(struct_name), type0()),
    );
    c.value = Some(ParsedExpr::Lam(
        "self".into(),
        Box::new(cnst(struct_name)),
        Box::new(ParsedExpr::Proj(
            struct_name.into(),
            u64::from(idx),
            Box::new(ParsedExpr::BVar(0)),
        )),
        ParsedBinderInfo::Default,
    ));
    c
}

#[test]
fn test_import_passes_structure_fields_registered_when_projections_complete_across_modules() {
    let s = "P1Import.S";
    let mut first: Vec<ParsedConstant> = family(
        s,
        type0(),
        0,
        "mk",
        pi("a", type0(), pi("b", type0(), cnst(s))),
        2,
    )
    .into();
    first.push(projection(s, "a", 0));
    let mut env = Environment::new();
    load_parsed_module(
        &mut env,
        &module(first, true),
        Some("P1Import.First".into()),
    )
    .expect("first module loads");
    assert!(
        env.get_structure_field_names(&Name::from_string(s))
            .is_none(),
        "one of two projections: the set is incomplete, no table"
    );
    load_parsed_module(
        &mut env,
        &module(vec![projection(s, "b", 1)], true),
        Some("P1Import.Second".into()),
    )
    .expect("second module loads");
    let fields: Vec<String> = env
        .get_structure_field_names(&Name::from_string(s))
        .expect("the second module completes the projection set")
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(fields, vec!["a", "b"]);
}

#[test]
fn test_import_passes_prelude_large_elim_matches_lean_recursor_universes() {
    // The comparison is against the real `Init.Prelude`, so a missing pinned
    // Lean is a FAILURE, never a silent `ok`.
    let lib = crate::pinned_lean_lib_path().expect(crate::test_support::PINNED_LEAN_REQUIRED);
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude loads");
    let mut compared = 0usize;
    let mut disagreements = Vec::new();
    for ind in env.inductives() {
        let Some(rec) = env.get_recursor(&ind.name.clone().str("rec")) else {
            continue;
        };
        compared += 1;
        let lean_large = rec.level_params.len() > ind.level_params.len();
        if ind.is_large_elim != lean_large {
            disagreements.push(ind.name.to_string());
        }
    }
    assert!(
        compared > 50,
        "Init.Prelude has many inductives, compared {compared}"
    );
    assert!(
        disagreements.is_empty(),
        "large elimination disagrees with Lean's recursor universes for {disagreements:?}"
    );
    assert!(large_elim(&env, "And") && !large_elim(&env, "Nonempty") && !large_elim(&env, "Or"));
    let prod: Vec<String> = env
        .get_structure_field_names(&Name::from_string("Prod"))
        .expect("Prod carries a field table")
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(prod, vec!["fst", "snd"]);
    assert!(env.is_instance(&Name::from_string("instInhabitedNat")));
}

/// `S.<field> : S → result`, as a value-free stub (`value: None`) or as the
/// canonical projection `λ (self : S). self.<idx>`.
fn typed_projection(
    struct_name: &str,
    field: &str,
    idx: u32,
    result: &str,
    with_value: bool,
) -> ParsedConstant {
    let kind = if with_value {
        ConstantKind::Definition
    } else {
        ConstantKind::Axiom
    };
    let mut c = constant(
        &format!("{struct_name}.{field}"),
        kind,
        pi("self", cnst(struct_name), cnst(result)),
    );
    if with_value {
        c.value = Some(ParsedExpr::Lam(
            "self".into(),
            Box::new(cnst(struct_name)),
            Box::new(ParsedExpr::Proj(
                struct_name.into(),
                u64::from(idx),
                Box::new(ParsedExpr::BVar(0)),
            )),
            ParsedBinderInfo::Default,
        ));
    }
    c
}

/// P1_IMPORT review (2026-09-26), rebuilt 2026-09-28. A structure-like
/// family whose projections the base and server parts of ONE module-system
/// artifact state as VALUE-FREE stubs (`axiom`) and whose private part
/// completes them through the checked stub upgrade (#3134,
/// `upgrade_axiom_stubs_checked`) — the shape the pinned Lean writes for a
/// public, non-`@[expose]` `def` (measured in
/// `tests_import_passes_fixture.rs` on the real triple). The parts are loaded
/// the way the `ParsedModule` path takes them: one call per part, in level
/// order, under the artifact's one module name, so they are one artifact
/// (`artifact_ledger`). The private part ADDS no name, so the incremental
/// projection index learns of the completed projections only from the upgraded
/// names; the whole-environment scan it replaced saw them by reading every
/// constant. Both must register the table, and running that scan afterwards
/// must change nothing.
///
/// The review's first version loaded the completing records as a SECOND,
/// differently named module. That is not an artifact Lean can write — a module
/// completing another's stub must import it to name its structure, and then
/// `lean` refuses the redeclaration (measured, v4.30.0-rc2: "`P1Import.U.a`
/// has already been declared") — and the loader now refuses it as Lean does
/// (`ConflictingDeclaration`, rule 1 of `artifact_ledger`).
#[test]
fn test_import_passes_projections_arriving_as_stub_upgrades_register_the_table() {
    let s = "P1Import.U";
    let carrier = "P1Import.UN";
    // Every part of a module-system artifact states the family; the private
    // part states everything the earlier parts did, plus the values.
    let part = |completed: bool| -> ParsedModule {
        let mut constants: Vec<ParsedConstant> = Vec::new();
        constants.extend(family(carrier, type0(), 0, "z", cnst(carrier), 0));
        constants.extend(family(
            s,
            type0(),
            0,
            "mk",
            pi("a", cnst(carrier), pi("b", cnst(carrier), cnst(s))),
            2,
        ));
        constants.push(typed_projection(s, "a", 0, carrier, completed));
        constants.push(typed_projection(s, "b", 1, carrier, completed));
        module(constants, true)
    };
    let artifact = Some("P1Import.Base".to_string());
    let mut env = Environment::new();
    for (index, level) in ["base", "server"].into_iter().enumerate() {
        load_parsed_module_at_index(&mut env, &part(false), artifact.clone(), index)
            .unwrap_or_else(|e| panic!("the {level} part loads: {e}"));
        assert!(
            env.get_structure_field_names(&Name::from_string(s))
                .is_none(),
            "after the {level} part: value-free stubs are not projections yet"
        );
    }
    let summary = load_parsed_module_at_index(&mut env, &part(true), artifact, 2)
        .expect("the private part loads");
    assert_eq!(
        summary.added_constants, 2,
        "both stubs upgrade through the checked tier: {:?}",
        summary.skipped_constants
    );
    assert!(
        summary.added_names.is_empty(),
        "an upgrade adds no name — the index must learn of it another way"
    );
    let fields: Vec<String> = env
        .get_structure_field_names(&Name::from_string(s))
        .expect("the upgraded projections complete the table")
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(fields, vec!["a", "b"]);
    let before = env.content_digest().total;
    let mut rescanned = env.clone();
    super::load_register::register_structure_fields_from_projections(&mut rescanned);
    assert_eq!(rescanned.content_digest().total, before);
}

/// The stub/definition split the arm above rests on, from the other side: a
/// DIFFERENT artifact that states a definition of a name an earlier artifact
/// stated as a value-free stub is refused before it registers anything, as
/// pinned Lean refuses it — measured, v4.30.0-rc2, on a module (and on a
/// non-module file) that imports the stub's artifact and declares the same
/// `def`: "error: `StubParts.Pair.first` has already been declared"; and
/// `finalizeImport`'s `subsumesInfo` has no definition/axiom arm. So a stub
/// upgrade is only ever a later PART of the same artifact.
#[test]
fn test_import_passes_stub_completed_by_a_different_artifact_is_refused() {
    let s = "P1Import.V";
    let carrier = "P1Import.VN";
    let mut stubs: Vec<ParsedConstant> = Vec::new();
    stubs.extend(family(carrier, type0(), 0, "z", cnst(carrier), 0));
    stubs.extend(family(
        s,
        type0(),
        0,
        "mk",
        pi("a", cnst(carrier), pi("b", cnst(carrier), cnst(s))),
        2,
    ));
    stubs.push(typed_projection(s, "a", 0, carrier, false));
    stubs.push(typed_projection(s, "b", 1, carrier, false));
    let mut env = Environment::new();
    load_parsed_module_at_index(
        &mut env,
        &module(stubs, true),
        Some("P1Import.VBase".into()),
        0,
    )
    .expect("the stub artifact loads");
    let completions = vec![
        typed_projection(s, "a", 0, carrier, true),
        typed_projection(s, "b", 1, carrier, true),
    ];
    let err = load_parsed_module_at_index(
        &mut env,
        &module(completions, true),
        Some("P1Import.VOther".into()),
        1,
    )
    .expect_err("another artifact cannot complete the stubs");
    assert!(
        matches!(
            &err,
            super::ImportError::ConflictingDeclaration { name, first }
                if name.starts_with("P1Import.V.") && first == "P1Import.VBase"
        ),
        "{err:?}"
    );
    for field in ["a", "b"] {
        assert!(
            env.get_const(&Name::from_string(&format!("{s}.{field}")))
                .is_some_and(|c| c.value.is_none()),
            "{s}.{field} is still the stub the first artifact stated"
        );
    }
    assert!(
        env.get_structure_field_names(&Name::from_string(s))
            .is_none(),
        "the refused artifact registered no table"
    );
}

/// Mixed exposure within one artifact: `@[expose] public def S.b` carries its
/// value in every part while the non-exposed `public def S.a` is a stub until
/// the private part. The index learns `b` from the base part (whose table is
/// refused: index 0 is missing) and `a` only from the private part's UPGRADE,
/// so the table is complete only if the candidate learned two parts earlier
/// survived. The whole-environment scan sees both at once and must agree.
#[test]
fn test_import_passes_mixed_exposure_parts_register_the_table() {
    let s = "P1Import.W";
    let carrier = "P1Import.WN";
    let part = |a_completed: bool| -> ParsedModule {
        let mut constants: Vec<ParsedConstant> = Vec::new();
        constants.extend(family(carrier, type0(), 0, "z", cnst(carrier), 0));
        constants.extend(family(
            s,
            type0(),
            0,
            "mk",
            pi("a", cnst(carrier), pi("b", cnst(carrier), cnst(s))),
            2,
        ));
        constants.push(typed_projection(s, "a", 0, carrier, a_completed));
        constants.push(typed_projection(s, "b", 1, carrier, true));
        module(constants, true)
    };
    let artifact = Some("P1Import.WBase".to_string());
    let mut env = Environment::new();
    for (index, level) in ["base", "server"].into_iter().enumerate() {
        load_parsed_module_at_index(&mut env, &part(false), artifact.clone(), index)
            .unwrap_or_else(|e| panic!("the {level} part loads: {e}"));
        assert!(
            env.get_structure_field_names(&Name::from_string(s))
                .is_none(),
            "after the {level} part: only field 1 has a projection"
        );
    }
    let summary = load_parsed_module_at_index(&mut env, &part(true), artifact, 2)
        .expect("the private part loads");
    assert_eq!(
        summary.added_constants, 1,
        "only `a` upgrades: {:?}",
        summary.skipped_constants
    );
    let fields: Vec<String> = env
        .get_structure_field_names(&Name::from_string(s))
        .expect("the earlier part's `b` and the upgraded `a` complete the table")
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(fields, vec!["a", "b"]);
    let before = env.content_digest().total;
    let mut rescanned = env.clone();
    super::load_register::register_structure_fields_from_projections(&mut rescanned);
    assert_eq!(rescanned.content_digest().total, before);
}
