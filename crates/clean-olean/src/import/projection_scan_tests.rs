// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The incremental projection scan must register exactly the field tables the
//! whole-environment scan registers, after every module, including across
//! modules, for structures whose projections arrive late or never complete,
//! for structures that already have a table, and after a write the loader did
//! not see.

use super::{begin_module, end_module, note_touched, register_touched_structure_fields};
use crate::import::load_register::register_structure_fields_from_projections;
use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, TrustedEnvExt};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{ConstructorVal, InductiveVal};
use clean_kernel::name::Name;

fn projection_value(struct_name: &Name, idx: u32) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::const_(struct_name.clone(), clean_kernel::expr::LevelVec::new()),
        Expr::proj(struct_name.clone(), idx, Expr::bvar(0)),
    )
}

/// `structure name : Type where (f₀ … fₖ₋₁ : Prop)` as the importer receives
/// it: the inductive, and the constructor `name.mk : Prop → … → name` whose
/// TYPE has one binder per field. The constructor record's `num_fields` must
/// be what that type determines — the importer's structural tier refuses a
/// record whose type says otherwise (`check_imported_constructor`,
/// `clean-kernel/src/env/imported_family.rs`), exactly as no Lean-built
/// `.olean` can state one.
fn family(name: &Name, num_fields: u32) -> (InductiveVal, ConstructorVal) {
    let ctor_name = Name::append(name, "mk");
    let self_type = Expr::const_(name.clone(), clean_kernel::expr::LevelVec::new());
    let ctor_type = (0..num_fields).fold(self_type, |body, _| Expr::arrow(Expr::prop(), body));
    (
        InductiveVal {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
            num_params: 0,
            num_indices: 0,
            all_names: vec![name.clone()],
            constructor_names: vec![ctor_name.clone()],
            is_recursive: false,
            is_reflexive: false,
            is_large_elim: true,
            is_nested: false,
        },
        ConstructorVal {
            name: ctor_name,
            inductive_name: name.clone(),
            level_params: vec![],
            type_: ctor_type,
            num_params: 0,
            num_fields,
            constructor_idx: 0,
        },
    )
}

/// `struct_name.<field> : struct_name → Prop := λ self. self.<idx>`.
fn projection(struct_name: &Name, idx: u32, field: &str, kind: ConstantKind) -> ConstantInfo {
    let mut c = ConstantInfo::new(
        Name::append(struct_name, field),
        vec![],
        Expr::arrow(
            Expr::const_(struct_name.clone(), clean_kernel::expr::LevelVec::new()),
            Expr::prop(),
        ),
        Some(projection_value(struct_name, idx)),
        true,
    );
    c.kind = kind;
    c
}

/// What one module registers.
#[derive(Default, Clone)]
struct Module {
    families: Vec<(InductiveVal, ConstructorVal)>,
    constants: Vec<ConstantInfo>,
    decoded_tables: Vec<(Name, Vec<Name>)>,
}

/// Load `m` the way the importer does: family, constants, decoded tables,
/// then the per-module projection pass.
fn load(env: &mut Environment, m: &Module, incremental: bool) {
    if incremental {
        begin_module(env);
    }
    let mut touched: Vec<Name> = Vec::new();
    for (ind, ctor) in &m.families {
        touched.push(ind.name.clone());
        touched.push(ctor.name.clone());
        let refused = env.extend_inductives_structural(std::iter::once(ind.clone()));
        assert!(refused.is_empty(), "structural tier refused {refused:?}");
        let refused = env.extend_constructors_structural(std::iter::once(ctor.clone()));
        assert!(refused.is_empty(), "structural tier refused {refused:?}");
    }
    touched.extend(m.constants.iter().map(|c| c.name.clone()));
    let refused = env.extend_constants_structural(m.constants.iter().cloned());
    assert!(refused.is_empty(), "structural tier refused {refused:?}");
    for (s, fields) in &m.decoded_tables {
        env.register_structure_fields(s.clone(), fields.clone())
            .unwrap_or_else(|e| panic!("decoded table for {s} refused: {e:?}"));
    }
    if incremental {
        note_touched(env, touched.iter());
        register_touched_structure_fields(env);
        end_module(env);
    } else {
        register_structure_fields_from_projections(env);
    }
}

fn tables(env: &Environment, names: &[Name]) -> Vec<(String, Option<Vec<Name>>)> {
    names
        .iter()
        .map(|n| {
            (
                n.to_string(),
                env.get_structure_field_names(n).map(<[Name]>::to_vec),
            )
        })
        .collect()
}

/// Drive both scans over the same module sequence and compare every table
/// after every module. Returns the tables after the last module, so an arm
/// can also assert WHICH tables were registered: two scans that both
/// register nothing agree trivially, and a fixture every recovered table is
/// refused for (`structure_table_contradiction` walks the constructor's
/// telescope, so a record whose type has no field binders refuses them all)
/// would pass every equivalence arm while testing nothing.
fn assert_equivalent(modules: &[Module], watched: &[Name]) -> Vec<(String, Option<Vec<Name>>)> {
    let mut incremental = Environment::new();
    let mut full = Environment::new();
    for (i, m) in modules.iter().enumerate() {
        load(&mut incremental, m, true);
        load(&mut full, m, false);
        assert_eq!(
            tables(&incremental, watched),
            tables(&full, watched),
            "field tables diverge after module {i}"
        );
    }
    tables(&incremental, watched)
}

fn names(fields: &[&str]) -> Option<Vec<Name>> {
    Some(fields.iter().map(|f| Name::from_string(f)).collect())
}

#[test]
fn test_projection_scan_same_module_structure_matches_full_scan() {
    let s = Name::from_string("P1.Same");
    let mut m = Module::default();
    m.families.push(family(&s, 2));
    m.constants
        .push(projection(&s, 1, "b", ConstantKind::Theorem));
    m.constants
        .push(projection(&s, 0, "a", ConstantKind::Definition));
    let last = assert_equivalent(&[m], std::slice::from_ref(&s));
    assert_eq!(last, vec![(s.to_string(), names(&["a", "b"]))]);
}

/// A nomination SHORTER than the constructor (fields `0..k` recovered, the
/// rest not yet arrived) is refused by the count check the constructor
/// record's `num_fields` feeds, in both scans; the incremental index must
/// keep the structure's candidates so the module that brings the last
/// projection registers the whole table, as the whole-environment scan does.
#[test]
fn test_projection_scan_short_nomination_is_refused_then_completed_in_both_scans() {
    let s = Name::from_string("P1.Short");
    let mut first = Module::default();
    first.families.push(family(&s, 3));
    first
        .constants
        .push(projection(&s, 0, "u", ConstantKind::Definition));
    first
        .constants
        .push(projection(&s, 1, "v", ConstantKind::Theorem));
    let after_first = assert_equivalent(std::slice::from_ref(&first), std::slice::from_ref(&s));
    assert_eq!(
        after_first,
        vec![(s.to_string(), None)],
        "a two-field nomination for a three-field constructor is not a table"
    );
    let mut second = Module::default();
    second
        .constants
        .push(projection(&s, 2, "w", ConstantKind::Definition));
    let last = assert_equivalent(&[first, second], std::slice::from_ref(&s));
    assert_eq!(last, vec![(s.to_string(), names(&["u", "v", "w"]))]);
}

#[test]
fn test_projection_scan_projections_split_across_modules_match_full_scan() {
    let s = Name::from_string("P1.Split");
    let mut first = Module::default();
    first.families.push(family(&s, 3));
    first
        .constants
        .push(projection(&s, 0, "x", ConstantKind::Definition));
    let mut middle = Module::default();
    middle.constants.push(ConstantInfo::new(
        Name::from_string("Unrelated.c"),
        vec![],
        Expr::type_(),
        None,
        false,
    ));
    let mut last = Module::default();
    last.constants
        .push(projection(&s, 2, "z", ConstantKind::Theorem));
    last.constants
        .push(projection(&s, 1, "y", ConstantKind::Definition));
    let tables = assert_equivalent(&[first, middle, last], std::slice::from_ref(&s));
    assert_eq!(tables, vec![(s.to_string(), names(&["x", "y", "z"]))]);
}

#[test]
fn test_projection_scan_family_after_projections_and_gaps_match_full_scan() {
    let late = Name::from_string("P1.LateFamily");
    let gap = Name::from_string("P1.Gap");
    let decoded = Name::from_string("P1.Decoded");
    let mut first = Module::default();
    first
        .constants
        .push(projection(&late, 0, "p", ConstantKind::Definition));
    first.families.push(family(&gap, 3));
    first
        .constants
        .push(projection(&gap, 0, "g0", ConstantKind::Definition));
    first
        .constants
        .push(projection(&gap, 2, "g2", ConstantKind::Definition));
    first.families.push(family(&decoded, 1));
    first.constants.push(projection(
        &decoded,
        0,
        "recovered",
        ConstantKind::Definition,
    ));
    first
        .decoded_tables
        .push((decoded.clone(), vec![Name::from_string("fromLean")]));
    let mut second = Module::default();
    second.families.push(family(&late, 1));
    let tables = assert_equivalent(
        &[first, second],
        &[late.clone(), gap.clone(), decoded.clone()],
    );
    assert_eq!(
        tables,
        vec![
            (late.to_string(), names(&["p"])),
            (gap.to_string(), None),
            (decoded.to_string(), names(&["fromLean"])),
        ]
    );
}

#[test]
fn test_projection_scan_rebuilds_after_a_write_it_did_not_see() {
    let s = Name::from_string("P1.Outside");
    let mut env = Environment::new();
    load(&mut env, &Module::default(), true);
    // A writer other than the loader: a structure and its projections land
    // with no `note_touched`.
    let (ind, ctor) = family(&s, 1);
    let refused = env.extend_inductives_structural(std::iter::once(ind));
    assert!(refused.is_empty(), "structural tier refused {refused:?}");
    let refused = env.extend_constructors_structural(std::iter::once(ctor));
    assert!(refused.is_empty(), "structural tier refused {refused:?}");
    let refused = env.extend_constants_structural(std::iter::once(projection(
        &s,
        0,
        "only",
        ConstantKind::Definition,
    )));
    assert!(refused.is_empty(), "structural tier refused {refused:?}");
    // The next module touches nothing about `s`, yet the whole-environment
    // scan would register it; so must the incremental one.
    load(&mut env, &Module::default(), true);
    assert_eq!(
        env.get_structure_field_names(&s),
        Some([Name::from_string("only")].as_slice())
    );
}

/// A deterministic mixed sequence: twelve structures of 1-4 fields, their
/// families and projections scattered over eight modules, some families
/// arriving after their projections, some projections never arriving, some
/// structures carrying a decoded table first.
#[test]
fn test_projection_scan_scattered_sequence_matches_full_scan_after_every_module() {
    let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = move |bound: u64| {
        seed = seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (seed >> 33) % bound
    };
    let mut modules = vec![Module::default(); 8];
    let mut watched = Vec::new();
    for i in 0..12u32 {
        let s = Name::from_string(&format!("P1.Scatter{i}"));
        let fields = 1 + u32::try_from(next(4)).expect("small");
        let home = usize::try_from(next(8)).expect("small");
        modules[home].families.push(family(&s, fields));
        if next(5) == 0 {
            modules[home].decoded_tables.push((
                s.clone(),
                (0..fields)
                    .map(|k| Name::from_string(&format!("d{k}")))
                    .collect(),
            ));
        }
        for idx in 0..fields {
            if next(6) == 0 {
                continue; // never arrives: the set stays incomplete
            }
            let at = usize::try_from(next(8)).expect("small");
            let kind = if next(2) == 0 {
                ConstantKind::Definition
            } else {
                ConstantKind::Theorem
            };
            modules[at]
                .constants
                .push(projection(&s, idx, &format!("f{idx}"), kind));
        }
        watched.push(s);
    }
    let tables = assert_equivalent(&modules, &watched);
    // Not vacuous: the sequence ends with tables RECOVERED from projections
    // (fields `f<k>`, not a decoded table's `d<k>`) and with structures left
    // without one, so both decisions were compared.
    let recovered = tables
        .iter()
        .filter(|(_, t)| {
            t.as_ref()
                .and_then(|fs| fs.first())
                .is_some_and(|f| f.to_string().starts_with('f'))
        })
        .count();
    let absent = tables.iter().filter(|(_, t)| t.is_none()).count();
    assert!(
        recovered > 0 && absent > 0,
        "recovered {recovered}, absent {absent}: {tables:?}"
    );
}
