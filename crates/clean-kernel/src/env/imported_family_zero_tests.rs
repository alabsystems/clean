// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Imported recursors whose generation turns on the `is_zero` reading
//! (DECISIONS R150): `axiom A0 : Sort (max 0 0)`, `inductive P0 : Prop | mk :
//! A0 → P0` and `inductive Q0 : Sort (max 0 0) | mk : Q0`. Pinned Lean's
//! kernel reads `is_zero` structurally (`inductive.cpp:517,557`), so it stores
//! `P0.rec` with no universe parameter and `Q0.rec` with `k = false`
//! (`reports/level-lean-profile-2026-10-19/ReachVerdicts.txt`); Clean's
//! `Extended` reads it semantically and generates `P0.rec.{u}` and a K-like
//! `Q0.rec`. Records are imported as the `.olean` loader imports them.

use super::super::types::EnvError;
use super::super::{Declaration, Environment, KernelTheory};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType, RecursorVal};
use crate::level::Level;
use crate::name::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// `Sort (max 0 0)`, built raw as the verbatim decoders keep it.
fn sort_max00() -> Expr {
    Expr::sort(Level::lean_max_core(Level::zero(), Level::zero()))
}

fn one_ctor(name: &str, type_: Expr, ctor: &str, ctor_type: Expr) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n(name),
            type_,
            constructors: vec![Constructor {
                name: n(ctor),
                type_: ctor_type,
            }],
        }],
    }
}

fn p0() -> InductiveDecl {
    one_ctor(
        "P0",
        Expr::sort(Level::zero()),
        "P0.mk",
        Expr::pi(BinderInfo::Default, c("A0"), c("P0")),
    )
}

fn q0() -> InductiveDecl {
    one_ctor("Q0", sort_max00(), "Q0.mk", c("Q0"))
}

/// An environment in `theory` holding the axiom `A0`.
fn with_a0(theory: KernelTheory) -> Environment {
    let mut env = Environment::new();
    env.set_kernel_theory(theory);
    env.add_decl(Declaration::Axiom {
        name: n("A0"),
        level_params: vec![],
        type_: sort_max00(),
    })
    .expect("pinned Lean admits A0");
    env
}

/// The records native admission in `theory` generates for P0 and Q0.
struct Records {
    inductives: Vec<crate::inductive::InductiveVal>,
    constructors: Vec<crate::inductive::ConstructorVal>,
    recursors: Vec<RecursorVal>,
}

fn records_in(theory: KernelTheory) -> Records {
    let mut donor = with_a0(theory);
    let mut out = Records {
        inductives: vec![],
        constructors: vec![],
        recursors: vec![],
    };
    for decl in [p0(), q0()] {
        let name = decl.types[0].name.clone();
        donor
            .add_inductive(decl)
            .expect("pinned Lean and Extended admit P0 and Q0");
        let ind = donor.get_inductive(&name).expect("admitted").clone();
        for ctor in &ind.constructor_names {
            out.constructors
                .push(donor.get_constructor(ctor).expect("admitted ctor").clone());
        }
        out.recursors.push(
            donor
                .get_recursor(&name.clone().str("rec"))
                .expect("admitted rec")
                .clone(),
        );
        out.inductives.push(ind);
    }
    out
}

/// Import `records` into a fresh environment in `theory` through the loader's
/// three structural calls; what the recursor leg refused.
fn import_into(theory: KernelTheory, records: Records) -> Vec<(Name, EnvError)> {
    let mut env = with_a0(theory);
    assert!(env
        .extend_inductives_structural(records.inductives.into_iter())
        .is_empty());
    assert!(env
        .extend_constructors_structural(records.constructors.into_iter())
        .is_empty());
    env.extend_recursors_structural(records.recursors.into_iter())
}

/// The two generations differ (so the tests below are not vacuous): Lean's
/// `P0.rec` has no universe parameter and its `Q0.rec` is not K; Extended's
/// are `P0.rec.{u}` and K-like.
#[test]
fn test_zero_reading_separates_lean_and_extended_generations() {
    let lean = records_in(KernelTheory::Lean);
    let ext = records_in(KernelTheory::Extended);
    assert!(lean.recursors[0].level_params.is_empty());
    assert_eq!(ext.recursors[0].level_params.len(), 1);
    assert!(!lean.recursors[1].is_k);
    assert!(ext.recursors[1].is_k);
}

/// An `Extended` environment admits the records pinned Lean's kernel
/// generated (what a Lean `.olean` stores), and its own.
#[test]
fn test_extended_import_admits_lean_structural_zero_recursors() {
    let refused = import_into(KernelTheory::Extended, records_in(KernelTheory::Lean));
    assert!(refused.is_empty(), "Lean's own records: {refused:?}");
    let refused = import_into(KernelTheory::Extended, records_in(KernelTheory::Extended));
    assert!(refused.is_empty(), "Extended's own records: {refused:?}");
}

/// The retry is one comparison, not a relaxation: a Lean record with one
/// forged field (`P0.rec` claiming K, which neither generation gives a family
/// whose constructor has a field) is refused, and a Lean-theory environment
/// refuses Extended's more permissive records (it never retries).
#[test]
fn test_zero_reading_retry_refuses_what_neither_generation_gives() {
    let mut forged = records_in(KernelTheory::Lean);
    forged.recursors[0].is_k = true;
    let refused = import_into(KernelTheory::Extended, forged);
    assert!(
        refused.iter().any(|(name, _)| *name == n("P0.rec")),
        "forged P0.rec must be refused: {refused:?}"
    );
    let refused = import_into(KernelTheory::Lean, records_in(KernelTheory::Extended));
    let names: Vec<&Name> = refused.iter().map(|(name, _)| name).collect();
    assert!(
        names.contains(&&n("P0.rec")) && names.contains(&&n("Q0.rec")),
        "Lean refuses Extended's P0.rec.{{u}} and K-like Q0.rec: {refused:?}"
    );
}

/// `A2 (a b : Prop) : Prop | intro : a → b → A2 a b`, the container (`And`'s
/// shape) the nested families below occur in.
fn a2() -> InductiveDecl {
    let a = Expr::bvar(1);
    let app = |x: Expr, y: Expr| Expr::app(Expr::app(c("A2"), x), y);
    let prop = Expr::sort(Level::zero());
    InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: n("A2"),
            type_: Expr::pi(
                BinderInfo::Default,
                prop.clone(),
                Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
            ),
            constructors: vec![Constructor {
                name: n("A2.intro"),
                // Π (a b : Prop), a → b → A2 a b
                type_: Expr::pi(
                    BinderInfo::Default,
                    prop.clone(),
                    Expr::pi(
                        BinderInfo::Default,
                        prop,
                        Expr::pi(
                            BinderInfo::Default,
                            a.clone(),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::bvar(1),
                                app(Expr::bvar(3), Expr::bvar(2)),
                            ),
                        ),
                    ),
                ),
            }],
        }],
    }
}

/// `inductive PN : Prop | mk : A0 → A2 PN PN → PN` (a field of sort
/// `max 0 0`) and `inductive QN : Sort (max 0 0) | mk : A2 QN QN → QN` (a
/// result level that is zero only semantically), each nested through `A2`.
/// Pinned Lean v4.30.0-rc2 admits both and stores `PN.rec` and `QN.rec` with
/// no universe parameter and `k = false` (`lean --run` probe, DECISIONS R150).
fn nested_families() -> [InductiveDecl; 2] {
    let nest = |t: &str| Expr::app(Expr::app(c("A2"), c(t)), c(t));
    [
        one_ctor(
            "PN",
            Expr::sort(Level::zero()),
            "PN.mk",
            Expr::pi(
                BinderInfo::Default,
                c("A0"),
                Expr::pi(BinderInfo::Default, nest("PN"), c("PN")),
            ),
        ),
        one_ctor(
            "QN",
            sort_max00(),
            "QN.mk",
            Expr::pi(BinderInfo::Default, nest("QN"), c("QN")),
        ),
    ]
}

/// An environment in `theory` holding `A0` and `A2`.
fn with_a0_a2(theory: KernelTheory) -> Environment {
    let mut env = with_a0(theory);
    env.add_inductive(a2())
        .expect("pinned Lean admits And's shape");
    env
}

/// The records native admission in `theory` generates for the nested
/// families, with every recursor of each family's name.
fn nested_records_in(theory: KernelTheory) -> Records {
    let mut donor = with_a0_a2(theory);
    let mut out = Records {
        inductives: vec![],
        constructors: vec![],
        recursors: vec![],
    };
    for decl in nested_families() {
        let name = decl.types[0].name.clone();
        donor
            .add_inductive(decl)
            .expect("pinned Lean and Extended admit PN and QN");
        let ind = donor.get_inductive(&name).expect("admitted").clone();
        assert!(ind.is_nested, "{name} must go through the nested pipeline");
        for ctor in &ind.constructor_names {
            out.constructors
                .push(donor.get_constructor(ctor).expect("admitted ctor").clone());
        }
        let mut recs: Vec<RecursorVal> = ["rec", "rec_1", "rec_2"]
            .iter()
            .filter_map(|suffix| donor.get_recursor(&name.clone().str(*suffix)).cloned())
            .collect();
        assert!(!recs.is_empty(), "{name}: no recursor generated");
        out.recursors.append(&mut recs);
        out.inductives.push(ind);
    }
    out
}

/// The loader's Lean-reading comparison skips nested families
/// (`matches_lean_structural_generation`) because neither `is_zero` reading
/// changes their records: a nested family is generated as a block with its
/// auxiliary types, so the elimination level never reads a field's sort (a
/// possibly-zero mutual block eliminates only into `Prop`) and the K test
/// never reads the result level (K needs a one-type block). This pins it on
/// the two shapes that separate the readings for a non-nested family: Lean's
/// and Extended's generations agree, match what pinned Lean stores, and an
/// `Extended` environment's loader admits Lean's records with no retry. The
/// day a nested generation reads `is_zero`, this fails, and the retry must
/// learn nested families.
#[test]
fn test_zero_reading_never_separates_nested_generations() {
    let lean = nested_records_in(KernelTheory::Lean);
    let ext = nested_records_in(KernelTheory::Extended);
    assert_eq!(lean.recursors.len(), ext.recursors.len());
    for (l, e) in lean.recursors.iter().zip(&ext.recursors) {
        assert_eq!(l.name, e.name);
        assert!(
            l.level_params.is_empty() && !l.is_k,
            "pinned Lean stores {} with no universe parameter and k = false: {:?} k={}",
            l.name,
            l.level_params,
            l.is_k
        );
        super::compare_recursor(l, e, crate::level::LeanLevelProfile::Lean430)
            .unwrap_or_else(|detail| panic!("{}: the readings separate it: {detail}", l.name));
    }
    let mut env = with_a0_a2(KernelTheory::Extended);
    assert!(env
        .extend_inductives_structural(lean.inductives.into_iter())
        .is_empty());
    assert!(env
        .extend_constructors_structural(lean.constructors.into_iter())
        .is_empty());
    let refused = env.extend_recursors_structural(lean.recursors.into_iter());
    assert!(refused.is_empty(), "Lean's nested records: {refused:?}");
}
