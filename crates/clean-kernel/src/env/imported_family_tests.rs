// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Imported inductive-family record regressions.
//!
//! Every fixture registers its "imported" family exactly as the `.olean`
//! loader does (`register_converted_constants`, passes 1-3):
//! `extend_inductives_structural`, then `extend_constructors_structural`, then
//! `extend_recursors_structural`. The records are the kernel's own, generated
//! natively in a donor environment, so the only thing a test changes is the
//! one field a crafted file would forge.

use super::super::types::EnvError;
use super::super::{Declaration, Environment};
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

/// `inductive B : Type | t | f` — two distinct values.
fn bool_like() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("B"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: n("B.t"),
                    type_: c("B"),
                },
                Constructor {
                    name: n("B.f"),
                    type_: c("B"),
                },
            ],
        }],
    }
}

/// `inductive S : B → Type | mk : (a : B) → S B.t` — Type-valued, one
/// constructor carrying a field the index does not determine. Lean's kernel
/// makes its recursor `k := false` (not an inductive predicate, and the
/// constructor has a field), and so does this kernel's native admission.
fn singleton_index_family() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("S"),
            type_: Expr::pi(BinderInfo::Default, c("B"), Expr::type_()),
            constructors: vec![Constructor {
                name: n("S.mk"),
                type_: Expr::pi(BinderInfo::Default, c("B"), Expr::app(c("S"), c("B.t"))),
            }],
        }],
    }
}

/// The kernel-generated records for `decl` (family, constructors, `.rec`s),
/// taken from a donor environment that admitted it natively.
struct FamilyRecords {
    inductives: Vec<crate::inductive::InductiveVal>,
    constructors: Vec<crate::inductive::ConstructorVal>,
    recursors: Vec<RecursorVal>,
}

fn native_records(donor: &mut Environment, decl: InductiveDecl) -> FamilyRecords {
    let names: Vec<Name> = decl.types.iter().map(|t| t.name.clone()).collect();
    donor
        .add_inductive(decl)
        .expect("fixture family must pass native admission");
    let mut records = FamilyRecords {
        inductives: vec![],
        constructors: vec![],
        recursors: vec![],
    };
    for name in names {
        let ind = donor.get_inductive(&name).expect("admitted family").clone();
        for ctor in &ind.constructor_names {
            records
                .constructors
                .push(donor.get_constructor(ctor).expect("admitted ctor").clone());
        }
        records.recursors.push(
            donor
                .get_recursor(&name.clone().str("rec"))
                .expect("admitted rec")
                .clone(),
        );
        records.inductives.push(ind);
    }
    records
}

/// Register `records` through the loader's three structural calls and return
/// what the recursor leg refused.
fn import_structurally(env: &mut Environment, records: FamilyRecords) -> Vec<(Name, EnvError)> {
    assert!(env
        .extend_inductives_structural(records.inductives.into_iter())
        .is_empty());
    assert!(env
        .extend_constructors_structural(records.constructors.into_iter())
        .is_empty());
    env.extend_recursors_structural(records.recursors.into_iter())
}

/// An environment with `Eq`, the dependency `B` imported honestly, and the
/// donor that generated every record.
fn base() -> (Environment, Environment) {
    let mut donor = Environment::new();
    donor.init_eq().expect("Eq");
    let mut env = Environment::new();
    env.init_eq().expect("Eq");
    let b = native_records(&mut donor, bool_like());
    assert!(import_structurally(&mut env, b).is_empty());
    (env, donor)
}

/// The ordinary mutual Ev/Od shape also present in the pinned-Lean
/// `family_records` loader fixture. Retain all three native recursor entries
/// for each member, not just `.rec`.
fn mutual_cache_fixture() -> (Environment, Vec<RecursorVal>) {
    let (mut env, mut donor) = base();
    let records = native_records(
        &mut donor,
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![
                InductiveType {
                    name: n("Ev"),
                    type_: Expr::type_(),
                    constructors: vec![
                        Constructor {
                            name: n("Ev.zero"),
                            type_: c("Ev"),
                        },
                        Constructor {
                            name: n("Ev.succ"),
                            type_: Expr::arrow(c("Od"), c("Ev")),
                        },
                    ],
                },
                InductiveType {
                    name: n("Od"),
                    type_: Expr::type_(),
                    constructors: vec![Constructor {
                        name: n("Od.succ"),
                        type_: Expr::arrow(c("Ev"), c("Od")),
                    }],
                },
            ],
        },
    );
    assert!(env
        .extend_inductives_structural(records.inductives.into_iter())
        .is_empty());
    assert!(env
        .extend_constructors_structural(records.constructors.into_iter())
        .is_empty());
    let mut recursors = records.recursors;
    for member in ["Ev", "Od"] {
        for suffix in ["casesOn", "recOn"] {
            recursors.push(
                donor
                    .get_recursor(&n(&format!("{member}.{suffix}")))
                    .expect("native mutual auxiliary recursor")
                    .clone(),
            );
        }
    }
    (env, recursors)
}

#[test]
fn test_imported_recursor_mutual_cache_reuses_one_generation_in_both_orders() {
    let (env, recursors) = mutual_cache_fixture();
    assert_eq!(
        recursors.len(),
        6,
        "the fixture must exercise every mutual entry"
    );
    for reverse in [false, true] {
        let mut ordered = recursors.clone();
        if reverse {
            ordered.reverse();
        }
        let mut cache = super::GeneratedRecursorCache::new();
        let mut retained_table = None;
        for rec in &ordered {
            let admitted = env
                .admit_imported_recursor(rec.clone(), &mut cache)
                .expect("every honest mutual entry must match");
            super::compare_recursor(rec, &admitted, env.lean_level_profile())
                .expect("unchanged admitted record");
            assert_eq!(cache.len(), 1, "one block after every admission");
            let generated = cache
                .get(&n("Ev"))
                .expect("first declared member is the canonical key")
                .as_ref()
                .expect("successful generation");
            assert_eq!(generated.len(), 6);
            // A later admission retains the same owned table, not a clone or
            // a replacement generation whose allocation is then discarded.
            let table = retained_table.get_or_insert(generated.as_ptr());
            assert_eq!(generated.as_ptr(), *table);
        }
        // Exercise the production structural batch as well as the directly
        // observed cache seam, with the same two input orders.
        let mut loaded = env.clone();
        assert!(loaded
            .extend_recursors_structural(ordered.into_iter())
            .is_empty());
        for rec in &recursors {
            super::compare_recursor(
                rec,
                loaded
                    .get_recursor(&rec.name)
                    .expect("installed honest entry"),
                loaded.lean_level_profile(),
            )
            .expect("bulk loader retains the exact recursor");
        }
    }
}

#[test]
fn test_imported_recursor_mutual_cache_key_requires_exact_block_metadata() {
    let (env, _) = mutual_cache_fixture();
    assert_eq!(env.imported_recursor_cache_root(&n("Od")), n("Ev"));

    // Deliberately edit only fresh fixture copies BEFORE any cache is used.
    // Even structurally malformed metadata must not acquire an alias from a
    // shared first name. These are identity checks, not new admission rules.
    let mut changed = env.clone();
    changed
        .inductives
        .get_mut(&n("Od"))
        .unwrap()
        .all_names
        .reverse();
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env.clone();
    changed
        .inductives
        .get_mut(&n("Od"))
        .unwrap()
        .all_names
        .push(n("B"));
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env.clone();
    for member in ["Ev", "Od"] {
        changed.inductives.get_mut(&n(member)).unwrap().all_names = vec![n("Ev")];
    }
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env.clone();
    changed.inductives.get_mut(&n("Od")).unwrap().num_params = 1;
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env.clone();
    changed.inductives.get_mut(&n("Od")).unwrap().level_params = vec![n("u")];
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env.clone();
    changed.inductives.get_mut(&n("Ev")).unwrap().level_params = vec![n("u"), n("v")];
    changed.inductives.get_mut(&n("Od")).unwrap().level_params = vec![n("v"), n("u")];
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env.clone();
    changed
        .inductives
        .get_mut(&n("Od"))
        .unwrap()
        .all_names
        .clear();
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));

    let mut changed = env;
    changed.inductives.remove(&n("Ev"));
    assert_eq!(changed.imported_recursor_cache_root(&n("Od")), n("Od"));
    assert_eq!(
        changed.imported_recursor_cache_root(&n("Absent")),
        n("Absent")
    );
}

#[test]
fn test_imported_recursor_mutual_cache_mismatched_block_matches_cold_refusal() {
    let (mut env, recursors) = mutual_cache_fixture();
    // The two roots share a first name but rebuild different motive/minor
    // lists. This malformed structural metadata must not reuse Ev's success.
    env.inductives
        .get_mut(&n("Od"))
        .unwrap()
        .all_names
        .push(n("B"));
    let even = recursors.iter().find(|r| r.name == n("Ev.rec")).unwrap();
    let odd = recursors.iter().find(|r| r.name == n("Od.rec")).unwrap();
    let mut cache = super::GeneratedRecursorCache::new();
    env.admit_imported_recursor(even.clone(), &mut cache)
        .expect("Ev's own block remains unchanged");
    assert_eq!(cache.len(), 1);
    let warm = env
        .admit_imported_recursor(odd.clone(), &mut cache)
        .expect_err("Od's different block must be regenerated and compared");
    let cold = env
        .admit_imported_recursor(odd.clone(), &mut super::GeneratedRecursorCache::new())
        .expect_err("uncached admission refuses the same record");
    assert_eq!(warm.to_string(), cold.to_string());
    assert_refused(&[(odd.name.clone(), warm)], "Od.rec", "num_motives");
    assert_eq!(cache.len(), 2);
    assert!(matches!(cache.get(&n("Od")), Some(Ok(_))));
}

#[test]
fn test_imported_recursor_mutual_cache_warm_success_still_refuses_forgery() {
    let (env, recursors) = mutual_cache_fixture();
    let even = recursors.iter().find(|r| r.name == n("Ev.rec")).unwrap();
    let odd = recursors.iter().find(|r| r.name == n("Od.rec")).unwrap();
    let mut cache = super::GeneratedRecursorCache::new();
    env.admit_imported_recursor(even.clone(), &mut cache)
        .expect("warm Ev block");
    for (mut forged, needle) in [
        (odd.clone(), "K-like flag"),
        (odd.clone(), "iota right-hand side"),
    ] {
        if needle == "K-like flag" {
            forged.is_k = !forged.is_k;
        } else {
            forged.rules[0].rhs = c("B.t");
        }
        let error = env
            .admit_imported_recursor(forged, &mut cache)
            .expect_err("forged sibling");
        assert_refused(&[(n("Od.rec"), error)], "Od.rec", needle);
        assert_eq!(
            cache.len(),
            1,
            "a warm cache does not admit a file's metadata"
        );
    }
    env.admit_imported_recursor(odd.clone(), &mut cache)
        .expect("honest sibling still admitted");
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_imported_recursor_mutual_cache_keeps_unrelated_blocks_separate() {
    let (env, recursors) = mutual_cache_fixture();
    let mut cache = super::GeneratedRecursorCache::new();
    for rec in recursors {
        env.admit_imported_recursor(rec, &mut cache)
            .expect("mutual entry");
    }
    let b = env.get_recursor(&n("B.rec")).expect("unrelated B").clone();
    env.admit_imported_recursor(b, &mut cache)
        .expect("unrelated entry");
    assert_eq!(cache.len(), 2);
    assert!(matches!(cache.get(&n("Ev")), Some(Ok(_))));
    assert!(matches!(cache.get(&n("B")), Some(Ok(_))));
}

#[test]
fn test_imported_recursor_mutual_cache_failures_keep_original_root_diagnostics() {
    let (mut env, recursors) = mutual_cache_fixture();
    // Remove a constructor before the batch starts; both roots now fail to
    // reconstruct the same block, with their own original diagnostic names.
    env.constructors.remove(&n("Od.succ"));
    for reverse in [false, true] {
        let mut ordered = recursors.clone();
        if reverse {
            ordered.reverse();
        }
        let mut cache = super::GeneratedRecursorCache::new();
        for rec in ordered {
            let root = super::recursor_family_root(&rec.name).expect("native recursor name");
            let expected = format!("family {root} is not resident with all its constructors");
            let error = env
                .admit_imported_recursor(rec.clone(), &mut cache)
                .expect_err("missing constructor");
            match error {
                EnvError::ImportedFamilyRecordMismatch { name, detail } => {
                    assert_eq!(name, rec.name);
                    assert_eq!(detail, expected);
                }
                other => panic!("expected generation refusal, got {other:?}"),
            }
            assert_eq!(cache.get(&root).unwrap().as_ref().unwrap_err(), &expected);
        }
        assert_eq!(cache.len(), 2, "failed roots remain separately cached");
        assert!(matches!(cache.get(&n("Ev")), Some(Err(_))));
        assert!(matches!(cache.get(&n("Od")), Some(Err(_))));
    }
}

fn eq_b(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(n("Eq"), vec![Level::succ(Level::zero())]),
                c("B"),
            ),
            lhs,
        ),
        rhs,
    )
}

fn refl_b(a: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(n("Eq.refl"), vec![Level::succ(Level::zero())]),
            c("B"),
        ),
        a,
    )
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// `@S.rec.{1} (fun _ _ => B) (fun a => a) B.t x`
fn s_rec_on(x: Expr) -> Expr {
    let motive = Expr::lam(
        BinderInfo::Default,
        c("B"),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(c("S"), Expr::bvar(0)),
            c("B"),
        ),
    );
    let minor = Expr::lam(BinderInfo::Default, c("B"), Expr::bvar(0));
    let head = Expr::const_(n("S.rec"), vec![Level::succ(Level::zero())]);
    Expr::app(
        Expr::app(Expr::app(Expr::app(head, motive), minor), c("B.t")),
        x,
    )
}

/// `bad : ∀ x : S B.t, S.rec … x = B.t := fun x => rfl` — holds only if K
/// fires on the Type-valued `S`; Lean's kernel rejects it (`S.rec … x` is
/// stuck on a variable).
fn bad_k_theorem() -> Declaration {
    let s_bt = Expr::app(c("S"), c("B.t"));
    theorem(
        "bad_k",
        Expr::pi(
            BinderInfo::Default,
            s_bt.clone(),
            eq_b(s_rec_on(Expr::bvar(0)), c("B.t")),
        ),
        Expr::lam(BinderInfo::Default, s_bt, refl_b(c("B.t"))),
    )
}

/// `worse : B.f = B.t := bad_k (S.mk B.f)` — two distinct constructors.
fn worse_theorem() -> Declaration {
    theorem(
        "worse",
        eq_b(c("B.f"), c("B.t")),
        Expr::app(c("bad_k"), Expr::app(c("S.mk"), c("B.f"))),
    )
}

fn assert_refused(rejected: &[(Name, EnvError)], rec: &str, needle: &str) {
    let [(name, error)] = rejected else {
        panic!("expected exactly one refusal of {rec}, got {rejected:?}");
    };
    assert_eq!(name, &n(rec));
    match error {
        EnvError::ImportedFamilyRecordMismatch { name, detail } => {
            assert_eq!(name, &n(rec));
            assert!(
                detail.contains(needle),
                "refusal of {rec} must name `{needle}`, got: {detail}"
            );
        }
        other => panic!("expected ImportedFamilyRecordMismatch for {rec}, got {other:?}"),
    }
}

/// The honest records import, and the kernel then REFUSES `bad_k` — the
/// control that makes the forged arms below non-vacuous.
#[test]
fn test_imported_recursor_honest_family_imports_and_refuses_bad_k() {
    let (mut env, mut donor) = base();
    let s = native_records(&mut donor, singleton_index_family());
    assert!(!s.recursors[0].is_k, "the kernel generates k=false for S");
    let rejected = import_structurally(&mut env, s);
    assert!(
        rejected.is_empty(),
        "honest S.rec must import: {rejected:?}"
    );
    assert!(env.get_recursor(&n("S.rec")).is_some());
    env.add_decl(bad_k_theorem())
        .expect_err("with the generated recursor, `S.rec … x` is stuck and bad_k is false");
}

/// A crafted file sets `k = true` on the Type-valued, field-carrying `S`.
/// The import tier must refuse the record; if it does not, the kernel goes on
/// to accept `B.f = B.t`.
#[test]
fn test_imported_recursor_forged_k_on_type_valued_family_is_refused() {
    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    s.recursors[0].is_k = true;
    let rejected = import_structurally(&mut env, s);
    if rejected.is_empty() {
        let bad = env.add_decl(bad_k_theorem());
        let worse = env.add_decl(worse_theorem());
        panic!(
            "forged k=true S.rec was ADMITTED by extend_recursors_structural; \
             the kernel then decided bad_k: {bad:?}, and `B.f = B.t`: {worse:?}"
        );
    }
    assert_refused(&rejected, "S.rec", "K-like flag");
    assert!(env.get_recursor(&n("S.rec")).is_none());
    assert!(env.get_const(&n("S.rec")).is_none());
    assert!(env.add_decl(bad_k_theorem()).is_err());
}

/// A crafted file swaps an iota rule: `B.rec … B.t ↦` the `f` minor. The
/// import tier must refuse it; if it does not, the kernel accepts
/// `B.rec (fun _ => B) B.t B.f B.t = B.f`, which Lean's kernel rejects.
#[test]
fn test_imported_recursor_forged_iota_rule_is_refused() {
    let mut donor = Environment::new();
    donor.init_eq().expect("Eq");
    let mut env = Environment::new();
    env.init_eq().expect("Eq");
    let mut b = native_records(&mut donor, bool_like());
    let f_rule = b.recursors[0].rules[1].rhs.clone();
    b.recursors[0].rules[0].rhs = f_rule;
    let rejected = import_structurally(&mut env, b);
    let motive = Expr::lam(BinderInfo::Default, c("B"), c("B"));
    let b_rec_t = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(n("B.rec"), vec![Level::succ(Level::zero())]),
                    motive,
                ),
                c("B.t"),
            ),
            c("B.f"),
        ),
        c("B.t"),
    );
    let wrong = theorem("wrong_iota", eq_b(b_rec_t, c("B.f")), refl_b(c("B.f")));
    if rejected.is_empty() {
        let accepted = env.add_decl(wrong);
        panic!(
            "forged iota rule for B.rec was ADMITTED by extend_recursors_structural; \
             the kernel then decided `B.rec (fun _ => B) B.t B.f B.t = B.f`: {accepted:?}"
        );
    }
    assert_refused(&rejected, "B.rec", "iota right-hand side");
    assert!(env.add_decl(wrong).is_err());
}

/// A crafted file gives the Prop-only family a large-eliminating recursor
/// (an extra motive universe), the proof-irrelevance break. Refused on the
/// universe arity before any type comparison.
#[test]
fn test_imported_recursor_forged_large_elimination_is_refused() {
    let (mut env, mut donor) = base();
    // `inductive P : Prop | a | b` — two constructors, Prop-only elimination.
    let p = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("P"),
            type_: Expr::prop(),
            constructors: vec![
                Constructor {
                    name: n("P.a"),
                    type_: c("P"),
                },
                Constructor {
                    name: n("P.b"),
                    type_: c("P"),
                },
            ],
        }],
    };
    let mut p = native_records(&mut donor, p);
    let rec = &mut p.recursors[0];
    assert!(
        rec.level_params.is_empty(),
        "P.rec eliminates into Prop only"
    );
    // Forge `P.rec.{u}` with motive `P → Sort u` — B's large recursor's shape.
    let u = n("u");
    rec.level_params = vec![u.clone()];
    rec.type_ = replace_motive_sort(&rec.type_, Level::param(u));
    let rejected = import_structurally(&mut env, p);
    assert_refused(&rejected, "P.rec", "universe parameters");
}

fn replace_motive_sort(rec_type: &Expr, level: Level) -> Expr {
    use crate::expr::ExprKind;
    let ExprKind::Pi(bi, motive_ty, body) = rec_type.kind() else {
        panic!("recursor type starts with the motive binder");
    };
    let ExprKind::Pi(mbi, dom, _) = motive_ty.kind() else {
        panic!("motive is a function of the major");
    };
    let motive = Expr::pi(*mbi, dom.as_ref().clone(), Expr::sort(level));
    Expr::pi(*bi, motive, body.as_ref().clone())
}

/// Forged metadata counts, and a recursor under a name the kernel never
/// generates, are refused; a recursor whose family is absent is refused.
#[test]
fn test_imported_recursor_forged_counts_foreign_name_and_orphan_are_refused() {
    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    s.recursors[0].num_indices = 0;
    s.recursors[0].num_params = 1;
    assert_refused(&import_structurally(&mut env, s), "S.rec", "num_params");

    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    s.recursors[0].name = n("S.elim");
    assert_refused(
        &import_structurally(&mut env, s),
        "S.elim",
        "not a name the kernel generates",
    );

    let (mut env, mut donor) = base();
    let s = native_records(&mut donor, singleton_index_family());
    let orphan = env.extend_recursors_structural(s.recursors.into_iter());
    assert_refused(&orphan, "S.rec", "is not resident");
}

/// `inductive Pair : Type | mk : B → B → Pair` — a two-field structure.
fn pair() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("Pair"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: n("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    c("B"),
                    Expr::pi(BinderInfo::Default, c("B"), c("Pair")),
                ),
            }],
        }],
    }
}

/// A crafted file gives `Pair.mk` one more parameter and one fewer field.
/// Projection reduction indexes fields past `num_params`, so if the record
/// were admitted `(Pair.mk B.t B.f).1` would reduce to `B.f`.
#[test]
fn test_imported_family_forged_constructor_arity_is_refused() {
    let (mut env, mut donor) = base();
    let mut p = native_records(&mut donor, pair());
    p.constructors[0].num_params = 1;
    p.constructors[0].num_fields = 1;
    assert!(env
        .extend_inductives_structural(p.inductives.into_iter())
        .is_empty());
    let rejected = env.extend_constructors_structural(p.constructors.into_iter());
    let first = Expr::proj(
        n("Pair"),
        0,
        Expr::app(Expr::app(c("Pair.mk"), c("B.t")), c("B.f")),
    );
    let wrong = theorem("wrong_proj", eq_b(first, c("B.f")), refl_b(c("B.f")));
    if rejected.is_empty() {
        let accepted = env.add_decl(wrong);
        panic!(
            "forged Pair.mk arity was ADMITTED by extend_constructors_structural; \
             the kernel then decided `(Pair.mk B.t B.f).1 = B.f`: {accepted:?}"
        );
    }
    assert_refused(&rejected, "Pair.mk", "num_params=1 num_fields=1");
    assert!(env.get_constructor(&n("Pair.mk")).is_none());
    // The family is now incomplete, so its recursor cannot be admitted either.
    assert_refused(
        &env.extend_recursors_structural(p.recursors.into_iter()),
        "Pair.rec",
        "is not resident with all its constructors",
    );
}

/// A constructor listed at another position, or with other universes, or
/// whose owner is absent, is refused.
#[test]
fn test_imported_family_constructor_position_owner_and_levels_are_checked() {
    let (mut env, mut donor) = base();
    let mut p = native_records(&mut donor, pair());
    p.constructors[0].constructor_idx = 1;
    assert!(env
        .extend_inductives_structural(p.inductives.into_iter())
        .is_empty());
    assert_refused(
        &env.extend_constructors_structural(p.constructors.into_iter()),
        "Pair.mk",
        "constructor_idx=1",
    );

    let (mut env, mut donor) = base();
    let mut p = native_records(&mut donor, pair());
    p.constructors[0].level_params = vec![n("u")];
    assert!(env
        .extend_inductives_structural(p.inductives.into_iter())
        .is_empty());
    assert_refused(
        &env.extend_constructors_structural(p.constructors.into_iter()),
        "Pair.mk",
        "universe parameters",
    );

    let (mut env, mut donor) = base();
    let p = native_records(&mut donor, pair());
    assert_refused(
        &env.extend_constructors_structural(p.constructors.into_iter()),
        "Pair.mk",
        "owning inductive Pair is not resident",
    );
}

/// An inductive whose `num_indices` is not its type's arity minus its
/// parameters is refused (structure eta and K read `num_indices`).
#[test]
fn test_imported_family_forged_index_count_is_refused() {
    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    s.inductives[0].num_indices = 0;
    assert_refused(
        &env.extend_inductives_structural(s.inductives.into_iter()),
        "S",
        "does not split",
    );
}

/// Clean's own payload carries the native `casesOn`/`recOn` recursor-table
/// entries; the kernel generates them too, so they import — and a forged
/// argument order on one of them is refused.
#[test]
fn test_imported_family_native_cases_on_and_rec_on_entries_import() {
    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    for suffix in ["casesOn", "recOn"] {
        s.recursors.push(
            donor
                .get_recursor(&n(&format!("S.{suffix}")))
                .expect("native admission generates the entry")
                .clone(),
        );
    }
    let rejected = import_structurally(&mut env, s);
    assert!(
        rejected.is_empty(),
        "native entries must import: {rejected:?}"
    );
    assert!(env.get_recursor(&n("S.casesOn")).is_some());

    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    let mut cases = donor
        .get_recursor(&n("S.casesOn"))
        .expect("native casesOn")
        .clone();
    cases.arg_order = crate::inductive::RecursorArgOrder::MajorAfterMinors;
    s.recursors.push(cases);
    assert_refused(
        &import_structurally(&mut env, s),
        "S.casesOn",
        "argument order",
    );
}

/// Replace the domain of the `n`-th (0-based) binder of a Pi telescope.
fn replace_nth_pi_domain(ty: &Expr, n: usize, domain: Expr) -> Expr {
    use crate::expr::ExprKind;
    let ExprKind::Pi(bi, dom, body) = ty.kind() else {
        panic!("telescope ended before binder {n}");
    };
    if n == 0 {
        Expr::pi(*bi, domain, body.as_ref().clone())
    } else {
        Expr::pi(
            *bi,
            dom.as_ref().clone(),
            replace_nth_pi_domain(body, n - 1, domain),
        )
    }
}

/// `@Quot.lift.{1,1} B r B (fun x => x) h (@Quot.mk.{1} B r B.f)` with
/// `r := fun _ _ => B.t = B.t`.
fn quot_lift_on_mk(h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    let r = Expr::lam(
        BinderInfo::Default,
        c("B"),
        Expr::lam(BinderInfo::Default, c("B"), eq_b(c("B.t"), c("B.t"))),
    );
    let id_b = Expr::lam(BinderInfo::Default, c("B"), Expr::bvar(0));
    let mk = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(n("Quot.mk"), vec![one.clone()]), c("B")),
            r.clone(),
        ),
        c("B.f"),
    );
    let lift = Expr::const_(n("Quot.lift"), vec![one.clone(), one]);
    [c("B"), r, c("B"), id_b, h, mk]
        .into_iter()
        .fold(lift, Expr::app)
}

/// A `Quot.lift` whose TYPE a file chose — registered as the plain axiom the
/// importer used to make of a `Quot`-kind record, here with the respect
/// premise `∀ a b, r a b → f a = f b` replaced by `β → β` — must carry no
/// quotient reduction. The kernel-built primitive keeps it (control).
#[test]
fn test_imported_family_file_typed_quot_lift_has_no_reduction() {
    use crate::env::{ConstantInfo, ConstantKind, Reducibility};
    use crate::quot::{quot_lift_type, quot_mk_type, quot_type};
    let (u, v) = (n("u"), n("v"));
    let mut env = Environment::new();
    env.init_eq().expect("Eq");
    env.add_inductive(bool_like()).expect("B");
    // Binder 4 of Quot.lift is `h`; under α r β f, β is bvar 1.
    let forged_lift = replace_nth_pi_domain(
        &quot_lift_type(&u, &v),
        4,
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
    );
    let file_records = [
        ("Quot", vec![u.clone()], quot_type(&u)),
        ("Quot.mk", vec![u.clone()], quot_mk_type(&u)),
        ("Quot.lift", vec![u.clone(), v], forged_lift),
    ]
    .into_iter()
    .map(|(name, levels, ty)| {
        ConstantInfo::new_with_reducibility(
            n(name),
            levels,
            ty,
            None,
            Reducibility::Regular(0),
            ConstantKind::Axiom,
        )
    });
    assert!(env.extend_constants_structural(file_records).is_empty());
    let id_b = Expr::lam(BinderInfo::Default, c("B"), Expr::bvar(0));
    let file_term = quot_lift_on_mk(id_b);
    assert!(
        !crate::tc::TypeChecker::new(&env).is_def_eq(&file_term, &c("B.f")),
        "a file-typed `Quot.lift` axiom was given the kernel's quotient reduction"
    );

    let mut kernel = Environment::new();
    kernel.init_eq().expect("Eq");
    kernel.add_inductive(bool_like()).expect("B");
    kernel.init_quot();
    let kernel_term = quot_lift_on_mk(c("B.t"));
    assert!(
        crate::tc::TypeChecker::new(&kernel).is_def_eq(&kernel_term, &c("B.f")),
        "the kernel-built `Quot.lift` must still reduce on `Quot.mk`"
    );
}

/// `(fun x : Sort 2 => x) e` — a β-redex whose contractum is `e`.
fn beta_redex_around(e: Expr) -> Expr {
    let two = Level::succ(Level::succ(Level::zero()));
    Expr::app(
        Expr::lam(BinderInfo::Default, Expr::sort(two), Expr::bvar(0)),
        e,
    )
}

/// Lean writes some recursor types with a β-redex the kernel's own pipeline
/// reduces (a nested family's dependent container parameter). β is part of
/// the kernel's definitional equality, so a record that differs from the
/// generated one only by β imports; a non-normalizing term in the same
/// position is refused on the budget instead of hanging the import.
#[test]
fn test_imported_family_beta_equal_type_imports_and_omega_is_refused() {
    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    // Wrap the index binder's domain `B` of `S.rec`'s motive in a redex.
    let rec = &mut s.recursors[0];
    rec.type_ = replace_motive_domain(&rec.type_, beta_redex_around(c("B")));
    let rejected = import_structurally(&mut env, s);
    assert!(
        rejected.is_empty(),
        "a β-equal type must import: {rejected:?}"
    );

    let (mut env, mut donor) = base();
    let mut s = native_records(&mut donor, singleton_index_family());
    let delta = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(Expr::bvar(0), Expr::bvar(0)),
    );
    let omega = Expr::app(delta.clone(), delta);
    let rec = &mut s.recursors[0];
    rec.type_ = replace_motive_domain(&rec.type_, omega);
    assert_refused(
        &import_structurally(&mut env, s),
        "S.rec",
        "budget exhausted",
    );
}

/// Replace the first binder domain of the motive (`S.rec`'s motive is
/// `(a : B) → S a → Sort u`).
fn replace_motive_domain(rec_type: &Expr, domain: Expr) -> Expr {
    use crate::expr::ExprKind;
    let ExprKind::Pi(bi, motive_ty, body) = rec_type.kind() else {
        panic!("recursor type starts with the motive binder");
    };
    let motive = replace_nth_pi_domain(motive_ty, 0, domain);
    Expr::pi(*bi, motive, body.as_ref().clone())
}

/// A type former hidden behind a definition (Mathlib's
/// `ObjectProperty C := C → Prop`, measured on the pinned closure): Lean's
/// kernel counts the index the definition unfolds to, so the stored
/// `num_indices` exceeds the syntactic remainder. That record imports; a
/// `Sort`-headed type keeps the exact split (the forged-index arm above).
#[test]
fn test_imported_family_hidden_type_former_may_carry_extra_indices() {
    use crate::inductive::InductiveVal;
    let mut env = Environment::new();
    let hidden = InductiveVal {
        name: n("Hidden"),
        level_params: vec![],
        // `Hidden : Pred` where `Pred` is a definition, not a `Sort`.
        type_: c("Pred"),
        num_params: 0,
        num_indices: 1,
        all_names: vec![n("Hidden")],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    };
    assert!(
        env.extend_inductives_structural(std::iter::once(hidden))
            .is_empty(),
        "a hidden type former's extra index is Lean's count, not a forgery"
    );
    let mut fewer = InductiveVal {
        name: n("Fewer"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, c("B"), c("Pred")),
        num_params: 0,
        num_indices: 0,
        all_names: vec![n("Fewer")],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    };
    assert_refused(
        &env.extend_inductives_structural(std::iter::once(fewer.clone())),
        "Fewer",
        "does not split",
    );
    fewer.num_indices = 1;
    assert!(env
        .extend_inductives_structural(std::iter::once(fewer))
        .is_empty());
}
