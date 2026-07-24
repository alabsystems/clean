// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! B1 structural tests for the rebuilt nested-inductive elimination
//! (`designs/2026-07-02-parameterized-nested-inductives.md` §1–§3, §6 B1).
//!
//! These call `eliminate_nested_inductives` DIRECTLY, so the parameterized
//! (`num_params > 0`) construction is exercised even while the
//! reject-all-parameterized guard is still up at the `add_inductive` entry
//! (guard narrowing is brick B5). Every expected term is written out in
//! exact de Bruijn form — the worked examples from design §1.3.

use std::collections::HashSet;

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveError, InductiveType};

/// `Type u` as an expression.
fn sort_param(u: &Name) -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::param(u.clone())))
}

/// Register a `List`-shaped container: `List.{v} : Type v → Type v` with
/// `nil : Π (A : Type v). List A` and
/// `cons : Π (A : Type v) (head : A) (tail : List A). List A`.
fn add_list(env: &mut Environment) {
    let v = Name::from_string("v");
    let list = Name::from_string("List");
    let list_at = |lvl: Level| Expr::const_(list.clone(), vec![lvl]);

    let list_type = Expr::pi(BinderInfo::Default, sort_param(&v), sort_param(&v));
    // nil : Π (A : Type v). List A
    let nil_type = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::app(list_at(Level::param(v.clone())), Expr::bvar(0)),
    );
    // cons : Π (A : Type v) (head : A) (tail : List A). List A
    let cons_type = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(list_at(Level::param(v.clone())), Expr::bvar(1)),
                Expr::app(list_at(Level::param(v.clone())), Expr::bvar(2)),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![v],
        num_params: 1,
        types: vec![InductiveType {
            name: list,
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    })
    .expect("List container should register");
}

/// The F1 fixture: `T.{u} (α : Type u) | mk : List (T α) → T α`,
/// `level_params = [u]`, `num_params = 1`.
fn f1_decl(u: &Name) -> InductiveDecl {
    let t = Name::from_string("T");
    let t_at = Expr::const_(t.clone(), vec![Level::param(u.clone())]);
    let list_at = Expr::const_(Name::from_string("List"), vec![Level::param(u.clone())]);

    // T : Π (α : Type u). Type u
    let t_type = Expr::pi(BinderInfo::Default, sort_param(u), sort_param(u));
    // mk : Π (α : Type u) (_ : List (T α)). T α
    //    = Π (α). Π (_ : List (T #0)). T #1
    let mk_type = Expr::pi(
        BinderInfo::Default,
        sort_param(u),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(list_at, Expr::app(t_at.clone(), Expr::bvar(0))),
            Expr::app(t_at, Expr::bvar(1)),
        ),
    );

    InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: t.clone(),
            type_: t_type,
            constructors: vec![Constructor {
                name: Name::from_string("T.mk"),
                type_: mk_type,
            }],
        }],
    }
}

fn nested_set(names: &[&str]) -> HashSet<Name> {
    names.iter().map(|n| Name::from_string(n)).collect()
}

/// F1 (design §1.3 worked form): the parameterized aux mirror gets the outer
/// telescope, and every constructor comes out in the exact de Bruijn shape
/// `_nested.List_1.cons : Π α (head : T #0) (tail : _nested.List_1 #1).
/// _nested.List_1 #2`.
#[test]
fn test_param_nested_f1_transformed_shape() {
    let mut env = Environment::new();
    add_list(&mut env);
    let u = Name::from_string("u");
    let decl = f1_decl(&u);

    let (transformed, occurrences) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["T"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");

    assert_eq!(transformed.num_params, 1, "shared telescope preserved");
    assert_eq!(
        transformed.types.len(),
        2,
        "T plus exactly one aux mirror expected"
    );
    assert_eq!(occurrences.len(), 1, "one aux entry expected");

    let aux = Name::from_string("_nested.List_1");
    let t_at = Expr::const_(Name::from_string("T"), vec![Level::param(u.clone())]);
    let aux_at = Expr::const_(aux.clone(), vec![Level::param(u.clone())]);

    // T.mk rewritten: Π (α : Type u) (_ : _nested.List_1 #0). T #1
    let expected_mk = Expr::pi(
        BinderInfo::Default,
        sort_param(&u),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(aux_at.clone(), Expr::bvar(0)),
            Expr::app(t_at.clone(), Expr::bvar(1)),
        ),
    );
    assert_eq!(
        transformed.types[0].constructors[0].type_, expected_mk,
        "T.mk must reference the aux mirror at the shared param"
    );

    // Aux type former: Π (α : Type u). Type u  (container level param killed).
    let aux_ty = &transformed.types[1];
    assert_eq!(aux_ty.name, aux);
    let expected_aux_former = Expr::pi(BinderInfo::Default, sort_param(&u), sort_param(&u));
    assert_eq!(
        aux_ty.type_, expected_aux_former,
        "aux former must carry the outer telescope with the container's \
         level params eliminated"
    );

    // nil : Π (α : Type u). _nested.List_1 #0
    let expected_nil = Expr::pi(
        BinderInfo::Default,
        sort_param(&u),
        Expr::app(aux_at.clone(), Expr::bvar(0)),
    );
    assert_eq!(
        aux_ty.constructors[0].name,
        Name::from_string("_nested.List_1.nil")
    );
    assert_eq!(aux_ty.constructors[0].type_, expected_nil);

    // cons : Π (α : Type u) (head : T #0) (tail : _nested.List_1 #1).
    //        _nested.List_1 #2
    let expected_cons = Expr::pi(
        BinderInfo::Default,
        sort_param(&u),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(t_at, Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(aux_at.clone(), Expr::bvar(1)),
                Expr::app(aux_at, Expr::bvar(2)),
            ),
        ),
    );
    assert_eq!(
        aux_ty.constructors[1].name,
        Name::from_string("_nested.List_1.cons")
    );
    assert_eq!(
        aux_ty.constructors[1].type_, expected_cons,
        "cons must come out in the design's exact de Bruijn form"
    );
}

/// Dedup is depth-canonical: the same instantiation at two different Pi
/// depths collapses to ONE aux type (the current-impl defect the design
/// fixes — the old key was depth-sensitive).
#[test]
fn test_param_nested_dedup_across_depths() {
    let mut env = Environment::new();
    add_list(&mut env);
    let u = Name::from_string("u");
    let t_at = Expr::const_(Name::from_string("T"), vec![Level::param(u.clone())]);
    let list_at = Expr::const_(Name::from_string("List"), vec![Level::param(u.clone())]);

    // mk : Π (α) (a : List (T α)) (b : List (T α)). T α — the second
    // occurrence sits one binder deeper; canonically identical.
    let mk_type = Expr::pi(
        BinderInfo::Default,
        sort_param(&u),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(list_at.clone(), Expr::app(t_at.clone(), Expr::bvar(0))),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(list_at, Expr::app(t_at.clone(), Expr::bvar(1))),
                Expr::app(t_at, Expr::bvar(2)),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("T"),
            type_: Expr::pi(BinderInfo::Default, sort_param(&u), sort_param(&u)),
            constructors: vec![Constructor {
                name: Name::from_string("T.mk"),
                type_: mk_type,
            }],
        }],
    };

    let (transformed, occurrences) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["T"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");

    assert_eq!(
        occurrences.len(),
        1,
        "same instantiation at two depths must dedup to one aux type"
    );
    assert_eq!(transformed.types.len(), 2);

    // Both fields reference the SAME aux, at the respective depths.
    let aux = Name::from_string("_nested.List_1");
    let aux_at = Expr::const_(aux, vec![Level::param(u.clone())]);
    let mk = &transformed.types[0].constructors[0].type_;
    let ExprKind::Pi(_, _, body_a) = &mk.kind else {
        panic!("mk must start with the param binder");
    };
    let ExprKind::Pi(_, field_a, body_b) = &body_a.kind else {
        panic!("mk must have field a");
    };
    let ExprKind::Pi(_, field_b, _) = &body_b.kind else {
        panic!("mk must have field b");
    };
    assert_eq!(
        **field_a,
        Expr::app(aux_at.clone(), Expr::bvar(0)),
        "field a references the aux at depth 1"
    );
    assert_eq!(
        **field_b,
        Expr::app(aux_at, Expr::bvar(1)),
        "field b references the SAME aux at depth 2"
    );
}

/// Dedup is level-inclusive: the same instantiation at two DIFFERENT concrete
/// universe levels yields two distinct aux types (the old key was
/// level-blind and collided them).
#[test]
fn test_nested_level_distinct_instantiations() {
    let mut env = Environment::new();
    add_list(&mut env);
    let t = Name::from_string("T");
    let t_ref = Expr::const_(t.clone(), vec![]);
    let list_at = |lvl: Level| Expr::const_(Name::from_string("List"), vec![lvl]);

    // T : Type 2 (so `List.{1} T` and `List.{2} T`... use levels 1 and 2 as
    // the occurrence levels; elimination is pre-typecheck, so only the level
    // LISTS matter for the key).
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(list_at(Level::succ(Level::zero())), t_ref.clone()),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                list_at(Level::succ(Level::succ(Level::zero()))),
                t_ref.clone(),
            ),
            t_ref,
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: t,
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
            constructors: vec![Constructor {
                name: Name::from_string("T.mk"),
                type_: mk_type,
            }],
        }],
    };

    let (transformed, occurrences) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["T"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");

    assert_eq!(
        occurrences.len(),
        2,
        "level-distinct instantiations must yield distinct aux types"
    );
    assert_eq!(transformed.types.len(), 3);
    assert_eq!(
        transformed.types[1].name,
        Name::from_string("_nested.List_1")
    );
    assert_eq!(
        transformed.types[2].name,
        Name::from_string("_nested.List_2")
    );
}

/// Multi-level nesting resolves through the worklist: `Trie α` nesting
/// `Array (Prod Nat (Trie α))` spawns `_nested.Array_1`, whose mirror field
/// `List (Prod Nat (Trie α))` spawns `_nested.List_2`, whose `cons` head
/// spawns `_nested.Prod_3` — creation order pinned (drives `rec_N`
/// numbering in restore).
#[test]
fn test_nested_deep_chain_creation_order() {
    let mut env = Environment::new();
    add_list(&mut env);

    // Nat : Type
    let nat = Name::from_string("Nat");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.zero"),
                type_: Expr::const_(nat.clone(), vec![]),
            }],
        }],
    })
    .expect("Nat should register");

    // Prod.{v} (A B : Type v) | mk : A → B → Prod A B
    let v = Name::from_string("v");
    let prod = Name::from_string("Prod");
    let prod_at = |lvl: Level| Expr::const_(prod.clone(), vec![lvl]);
    let prod_type = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(BinderInfo::Default, sort_param(&v), sort_param(&v)),
    );
    // mk : Π (A B : Type v) (a : A) (b : B). Prod A B
    //    = Π A B (a : #1) (b : #1). Prod #3 #2
    let prod_mk = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(
            BinderInfo::Default,
            sort_param(&v),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(prod_at(Level::param(v.clone())), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![v.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: prod.clone(),
            type_: prod_type,
            constructors: vec![Constructor {
                name: Name::from_string("Prod.mk"),
                type_: prod_mk,
            }],
        }],
    })
    .expect("Prod should register");

    // Array.{v} (A : Type v) | mk : List A → Array A
    let array = Name::from_string("Array");
    let array_type = Expr::pi(BinderInfo::Default, sort_param(&v), sort_param(&v));
    let array_mk = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::param(v.clone())]),
                Expr::bvar(0),
            ),
            Expr::app(
                Expr::const_(array.clone(), vec![Level::param(v.clone())]),
                Expr::bvar(1),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![v],
        num_params: 1,
        types: vec![InductiveType {
            name: array.clone(),
            type_: array_type,
            constructors: vec![Constructor {
                name: Name::from_string("Array.mk"),
                type_: array_mk,
            }],
        }],
    })
    .expect("Array should register");

    // Trie.{u} (α : Type u) | node : Array (Prod Nat (Trie α)) → Trie α
    let u = Name::from_string("u");
    let trie = Name::from_string("Trie");
    let ul = Level::param(u.clone());
    let trie_at = Expr::const_(trie.clone(), vec![ul.clone()]);
    let payload = Expr::app(
        Expr::app(prod_at(ul.clone()), Expr::const_(nat, vec![])),
        Expr::app(trie_at.clone(), Expr::bvar(0)),
    );
    let node_type = Expr::pi(
        BinderInfo::Default,
        sort_param(&u),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(array, vec![ul.clone()]), payload),
            Expr::app(trie_at, Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: trie,
            type_: Expr::pi(
                BinderInfo::Default,
                sort_param(&Name::from_string("u")),
                sort_param(&Name::from_string("u")),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("Trie.node"),
                type_: node_type,
            }],
        }],
    };

    let (transformed, occurrences) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["Trie"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");

    let names: Vec<String> = occurrences.iter().map(|o| o.aux_name.to_string()).collect();
    assert_eq!(
        names,
        vec!["_nested.Array_1", "_nested.List_2", "_nested.Prod_3"],
        "worklist must resolve the whole chain in creation order"
    );
    assert_eq!(transformed.types.len(), 4, "Trie + three aux mirrors");
}

/// Rule 5 (Lean parity): a container parameter instantiated with an
/// expression referencing a constructor-local binder is a typed, fail-closed
/// error — previously the un-diagnosed birth of the de Bruijn corruption.
#[test]
fn test_nested_params_contain_locals_rejected() {
    let mut env = Environment::new();
    add_list(&mut env);
    let t = Name::from_string("T");
    let t_ref = Expr::const_(t.clone(), vec![]);

    // mk : Π (x : T) (_ : List (List T with x smuggled in)). T — concretely:
    // the inner occurrence's param arg `Prod`-free but mentions BVar(0) (= x)
    // alongside T. Use `List (App T #0)`-shaped arg: mentions T (nested
    // trigger) AND the local x (must be rejected).
    let bad_arg = Expr::app(t_ref.clone(), Expr::bvar(0));
    let mk_type = Expr::pi(
        BinderInfo::Default,
        t_ref.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]),
                bad_arg,
            ),
            t_ref,
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: t,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("T.mk"),
                type_: mk_type,
            }],
        }],
    };

    let err = env
        .eliminate_nested_inductives(&decl, &nested_set(&["T"]))
        .expect_err("local-capturing container params must fail closed");
    assert!(
        matches!(err, InductiveError::NestedParamsContainLocals),
        "expected NestedParamsContainLocals, got: {err:?}"
    );
}

/// Whole-mutual-block copy: nesting ONE member of a mutual container copies
/// EVERY sibling, with memo entries for all (design §1.3, Lean :996-1026).
#[test]
fn test_nested_mutual_container_copies_block() {
    let mut env = Environment::new();

    // Mutual container: M1.{v} (A : Type v) | m1 : M2 A → M1 A
    //                   M2.{v} (A : Type v) | m2 : M1 A → M2 A
    let v = Name::from_string("v");
    let m1 = Name::from_string("M1");
    let m2 = Name::from_string("M2");
    let vl = Level::param(v.clone());
    let former = Expr::pi(BinderInfo::Default, sort_param(&v), sort_param(&v));
    let m1_ctor = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(m2.clone(), vec![vl.clone()]), Expr::bvar(0)),
            Expr::app(Expr::const_(m1.clone(), vec![vl.clone()]), Expr::bvar(1)),
        ),
    );
    let m2_ctor = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(m1.clone(), vec![vl.clone()]), Expr::bvar(0)),
            Expr::app(Expr::const_(m2.clone(), vec![vl.clone()]), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![v],
        num_params: 1,
        types: vec![
            InductiveType {
                name: m1.clone(),
                type_: former.clone(),
                constructors: vec![Constructor {
                    name: Name::from_string("M1.m1"),
                    type_: m1_ctor,
                }],
            },
            InductiveType {
                name: m2,
                type_: former,
                constructors: vec![Constructor {
                    name: Name::from_string("M2.m2"),
                    type_: m2_ctor,
                }],
            },
        ],
    })
    .expect("mutual container should register");

    // T | mk : M1 T → T   (num_params = 0 so the full add path also works,
    // but call elimination directly for shape assertions)
    let t = Name::from_string("T");
    let t_ref = Expr::const_(t.clone(), vec![]);
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::const_(m1, vec![Level::succ(Level::zero())]),
            t_ref.clone(),
        ),
        t_ref,
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: t,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("T.mk"),
                type_: mk_type,
            }],
        }],
    };

    let (transformed, occurrences) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["T"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");

    let names: Vec<String> = occurrences.iter().map(|o| o.aux_name.to_string()).collect();
    assert_eq!(
        names,
        vec!["_nested.M1_1", "_nested.M2_2"],
        "nesting one member must copy the whole mutual block"
    );
    assert_eq!(transformed.types.len(), 3, "T + both siblings");

    // The M1 mirror's field references the M2 mirror (memo pre-insertion for
    // siblings), not the raw container.
    let aux_m1 = &transformed.types[1];
    let ExprKind::Pi(_, field, _) = &aux_m1.constructors[0].type_.kind else {
        panic!("aux M1 ctor must have its field binder");
    };
    assert_eq!(
        **field,
        Expr::const_(Name::from_string("_nested.M2_2"), Vec::<Level>::new()),
        "sibling self-reference must memo-hit the sibling's mirror"
    );
}

// =====================================================================
// Dependent-parameter container tests (design
// 2026-07-05-nested-dependent-param-container.md).
//
// A dependent-parameter container (`β : α → Type v`, field `β k`) nested
// through a const map `fun _ => V` produces the redex `(fun _ => V) k` in the
// aux mirror's field. The fix beta-normalizes it to `V` at the elimination
// substitution point so Clean's syntactic strict-positivity gate sees a
// `Const`-headed occurrence — recovering Lean's verdict (whnf-per-site) while
// KEEPING full rejection power on a genuinely bad occurrence (§7.3).
// =====================================================================

use crate::inductive::validate_inductive_strict;

/// Register a dependent-parameter container mirroring
/// `Std.DTreeMap.Internal.Impl` / `Lean.RBNode`:
/// `DMap.{v} (α : Sort v) (β : α → Sort v) : Sort v` with the dependent field
/// `β k` (the shape that, once β is a const map `fun _ => V`, produces the
/// redex `(fun _ => V) k`), plus a recursive field and a leaf.
fn add_dmap(env: &mut Environment) {
    let v = Name::from_string("v");
    let dmap = Name::from_string("DMap");
    let dmap_v = Expr::const_(dmap.clone(), vec![Level::param(v.clone())]);
    // β : α → Sort v  (α is the immediately enclosing binder = BVar(0)).
    let beta_ty = Expr::pi(BinderInfo::Default, Expr::bvar(0), sort_param(&v));
    let dmap_app = |a: Expr, b: Expr| Expr::app(Expr::app(dmap_v.clone(), a), b);

    // DMap : Π (α : Sort v) (β : α → Sort v). Sort v
    let former = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(BinderInfo::Default, beta_ty.clone(), sort_param(&v)),
    );
    // node : Π (α)(β)(k : α)(val : β k)(rest : DMap α β). DMap α β
    let node = Expr::pi(
        BinderInfo::Default,
        sort_param(&v), // α [0]
        Expr::pi(
            BinderInfo::Default,
            beta_ty.clone(), // β : α → Sort v [1]
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // k : α [2]
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(1), Expr::bvar(0)), // val : β k [3]
                    Expr::pi(
                        BinderInfo::Default,
                        dmap_app(Expr::bvar(3), Expr::bvar(2)), // rest : DMap α β [4]
                        dmap_app(Expr::bvar(4), Expr::bvar(3)), // DMap α β
                    ),
                ),
            ),
        ),
    );
    // leaf : Π (α)(β). DMap α β
    let leaf = Expr::pi(
        BinderInfo::Default,
        sort_param(&v),
        Expr::pi(
            BinderInfo::Default,
            beta_ty,
            dmap_app(Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![v],
        num_params: 2,
        types: vec![InductiveType {
            name: dmap,
            type_: former,
            constructors: vec![
                Constructor {
                    name: Name::from_string("DMap.node"),
                    type_: node,
                },
                Constructor {
                    name: Name::from_string("DMap.leaf"),
                    type_: leaf,
                },
            ],
        }],
    })
    .expect("dependent-parameter container DMap should register");
}

/// The ordered Pi-binder domains of `e`.
fn pi_domains(e: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut cur = e;
    while let ExprKind::Pi(_, dom, body) = &cur.kind {
        out.push((**dom).clone());
        cur = body;
    }
    out
}

/// Every constructor type in `decl` is beta-normal (proof the redex was
/// contracted at its source, not left for a head-reading pass to trip over).
fn assert_all_ctors_beta_normal(decl: &InductiveDecl) {
    for ty in &decl.types {
        for c in &ty.constructors {
            assert_eq!(
                c.type_,
                c.type_.beta_normalize(),
                "aux ctor {} still carries an un-reduced beta-redex",
                c.name
            );
        }
    }
}

/// POSITIVE CONTROL (the Json / PrefixTreeNode shape): a block nested through
/// a dependent container with a well-behaved const map `fun _ => J` is
/// ACCEPTED, and the mirror's `β k` field is the bare block const `J` — NOT
/// the redex `(fun _ => J) k` (which the pre-fix gate rejected as a
/// non-`Const` head).
#[test]
fn test_dep_container_positive_const_map_accepts() {
    let mut env = Environment::new();
    add_dmap(&mut env);

    let j = Name::from_string("J");
    let j_ref = Expr::const_(j.clone(), Vec::<Level>::new());
    let dmap_at = Expr::const_(Name::from_string("DMap"), vec![Level::zero()]);
    let str_ty = Expr::const_str("String");
    let const_map = Expr::lam(BinderInfo::Default, str_ty.clone(), j_ref.clone());
    // J.obj : DMap String (fun _ => J) → J
    let obj = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::app(dmap_at, str_ty), const_map),
        j_ref.clone(),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: j.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("J.obj"),
                type_: obj,
            }],
        }],
    };

    let (transformed, _) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["J"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");

    validate_inductive_strict(&transformed)
        .expect("dependent-param container with a positive const map must be accepted");
    assert_all_ctors_beta_normal(&transformed);

    let aux = transformed
        .types
        .iter()
        .find(|t| t.name.to_string() == "_nested.DMap_1")
        .expect("DMap aux mirror expected");
    let node = aux
        .constructors
        .iter()
        .find(|c| c.name.to_string().ends_with(".node"))
        .expect("aux node ctor expected");
    let doms = pi_domains(&node.type_);
    assert!(
        doms.contains(&j_ref),
        "the reduced `β k` field must be the bare block const `J`; domains = {doms:?}"
    );
}

/// ADVERSARIAL — NEGATIVE through the const map: the map value `fun _ =>
/// (Bad → Empty)` puts `Bad` left of an arrow. Beta EXPOSES the `Pi`
/// `Bad → Empty`; the strict gate must still reject `NonPositive`
/// (cross-checked: `lean` rejects the same declaration).
#[test]
fn test_dep_container_negative_const_map_rejected() {
    let mut env = Environment::new();
    add_dmap(&mut env);

    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), Vec::<Level>::new());
    let dmap_at = Expr::const_(Name::from_string("DMap"), vec![Level::zero()]);
    let str_ty = Expr::const_str("String");
    let neg = Expr::pi(
        BinderInfo::Default,
        bad_ref.clone(),
        Expr::const_str("Empty"),
    );
    let const_map = Expr::lam(BinderInfo::Default, str_ty.clone(), neg);
    let mk = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::app(dmap_at, str_ty), const_map),
        bad_ref,
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                type_: mk,
            }],
        }],
    };

    let (transformed, _) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["Bad"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");
    assert_all_ctors_beta_normal(&transformed);
    let err = validate_inductive_strict(&transformed)
        .expect_err("a const map hiding a NEGATIVE occurrence must still be rejected");
    assert!(
        matches!(err, InductiveError::NonPositive(..)),
        "beta must EXPOSE the negative occurrence (Bad → Empty) → NonPositive, got {err:?}"
    );
}

/// ADVERSARIAL — WRONG ARITY through the const map: the map value
/// `fun _ => Bad Extra` over-applies the `p = 0`/`0`-index block. Beta exposes
/// `Bad Extra`; the strict gate's arity check must reject
/// `InvalidInductiveOccurrence`.
#[test]
fn test_dep_container_wrong_arity_const_map_rejected() {
    let mut env = Environment::new();
    add_dmap(&mut env);

    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), Vec::<Level>::new());
    let dmap_at = Expr::const_(Name::from_string("DMap"), vec![Level::zero()]);
    let str_ty = Expr::const_str("String");
    let over = Expr::app(bad_ref.clone(), Expr::const_str("Extra"));
    let const_map = Expr::lam(BinderInfo::Default, str_ty.clone(), over);
    let mk = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::app(dmap_at, str_ty), const_map),
        bad_ref,
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                type_: mk,
            }],
        }],
    };

    let (transformed, _) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["Bad"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");
    assert_all_ctors_beta_normal(&transformed);
    let err = validate_inductive_strict(&transformed)
        .expect_err("a const map hiding a WRONG-ARITY occurrence must still be rejected");
    assert!(
        matches!(err, InductiveError::InvalidInductiveOccurrence { .. }),
        "beta exposes `Bad Extra` (arity 1 != 0) → InvalidInductiveOccurrence, got {err:?}"
    );
}

/// ADVERSARIAL — NON-UNIFORM parameter spine through the const map: the `p = 1`
/// block's map value `fun _ => Bad (Sort 0)` supplies `Sort 0` where the
/// enclosing telescope param `γ` is required. Beta exposes `Bad (Sort 0)`; the
/// strict gate's param-spine check must reject `ConstructorParamMismatch`.
#[test]
fn test_dep_container_non_uniform_const_map_rejected() {
    let mut env = Environment::new();
    add_dmap(&mut env);

    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), Vec::<Level>::new());
    let dmap_at = Expr::const_(Name::from_string("DMap"), vec![Level::zero()]);
    let str_ty = Expr::const_str("String");
    let non_uniform = Expr::app(
        bad_ref.clone(),
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );
    let const_map = Expr::lam(BinderInfo::Default, str_ty.clone(), non_uniform);
    // Bad (γ : Type) | mk : DMap String (fun _ => Bad (Sort 0)) → Bad γ
    let mk = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // γ : Type [0]
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::app(dmap_at, str_ty), const_map), // field [1]
            Expr::app(bad_ref.clone(), Expr::bvar(1)),        // Bad γ
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: bad,
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                type_: mk,
            }],
        }],
    };

    let (transformed, _) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["Bad"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");
    assert_all_ctors_beta_normal(&transformed);
    let err = validate_inductive_strict(&transformed)
        .expect_err("a const map hiding a NON-UNIFORM occurrence must still be rejected");
    assert!(
        matches!(err, InductiveError::ConstructorParamMismatch { .. }),
        "beta exposes `Bad (Sort 0)` (non-uniform spine) → ConstructorParamMismatch, got {err:?}"
    );
}

/// REGRESSION CONTROL (A5): a non-dependent-container family (`List`-nesting,
/// no field applies a parameter to an argument) carries no beta-redex, so
/// `beta_normalize` is the identity — the transform is byte-identical to
/// pre-fix. (The exact-shape lock is `test_param_nested_f1_transformed_shape`;
/// here we assert beta is a strict no-op on every aux term.)
#[test]
fn test_non_dependent_container_beta_is_identity() {
    let mut env = Environment::new();
    add_list(&mut env);
    let u = Name::from_string("u");
    let decl = f1_decl(&u);
    let (transformed, _) = env
        .eliminate_nested_inductives(&decl, &nested_set(&["T"]))
        .expect("elimination should succeed")
        .expect("nesting should be detected");
    for ty in &transformed.types {
        assert_eq!(
            ty.type_,
            ty.type_.beta_normalize(),
            "non-dependent former must already be beta-normal"
        );
    }
    assert_all_ctors_beta_normal(&transformed);
}
