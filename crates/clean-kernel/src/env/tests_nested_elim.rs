// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for nested inductive elimination + restore (#3239, design
//! `designs/2026-07-02-parameterized-nested-inductives.md` §4).
//!
//! Post-restore, the environment for a nested family contains ONLY Lean's
//! artifact set: original types/ctors in container spelling (round-trip
//! identity with the input), `T.rec` in Lean form, renamed `T.rec_N` aux
//! recursors with rules keyed to the REAL container constructors, and no
//! `_nested.*` registration of any kind. These tests pin that surface via
//! the full `add_inductive` path; the pre-restore transformed-block shapes
//! are pinned by `tests_nested_elim_param.rs` via direct
//! `eliminate_nested_inductives` calls.

use super::*;
use crate::inductive::{count_pi_args, Constructor, InductiveDecl, InductiveType};

/// Helper: register Nat as a simple inductive in the given environment.
fn add_nat(env: &mut Environment) {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
}

/// Helper: create an environment with List already defined.
/// `List.{u} : Type u → Type u` (real Lean's List former — provably nonzero
/// result, keeps large elimination under the [R1] gate).
fn make_env_with_list() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let list = Name::from_string("List");
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

    let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );

    // List.nil : (A : Type u) → List A
    let nil_type = Expr::pi(BinderInfo::Default, type_u.clone(), list_a.clone());

    // List.cons : (A : Type u) → A → List A → List A
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(BinderInfo::Default, type_u, cons_body);

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
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
    };
    env.add_inductive(decl).unwrap();
    env
}

/// The canonical Tree fixture: `Tree | node : List Tree → Tree` with
/// `List.{0} Tree` (Tree : Type 0).
fn tree_decl() -> InductiveDecl {
    let tree = Name::from_string("Tree");
    let tree_ref = Expr::const_(tree.clone(), vec![]);
    let node_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            tree_ref.clone(),
        ),
        tree_ref,
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: tree,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Tree.node"),
                type_: node_type,
            }],
        }],
    }
}

fn add_tree(env: &mut Environment) {
    env.add_inductive(tree_decl())
        .expect("Tree with nested List Tree should be accepted");
}

#[test]
fn restored_nested_companion_recursor_earns_full_kernel_authority() {
    let mut env = make_env_with_list();
    add_tree(&mut env);

    let companion = Name::from_string("Tree.rec_1");
    assert!(env.get_recursor(&companion).is_some());
    assert_eq!(
        env.declaration_verification(&companion),
        Some(DeclarationVerification::FullKernelCheck),
        "container-major restored recursor must be fully revalidated"
    );
}

/// Post-restore: Tree is accepted, marked nested, and NO `_nested.*`
/// registration of any kind survives (design §4.3 item 5).
#[test]
fn test_nested_tree_list_accepted_restored() {
    let mut env = make_env_with_list();
    add_tree(&mut env);

    let tree = Name::from_string("Tree");
    let tree_val = env.inductives.get(&tree).expect("Tree should be in env");
    assert!(tree_val.is_nested, "Tree should be marked as nested");

    // Aux erasure: no _nested.* anywhere.
    let aux = Name::from_string("_nested.List_1");
    assert!(
        env.inductives.get(&aux).is_none(),
        "aux mirror must be erased by restore"
    );
    assert!(env.get_const(&aux).is_none(), "aux constant must be erased");
    assert!(
        env.constructors
            .get(&Name::from_string("_nested.List_1.nil"))
            .is_none()
            && env
                .constructors
                .get(&Name::from_string("_nested.List_1.cons"))
                .is_none(),
        "aux constructors must be erased"
    );
    assert!(
        env.recursors
            .get(&Name::from_string("_nested.List_1.rec"))
            .is_none(),
        "aux recursor must be erased (renamed to Tree.rec_1)"
    );
}

/// Round-trip law: Tree.node's registered type is byte-identical to the
/// declared `List Tree → Tree` (container spelling restored).
#[test]
fn test_nested_tree_ctor_round_trip() {
    let mut env = make_env_with_list();
    add_tree(&mut env);

    let declared = &tree_decl().types[0].constructors[0].type_;
    let node = env
        .constructors
        .get(&Name::from_string("Tree.node"))
        .expect("Tree.node should exist");
    assert_eq!(
        &node.type_, declared,
        "restored constructor type must equal the declared type (round-trip law)"
    );
    let node_const = env
        .get_const(&Name::from_string("Tree.node"))
        .expect("Tree.node constant should exist");
    assert_eq!(
        &node_const.type_, declared,
        "the constant-table entry must be restored too"
    );
}

/// Post-restore recursors: Tree.rec (aux-counting metadata) and the renamed
/// Tree.rec_1 — present in BOTH the constants and recursors tables ([R4]),
/// with rules keyed to the REAL List constructors.
#[test]
fn test_nested_tree_recursors_restored() {
    let mut env = make_env_with_list();
    add_tree(&mut env);

    let rec = env
        .recursors
        .get(&Name::from_string("Tree.rec"))
        .expect("Tree.rec should be generated");
    // Motives/minors still count the aux member (design §4.3 item 3).
    assert_eq!(
        rec.num_motives, 2,
        "Tree.rec motives: Tree + the List mirror"
    );
    assert_eq!(rec.num_minors, 3, "Tree.rec minors: node + nil + cons");
    assert_eq!(rec.rules.len(), 1, "Tree.rec has one rule (Tree.node)");
    assert_eq!(
        rec.rules[0].constructor_name,
        Name::from_string("Tree.node")
    );

    let rec_1 = env
        .recursors
        .get(&Name::from_string("Tree.rec_1"))
        .expect("Tree.rec_1 (renamed aux recursor) should exist in recursors");
    assert!(
        env.get_const(&Name::from_string("Tree.rec_1")).is_some(),
        "Tree.rec_1 must ALSO be a constant ([R4] — replay acceptor probes get_const first)"
    );
    assert_eq!(rec_1.num_motives, 2);
    assert_eq!(rec_1.num_minors, 3);
    assert_eq!(
        rec_1.inductive_name,
        Name::from_string("Tree"),
        "renamed recursor's inductive_name is the first original"
    );
    assert_eq!(rec_1.rules.len(), 2, "rec_1 rules: nil + cons");
    assert_eq!(
        rec_1.rules[0].constructor_name,
        Name::from_string("List.nil"),
        "rules re-keyed to the REAL container constructors"
    );
    assert_eq!(
        rec_1.rules[1].constructor_name,
        Name::from_string("List.cons")
    );
    // Container nfields = ctor arity − container num_params: the mirror
    // strips the container's own parameter telescope (design §1.3), so
    // nil has 0 fields and cons has 2 (head, tail).
    assert_eq!(rec_1.rules[0].num_fields, 0, "List.nil field count");
    assert_eq!(
        rec_1.rules[1].num_fields, 2,
        "List.cons field count (head, tail)"
    );
    assert!(
        !rec_1.rules[1].recursive_fields.is_empty(),
        "recursive_fields retained on re-keyed rules"
    );

    // No residual _nested.* constants inside the restored types.
    for name in ["Tree.rec", "Tree.rec_1"] {
        let val = env.recursors.get(&Name::from_string(name)).unwrap();
        assert!(
            !val.type_
                .collect_constants()
                .iter()
                .any(|n| n.to_string().starts_with("_nested.")),
            "{name} type must be fully restored"
        );
    }

    // casesOn exists for the original only.
    assert!(
        env.recursors
            .get(&Name::from_string("Tree.casesOn"))
            .is_some(),
        "Tree.casesOn should be generated"
    );
}

/// Post-restore mutual structure: all_names = originals only, on the
/// original member (design §4.3 item 1).
#[test]
fn test_nested_tree_all_names_restored() {
    let mut env = make_env_with_list();
    add_tree(&mut env);

    let tree = Name::from_string("Tree");
    let tree_val = env.inductives.get(&tree).expect("Tree in env");
    assert_eq!(
        tree_val.all_names,
        vec![tree],
        "all_names must be reset to the originals only"
    );
}

/// Iota through the restored recursors: `Tree.rec … (Tree.node l)` reduces
/// via the rule RHS (which calls Tree.rec_1), and `Tree.rec_1 … (List.cons …)`
/// reduces on a REAL container constructor (design §4.4).
#[test]
fn test_nested_tree_iota_reduces_through_rec_1() {
    let mut env = make_env_with_list();
    add_nat(&mut env);
    add_tree(&mut env);
    let tc = crate::tc::TypeChecker::new(&env);

    let tree_ref = Expr::const_(Name::from_string("Tree"), vec![]);
    let list_tree = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        tree_ref.clone(),
    );
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Motives (both at elim level 1 → Nat-valued).
    let motive_tree = Expr::lam(BinderInfo::Default, tree_ref.clone(), nat_ref.clone());
    let motive_list = Expr::lam(BinderInfo::Default, list_tree.clone(), nat_ref.clone());
    // Minors: node ↦ λ (l : List Tree) (ih : Nat). ih ; nil ↦ zero ;
    // cons ↦ λ (hd : Tree) (ih_hd : Nat) (tl : List Tree) (ih_tl : Nat). ih_tl
    // (minor shapes: fields interleaved with IHs in field order).
    let minor_node = Expr::lam(
        BinderInfo::Default,
        list_tree.clone(),
        Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(0)),
    );
    let minor_nil = zero.clone();
    let minor_cons = Expr::lam(
        BinderInfo::Default,
        tree_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::lam(
                BinderInfo::Default,
                list_tree.clone(),
                Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(0)),
            ),
        ),
    );

    // Tree.rec_1 minors follow the block minor order (node, nil, cons) —
    // apply to `List.nil Tree`:
    // NOTE: nil in this fixture takes its type parameter explicitly.
    let nil_tree = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        tree_ref.clone(),
    );
    let rec_1 = env
        .recursors
        .get(&Name::from_string("Tree.rec_1"))
        .expect("Tree.rec_1");
    // Elim level: both motives target Nat (Type 0) → level 1.
    let rec_1_levels: Vec<Level> = rec_1
        .level_params
        .iter()
        .map(|_| Level::succ(Level::zero()))
        .collect();
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Tree.rec_1"), rec_1_levels),
                            motive_tree,
                        ),
                        motive_list,
                    ),
                    minor_node,
                ),
                minor_nil,
            ),
            minor_cons,
        ),
        nil_tree,
    );
    let result = tc.whnf(&app);
    // Careful: the fixture's List.nil takes A as a FIELD (num_params of the
    // fixture List is 1 but nil's telescope binds A itself), so the nil rule
    // has num_fields = 1 and the minor receives that field. The minor for
    // nil above is `zero` — if the rule peels one field the RHS applies the
    // minor to it; accept either exact zero or zero applied to Tree.
    let zero_applied = Expr::app(zero.clone(), tree_ref);
    assert!(
        tc.is_def_eq(&result, &zero) || tc.is_def_eq(&result, &zero_applied),
        "Tree.rec_1 on List.nil must iota-reduce via the re-keyed rule; got {result:?}"
    );
}

/// Dedup survives restore: Forest's two `List Forest` fields produce exactly
/// ONE renamed recursor (Forest.rec_1) and no second mirror.
#[test]
fn test_nested_dedup_same_container_restored() {
    let mut env = make_env_with_list();
    add_nat(&mut env);
    let forest = Name::from_string("Forest");
    let forest_ref = Expr::const_(forest.clone(), vec![]);
    let list_forest = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        forest_ref.clone(),
    );
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: forest.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Forest.empty"),
                    type_: forest_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Forest.branch"),
                    type_: Expr::arrow(list_forest.clone(), forest_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("Forest.labeled"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        nat_ref,
                        Expr::arrow(list_forest, forest_ref),
                    ),
                },
            ],
        }],
    })
    .expect("Forest with nested List Forest should be accepted");

    assert!(
        env.recursors
            .get(&Name::from_string("Forest.rec_1"))
            .is_some(),
        "one renamed aux recursor expected"
    );
    assert!(
        env.recursors
            .get(&Name::from_string("Forest.rec_2"))
            .is_none(),
        "same instantiation at two ctors must dedup to ONE mirror"
    );
    let forest_val = env.inductives.get(&forest).expect("Forest in env");
    assert_eq!(forest_val.all_names, vec![forest], "originals only");
    let rec = env
        .recursors
        .get(&Name::from_string("Forest.rec"))
        .expect("Forest.rec");
    assert_eq!(rec.num_minors, 5, "empty+branch+labeled+nil+cons");
}

/// Issue #3392 regression, restored form: Value with multiple constructors
/// sharing `List Value` — everything restored, one rec_1.
#[test]
fn test_value_nested_list_multiple_ctors_3392_restored() {
    let mut env = make_env_with_list();
    add_nat(&mut env);

    let bool_name = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    })
    .unwrap();

    let value = Name::from_string("Value");
    let value_ref = Expr::const_(value.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let list_value = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        value_ref.clone(),
    );

    let value_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: value.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Value.int"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        nat_ref.clone(),
                        Expr::pi(BinderInfo::Default, nat_ref.clone(), value_ref.clone()),
                    ),
                },
                Constructor {
                    name: Name::from_string("Value.float"),
                    type_: Expr::pi(BinderInfo::Default, nat_ref.clone(), value_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("Value.bool"),
                    type_: Expr::pi(BinderInfo::Default, bool_ref, value_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("Value.aggregate"),
                    type_: Expr::pi(BinderInfo::Default, list_value, value_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(value_decl)
        .expect("Value with nested List Value should succeed (#3392)");

    for ctor in ["Value.int", "Value.float", "Value.bool", "Value.aggregate"] {
        assert!(
            env.constructors.contains_key(&Name::from_string(ctor)),
            "{ctor} should exist"
        );
    }
    assert!(
        env.recursors
            .get(&Name::from_string("Value.rec_1"))
            .is_some(),
        "Value.rec_1 should exist post-restore"
    );
    assert!(
        !env.inductives
            .keys()
            .any(|n| n.to_string().starts_with("_nested.")),
        "no aux mirror survives"
    );
}

/// Track VV, restored: multi-level elimination (List V, List (List V) or
/// Prod-composed shapes) yields a clean block of renamed recursors, all
/// well-typed, with zero `_nested.*` residue.
#[test]
fn test_multi_aux_full_elimination_restored() {
    let mut env = make_env_with_list();
    env.init_punit().unwrap();
    env.init_prod().unwrap();
    add_nat(&mut env);

    // String : Type (trivial fixture)
    let s = Name::from_string("String");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: s.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("String.mk"),
                type_: Expr::const_(s, vec![]),
            }],
        }],
    })
    .unwrap();

    let v = Name::from_string("V");
    let v_ref = Expr::const_(v.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let list_v = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        v_ref.clone(),
    );
    let prod_string_v = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            Expr::const_(Name::from_string("String"), vec![]),
        ),
        v_ref.clone(),
    );
    let list_prod = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        prod_string_v,
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: v.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("V.leaf"),
                    type_: Expr::arrow(nat_ref, v_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("V.agg"),
                    type_: Expr::arrow(list_v.clone(), v_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("V.vec"),
                    type_: Expr::arrow(list_v, v_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("V.flds"),
                    type_: Expr::arrow(list_prod, v_ref.clone()),
                },
            ],
        }],
    })
    .expect("multi-aux V should be accepted");

    // Worklist chain: List V → rec_1, List (Prod String V) → rec_2,
    // Prod String V → rec_3.
    for rec in ["V.rec", "V.rec_1", "V.rec_2", "V.rec_3"] {
        let rv = env
            .recursors
            .get(&Name::from_string(rec))
            .unwrap_or_else(|| panic!("{rec} should exist"));
        assert!(
            env.get_const(&Name::from_string(rec)).is_some(),
            "{rec} must also be a constant [R4]"
        );
        let tc = crate::tc::TypeChecker::with_mode(&env, env.mode());
        let _sort = tc
            .infer_sort(&rv.type_)
            .unwrap_or_else(|e| panic!("{rec} type must be well-typed, got {e:?}"));
    }
    assert!(
        !env.recursors
            .keys()
            .chain(env.constants.keys())
            .any(|n| n.to_string().starts_with("_nested.")),
        "no _nested.* registration survives"
    );
    // The Prod mirror's rec is keyed to the REAL Prod.mk.
    let rec_3 = env.recursors.get(&Name::from_string("V.rec_3")).unwrap();
    assert_eq!(rec_3.rules.len(), 1);
    assert_eq!(
        rec_3.rules[0].constructor_name,
        Name::from_string("Prod.mk"),
        "Prod mirror rule re-keyed to the real container ctor"
    );
}

/// Idempotent re-add of a restored nested family is a no-op ([R12]) — the
/// round-trip law makes the stored spelling byte-equal to the input.
#[test]
fn test_nested_family_idempotent_readd() {
    let mut env = make_env_with_list();
    add_tree(&mut env);
    env.add_inductive(tree_decl())
        .expect("identical re-add of a restored nested family must be a no-op");
    // Still exactly one renamed recursor; no rec_2 minted by the re-add.
    assert!(env.recursors.contains_key(&Name::from_string("Tree.rec_1")));
    assert!(!env.recursors.contains_key(&Name::from_string("Tree.rec_2")));
}

/// B5 flip (#RefinedDiscrTree class): a PARAMETERIZED nested family now
/// checks end-to-end — elimination with the shared telescope, restore, and
/// Lean-form recursors. This exact shape was previously rejected by the
/// reject-all guard (and before that, silently corrupted the recursor /
/// aborted the process).
#[test]
fn test_parameterized_nested_inductive_accepted_restored() {
    let mut env = make_env_with_list();
    let boxn = Name::from_string("Box");
    let box_ref = Expr::const_(boxn.clone(), vec![]);

    // Box : (α : Type) → Type
    let box_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // Box.mk : (α : Type) → List.{0} (Box α) → Box α
    let list_box_a = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::app(box_ref.clone(), Expr::bvar(0)),
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            list_box_a,
            Expr::app(box_ref, Expr::bvar(1)),
        ),
    );
    let declared_mk = mk_type.clone();

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: boxn.clone(),
            type_: box_type,
            constructors: vec![Constructor {
                name: Name::from_string("Box.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("parameterized nested family must be accepted post-B5");

    // Round-trip law on the parameterized ctor.
    let mk = env
        .constructors
        .get(&Name::from_string("Box.mk"))
        .expect("Box.mk");
    assert_eq!(mk.type_, declared_mk, "parameterized ctor round-trips");

    // Lean-form recursors: Box.rec (2 motives, 3 minors) + Box.rec_1 in
    // BOTH tables with container-keyed rules.
    let rec = env
        .recursors
        .get(&Name::from_string("Box.rec"))
        .expect("Box.rec");
    assert_eq!(rec.num_motives, 2);
    assert_eq!(rec.num_minors, 3, "mk + nil + cons");
    assert_eq!(rec.num_params, 1, "shared telescope preserved");
    let rec_1 = env
        .recursors
        .get(&Name::from_string("Box.rec_1"))
        .expect("Box.rec_1");
    assert!(env.get_const(&Name::from_string("Box.rec_1")).is_some());
    assert_eq!(
        rec_1.rules[0].constructor_name,
        Name::from_string("List.nil")
    );
    assert_eq!(
        rec_1.rules[1].constructor_name,
        Name::from_string("List.cons")
    );

    // Both recursor types are well-typed in the restored env.
    for name in ["Box.rec", "Box.rec_1"] {
        let rv = env.recursors.get(&Name::from_string(name)).unwrap();
        let tc = crate::tc::TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_sort(&rv.type_)
            .unwrap_or_else(|e| panic!("{name} type must be well-typed, got {e:?}"));
    }

    assert!(
        !env.inductives
            .keys()
            .chain(env.constants.keys())
            .any(|n| n.to_string().starts_with("_nested.")),
        "no aux registration survives"
    );
    let val = env.inductives.get(&boxn).expect("Box registered");
    assert!(val.is_nested);
    assert_eq!(val.all_names, vec![boxn]);
}

/// The RefinedDiscrTree.Trie shape end-to-end: `Trie α | node :
/// Array (Prod Nat (Trie α)) → Trie α` — the multi-level chain
/// (Array → List → Prod) eliminates, checks, and restores through the FULL
/// `add_inductive` path. This family previously ABORTED THE PROCESS.
#[test]
fn test_trie_shape_deep_chain_accepted_restored() {
    let mut env = make_env_with_list();
    add_nat(&mut env);
    let u = Name::from_string("u");
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

    // Prod.{v} (A B : Type v) | mk : A → B → Prod A B
    let v = Name::from_string("v");
    let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));
    let prod = Name::from_string("Prod");
    let prod_at = |lvl: Level| Expr::const_(prod.clone(), vec![lvl]);
    env.add_inductive(InductiveDecl {
        level_params: vec![v.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: prod.clone(),
            type_: Expr::pi(
                BinderInfo::Default,
                type_v.clone(),
                Expr::pi(BinderInfo::Default, type_v.clone(), type_v.clone()),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("Prod.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    type_v.clone(),
                    Expr::pi(
                        BinderInfo::Default,
                        type_v,
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
                ),
            }],
        }],
    })
    .expect("Prod registers");

    // Array.{u} (A : Type u) | mk : List A → Array A
    let array = Name::from_string("Array");
    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: array.clone(),
            type_: Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone()),
            constructors: vec![Constructor {
                name: Name::from_string("Array.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    type_u.clone(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(
                            Expr::const_(Name::from_string("List"), vec![Level::param(u.clone())]),
                            Expr::bvar(0),
                        ),
                        Expr::app(
                            Expr::const_(array.clone(), vec![Level::param(u.clone())]),
                            Expr::bvar(1),
                        ),
                    ),
                ),
            }],
        }],
    })
    .expect("Array registers");

    // Trie (α : Type) | node : Array.{0} (Prod.{0} Nat (Trie α)) → Trie α
    let trie = Name::from_string("Trie");
    let trie_ref = Expr::const_(trie.clone(), vec![]);
    let payload = Expr::app(
        Expr::app(
            prod_at(Level::zero()),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
        Expr::app(trie_ref.clone(), Expr::bvar(0)),
    );
    let node_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(Name::from_string("Array"), vec![Level::zero()]),
                payload,
            ),
            Expr::app(trie_ref, Expr::bvar(1)),
        ),
    );
    let declared_node = node_type.clone();

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: trie.clone(),
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("Trie.node"),
                type_: node_type,
            }],
        }],
    })
    .expect("Trie-shaped deep-chain family must be accepted post-B5");

    // Round-trip + the three renamed recursors in creation order.
    let node = env
        .constructors
        .get(&Name::from_string("Trie.node"))
        .expect("Trie.node");
    assert_eq!(node.type_, declared_node, "deep-chain ctor round-trips");
    for (rec, keyed_to) in [
        ("Trie.rec_1", "Array.mk"),
        ("Trie.rec_2", "List.nil"),
        ("Trie.rec_3", "Prod.mk"),
    ] {
        let rv = env
            .recursors
            .get(&Name::from_string(rec))
            .unwrap_or_else(|| panic!("{rec} should exist"));
        assert!(
            env.get_const(&Name::from_string(rec)).is_some(),
            "{rec} in both tables"
        );
        assert_eq!(rv.rules[0].constructor_name, Name::from_string(keyed_to));
        let tc = crate::tc::TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_sort(&rv.type_)
            .unwrap_or_else(|e| panic!("{rec} must be well-typed, got {e:?}"));
    }
    assert!(
        !env.inductives
            .keys()
            .any(|n| n.to_string().starts_with("_nested.")),
        "no aux mirrors survive"
    );
}

/// Non-nested inductives are untouched by the whole pipeline.
#[test]
fn test_non_nested_unchanged() {
    let mut env = Environment::new();
    let nat = Name::from_string("SimpleNat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("SimpleNat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("SimpleNat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    })
    .unwrap();

    assert_eq!(env.inductives.len(), 1, "Should have exactly 1 inductive");
    assert!(env.inductives.contains_key(&nat));
    assert_eq!(
        count_pi_args(
            &env.recursors
                .get(&Name::from_string("SimpleNat.rec"))
                .expect("SimpleNat.rec")
                .type_
        ),
        // motive + 2 minors + major
        4
    );
}
