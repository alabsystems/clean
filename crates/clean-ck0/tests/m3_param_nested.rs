// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ck0 M3 — **PARAMETERIZED** nested inductive admission (design §5.2).
//!
//! The canonical nested inductive in real mathematics is the parametric rose
//! tree:
//! ```text
//!   Tree (A : Type) where node : A -> List (Tree A) -> Tree A
//! ```
//! ck0 compiles this to a mutual block `[Tree, Tree._List]` via the auxiliary
//! construction, where the auxiliary `Tree._List` is itself **parametric in A**
//! (`Tree._List (A : Type) : Type`), NOT a parameterless aux with `A`
//! substituted away. This file drives that whole path through ck0's REAL
//! machinery (`Term::validate` chokepoint -> `add_inductive_nested` with
//! kernel-checked derived recursors -> genuine ι-reduction):
//!
//! * Tree(A) ADMITS; the aux `Tree._List` is created PARAMETRIC in A (1 leading
//!   Pi binder, shared level params); both derived recursors kernel-check.
//! * A real `Tree Nat` value with NON-EMPTY children builds and `Tree.rec`
//!   ι-reduces THROUGH the nested children list (the nested IH) to the correct
//!   label-sum, and is NOT def-eq to a wrong value (load-bearing, not vacuous).
//! * Tree over a Prop parameter admits (parameter generality).
//! * Every non-strictly-positive / non-uniform parameterized nesting is
//!   REJECTED for the right reason (a false-accept here is inconsistency).

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::term::TermKind;
use clean_ck0::{
    add_inductive, add_inductive_nested, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name,
    NestedError, RawExpr, RawLevel, Term, Transparency,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

// ---- RawExpr builders ----
fn r_sort(level: u32) -> RawExpr {
    let mut l = RawLevel::Zero;
    for _ in 0..level {
        l = RawLevel::Succ(Box::new(l));
    }
    RawExpr::Sort(l)
}
fn r_prop() -> RawExpr {
    RawExpr::Sort(RawLevel::Zero)
}
fn r_sort_param(i: u32) -> RawExpr {
    RawExpr::Sort(RawLevel::Param(i))
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_const_p(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter().fold(f, r_app)
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn lzero() -> RawLevel {
    RawLevel::Zero
}
fn lone() -> RawLevel {
    RawLevel::Succ(Box::new(RawLevel::Zero))
}
fn lparam(i: u32) -> RawLevel {
    RawLevel::Param(i)
}

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

fn nat_zero() -> RawExpr {
    r_const("Nat.zero")
}
fn nat_succ(x: RawExpr) -> RawExpr {
    r_app(r_const("Nat.succ"), x)
}
fn nat_lit(k: u32) -> RawExpr {
    let mut e = nat_zero();
    for _ in 0..k {
        e = nat_succ(e);
    }
    e
}

// ===========================================================================
// Base inductives: List.{u} (A : Type u), Nat.
// ===========================================================================

fn env_with_list() -> MinimalEnv {
    let b = boot(&[("List", 1), ("List.nil", 1), ("List.cons", 1)]);
    let ty = vlvl(&b, &r_pi(r_sort_param(0), r_sort_param(0)), 1);
    let nil_ty = r_pi(
        r_sort_param(0),
        r_app(r_const_p("List", vec![lparam(0)]), r_bvar(0)),
    );
    let list_a = |db: u32| r_app(r_const_p("List", vec![lparam(0)]), r_bvar(db));
    let cons_ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(list_a(1), list_a(2))));
    let list_decl = InductiveDecl {
        name: n("List"),
        num_level_params: 1,
        num_params: 1,
        type_: ty,
        constructors: vec![
            Constructor {
                name: n("List.nil"),
                type_: vlvl(&b, &nil_ty, 1),
            },
            Constructor {
                name: n("List.cons"),
                type_: vlvl(&b, &cons_ty, 1),
            },
        ],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, list_decl).expect("List admits");
    env
}

fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![
            Constructor {
                name: n("Nat.zero"),
                type_: vlvl(&b, &r_const("Nat"), 0),
            },
            Constructor {
                name: n("Nat.succ"),
                type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat")), 0),
            },
        ],
    }
}

// ===========================================================================
// Tree (A : Type) where node : A -> List (Tree A) -> Tree A.
// ===========================================================================

/// The canonical PARAMETERIZED nested inductive. `Tree : Type -> Type`
/// (`num_params = 1`). Inside `node`, the param `A` is `BVar(0)` under the param
/// binder and shifts to `BVar(1)` under the leading `(a : A)` field. The nesting
/// container `List` is applied at level 1 (`Tree A : Type 0 = Sort 1`).
fn tree_decl() -> InductiveDecl {
    let b = MinimalEnv::new()
        .with_const(n("Tree"), 0)
        .with_const(n("Tree.node"), 0)
        .with_const(n("List"), 1);
    // Tree : Type -> Type  (Sort 1 -> Sort 1).
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    // node : (A:Type) -> A -> List.{1} (Tree A) -> Tree A.
    //   depth at `List (Tree A)`: under A and (a:A) => A is BVar(1).
    let tree_a = |db: u32| r_app(r_const("Tree"), r_bvar(db));
    let list_tree_a = r_app(r_const_p("List", vec![lone()]), tree_a(1));
    let node_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),                                     // (A : Type)
            r_pi(r_bvar(0), r_pi(list_tree_a, tree_a(2))), // A -> List (Tree A) -> Tree A
        ),
        0,
    );
    InductiveDecl {
        name: n("Tree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Tree.node"),
            type_: node_ty,
        }],
    }
}

/// Env with List + Nat + the nested parametric Tree admitted.
fn tree_env() -> MinimalEnv {
    let mut env = env_with_list();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive_nested(&mut env, tree_decl())
        .expect("parametric Tree (nested through List) admits via auxiliary");
    env
}

fn count_leading_pis(ty: &Term) -> u32 {
    let mut c = 0u32;
    let mut cur = ty.clone();
    while let TermKind::Pi(_, _, codom) = cur.kind() {
        c = c.saturating_add(1);
        cur = codom.clone();
    }
    c
}

#[test]
fn test_param_tree_admits_and_aux_is_parametric() {
    let env = tree_env();
    let aux = n("Tree._List");

    // (i) The aux `Tree._List` exists and is PARAMETRIC in A: its type former has
    // (at least) one leading Pi binder for the parameter (parameterless would be
    // a bare `Sort`). It shares the parent's level-param count (0).
    let aux_ty = env.const_type(&aux).expect("Tree._List type former stored");
    assert!(
        count_leading_pis(&aux_ty) >= 1,
        "aux Tree._List must be parametric (>=1 leading Pi for the parameter), got {aux_ty:?}"
    );
    assert_eq!(
        env.num_level_params(&aux),
        Some(0),
        "aux shares the parent's level params"
    );

    // (ii) Both derived recursors exist and kernel-check (infer to a Sort).
    for ind in ["Tree", "Tree._List"] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }

    // (iii) The rewritten `Tree.node` is well-typed at the env: it references the
    // parametric aux `Tree._List A`, so its type former kernel-checks.
    let node_ty = env.const_type(&n("Tree.node")).expect("Tree.node type");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &node_ty, &mut budget)
        .expect("rewritten Tree.node type kernel-checks");
}

// --- A transparent Nat.add (via Nat.rec on the 2nd arg) for the fold motive. ---
fn add_def_body() -> RawExpr {
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
    let motive = r_lam(r_const("Nat"), r_const("Nat"));
    let base = r_bvar(1);
    let step = r_lam(r_const("Nat"), r_lam(r_const("Nat"), nat_succ(r_bvar(0))));
    r_lam(
        r_const("Nat"),
        r_lam(
            r_const("Nat"),
            r_apps(elim, vec![motive, base, step, r_bvar(0)]),
        ),
    )
}

fn tree_env_with_add() -> MinimalEnv {
    let env = tree_env();
    let add_ty = Term::validate_closed(
        &env,
        &r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat"))),
    )
    .expect("add type validates");
    let add_body = Term::validate_closed(&env, &add_def_body()).expect("add body validates");
    let mut budget = Budget::default_budget();
    clean_ck0::check(&env, &add_body, &add_ty, &mut budget)
        .expect("Nat.add body checks against Nat -> Nat -> Nat");
    env.with_def(n("Nat.add"), 0, add_ty, add_body, Transparency::Transparent)
}

fn add(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("Nat.add"), vec![x, y])
}

#[test]
fn test_param_tree_rec_folds_through_nonempty_children_to_label_sum() {
    let env = tree_env_with_add();

    // ---- Build a NON-EMPTY Tree Nat: node 3 [node 4 [], node 5 []] ----
    // Tree.node : (A) -> A -> Tree._List A -> Tree A   (rewritten).
    // Tree._List.nil  : (A) -> Tree._List A
    // Tree._List.cons : (A) -> Tree A -> Tree._List A -> Tree._List A
    let nat = || r_const("Nat");
    let tnode = |a: RawExpr, ch: RawExpr| r_apps(r_const("Tree.node"), vec![nat(), a, ch]);
    let lnil = r_apps(r_const("Tree._List.nil"), vec![nat()]);
    let lcons = |h: RawExpr, t: RawExpr| r_apps(r_const("Tree._List.cons"), vec![nat(), h, t]);

    let leaf = |k: u32| tnode(nat_lit(k), lnil.clone());
    let children = lcons(leaf(4), lcons(leaf(5), lnil.clone()));
    let root = tnode(nat_lit(3), children);

    // The value type-checks as `Tree Nat`.
    let root_t = Term::validate_closed(&env, &root).expect("root validates");
    let mut budget = Budget::default_budget();
    let inferred = clean_ck0::infer(&env, &root_t, &mut budget).expect("root infers");
    let tree_nat = Term::validate_closed(&env, &r_app(r_const("Tree"), nat())).expect("Tree Nat");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &tree_nat, &mut budget).expect("def_eq"),
        "root : Tree Nat"
    );

    // ---- label-sum fold via Tree.rec ----
    // Tree.rec @{1} (A:=Nat) {motive_T} {motive_L} m_node m_nil m_cons (major).
    // Block ctor order: [Tree.node, Tree._List.nil, Tree._List.cons] => 3 minors.
    // motives into Nat (ignore the major):
    let motive_t = r_lam(r_app(r_const("Tree"), nat()), nat()); // λ _:Tree Nat. Nat
    let motive_l = r_lam(r_app(r_const("Tree._List"), nat()), nat()); // λ _:Tree._List Nat. Nat
                                                                      // m_node : (a:Nat)(ch:Tree._List Nat)(ih:Nat) -> Nat := λ a ch ih. a + ih.
    let m_node = r_lam(
        nat(),
        r_lam(
            r_app(r_const("Tree._List"), nat()),
            r_lam(nat(), add(r_bvar(2), r_bvar(0))),
        ),
    );
    // m_nil : Nat := 0.
    let m_nil = nat_lit(0);
    // m_cons : (h:Tree Nat)(t:Tree._List Nat)(ih_h:Nat)(ih_t:Nat) -> Nat
    //        := λ h t ih_h ih_t. ih_h + ih_t.
    let m_cons = r_lam(
        r_app(r_const("Tree"), nat()),
        r_lam(
            r_app(r_const("Tree._List"), nat()),
            r_lam(nat(), r_lam(nat(), add(r_bvar(1), r_bvar(0)))),
        ),
    );

    let elim = RawExpr::Elim(n("Tree"), lone(), vec![]); // Type-valued => large elim
    let fold = r_apps(
        elim,
        vec![
            nat(),
            motive_t,
            motive_l,
            m_node,
            m_nil,
            m_cons,
            root.clone(),
        ],
    );
    let fold_t = Term::validate_closed(&env, &fold).expect("fold validates");

    // The fold ι-reduces THROUGH the nested children list (nested IH) to 3+4+5=12.
    let twelve = Term::validate_closed(&env, &nat_lit(12)).expect("12");
    assert!(
        clean_ck0::is_def_eq(&env, &fold_t, &twelve, &mut budget).expect("def_eq"),
        "Tree.rec label-sum of node 3 [node 4 [], node 5 []] ι-reduces (nested IH) to 12"
    );
    // Load-bearing: it is NOT def-eq to a wrong value (e.g. 11 or just 3).
    let eleven = Term::validate_closed(&env, &nat_lit(11)).expect("11");
    assert!(
        !clean_ck0::is_def_eq(&env, &fold_t, &eleven, &mut budget).expect("def_eq"),
        "fold must NOT be def-eq to 11 (the nested IH really threaded the children)"
    );
    let three = Term::validate_closed(&env, &nat_lit(3)).expect("3");
    assert!(
        !clean_ck0::is_def_eq(&env, &fold_t, &three, &mut budget).expect("def_eq"),
        "fold must NOT be def-eq to the root label alone (children were folded)"
    );
}

#[test]
fn test_param_tree_over_prop_admits() {
    // Parameter generality: Tree (A : Prop) where node : A -> List (Tree A) -> Tree A.
    // Tree : Prop -> Prop. `Tree A : Prop = Sort 0`, so List is applied at level 0.
    let mut env = env_with_list();
    let b = MinimalEnv::new()
        .with_const(n("PTree"), 0)
        .with_const(n("PTree.node"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_pi(r_prop(), r_prop()), 0);
    let ptree_a = |db: u32| r_app(r_const("PTree"), r_bvar(db));
    let list_ptree_a = r_app(r_const_p("List", vec![lzero()]), ptree_a(1));
    let node_ty = vlvl(
        &b,
        &r_pi(r_prop(), r_pi(r_bvar(0), r_pi(list_ptree_a, ptree_a(2)))),
        0,
    );
    let decl = InductiveDecl {
        name: n("PTree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("PTree.node"),
            type_: node_ty,
        }],
    };
    add_inductive_nested(&mut env, decl).expect("Tree over a Prop parameter admits");
    let aux_ty = env
        .const_type(&n("PTree._List"))
        .expect("PTree._List parametric aux exists");
    assert!(
        count_leading_pis(&aux_ty) >= 1,
        "aux over Prop param is still parametric"
    );
    for ind in ["PTree", "PTree._List"] {
        let rec_ty = env.recursor_type(&n(ind)).expect("rec stored");
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }
}

// ===========================================================================
// CAPABILITY (over-rejection) regressions — textbook COVARIANT nestings that
// the spec lists as MUST-ADMIT. A `false` reject here is a soundness-safe but
// real capability bug: the variance oracle must be sign-aware, not a blacklist.
// ===========================================================================

/// O2: `Tree (A) where node : List (List (Tree A)) -> Tree A` — the textbook
/// nested-of-nested inductive (finite trees of lists-of-children). `List` is
/// covariant in its element slot, so two covariant layers compose to covariant.
/// MUST ADMIT. (Before the fix the oracle misread `List.cons`'s plain `head : A`
/// field as a left-of-arrow occurrence and rejected the folded inner container.)
#[test]
fn test_admit_list_of_list_of_tree() {
    let mut env = env_with_list();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    let b = MinimalEnv::new()
        .with_const(n("Tree"), 0)
        .with_const(n("Tree.node"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    let tree_a = |db: u32| r_app(r_const("Tree"), r_bvar(db));
    // inner: List (Tree A). At `List (List (Tree A))`: depth 1 ⇒ A = BVar(0).
    let inner_list = r_app(r_const_p("List", vec![lone()]), tree_a(0));
    let outer_list = r_app(r_const_p("List", vec![lone()]), inner_list);
    let node_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(outer_list, tree_a(1))), 0);
    let decl = InductiveDecl {
        name: n("Tree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Tree.node"),
            type_: node_ty,
        }],
    };
    add_inductive_nested(&mut env, decl)
        .expect("List (List (Tree A)) is doubly-covariant and MUST admit");
}

/// O1: a custom covariant container `Box (A : Type 0) : Type 1` with
/// `Box.mk : (A) -> A -> Box A` (covariant in `A`), then
/// `Tree (A) where node : List (Box (Tree A)) -> Tree A`. `Box` and `List` are
/// both covariant, so the composite is covariant. MUST ADMIT.
#[test]
fn test_admit_list_of_box_of_tree() {
    let mut env = env_with_list();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");

    // Box.{u} (A : Type u) : Type u ; Box.mk : (A : Type u) -> A -> Box A.
    // Level-polymorphic (1 level param), universe-preserving so `Box (Tree A)`
    // stays at `Tree A`'s level and the aux List can hold it. Covariant in `A`
    // (the field `A` is a strictly-positive ctor field).
    let bb = MinimalEnv::new()
        .with_const(n("Box"), 1)
        .with_const(n("Box.mk"), 1);
    let box_ty = vlvl(&bb, &r_pi(r_sort_param(0), r_sort_param(0)), 1);
    let box_mk_ty = vlvl(
        &bb,
        &r_pi(
            r_sort_param(0),
            r_pi(
                r_bvar(0),
                r_app(r_const_p("Box", vec![lparam(0)]), r_bvar(1)),
            ),
        ),
        1,
    );
    add_inductive(
        &mut env,
        InductiveDecl {
            name: n("Box"),
            num_level_params: 1,
            num_params: 1,
            type_: box_ty,
            constructors: vec![Constructor {
                name: n("Box.mk"),
                type_: box_mk_ty,
            }],
        },
    )
    .expect("covariant Box admits");

    // Tree (A) where node : List (Box (Tree A)) -> Tree A.
    let b = MinimalEnv::new()
        .with_const(n("Tree"), 0)
        .with_const(n("Tree.node"), 0)
        .with_const(n("List"), 1)
        .with_const(n("Box"), 1);
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    let tree_a = |db: u32| r_app(r_const("Tree"), r_bvar(db));
    // inner: Box (Tree A). At `List (Box (Tree A))`: depth 1 ⇒ A = BVar(0).
    // Box is applied at level 1 (Tree A : Type 0 = Sort 1).
    let box_tree = r_app(r_const_p("Box", vec![lone()]), tree_a(0));
    let list_box = r_app(r_const_p("List", vec![lone()]), box_tree);
    let node_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(list_box, tree_a(1))), 0);
    let decl = InductiveDecl {
        name: n("Tree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Tree.node"),
            type_: node_ty,
        }],
    };
    add_inductive_nested(&mut env, decl)
        .expect("List (Box (Tree A)) is covariant-of-covariant and MUST admit");
}

// ===========================================================================
// NEGATIVE CONTROLS — every non-strictly-positive / non-uniform parameterized
// nesting MUST be rejected (a false-accept is inconsistency).
// ===========================================================================

/// `Tree (A) where node : A -> List (Tree A -> Tree A) -> Tree A`. The nesting
/// argument `(Tree A -> Tree A)` puts the parent in a NEGATIVE position inside
/// the container. Must reject `NonStrictlyPositiveNesting`.
#[test]
fn test_reject_parent_negative_inside_container() {
    let mut env = env_with_list();
    let b = MinimalEnv::new()
        .with_const(n("Bad"), 0)
        .with_const(n("Bad.node"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    let bad_a = |db: u32| r_app(r_const("Bad"), r_bvar(db));
    // inner: Bad A -> Bad A  (parent A in a function domain).
    let inner = r_pi(bad_a(1), bad_a(2));
    let list_inner = r_app(r_const_p("List", vec![lone()]), inner);
    let node_ty = vlvl(
        &b,
        &r_pi(r_sort(1), r_pi(r_bvar(0), r_pi(list_inner, bad_a(2)))),
        0,
    );
    let decl = InductiveDecl {
        name: n("Bad"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Bad.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(r, Err(NestedError::NonStrictlyPositiveNesting { .. })),
        "parent in negative position inside the container must reject, got {r:?}"
    );
}

/// `Tree (A) where node : (Tree A -> A) -> Tree A`. Direct negative occurrence
/// (no container at all): the parent is in a function domain. Must reject.
#[test]
fn test_reject_direct_negative() {
    let mut env = env_with_list();
    let b = MinimalEnv::new()
        .with_const(n("Neg"), 0)
        .with_const(n("Neg.node"), 0);
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    let neg_a = |db: u32| r_app(r_const("Neg"), r_bvar(db));
    // node : (A:Type) -> (Neg A -> A) -> Neg A.
    let node_ty = vlvl(
        &b,
        &r_pi(r_sort(1), r_pi(r_pi(neg_a(0), r_bvar(1)), neg_a(1))),
        0,
    );
    let decl = InductiveDecl {
        name: n("Neg"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Neg.node"),
            type_: node_ty,
        }],
    };
    // This has NO nested container (the `Neg A -> A` field is a direct negative
    // recursive occurrence). The nested path reports NotNested; admitting it via
    // the single path must reject NonPositive. Either way it is NEVER accepted.
    let r = add_inductive_nested(&mut env, decl.clone());
    assert!(
        matches!(r, Err(NestedError::NotNested { .. })),
        "direct-negative decl has no nesting => NotNested, got {r:?}"
    );
    let r2 = add_inductive(&mut env, decl);
    assert!(
        matches!(r2, Err(clean_ck0::AdmitError::NonPositive { .. })),
        "direct negative occurrence must be NonPositive via the single path, got {r2:?}"
    );
}

/// Nesting through a CONTRAVARIANT-parameter container applied to `Tree A` in
/// its negative slot. `Hom (X : Type) (Y : Type)` with constructor
/// `Hom.mk : (X -> Y) -> Hom X Y` makes `X` contravariant. `Tree (A) where
/// node : Hom (Tree A) A -> Tree A` then puts the parent in a negative position
/// of the unfolded aux. The block-positivity re-check MUST reject it.
#[test]
fn test_reject_contravariant_container() {
    // Build env with Hom (a contravariant-in-X container).
    let mut env = MinimalEnv::new();
    let b = boot(&[("Hom", 0), ("Hom.mk", 0)]);
    // Hom : Type -> Type -> Type.
    let hom_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1))), 0);
    // Hom.mk : (X:Type)(Y:Type) -> (X -> Y) -> Hom X Y.
    let hom_mk_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),
            r_pi(
                r_sort(1),
                r_pi(
                    r_pi(r_bvar(1), r_bvar(1)), // X -> Y
                    r_apps(r_const("Hom"), vec![r_bvar(2), r_bvar(1)]),
                ),
            ),
        ),
        0,
    );
    let hom_decl = InductiveDecl {
        name: n("Hom"),
        num_level_params: 0,
        num_params: 2,
        type_: hom_ty,
        constructors: vec![Constructor {
            name: n("Hom.mk"),
            type_: hom_mk_ty,
        }],
    };
    add_inductive(&mut env, hom_decl).expect("Hom admits");

    // CTree (A) where node : Hom (CTree A) A -> CTree A.
    let b2 = MinimalEnv::new()
        .with_const(n("CTree"), 0)
        .with_const(n("CTree.node"), 0)
        .with_const(n("Hom"), 0);
    let ty = vlvl(&b2, &r_pi(r_sort(1), r_sort(1)), 0);
    let ctree_a = |db: u32| r_app(r_const("CTree"), r_bvar(db));
    // node : (A:Type) -> Hom (CTree A) A -> CTree A.
    let hom_field = r_apps(r_const("Hom"), vec![ctree_a(0), r_bvar(0)]);
    let node_ty = vlvl(&b2, &r_pi(r_sort(1), r_pi(hom_field, ctree_a(1))), 0);
    let decl = InductiveDecl {
        name: n("CTree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("CTree.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(
            r,
            Err(NestedError::NonStrictlyPositiveNesting { .. })
                | Err(NestedError::Aux {
                    source: clean_ck0::AdmitError::NonPositive { .. },
                    ..
                })
        ),
        "contravariant-container nesting of the parent must reject, got {r:?}"
    );
}

/// REGRESSION (soundness, critical). A contravariant container `Hom` nested ONE
/// layer inside a covariant container `List` stays FOLDED, so its contravariance
/// would never be exposed by the per-occurrence eager guard and — before the fix
/// — the aux block-positivity re-check treated `Hom`'s slots as covariant and
/// ADMITTED the forged type. `Tree (A) where node : List (Hom (Tree A) (Tree A))
/// -> Tree A` stores an effectively `Tree A -> Tree A` inside `Tree A` (the
/// classic Cantor/Reynolds route to `False`). It MUST be rejected: the unfolded
/// aux `Tree._List.cons : (A) -> Hom (Tree A) (Tree A) -> Tree._List A ->
/// Tree._List A` puts `Tree` in `Hom`'s contravariant first slot, and the
/// variance-aware positivity check now rejects it.
#[test]
fn test_reject_contravariant_container_folded_inside_covariant() {
    // env: List.{u} + Hom (contravariant in its first param).
    let mut env = env_with_list();
    let b = boot(&[("Hom", 0), ("Hom.mk", 0)]);
    let hom_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1))), 0);
    // Hom.mk : (X:Type)(Y:Type) -> (X -> Y) -> Hom X Y.  X is contravariant.
    let hom_mk_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),
            r_pi(
                r_sort(1),
                r_pi(
                    r_pi(r_bvar(1), r_bvar(1)),
                    r_apps(r_const("Hom"), vec![r_bvar(2), r_bvar(1)]),
                ),
            ),
        ),
        0,
    );
    add_inductive(
        &mut env,
        InductiveDecl {
            name: n("Hom"),
            num_level_params: 0,
            num_params: 2,
            type_: hom_ty,
            constructors: vec![Constructor {
                name: n("Hom.mk"),
                type_: hom_mk_ty,
            }],
        },
    )
    .expect("Hom admits");

    // Forge: Tree (A) where node : List (Hom (Tree A) (Tree A)) -> Tree A.
    let b2 = MinimalEnv::new()
        .with_const(n("Tree"), 0)
        .with_const(n("Tree.node"), 0)
        .with_const(n("List"), 1)
        .with_const(n("Hom"), 0);
    let ty = vlvl(&b2, &r_pi(r_sort(1), r_sort(1)), 0);
    let tree_a = |db: u32| r_app(r_const("Tree"), r_bvar(db));
    // inner: Hom (Tree A) (Tree A). At `List (..)`: depth 1 (only A) ⇒ A = BVar(0).
    let hom_inner = r_apps(r_const("Hom"), vec![tree_a(0), tree_a(0)]);
    let list_hom = r_app(r_const_p("List", vec![lone()]), hom_inner);
    let node_ty = vlvl(&b2, &r_pi(r_sort(1), r_pi(list_hom, tree_a(1))), 0);
    let decl = InductiveDecl {
        name: n("Tree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Tree.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    // The DECISIVE gate is the unfolded-block positivity re-check, which now sees
    // `Hom`'s contravariant slot (the eager per-occurrence guard cannot, since the
    // inner `Hom` stays folded). Assert exactly that arm so a future regression
    // that re-folds the slot (re-admitting it) fails loudly here.
    assert!(
        matches!(
            r,
            Err(NestedError::Aux {
                source: clean_ck0::AdmitError::NonPositive { .. },
                ..
            })
        ),
        "Hom (contravariant) folded inside List must be rejected by the block \
         positivity re-check (false-accept => inconsistency), got {r:?}"
    );
}

/// REGRESSION companion: `Hom (List (Tree A)) (Tree A)` — the parent appears
/// inside a COVARIANT container (`List`) that is itself in `Hom`'s contravariant
/// slot. The parent is still ultimately in a negative position and MUST reject.
#[test]
fn test_reject_covariant_inside_contravariant_slot() {
    let mut env = env_with_list();
    let b = boot(&[("Hom", 0), ("Hom.mk", 0)]);
    let hom_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1))), 0);
    let hom_mk_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),
            r_pi(
                r_sort(1),
                r_pi(
                    r_pi(r_bvar(1), r_bvar(1)),
                    r_apps(r_const("Hom"), vec![r_bvar(2), r_bvar(1)]),
                ),
            ),
        ),
        0,
    );
    add_inductive(
        &mut env,
        InductiveDecl {
            name: n("Hom"),
            num_level_params: 0,
            num_params: 2,
            type_: hom_ty,
            constructors: vec![Constructor {
                name: n("Hom.mk"),
                type_: hom_mk_ty,
            }],
        },
    )
    .expect("Hom admits");

    // Forge: HTree (A) where node : Hom (List (HTree A)) (HTree A) -> HTree A.
    let b2 = MinimalEnv::new()
        .with_const(n("HTree"), 0)
        .with_const(n("HTree.node"), 0)
        .with_const(n("List"), 1)
        .with_const(n("Hom"), 0);
    let ty = vlvl(&b2, &r_pi(r_sort(1), r_sort(1)), 0);
    let htree_a = |db: u32| r_app(r_const("HTree"), r_bvar(db));
    // node : (A) -> Hom (List (HTree A)) (HTree A) -> HTree A. depth 1 ⇒ A=BVar(0).
    let list_htree = r_app(r_const_p("List", vec![lone()]), htree_a(0));
    let hom_field = r_apps(r_const("Hom"), vec![list_htree, htree_a(0)]);
    let node_ty = vlvl(&b2, &r_pi(r_sort(1), r_pi(hom_field, htree_a(1))), 0);
    let decl = InductiveDecl {
        name: n("HTree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("HTree.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(
            r,
            Err(NestedError::NonStrictlyPositiveNesting { .. })
                | Err(NestedError::Aux {
                    source: clean_ck0::AdmitError::NonPositive { .. },
                    ..
                })
        ),
        "covariant container in Hom's contravariant slot must reject, got {r:?}"
    );
}

/// The parameter `A` itself appearing in a negative position that would let a
/// fixpoint be built: `Tree (A) where node : List (A -> Tree A) -> Tree A`. The
/// nesting argument `(A -> Tree A)` has the parent `Tree A` strictly-positive but
/// puts `A` to the left of an arrow; the resulting field `A -> Tree A` is fine
/// for `A` but the occurrence still nests `Tree` under an arrow's CODOMAIN — the
/// arrow domain `A` is harmless, yet the container arg `(A -> Tree A)` mentions
/// `Tree` only positively. To make a TRUE negative-`A` fixpoint we instead use
/// `node : List (Tree A -> A) -> Tree A`, which puts `Tree A` to the LEFT of the
/// arrow (negative), and must reject.
#[test]
fn test_reject_param_enables_negative_fixpoint() {
    let mut env = env_with_list();
    let b = MinimalEnv::new()
        .with_const(n("FxTree"), 0)
        .with_const(n("FxTree.node"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    let fx_a = |db: u32| r_app(r_const("FxTree"), r_bvar(db));
    // node : (A:Type) -> List (FxTree A -> A) -> FxTree A.
    //   At `List (..)`: depth 1 (only A). inner = Pi(FxTree A, A): domain A is
    //   BVar(0) (under A), codomain A is BVar(1) (under A and the arrow binder).
    let inner = r_pi(fx_a(0), r_bvar(1));
    let list_inner = r_app(r_const_p("List", vec![lone()]), inner);
    let node_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(list_inner, fx_a(1))), 0);
    let decl = InductiveDecl {
        name: n("FxTree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("FxTree.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(r, Err(NestedError::NonStrictlyPositiveNesting { .. })),
        "parent-left-of-arrow inside container must reject, got {r:?}"
    );
}

/// NON-UNIFORM nesting: an occurrence argument depends on a constructor FIELD
/// (not just the parameter), so a single parametric aux cannot represent it.
/// `Tree (A) where node : (B : Type) -> List (Tree B) -> Tree A`. The container
/// arg `Tree B` mentions the field binder `B`, not the parameter `A`. Must reject
/// (fail-closed) rather than build an unsound aux.
#[test]
fn test_reject_nonuniform_field_dependent_nesting() {
    let mut env = env_with_list();
    let b = MinimalEnv::new()
        .with_const(n("NU"), 0)
        .with_const(n("NU.node"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_pi(r_sort(1), r_sort(1)), 0);
    // node : (A:Type) -> (B:Type) -> List (NU B) -> NU A.
    //   At `List (NU B)`: depth = 2 (A, B); B = BVar(0) is a FIELD, not the param.
    let nu_b = r_app(r_const("NU"), r_bvar(0));
    let list_nu_b = r_app(r_const_p("List", vec![lone()]), nu_b);
    let node_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),
            r_pi(r_sort(1), r_pi(list_nu_b, r_app(r_const("NU"), r_bvar(2)))),
        ),
        0,
    );
    let decl = InductiveDecl {
        name: n("NU"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("NU.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(r, Err(NestedError::NonUniformNesting { .. })),
        "field-dependent (non-uniform) nesting must reject, got {r:?}"
    );
}

/// REGRESSION (soundness, critical) — DEEPEST recursion path. The contravariance
/// is reached through a SECOND custom container `G` that is itself folded inside
/// `List`. `Hom (X)(Y)` is contravariant in `X` (`Hom.mk : (X -> Y) -> Hom X Y`).
/// `G (X)` laundres `X` into `Hom`'s contravariant slot
/// (`G.mk : (X) -> Hom X X -> G X`), so `G` is itself contravariant in `X`.
/// Forge `Tree (A) where node : List (G (Tree A)) -> Tree A`: the outer `List`
/// becomes the aux, whose stored field is `G (Tree A)`; the unfolded-block
/// positivity re-check must consult the variance oracle, which must RECURSE
/// through `G`'s constructor to discover `Hom`'s contravariance and REJECT.
/// A false-accept here is inconsistency: `Tree A` would store an effective
/// `Tree A -> Tree A` (laundered through `G`/`Hom`).
#[test]
fn test_reject_two_container_folded_contravariance() {
    // env: List.{u} + Hom (contravariant in its first param) + G (contravariant
    // in its param, laundered through Hom's contravariant slot).
    let mut env = env_with_list();
    let b = boot(&[("Hom", 0), ("Hom.mk", 0)]);
    let hom_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1))), 0);
    // Hom.mk : (X:Type)(Y:Type) -> (X -> Y) -> Hom X Y.  X is contravariant.
    let hom_mk_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),
            r_pi(
                r_sort(1),
                r_pi(
                    r_pi(r_bvar(1), r_bvar(1)),
                    r_apps(r_const("Hom"), vec![r_bvar(2), r_bvar(1)]),
                ),
            ),
        ),
        0,
    );
    add_inductive(
        &mut env,
        InductiveDecl {
            name: n("Hom"),
            num_level_params: 0,
            num_params: 2,
            type_: hom_ty,
            constructors: vec![Constructor {
                name: n("Hom.mk"),
                type_: hom_mk_ty,
            }],
        },
    )
    .expect("Hom admits");

    // G (X : Type) : Type ; G.mk : (X:Type) -> Hom X X -> G X.
    //   Under (X:Type) the param X = BVar(0); the field `Hom X X` puts X into
    //   Hom's CONTRAVARIANT slot 0 => G is contravariant in X. After the field
    //   binder the result `G X` = G (BVar 1).
    let bg = MinimalEnv::new()
        .with_const(n("G"), 0)
        .with_const(n("G.mk"), 0)
        .with_const(n("Hom"), 0);
    let g_ty = vlvl(&bg, &r_pi(r_sort(1), r_sort(1)), 0);
    let g_mk_ty = vlvl(
        &bg,
        &r_pi(
            r_sort(1), // (X : Type)
            r_pi(
                r_apps(r_const("Hom"), vec![r_bvar(0), r_bvar(0)]), // Hom X X
                r_app(r_const("G"), r_bvar(1)),                     // G X
            ),
        ),
        0,
    );
    add_inductive(
        &mut env,
        InductiveDecl {
            name: n("G"),
            num_level_params: 0,
            num_params: 1,
            type_: g_ty,
            constructors: vec![Constructor {
                name: n("G.mk"),
                type_: g_mk_ty,
            }],
        },
    )
    .expect("G admits (G is contravariant in X, but G itself is a fine inductive)");

    // Forge: Tree (A) where node : List (G (Tree A)) -> Tree A.
    let b2 = MinimalEnv::new()
        .with_const(n("Tree"), 0)
        .with_const(n("Tree.node"), 0)
        .with_const(n("List"), 1)
        .with_const(n("G"), 0);
    let ty = vlvl(&b2, &r_pi(r_sort(1), r_sort(1)), 0);
    let tree_a = |db: u32| r_app(r_const("Tree"), r_bvar(db));
    // inner: G (Tree A). At `List (..)`: depth 1 (only A) ⇒ A = BVar(0).
    // G is applied at level 0 (G : Type -> Type, Tree A : Type 0).
    let g_inner = r_app(r_const("G"), tree_a(0));
    let list_g = r_app(r_const_p("List", vec![lone()]), g_inner);
    let node_ty = vlvl(&b2, &r_pi(r_sort(1), r_pi(list_g, tree_a(1))), 0);
    let decl = InductiveDecl {
        name: n("Tree"),
        num_level_params: 0,
        num_params: 1,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Tree.node"),
            type_: node_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    // The DECISIVE gate is the unfolded-block positivity re-check, which must
    // RECURSE through G's constructor into Hom's contravariant slot. Assert
    // exactly that arm so a future regression that stops recursing through G
    // (re-admitting it) fails loudly here. A false-accept => inconsistency
    // (Tree A stores an effective Tree A -> Tree A through G/Hom).
    assert!(
        matches!(
            r,
            Err(NestedError::Aux {
                source: clean_ck0::AdmitError::NonPositive { .. },
                ..
            })
        ),
        "contravariance laundered through G (folded inside List) must be rejected \
         by the recursive block positivity re-check (false-accept => inconsistency), \
         got {r:?}"
    );
}

/// REGRESSION (soundness, critical) — PARAMETERLESS analogue (the property is
/// GENERAL, not parameter-specific). `Hom (X)(Y)` is contravariant in `X`
/// (`Hom.mk : (X -> Y) -> Hom X Y`). Forge a parameterless inductive
/// `RH where mk : List (Hom RH RH) -> RH` (num_params = 0): the block type `RH`
/// itself sits in `Hom`'s contravariant slot 0. The aux `RH._List` stores
/// `Hom RH RH`; the block-positivity check sees the block name `RH` in `Hom`'s
/// contravariant slot and must REJECT. This confirms the contravariant-container
/// guard is a property of the NESTING, not of parameters (the parameterless
/// route to `False` is the original exploit).
#[test]
fn test_reject_parameterless_hom_self_nesting() {
    // env: List.{u} + Hom (contravariant in its first param).
    let mut env = env_with_list();
    let b = boot(&[("Hom", 0), ("Hom.mk", 0)]);
    let hom_ty = vlvl(&b, &r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1))), 0);
    // Hom.mk : (X:Type)(Y:Type) -> (X -> Y) -> Hom X Y.  X is contravariant.
    let hom_mk_ty = vlvl(
        &b,
        &r_pi(
            r_sort(1),
            r_pi(
                r_sort(1),
                r_pi(
                    r_pi(r_bvar(1), r_bvar(1)),
                    r_apps(r_const("Hom"), vec![r_bvar(2), r_bvar(1)]),
                ),
            ),
        ),
        0,
    );
    add_inductive(
        &mut env,
        InductiveDecl {
            name: n("Hom"),
            num_level_params: 0,
            num_params: 2,
            type_: hom_ty,
            constructors: vec![Constructor {
                name: n("Hom.mk"),
                type_: hom_mk_ty,
            }],
        },
    )
    .expect("Hom admits");

    // Forge: RH (parameterless) where mk : List (Hom RH RH) -> RH.
    //   RH : Type. RH is a const (no binders), so the block name RH itself sits
    //   in Hom's contravariant slot 0.
    let b2 = MinimalEnv::new()
        .with_const(n("RH"), 0)
        .with_const(n("RH.mk"), 0)
        .with_const(n("List"), 1)
        .with_const(n("Hom"), 0);
    let ty = vlvl(&b2, &r_sort(1), 0);
    let hom_inner = r_apps(r_const("Hom"), vec![r_const("RH"), r_const("RH")]);
    let list_hom = r_app(r_const_p("List", vec![lone()]), hom_inner);
    let mk_ty = vlvl(&b2, &r_pi(list_hom, r_const("RH")), 0);
    let decl = InductiveDecl {
        name: n("RH"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("RH.mk"),
            type_: mk_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    // Whichever arm fires, it MUST be an Err: the eager per-occurrence guard may
    // catch the block name RH in Hom's contravariant slot
    // (NonStrictlyPositiveNesting), or the unfolded-block re-check does
    // (Aux{NonPositive}). Accept either; this confirms the contravariant-container
    // guard is a property of the nesting, not of parameters. A false-accept =>
    // inconsistency (RH stores an effective RH -> RH).
    assert!(
        matches!(
            r,
            Err(NestedError::NonStrictlyPositiveNesting { .. })
                | Err(NestedError::Aux {
                    source: clean_ck0::AdmitError::NonPositive { .. },
                    ..
                })
        ),
        "parameterless RH in Hom's contravariant slot must reject (false-accept \
         => inconsistency), got {r:?}"
    );
}
