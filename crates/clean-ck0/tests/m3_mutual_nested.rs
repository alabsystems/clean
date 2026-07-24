// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! M3 targeted tests (design §5.2, §7): mutual inductive admission +
//! multi-motive recursor derivation (Even/Odd, Tree/Forest), and nested
//! inductive admission via the auxiliary construction (RoseTree : List RoseTree
//! -> RoseTree). Each derived recursor is kernel-checked, ι reduces on literal
//! constructors, cross-type recursive fields are handled, and a non-strictly-
//! positive nesting is rejected.
//!
//! Full Lean-corpus recursor def-eq conformance is M4 (no Lean kernel here); M3
//! verifies kernel-check + iota + expected-shape on representative cases.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, add_inductive_mutual, add_inductive_nested, Budget, Constructor, Env,
    InductiveDecl, MinimalEnv, MutualBlock, Name, NestedError, RawExpr, RawLevel, Term,
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
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_const_p(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
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

// ===========================================================================
// Even / Odd mutual block over Nat-shaped naturals (no params, no indices).
// ===========================================================================
//
//   Even : Type   with  Even.zero : Even
//                       Even.succ : Odd  -> Even
//   Odd  : Type   with  Odd.succ  : Even -> Odd
//
// Even.rec has TWO motives and THREE minors; the recursive field of Even.succ
// targets the Odd motive (cross-type), and vice-versa.

fn even_odd_block() -> MutualBlock {
    let b = boot(&[
        ("Even", 0),
        ("Odd", 0),
        ("Even.zero", 0),
        ("Even.succ", 0),
        ("Odd.succ", 0),
    ]);
    let even_ty = vlvl(&b, &r_sort(1), 0);
    let odd_ty = vlvl(&b, &r_sort(1), 0);
    let even_zero = Constructor {
        name: n("Even.zero"),
        type_: vlvl(&b, &r_const("Even"), 0),
    };
    // Even.succ : Odd -> Even
    let even_succ = Constructor {
        name: n("Even.succ"),
        type_: vlvl(&b, &r_pi(r_const("Odd"), r_const("Even")), 0),
    };
    // Odd.succ : Even -> Odd
    let odd_succ = Constructor {
        name: n("Odd.succ"),
        type_: vlvl(&b, &r_pi(r_const("Even"), r_const("Odd")), 0),
    };
    MutualBlock {
        decls: vec![
            InductiveDecl {
                name: n("Even"),
                num_level_params: 0,
                num_params: 0,
                type_: even_ty,
                constructors: vec![even_zero, even_succ],
            },
            InductiveDecl {
                name: n("Odd"),
                num_level_params: 0,
                num_params: 0,
                type_: odd_ty,
                constructors: vec![odd_succ],
            },
        ],
    }
}

#[test]
fn test_even_odd_block_admits_and_recursors_kernel_check() {
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, even_odd_block()).expect("Even/Odd block admits");

    // Two recursors exist, each kernel-checks (infers a sort cleanly).
    for ind in ["Even", "Odd"] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec type stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec type kernel-checks: {e:?}"));
    }

    // Even.rec telescope: 2 motives + 3 minors + major = 6 leading Pis.
    let rec_ty = env.recursor_type(&n("Even")).expect("Even.rec");
    let mut count = 0u32;
    let mut cur = rec_ty;
    while let clean_ck0::term::TermKind::Pi(_, _, codom) = cur.kind() {
        count += 1;
        cur = codom.clone();
    }
    assert_eq!(
        count, 6,
        "Even.rec = 2 motives + 3 minors + major (got {count})"
    );
    // Type-valued block large-eliminates → extra motive level param.
    assert_eq!(env.num_level_params(&n("Even.rec")), Some(1));
    assert_eq!(env.num_level_params(&n("Odd.rec")), Some(1));
}

#[test]
fn test_even_odd_iota_reduces_on_literal_constructors() {
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, even_odd_block()).expect("Even/Odd block admits");

    // Build Even.rec eliminating into a small motive (λ _. Nat-ish), but we only
    // need ι to fire: use motive_even = λ _:Even. Even, motive_odd = λ _:Odd. Even.
    // minors: m_even_zero : Even, m_even_succ : (o:Odd)->motive_odd o-> Even,
    //         m_odd_succ  : (e:Even)->motive_even e-> Even.
    // We pick everything to land in `Even` so the result is observable.
    let m_even = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Even")),
        Box::new(r_const("Even")),
    );
    let m_odd = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Odd")),
        Box::new(r_const("Even")),
    );
    // m_even_zero := Even.zero
    let m_ez = r_const("Even.zero");
    // m_even_succ := λ (o:Odd) (ih:Even). ih   -- returns the recursive result
    let m_es = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Odd")),
        Box::new(RawExpr::Lam(
            BinderInfo::Default,
            Box::new(r_const("Even")),
            Box::new(r_bvar(0)),
        )),
    );
    // m_odd_succ := λ (e:Even) (ih:Even). ih
    let m_os = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Even")),
        Box::new(RawExpr::Lam(
            BinderInfo::Default,
            Box::new(r_const("Even")),
            Box::new(r_bvar(0)),
        )),
    );

    // Even.rec @{0} {m_even} {m_odd} m_ez m_es m_os (major)
    let elim = RawExpr::Elim(n("Even"), RawLevel::Succ(Box::new(RawLevel::Zero)), vec![]);
    let rec_apps = |major: RawExpr| {
        RawExpr::App(
            Box::new(RawExpr::App(
                Box::new(RawExpr::App(
                    Box::new(RawExpr::App(
                        Box::new(RawExpr::App(
                            Box::new(RawExpr::App(
                                Box::new(elim.clone()),
                                Box::new(m_even.clone()),
                            )),
                            Box::new(m_odd.clone()),
                        )),
                        Box::new(m_ez.clone()),
                    )),
                    Box::new(m_es.clone()),
                )),
                Box::new(m_os.clone()),
            )),
            Box::new(major),
        )
    };

    // major = Even.zero  →  m_ez = Even.zero
    let t0 = Term::validate_closed(&env, &rec_apps(r_const("Even.zero"))).expect("validates");
    let mut b0 = Budget::default_budget();
    let w0 = clean_ck0::whnf(&env, &t0, &mut b0).expect("whnf");
    let expect_zero = Term::validate_closed(&env, &r_const("Even.zero")).expect("zero");
    assert_eq!(w0, expect_zero, "Even.rec on Even.zero ~> m_even_zero");

    // major = Even.succ (Odd.succ Even.zero)
    //   ~> m_es (Odd.succ Even.zero) (Even.rec ... (Odd.succ Even.zero))
    //   ~> Even.rec ... (Odd.succ Even.zero)            (m_es returns its IH)
    //   ~> m_os Even.zero (Even.rec ... Even.zero)
    //   ~> Even.rec ... Even.zero
    //   ~> Even.zero
    // i.e. the whole thing is def-eq to Even.zero.
    let inner = r_app(r_const("Odd.succ"), r_const("Even.zero"));
    let major = r_app(r_const("Even.succ"), inner);
    let t1 = Term::validate_closed(&env, &rec_apps(major)).expect("validates");
    let mut b1 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &t1, &expect_zero, &mut b1).expect("def_eq"),
        "Even.rec on Even.succ (Odd.succ Even.zero) reduces (cross-type IH) to Even.zero"
    );
}

// ===========================================================================
// Tree / Forest mutual block (Forest carries a recursive Tree field).
// ===========================================================================
//
//   Tree   : Type  with  Tree.node : Forest -> Tree
//   Forest : Type  with  Forest.nil  : Forest
//                        Forest.cons : Tree -> Forest -> Forest

fn tree_forest_block() -> MutualBlock {
    let b = boot(&[
        ("Tree", 0),
        ("Forest", 0),
        ("Tree.node", 0),
        ("Forest.nil", 0),
        ("Forest.cons", 0),
    ]);
    let tree_ty = vlvl(&b, &r_sort(1), 0);
    let forest_ty = vlvl(&b, &r_sort(1), 0);
    let tree_node = Constructor {
        name: n("Tree.node"),
        type_: vlvl(&b, &r_pi(r_const("Forest"), r_const("Tree")), 0),
    };
    let forest_nil = Constructor {
        name: n("Forest.nil"),
        type_: vlvl(&b, &r_const("Forest"), 0),
    };
    // Forest.cons : Tree -> Forest -> Forest
    let forest_cons = Constructor {
        name: n("Forest.cons"),
        type_: vlvl(
            &b,
            &r_pi(r_const("Tree"), r_pi(r_const("Forest"), r_const("Forest"))),
            0,
        ),
    };
    MutualBlock {
        decls: vec![
            InductiveDecl {
                name: n("Tree"),
                num_level_params: 0,
                num_params: 0,
                type_: tree_ty,
                constructors: vec![tree_node],
            },
            InductiveDecl {
                name: n("Forest"),
                num_level_params: 0,
                num_params: 0,
                type_: forest_ty,
                constructors: vec![forest_nil, forest_cons],
            },
        ],
    }
}

#[test]
fn test_tree_forest_block_admits_and_kernel_checks() {
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, tree_forest_block()).expect("Tree/Forest admits");
    for ind in ["Tree", "Forest"] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }
    // Tree.rec: 2 motives + 3 minors (node, nil, cons) + major = 6.
    let rec_ty = env.recursor_type(&n("Tree")).expect("Tree.rec");
    let mut count = 0u32;
    let mut cur = rec_ty;
    while let clean_ck0::term::TermKind::Pi(_, _, codom) = cur.kind() {
        count += 1;
        cur = codom.clone();
    }
    assert_eq!(count, 6, "Tree.rec = 2 motives + 3 minors + major");
}

#[test]
fn test_single_type_block_matches_m2_shape() {
    // A single-element mutual block must degenerate to the M2 recursor shape:
    // Nat as a 1-type block has Nat.rec = 1 motive + 2 minors + major = 4.
    let b = boot(&[("MNat", 0), ("MNat.zero", 0), ("MNat.succ", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    let zero = Constructor {
        name: n("MNat.zero"),
        type_: vlvl(&b, &r_const("MNat"), 0),
    };
    let succ = Constructor {
        name: n("MNat.succ"),
        type_: vlvl(&b, &r_pi(r_const("MNat"), r_const("MNat")), 0),
    };
    let block = MutualBlock {
        decls: vec![InductiveDecl {
            name: n("MNat"),
            num_level_params: 0,
            num_params: 0,
            type_: ty,
            constructors: vec![zero, succ],
        }],
    };
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, block).expect("single block admits");
    let rec_ty = env.recursor_type(&n("MNat")).expect("MNat.rec");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget).expect("kernel-checks");
    let mut count = 0u32;
    let mut cur = rec_ty;
    while let clean_ck0::term::TermKind::Pi(_, _, codom) = cur.kind() {
        count += 1;
        cur = codom.clone();
    }
    assert_eq!(
        count, 4,
        "single-type block Nat.rec = motive + 2 minors + major"
    );
}

#[test]
fn test_mutual_block_positivity_rejects_cross_type_negative() {
    // A : Type with A.mk : (B -> A) -> A  in a block [A, B]: B occurs to the left
    // of an arrow in A.mk's field, so the WHOLE-BLOCK positivity must reject it.
    let b = boot(&[("A", 0), ("B", 0), ("A.mk", 0), ("B.mk", 0)]);
    let a_ty = vlvl(&b, &r_sort(1), 0);
    let b_ty = vlvl(&b, &r_sort(1), 0);
    // A.mk : (B -> A) -> A   (B negative)
    let a_mk = Constructor {
        name: n("A.mk"),
        type_: vlvl(&b, &r_pi(r_pi(r_const("B"), r_const("A")), r_const("A")), 0),
    };
    let b_mk = Constructor {
        name: n("B.mk"),
        type_: vlvl(&b, &r_const("B"), 0),
    };
    let block = MutualBlock {
        decls: vec![
            InductiveDecl {
                name: n("A"),
                num_level_params: 0,
                num_params: 0,
                type_: a_ty,
                constructors: vec![a_mk],
            },
            InductiveDecl {
                name: n("B"),
                num_level_params: 0,
                num_params: 0,
                type_: b_ty,
                constructors: vec![b_mk],
            },
        ],
    };
    let mut env = MinimalEnv::new();
    let r = add_inductive_mutual(&mut env, block);
    assert!(
        matches!(r, Err(clean_ck0::AdmitError::NonPositive { .. })),
        "cross-type negative occurrence must be NonPositive, got {r:?}"
    );
}

#[test]
fn test_mutual_idempotent_readd() {
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, even_odd_block()).expect("first add");
    add_inductive_mutual(&mut env, even_odd_block()).expect("idempotent re-add");
}

// ===========================================================================
// Nested: RoseTree : List RoseTree -> RoseTree.
// ===========================================================================

/// An env with `List.{u} (A : Type u)` admitted as a real inductive (so it can
/// be a nesting container). We admit List via the single-inductive path so its
/// constructors + num_params are recorded.
fn env_with_list() -> MinimalEnv {
    let b = boot(&[("List", 1), ("List.nil", 1), ("List.cons", 1)]);
    let ty = vlvl(
        &b,
        &r_pi(
            RawExpr::Sort(RawLevel::Param(0)),
            RawExpr::Sort(RawLevel::Param(0)),
        ),
        1,
    );
    let nil_ty = r_pi(
        RawExpr::Sort(RawLevel::Param(0)),
        r_app(r_const_p("List", vec![RawLevel::Param(0)]), r_bvar(0)),
    );
    let list_a = |db: u32| r_app(r_const_p("List", vec![RawLevel::Param(0)]), r_bvar(db));
    let cons_ty = r_pi(
        RawExpr::Sort(RawLevel::Param(0)),
        r_pi(r_bvar(0), r_pi(list_a(1), list_a(2))),
    );
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

/// RoseTree : Type with `RoseTree.mk : List RoseTree -> RoseTree` (List @ level 0).
fn rosetree_decl(env: &MinimalEnv) -> InductiveDecl {
    // Build the decl's terms against a bootstrap env that knows RoseTree + List.
    let b = MinimalEnv::new()
        .with_const(n("RoseTree"), 0)
        .with_const(n("RoseTree.mk"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_sort(1), 0);
    // mk : List.{1} RoseTree -> RoseTree   (List.{u} : Sort u -> Sort u, so with
    // RoseTree : Type 0 = Sort 1 the level arg is 1.)
    let lvl1 = RawLevel::Succ(Box::new(RawLevel::Zero));
    let field = r_app(r_const_p("List", vec![lvl1]), r_const("RoseTree"));
    let mk_ty = vlvl(&b, &r_pi(field, r_const("RoseTree")), 0);
    let _ = env;
    InductiveDecl {
        name: n("RoseTree"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("RoseTree.mk"),
            type_: mk_ty,
        }],
    }
}

#[test]
fn test_rosetree_nested_admits_via_auxiliary() {
    let mut env = env_with_list();
    let decl = rosetree_decl(&env);
    add_inductive_nested(&mut env, decl).expect("RoseTree nested admits via auxiliary");

    // The auxiliary type RoseTree._List was created and its recursor kernel-checks.
    let aux = n("RoseTree._List");
    assert!(
        env.recursor_type(&aux).is_some(),
        "auxiliary RoseTree._List recursor exists"
    );
    // RoseTree's own recursor exists and kernel-checks.
    let rt_rec = env
        .recursor_type(&n("RoseTree"))
        .expect("RoseTree.rec stored");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &rt_rec, &mut budget)
        .expect("RoseTree.rec kernel-checks");
    let aux_rec = env.recursor_type(&aux).expect("aux rec stored");
    clean_ck0::infer_sort_in_context(&env, &[], &aux_rec, &mut budget)
        .expect("RoseTree._List.rec kernel-checks");
}

#[test]
fn test_rosetree_iota_on_literal_constructor() {
    let mut env = env_with_list();
    let decl = rosetree_decl(&env);
    add_inductive_nested(&mut env, decl).expect("RoseTree nested admits");

    // The aux nil constructor: RoseTree._List.nil : RoseTree._List.
    // RoseTree._List.rec eliminating into λ_. RoseTree, with the nil minor =
    // (some RoseTree), cons minor ignored, on the literal `RoseTree._List.nil`
    // must ι-reduce to the nil minor.
    // We need a RoseTree value for the nil minor: RoseTree.mk applied to nil.
    // First build `RoseTree._List.nil` and `RoseTree.mk RoseTree._List.nil`.
    let lam = |dom: RawExpr, body: RawExpr| {
        RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
    };
    let apps = |head: RawExpr, args: Vec<RawExpr>| args.into_iter().fold(head, r_app);

    let aux_nil = r_const("RoseTree._List.nil");
    // The block is [RoseTree, RoseTree._List], so RoseTree._List.rec takes TWO
    // motives (one per block type) and TWO minors (nil, cons of the _List type;
    // RoseTree.mk's minor belongs to RoseTree.rec, not _List.rec). Eliminate
    // everything into RoseTree.
    let motive_rt = lam(r_const("RoseTree"), r_const("RoseTree"));
    let motive_list = lam(r_const("RoseTree._List"), r_const("RoseTree"));
    // Mutual recursors share ALL block minors (one per constructor of EVERY block
    // type), in block-then-declaration order: [RoseTree.mk, _List.nil, _List.cons].
    let rt_witness = r_app(r_const("RoseTree.mk"), aux_nil.clone());
    // mk minor : (l:RoseTree._List)(ih_l:RoseTree) -> RoseTree := λ l ih_l. ih_l.
    let mk_minor = lam(
        r_const("RoseTree._List"),
        lam(r_const("RoseTree"), r_bvar(0)),
    );
    // nil minor := rt_witness : RoseTree.
    let nil_minor = rt_witness.clone();
    // cons minor : (h:RoseTree)(t:RoseTree._List)(ih_h:RoseTree)(ih_t:RoseTree)
    //   -> RoseTree := λ h t ih_h ih_t. ih_t.
    let cons_minor = lam(
        r_const("RoseTree"),
        lam(
            r_const("RoseTree._List"),
            lam(r_const("RoseTree"), lam(r_const("RoseTree"), r_bvar(0))),
        ),
    );
    // RoseTree._List.rec @{1} {motive_rt} {motive_list} mk nil cons (RoseTree._List.nil)
    let elim = RawExpr::Elim(
        n("RoseTree._List"),
        RawLevel::Succ(Box::new(RawLevel::Zero)),
        vec![],
    );
    let app = apps(
        elim,
        vec![
            motive_rt,
            motive_list,
            mk_minor,
            nil_minor,
            cons_minor,
            aux_nil,
        ],
    );
    let t = Term::validate_closed(&env, &app).expect("validates");
    let mut budget = Budget::default_budget();
    let w = clean_ck0::whnf(&env, &t, &mut budget).expect("whnf");
    let expected = Term::validate_closed(&env, &rt_witness).expect("witness");
    assert_eq!(
        w, expected,
        "RoseTree._List.rec on nil ι-reduces to the nil minor"
    );
}

#[test]
fn test_nested_negative_is_rejected() {
    // A negative nesting: Bad : Type with `Bad.mk : List (Bad -> Nat) -> Bad`.
    // The nesting argument `(Bad -> Nat)` puts Bad to the LEFT of an arrow, so
    // the nesting is non-strictly-positive and must be rejected.
    let mut env = env_with_list();
    env = env.with_const(n("Nat"), 0);
    let b = MinimalEnv::new()
        .with_const(n("Bad"), 0)
        .with_const(n("Bad.mk"), 0)
        .with_const(n("List"), 1)
        .with_const(n("Nat"), 0);
    let ty = vlvl(&b, &r_sort(1), 0);
    // field : List.{0} (Bad -> Nat)
    let inner = r_pi(r_const("Bad"), r_const("Nat"));
    let field = r_app(r_const_p("List", vec![RawLevel::Zero]), inner);
    let mk_ty = vlvl(&b, &r_pi(field, r_const("Bad")), 0);
    let decl = InductiveDecl {
        name: n("Bad"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Bad.mk"),
            type_: mk_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(r, Err(NestedError::NonStrictlyPositiveNesting { .. })),
        "negative nesting must be NonStrictlyPositiveNesting, got {r:?}"
    );
}

#[test]
fn test_non_nested_routed_to_nested_is_not_nested() {
    // A plain Nat sent to the nested path reports NotNested (no nesting found).
    let mut env = env_with_list();
    let b = boot(&[("PNat", 0), ("PNat.zero", 0), ("PNat.succ", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    let decl = InductiveDecl {
        name: n("PNat"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![
            Constructor {
                name: n("PNat.zero"),
                type_: vlvl(&b, &r_const("PNat"), 0),
            },
            Constructor {
                name: n("PNat.succ"),
                type_: vlvl(&b, &r_pi(r_const("PNat"), r_const("PNat")), 0),
            },
        ],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(r, Err(NestedError::NotNested { .. })),
        "non-nested decl on the nested path must be NotNested, got {r:?}"
    );
}

#[test]
fn test_rosetree_block_manual_admits() {
    // Manually build the block [RoseTree, RoseTree._List] that the nested path
    // produces — a two-type block with a cross-type recursive field in
    // _List.cons (head : RoseTree targets motive 0, tail : _List targets motive
    // 1) — and admit it directly through add_inductive_mutual.
    let b = MinimalEnv::new()
        .with_const(n("RoseTree"), 0)
        .with_const(n("RoseTree._List"), 0)
        .with_const(n("RoseTree.mk"), 0)
        .with_const(n("RoseTree._List.nil"), 0)
        .with_const(n("RoseTree._List.cons"), 0);
    let rt_ty = vlvl(&b, &r_sort(1), 0);
    let lst_ty = vlvl(&b, &r_sort(1), 0);
    // RoseTree.mk : RoseTree._List -> RoseTree
    let rt_mk = Constructor {
        name: n("RoseTree.mk"),
        type_: vlvl(&b, &r_pi(r_const("RoseTree._List"), r_const("RoseTree")), 0),
    };
    // RoseTree._List.nil : RoseTree._List
    let lst_nil = Constructor {
        name: n("RoseTree._List.nil"),
        type_: vlvl(&b, &r_const("RoseTree._List"), 0),
    };
    // RoseTree._List.cons : RoseTree -> RoseTree._List -> RoseTree._List
    let lst_cons = Constructor {
        name: n("RoseTree._List.cons"),
        type_: vlvl(
            &b,
            &r_pi(
                r_const("RoseTree"),
                r_pi(r_const("RoseTree._List"), r_const("RoseTree._List")),
            ),
            0,
        ),
    };
    let block = MutualBlock {
        decls: vec![
            InductiveDecl {
                name: n("RoseTree"),
                num_level_params: 0,
                num_params: 0,
                type_: rt_ty,
                constructors: vec![rt_mk],
            },
            InductiveDecl {
                name: n("RoseTree._List"),
                num_level_params: 0,
                num_params: 0,
                type_: lst_ty,
                constructors: vec![lst_nil, lst_cons],
            },
        ],
    };
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, block).expect("manual RoseTree block admits");
    // Both recursors kernel-check.
    for ind in ["RoseTree", "RoseTree._List"] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }
}
