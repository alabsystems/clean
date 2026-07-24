// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! M2 targeted + adversarial tests (design §2, §5.2): inductive admission
//! (structural-identity idempotency, strict positivity incl. max-depth
//! stack-safety + chokepoint depth-DoS reject, universe constraint), the
//! subsingleton / large-elim gate
//! (Eq/And/False/Acc large-eliminate; Int.NonNeg + Or do NOT; a 2-ctor Prop
//! cannot derive a Type-recursor), recursor derivation (Nat.rec / Eq.rec type
//! shape + ι on zero/succ), and Elim typing.
//!
//! `Term`s for the inductive + constructor types are built through the
//! validation chokepoint against a *bootstrap* env that knows the relevant
//! names (so `ConstRef::mk` succeeds), then `add_inductive` is run on a fresh
//! `MinimalEnv` — exactly the producer→kernel boundary shape.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, AdmitError, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name, RawExpr,
    RawLevel, Term,
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
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}

/// Validate a closed raw term against `env` over `level_arity` universe params.
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

// ---------------------------------------------------------------------------
// Inductive fixtures. Each returns an InductiveDecl whose Terms are validated
// against a bootstrap env that knows the inductive + ctor names.
// ---------------------------------------------------------------------------

/// Bootstrap env: register `name`@`nlp`, plus each ctor name, as consts so their
/// types validate. Also registers any extra dependency consts.
fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}

/// `Nat : Type` with `Nat.zero : Nat`, `Nat.succ : Nat -> Nat`. num_params=0.
fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0); // Type 0
    let zero = Constructor {
        name: n("Nat.zero"),
        type_: vlvl(&b, &r_const("Nat"), 0),
    };
    let succ = Constructor {
        name: n("Nat.succ"),
        type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat")), 0),
    };
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![zero, succ],
    }
}

/// `List.{u} (A : Type u) : Type u` with `nil : List A`, `cons : A -> List A ->
/// List A`. num_params=1.
fn list_decl() -> InductiveDecl {
    let b = boot(&[("List", 1), ("List.nil", 1), ("List.cons", 1)]);
    // List : Type u -> Type u
    let ty = vlvl(&b, &r_pi(r_sort_param(0), r_sort_param(0)), 1);
    // nil : (A : Type u) -> List A
    let nil_ty = r_pi(
        r_sort_param(0),
        r_app(r_const_p("List", vec![RawLevel::Param(0)]), r_bvar(0)),
    );
    // cons : (A : Type u) -> A -> List A -> List A
    let list_a = |db: u32| r_app(r_const_p("List", vec![RawLevel::Param(0)]), r_bvar(db));
    let cons_ty = r_pi(
        r_sort_param(0), // A   (bvar increases inward)
        r_pi(r_bvar(0), r_pi(list_a(1), list_a(2))),
    );
    InductiveDecl {
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
    }
}

/// A binary `Tree : Type` with `leaf : Tree`, `node : Tree -> Tree -> Tree`.
fn tree_decl() -> InductiveDecl {
    let b = boot(&[("Tree", 0), ("Tree.leaf", 0), ("Tree.node", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    let leaf = Constructor {
        name: n("Tree.leaf"),
        type_: vlvl(&b, &r_const("Tree"), 0),
    };
    let node = Constructor {
        name: n("Tree.node"),
        type_: vlvl(
            &b,
            &r_pi(r_const("Tree"), r_pi(r_const("Tree"), r_const("Tree"))),
            0,
        ),
    };
    InductiveDecl {
        name: n("Tree"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![leaf, node],
    }
}

/// `False : Prop` with no constructors. Large-eliminates (subsingleton).
fn false_decl() -> InductiveDecl {
    let b = boot(&[("False", 0)]);
    InductiveDecl {
        name: n("False"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(0), 0),
        constructors: vec![],
    }
}

/// `And.{} (a b : Prop) : Prop` with `intro : a -> b -> And a b`. One ctor; both
/// fields are Prop → large-eliminates.
fn and_decl() -> InductiveDecl {
    let b = boot(&[("And", 0), ("And.intro", 0)]);
    // And : Prop -> Prop -> Prop
    let ty = vlvl(&b, &r_pi(r_sort(0), r_pi(r_sort(0), r_sort(0))), 0);
    // And.intro : (a : Prop) -> (b : Prop) -> a -> b -> And a b
    let intro_ty = r_pi(
        r_sort(0),
        r_pi(
            r_sort(0),
            r_pi(
                r_bvar(1), // a
                r_pi(
                    r_bvar(1), // b
                    r_apps(r_const("And"), vec![r_bvar(3), r_bvar(2)]),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("And"),
        num_level_params: 0,
        num_params: 2,
        type_: ty,
        constructors: vec![Constructor {
            name: n("And.intro"),
            type_: vlvl(&b, &intro_ty, 0),
        }],
    }
}

/// `Or.{} (a b : Prop) : Prop` with two ctors `inl : a -> Or a b`, `inr : b ->
/// Or a b`. Two constructors → does NOT large-eliminate.
fn or_decl() -> InductiveDecl {
    let b = boot(&[("Or", 0), ("Or.inl", 0), ("Or.inr", 0)]);
    let ty = vlvl(&b, &r_pi(r_sort(0), r_pi(r_sort(0), r_sort(0))), 0);
    let inl_ty = r_pi(
        r_sort(0),
        r_pi(
            r_sort(0),
            r_pi(r_bvar(1), r_apps(r_const("Or"), vec![r_bvar(2), r_bvar(1)])),
        ),
    );
    let inr_ty = r_pi(
        r_sort(0),
        r_pi(
            r_sort(0),
            r_pi(r_bvar(0), r_apps(r_const("Or"), vec![r_bvar(2), r_bvar(1)])),
        ),
    );
    InductiveDecl {
        name: n("Or"),
        num_level_params: 0,
        num_params: 2,
        type_: ty,
        constructors: vec![
            Constructor {
                name: n("Or.inl"),
                type_: vlvl(&b, &inl_ty, 0),
            },
            Constructor {
                name: n("Or.inr"),
                type_: vlvl(&b, &inr_ty, 0),
            },
        ],
    }
}

/// `Eq.{u} (A : Sort u) (a : A) : A -> Prop` with `refl : Eq A a a`. The single
/// non-Prop field `a` is a BARE INDEX of the result `Eq A a a` → large-elim.
/// (num_params = 2: A and a.)
fn eq_decl() -> InductiveDecl {
    let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
    // Eq : (A : Sort u) -> A -> A -> Prop
    let ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(r_bvar(1), r_sort(0))));
    // Eq.refl : (A : Sort u) -> (a : A) -> Eq A a a
    let refl_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_bvar(0), // a : A
            r_apps(
                r_const_p("Eq", vec![RawLevel::Param(0)]),
                vec![r_bvar(1), r_bvar(0), r_bvar(0)],
            ),
        ),
    );
    InductiveDecl {
        name: n("Eq"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &ty, 1),
        constructors: vec![Constructor {
            name: n("Eq.refl"),
            type_: vlvl(&b, &refl_ty, 1),
        }],
    }
}

/// `Acc.{u} (A : Sort u) (r : A -> A -> Prop) (x : A) : Prop` with
/// `intro : (x:A) -> ((y:A) -> r y x -> Acc A r y) -> Acc A r x`. The non-Prop
/// field `x` is the bare index of `Acc A r x` → large-eliminates. (num_params=2:
/// A, r. x is an index.)
fn acc_decl() -> InductiveDecl {
    let b = boot(&[("Acc", 1), ("Acc.intro", 1)]);
    // Acc : (A : Sort u) -> (r : A -> A -> Prop) -> A -> Prop
    let acc_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_pi(r_bvar(0), r_pi(r_bvar(1), r_sort(0))), // r : A -> A -> Prop
            r_pi(r_bvar(1), r_sort(0)),                  // (x : A) -> Prop
        ),
    );
    // Acc.intro : (A) (r) (x : A) -> ((y:A) -> r y x -> Acc A r y) -> Acc A r x
    // db at the IH point: A=.. r=.. x=.., y inside.
    let acc_app = |a: u32, rr: u32, idx: RawExpr| {
        r_apps(
            r_const_p("Acc", vec![RawLevel::Param(0)]),
            vec![r_bvar(a), r_bvar(rr), idx],
        )
    };
    // intro : (A:Sort u)(r:A->A->Prop)(x:A) -> ((y:A) -> r y x -> Acc A r y) -> Acc A r x
    let intro_ty = r_pi(
        r_sort_param(0), // A   bvar grows inward
        r_pi(
            r_pi(r_bvar(0), r_pi(r_bvar(1), r_sort(0))), // r
            r_pi(
                r_bvar(1), // x : A
                r_pi(
                    // (y : A) -> r y x -> Acc A r y
                    r_pi(
                        r_bvar(2), // y : A
                        r_pi(
                            r_apps(r_bvar(2), vec![r_bvar(0), r_bvar(1)]), // r y x
                            acc_app(4, 3, r_bvar(1)),                      // Acc A r y
                        ),
                    ),
                    acc_app(3, 2, r_bvar(1)), // Acc A r x
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("Acc"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &acc_ty, 1),
        constructors: vec![Constructor {
            name: n("Acc.intro"),
            type_: vlvl(&b, &intro_ty, 1),
        }],
    }
}

/// `Int.NonNeg : Int -> Prop` with `mk : (n : Nat) -> Int.NonNeg (Int.ofNat n)`.
/// The non-Prop field `n` is NOT a bare index (it sits under `Int.ofNat`), so
/// this does NOT large-eliminate. (num_params=0; Int is an index.)
fn int_nonneg_decl() -> (MinimalEnv, InductiveDecl) {
    // base env knows Int : Type, Int.ofNat : Nat -> Int, Nat : Type.
    let mut base = MinimalEnv::new()
        .with_const(n("Int"), 0)
        .with_const(n("Int.ofNat"), 0)
        .with_const(n("Nat"), 0);
    // type Int : Type 0 so field-sort inference resolves.
    let bb = boot(&[("Nat", 0)]);
    let int_ty = vlvl(&bb, &r_sort(1), 0);
    let nat_ty = vlvl(&bb, &r_sort(1), 0);
    let ofnat_ty = vlvl(
        &boot(&[("Nat", 0), ("Int", 0)]),
        &r_pi(r_const("Nat"), r_const("Int")),
        0,
    );
    base = base
        .with_const_typed(n("Int"), 0, int_ty)
        .with_const_typed(n("Nat"), 0, nat_ty)
        .with_const_typed(n("Int.ofNat"), 0, ofnat_ty);

    let b = boot(&[
        ("Int.NonNeg", 0),
        ("Int.NonNeg.mk", 0),
        ("Int", 0),
        ("Int.ofNat", 0),
        ("Nat", 0),
    ]);
    // Int.NonNeg : Int -> Prop
    let nn_ty = vlvl(&b, &r_pi(r_const("Int"), r_sort(0)), 0);
    // mk : (n : Nat) -> Int.NonNeg (Int.ofNat n)
    let mk_ty = vlvl(
        &b,
        &r_pi(
            r_const("Nat"),
            r_app(
                r_const("Int.NonNeg"),
                r_app(r_const("Int.ofNat"), r_bvar(0)),
            ),
        ),
        0,
    );
    let decl = InductiveDecl {
        name: n("Int.NonNeg"),
        num_level_params: 0,
        num_params: 0,
        type_: nn_ty,
        constructors: vec![Constructor {
            name: n("Int.NonNeg.mk"),
            type_: mk_ty,
        }],
    };
    (base, decl)
}

fn large_elim_of(env: &MinimalEnv, name: &str) -> bool {
    env.inductive_large_elim(&n(name))
        .expect("inductive registered")
}

// ===========================================================================
// Universe constraint
// ===========================================================================

#[test]
fn test_universe_constraint_rejects_oversized_field() {
    // Small : Type 0  with  mk : Type 0 -> Small. The field's sort is `Type 1`
    // (the type of `Type 0`), which exceeds the inductive's sort `Type 1`?  No:
    // `Type 0 : Type 1`, so the field sort is 1 and the inductive sort is 1 —
    // that is allowed. To force a violation, make the inductive `Type 0` but a
    // field live in `Type 0` (sort 1 > 0): `mk : (T : Type 0) -> Small`.
    let b = boot(&[("Small", 0), ("Small.mk", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0); // Small : Type 0  (sort = 1)
                                      // mk : (T : Type 0) -> Small.  field T : Type 0 has sort 1 > inductive sort?
                                      // inductive sort = 1 (Type 0). field sort = type-of(Type 0) = 2. 2 > 1 → reject.
    let mk_ty = vlvl(&b, &r_pi(r_sort(1), r_const("Small")), 0);
    let decl = InductiveDecl {
        name: n("Small"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Small.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::UniverseTooLarge { .. })),
        "field in Type 0 (sort 2) exceeds inductive Type 0 (sort 1): {r:?}"
    );
}

#[test]
fn test_prop_inductive_admits_large_field_impredicatively() {
    // A Prop inductive may quantify over a Type field (impredicativity): the
    // universe constraint is skipped for Prop. `P : Prop` with
    // `mk : (T : Type 0) -> P` must be admitted.
    let b = boot(&[("P", 0), ("P.mk", 0)]);
    let ty = vlvl(&b, &r_sort(0), 0); // P : Prop
    let mk_ty = vlvl(&b, &r_pi(r_sort(1), r_const("P")), 0); // (T : Type 0) -> P
    let decl = InductiveDecl {
        name: n("P"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("P.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, decl).expect("Prop inductive admits large field impredicatively");
}

// ===========================================================================
// Positivity
// ===========================================================================

#[test]
fn test_positivity_accepts_nat_list_tree() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admitted");
    let mut env2 = MinimalEnv::new();
    add_inductive(&mut env2, list_decl()).expect("List admitted");
    let mut env3 = MinimalEnv::new();
    add_inductive(&mut env3, tree_decl()).expect("Tree admitted");
}

#[test]
fn test_positivity_rejects_bad_arrow_to_self() {
    // Bad : (Bad -> Bad) -> Bad   — Bad occurs left of an arrow in the field.
    let b = boot(&[("Bad", 0), ("Bad.mk", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    let mk_ty = vlvl(
        &b,
        &r_pi(r_pi(r_const("Bad"), r_const("Bad")), r_const("Bad")),
        0,
    );
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
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::NonPositive { .. })),
        "expected NonPositive, got {r:?}"
    );
}

#[test]
fn test_positivity_rejects_nested_negative() {
    // Bad2 : ((Bad2 -> X) -> X) -> Bad2  — Bad2 negative under double arrow.
    let b = boot(&[("Bad2", 0), ("Bad2.mk", 0), ("X", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    // field: (Bad2 -> X) -> X
    let field = r_pi(r_pi(r_const("Bad2"), r_const("X")), r_const("X"));
    let mk_ty = vlvl(&b, &r_pi(field, r_const("Bad2")), 0);
    let decl = InductiveDecl {
        name: n("Bad2"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Bad2.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::NonPositive { .. })),
        "expected NonPositive, got {r:?}"
    );
}

/// Run `f` on a worker thread with a large (256 MiB) stack so the *recursive*
/// helpers in the test harness (`validate`, `Term`'s `Drop`) and the recursive
/// decision-core passes can build/walk a genuinely 20k-deep term — isolating the
/// question "does the iterative *positivity* check overflow" from the thread
/// stack limit. The positivity routine itself uses an explicit work stack, so it
/// never grows the native stack.
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("join");
}

#[test]
fn test_positivity_stack_safe_max_depth_admitted() {
    on_big_stack(|| {
        // A constructor type that is a right-nested Pi chain at the *deepest
        // admissible* depth (MAX_VALIDATE_DEPTH arrows), each domain a harmless
        // `Type`. The chokepoint admits it (it is exactly at the cap) and the
        // iterative positivity check must not overflow. `on_big_stack` gives the
        // *recursive* `validate_rec`/`Drop` room; the point under test is that
        // positivity itself (explicit work stack) stays flat.
        let depth = clean_ck0::MAX_VALIDATE_DEPTH;
        let b = boot(&[("Deep", 0), ("Deep.mk", 0)]);
        let ty = vlvl(&b, &r_sort(1), 0);
        let mut field_chain = r_const("Deep"); // return type
                                               // The whole ctor type's depth must stay <= cap: the chain is `depth`
                                               // Pi nodes ending in a Const, so use `depth - 1` arrows to leave room
                                               // for the leaf and stay within the cap.
        for _ in 0..(depth - 1) {
            field_chain = r_pi(r_sort(0), field_chain);
        }
        let mk_ty = vlvl(&b, &field_chain, 0);
        let decl = InductiveDecl {
            name: n("Deep"),
            num_level_params: 0,
            num_params: 0,
            type_: ty,
            constructors: vec![Constructor {
                name: n("Deep.mk"),
                type_: mk_ty,
            }],
        };
        let mut env = MinimalEnv::new();
        add_inductive(&mut env, decl).expect("max-depth positive ctor admitted");
    });
}

#[test]
fn test_chokepoint_rejects_overdeep_term_no_abort() {
    // A ~50k-deep right-nested Pi chain: the chokepoint must REJECT it with a
    // verdict (MaxDepthExceeded), not SIGABRT. This is the depth-DoS regression:
    // before the fix, `validate`'s native recursion (and the downstream nested
    // helpers + `Term::Drop`) overflowed the native stack and aborted the
    // process. The iterative depth gate now fails it closed. Run on a big stack
    // only so the *untrusted RawExpr's own recursive `Drop`* (owned by this
    // caller, not the kernel) has room — `validate` returns Err iteratively
    // regardless of stack size.
    on_big_stack(|| {
        let mut chain = RawExpr::Sort(RawLevel::Zero);
        for _ in 0..50_000u32 {
            chain = r_pi(r_sort(0), chain);
        }
        let env = MinimalEnv::new();
        let r = Term::validate_closed(&env, &chain);
        assert!(
            matches!(r, Err(clean_ck0::ValidateError::MaxDepthExceeded { .. })),
            "expected MaxDepthExceeded (verdict, not abort), got {r:?}"
        );
    });
}

#[test]
fn test_positivity_stack_safe_max_depth_negative_rejected() {
    on_big_stack(|| {
        // A chain at the deepest admissible depth then a negative occurrence:
        // must still be detected (stack-safe AND fail-closed). The negative
        // field is the OUTERMOST so positivity rejects it. Depth stays within
        // the chokepoint cap so the term validates and positivity is what does
        // the rejecting (a deeper term would be rejected earlier, at the
        // chokepoint — see `test_chokepoint_rejects_overdeep_term_no_abort`).
        let b = boot(&[("DeepN", 0), ("DeepN.mk", 0)]);
        let ty = vlvl(&b, &r_sort(1), 0);
        let mut chain = r_const("DeepN");
        // Reserve depth for the prepended negative field (`(DeepN -> DeepN) ->
        // ...`, which adds 3 levels) and the leaf, so the full ctor type stays
        // at or below the cap.
        for _ in 0..(clean_ck0::MAX_VALIDATE_DEPTH - 5) {
            chain = r_pi(r_sort(0), chain);
        }
        // prepend the negative field (DeepN -> DeepN).
        let mk_ty = vlvl(
            &b,
            &r_pi(r_pi(r_const("DeepN"), r_const("DeepN")), chain),
            0,
        );
        let decl = InductiveDecl {
            name: n("DeepN"),
            num_level_params: 0,
            num_params: 0,
            type_: ty,
            constructors: vec![Constructor {
                name: n("DeepN.mk"),
                type_: mk_ty,
            }],
        };
        let mut env = MinimalEnv::new();
        let r = add_inductive(&mut env, decl);
        assert!(
            matches!(r, Err(AdmitError::NonPositive { .. })),
            "expected NonPositive at depth, got {r:?}"
        );
    });
}

// ===========================================================================
// Structural-identity idempotency / conflict
// ===========================================================================

#[test]
fn test_idempotent_readd_identical_ok() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("first add");
    // Re-adding a byte/structurally-identical Nat is idempotent-OK.
    add_inductive(&mut env, nat_decl()).expect("idempotent re-add");
}

#[test]
fn test_conflicting_redeclaration_rejected() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("first add");
    // Same name, different type (Prop instead of Type) → Conflict.
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    let mut bad = nat_decl();
    bad.type_ = vlvl(&b, &r_sort(0), 0); // Nat : Prop now
    let r = add_inductive(&mut env, bad);
    assert!(
        matches!(r, Err(AdmitError::Conflict { .. })),
        "expected Conflict, got {r:?}"
    );
}

// ===========================================================================
// Subsingleton / large-elim gate (THE soundness gate, §2)
// ===========================================================================

#[test]
fn test_false_large_eliminates() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, false_decl()).expect("False admitted");
    assert!(large_elim_of(&env, "False"), "False must large-eliminate");
}

#[test]
fn test_and_large_eliminates() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, and_decl()).expect("And admitted");
    assert!(large_elim_of(&env, "And"), "And must large-eliminate");
}

#[test]
fn test_eq_large_eliminates() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, eq_decl()).expect("Eq admitted");
    assert!(large_elim_of(&env, "Eq"), "Eq must large-eliminate");
}

#[test]
fn test_acc_large_eliminates() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, acc_decl()).expect("Acc admitted");
    assert!(
        large_elim_of(&env, "Acc"),
        "Acc must large-eliminate (x is the bare index of Acc A r x)"
    );
}

#[test]
fn test_or_does_not_large_eliminate() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, or_decl()).expect("Or admitted");
    assert!(
        !large_elim_of(&env, "Or"),
        "Or must NOT large-eliminate (two constructors)"
    );
}

#[test]
fn test_int_nonneg_does_not_large_eliminate() {
    let (mut env, decl) = int_nonneg_decl();
    add_inductive(&mut env, decl).expect("Int.NonNeg admitted");
    assert!(
        !large_elim_of(&env, "Int.NonNeg"),
        "Int.NonNeg must NOT large-eliminate (n is under Int.ofNat, not a bare index)"
    );
}

#[test]
fn test_two_ctor_prop_recursor_is_prop_only() {
    // A 2-ctor Prop CANNOT derive a Type-eliminating recursor: its recursor's
    // level-param count is exactly num_level_params(I) (no extra motive level).
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, or_decl()).expect("Or admitted");
    // Or has num_level_params = 0; a large-elim recursor would have 1.
    // The recursor const is registered with its level-param count.
    assert_eq!(
        env.num_level_params(&n("Or.rec")),
        Some(0),
        "Or.rec must carry NO extra motive universe param (Prop-only elim)"
    );
}

#[test]
fn test_large_elim_recursor_has_extra_level_param() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, eq_decl()).expect("Eq admitted");
    // Eq has num_level_params = 1; large-elim adds the motive level → 2.
    assert_eq!(
        env.num_level_params(&n("Eq.rec")),
        Some(2),
        "Eq.rec must carry the extra motive universe param (large elim)"
    );
}

// ===========================================================================
// num_params structural validation (the gate-level soundness pre-check, §2/§12)
// ===========================================================================

#[test]
fn test_overdeclared_num_params_hides_field_rejected_at_gate() {
    // ADVERSARIAL (the confirmed finding): `Bad : Prop` with the single ctor
    // `Bad.mk : (T : Type 0) -> Bad`. The HONEST num_params is 0 (T is a genuine
    // data field). A producer that lies `num_params = 1` would, with the old
    // gate, drop T from the field set before the subsingleton analysis runs,
    // making `Bad` falsely large-eliminate (immediate CIC inconsistency).
    //
    // The fix must reject this AT THE GATE with a params-shape error, NOT merely
    // bounce it downstream off the recursor kernel-check.
    let b = boot(&[("Bad", 0), ("Bad.mk", 0)]);
    let ty = vlvl(&b, &r_sort(0), 0); // Bad : Prop
                                      // Bad.mk : (T : Type 0) -> Bad
    let mk_ty = vlvl(&b, &r_pi(r_sort(1), r_const("Bad")), 0);
    let decl = InductiveDecl {
        name: n("Bad"),
        num_level_params: 0,
        num_params: 1, // THE LIE — honest value is 0.
        type_: ty,
        constructors: vec![Constructor {
            name: n("Bad.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::MalformedParams { .. })),
        "over-declared num_params must be rejected AT THE GATE with MalformedParams \
         (not a downstream Derivation error), got {r:?}"
    );
}

#[test]
fn test_honest_num_params_zero_data_field_prop_is_prop_only() {
    // The HONEST counterpart: same `Bad : Prop`, ctor `(T : Type 0) -> Bad`, but
    // num_params = 0 (truthful). This is admissible (impredicative Prop field)
    // and the gate must correctly classify it as Prop-ONLY (T is a non-Prop data
    // field that is NOT a bare index), i.e. it does NOT large-eliminate.
    let b = boot(&[("Honest", 0), ("Honest.mk", 0)]);
    let ty = vlvl(&b, &r_sort(0), 0);
    let mk_ty = vlvl(&b, &r_pi(r_sort(1), r_const("Honest")), 0);
    let decl = InductiveDecl {
        name: n("Honest"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Honest.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, decl).expect("honest num_params=0 Prop with a data field admits");
    assert!(
        !large_elim_of(&env, "Honest"),
        "with honest num_params the non-Prop data field T is visible: Prop-only elimination"
    );
}

#[test]
fn test_num_params_exceeds_inductive_arity_rejected() {
    // `num_params` larger than the inductive type's own Pi arity is structurally
    // impossible (no such parameters exist). Nat : Type has arity 0; claiming 1
    // param must be rejected.
    let mut decl = nat_decl();
    decl.num_params = 1; // Nat : Type 0 has zero leading Pi binders.
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::MalformedParams { .. })),
        "num_params exceeding the inductive's Pi arity must be MalformedParams, got {r:?}"
    );
}

#[test]
fn test_overdeclared_num_params_on_real_param_inductive_rejected() {
    // `List.{u} (A : Type u)` honestly has num_params = 1. Lying num_params = 2
    // would try to treat the `cons` field `(_ : A)` as a uniform parameter — but
    // it is NOT a bare index of the result `List A` (the result applies List to
    // only ONE arg). Must be MalformedParams, caught at the gate.
    let mut decl = list_decl();
    decl.num_params = 2; // honest value is 1.
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::MalformedParams { .. })),
        "over-declared num_params on a real 1-param inductive must be MalformedParams, got {r:?}"
    );
}

#[test]
fn test_underdeclared_num_params_still_well_formed_for_eq() {
    // Robustness: Eq honestly has num_params = 2 (A and a). Declaring num_params
    // = 1 (only A is a "param", a becomes an index/field) is still a uniform,
    // well-formed shape — A is the bare index #0 of `Eq A a a`. It must pass the
    // structural validator (whether it large-eliminates is then the gate's
    // separate decision; we only assert it is NOT rejected as MalformedParams).
    let mut decl = eq_decl();
    decl.num_params = 1;
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        !matches!(r, Err(AdmitError::MalformedParams { .. })),
        "a uniform under-declared num_params (param A is a bare index) must not be \
         MalformedParams, got {r:?}"
    );
}

// ===========================================================================
// Recursor type shape (Nat / Eq)
// ===========================================================================

#[test]
fn test_nat_rec_type_is_well_typed_and_shaped() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admitted");
    // Nat.rec exists, large-eliminates (Type-valued inductive), level params = 1.
    assert_eq!(env.num_level_params(&n("Nat.rec")), Some(1));
    let rec_ty = env.recursor_type(&n("Nat")).expect("rec type stored");
    // Kernel-check the stored recursor type: it must infer a sort cleanly.
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
        .expect("Nat.rec type is a well-formed type");
    // Shape: Nat.rec : {motive : Nat -> Sort u} -> motive Nat.zero ->
    //   ((n : Nat) -> motive n -> motive (Nat.succ n)) -> (t : Nat) -> motive t
    // Count the top-level Pi binders: motive, 2 minors, major = 4.
    let mut count = 0u32;
    let mut cur = rec_ty.clone();
    while let clean_ck0::term::TermKind::Pi(_, _, codom) = cur.kind() {
        count += 1;
        cur = codom.clone();
    }
    assert_eq!(count, 4, "Nat.rec telescope = motive + 2 minors + major");
}

#[test]
fn test_eq_rec_type_is_well_typed() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, eq_decl()).expect("Eq admitted");
    let rec_ty = env.recursor_type(&n("Eq")).expect("rec type stored");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
        .expect("Eq.rec type is a well-formed type");
}

// ===========================================================================
// Nat.rec ι-reduction on zero and succ
// ===========================================================================

#[test]
fn test_nat_rec_iota_on_zero_and_succ() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admitted");

    // Build: Nat.rec @{0} (motive := λ_. Nat) (z := Nat.zero)
    //   (s := λ n ih. Nat.succ ih) (major)
    // Motive into Type? We'll eliminate into a small motive `λ _:Nat. Nat`,
    // major over zero then succ zero, checking the result reduces.
    // motive = λ (_ : Nat). Nat
    let r_motive = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Nat")),
        Box::new(r_const("Nat")),
    );
    // z = Nat.zero
    let r_z = r_const("Nat.zero");
    // s = λ (n : Nat) (ih : Nat). Nat.succ ih
    let r_s = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Nat")),
        Box::new(RawExpr::Lam(
            BinderInfo::Default,
            Box::new(r_const("Nat")),
            Box::new(r_app(r_const("Nat.succ"), r_bvar(0))),
        )),
    );
    // Elim head: Nat large-eliminates → motive level + (no ind levels).
    let elim = RawExpr::Elim(n("Nat"), RawLevel::Succ(Box::new(RawLevel::Zero)), vec![]);

    // rec applied to zero: Nat.rec motive z s Nat.zero  ~>  z = Nat.zero
    let app_zero = r_apps(
        elim.clone(),
        vec![
            r_motive.clone(),
            r_z.clone(),
            r_s.clone(),
            r_const("Nat.zero"),
        ],
    );
    let t_zero = Term::validate_closed(&env, &app_zero).expect("validates");
    let mut budget = Budget::default_budget();
    let w = clean_ck0::whnf(&env, &t_zero, &mut budget).expect("whnf");
    let expected_zero = Term::validate_closed(&env, &r_const("Nat.zero")).expect("z");
    assert_eq!(w, expected_zero, "Nat.rec on zero ~> z");

    // rec applied to (succ zero): the succ ι-rule fires →
    //   s zero (rec motive z s zero) = Nat.succ (rec motive z s zero).
    // WHNF only reduces the head, so the result is `Nat.succ (rec ... zero)`
    // (head = Nat.succ). It is def-eq to `Nat.succ Nat.zero` once the inner
    // recursor on zero reduces — checked via is_def_eq (full conversion).
    let succ_zero = r_app(r_const("Nat.succ"), r_const("Nat.zero"));
    let app_succ = r_apps(elim, vec![r_motive, r_z, r_s, succ_zero]);
    let t_succ = Term::validate_closed(&env, &app_succ).expect("validates");
    let mut budget2 = Budget::default_budget();
    let w2 = clean_ck0::whnf(&env, &t_succ, &mut budget2).expect("whnf");
    // Head must be Nat.succ applied to one arg.
    let (h2, a2) = w2.unfold_apps();
    assert!(
        matches!(h2.kind(), clean_ck0::term::TermKind::Const(c) if *c.name() == n("Nat.succ")),
        "Nat.rec on (succ zero) whnf head is Nat.succ"
    );
    assert_eq!(a2.len(), 1, "succ applied to one arg");
    // Full conversion: the whole thing is def-eq to `Nat.succ Nat.zero`.
    let expected_succ =
        Term::validate_closed(&env, &r_app(r_const("Nat.succ"), r_const("Nat.zero")))
            .expect("succ zero");
    let mut budget3 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &t_succ, &expected_succ, &mut budget3).expect("def_eq"),
        "Nat.rec on (succ zero) is def-eq to succ zero"
    );
}

// ===========================================================================
// List.rec ι-reduction at a CONCRETE level through a RECURSIVE minor
// (regression guard for the recursive-ι level-instantiation fix in
// whnf::try_iota — the embedded IH sub-recursor must land at the firing Elim's
// CONCRETE levels, not the rule's generic `Param(0)…`).
// ===========================================================================

#[test]
fn test_list_rec_iota_at_concrete_level_recursive_minor() {
    // Admit Nat and the level-polymorphic `List.{u} (A : Type u)`. We then build
    // an IDENTITY-FOLD recursor over a concrete 2-element `List Nat`, eliminating
    // at the CONCRETE level u = 1 (NOT a `Param`). The cons minor reconstructs
    // `List.cons Nat head ih`, so the IH (`ih`) is itself a `List.rec` call that
    // must recursively ι-reduce — and that embedded IH sub-recursor is the exact
    // regression surface: before the fix it kept the rule's generic `Param(0)…`
    // levels (instead of the firing Elim's concrete `{1}`), producing a
    // level-wrong term → TypeMismatch / not def-eq.
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admitted");
    add_inductive(&mut env, list_decl()).expect("List admitted");

    // The concrete element type and a few `List Nat` builders, all at level {1}.
    let one = RawLevel::Succ(Box::new(RawLevel::Zero));
    let r_list_nat = || r_app(r_const_p("List", vec![one.clone()]), r_const("Nat"));
    let r_nil = || r_app(r_const_p("List.nil", vec![one.clone()]), r_const("Nat"));
    // cons Nat h t  (List.cons : (A : Type u) -> A -> List A -> List A)
    let r_cons = |h: RawExpr, t: RawExpr| {
        r_apps(
            r_const_p("List.cons", vec![one.clone()]),
            vec![r_const("Nat"), h, t],
        )
    };
    // The concrete 2-element list  [Nat.zero, Nat.succ Nat.zero] : List Nat.
    let one_nat = r_app(r_const("Nat.succ"), r_const("Nat.zero"));
    let original = r_cons(r_const("Nat.zero"), r_cons(one_nat.clone(), r_nil()));

    // Identity-fold: List.{1}.rec
    //   (motive := fun _ : List Nat => List Nat)
    //   (nil-minor := List.nil Nat)
    //   (cons-minor := fun (head : Nat) (tail : List Nat) (ih : List Nat) =>
    //        List.cons Nat head ih)
    //   Nat            -- the single param A
    //   <major>
    // List is large-eliminating (List : Type u), so the Elim level vector is
    // [motive_level, ind_level]. The motive lands in `List.{1} Nat : Sort 1`,
    // hence motive_level = 1; the inductive level is the CONCRETE 1.
    let motive = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_list_nat()),
        Box::new(r_list_nat()),
    );
    let nil_minor = r_nil();
    // cons minor binds (head, tail, ih) innermost-last: head=bvar2, tail=bvar1,
    // ih=bvar0. The identity fold rebuilds `cons head ih` (drops/recurses tail
    // through ih).
    let cons_minor = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(r_const("Nat")), // head : Nat
        Box::new(RawExpr::Lam(
            BinderInfo::Default,
            Box::new(r_list_nat()), // tail : List Nat
            Box::new(RawExpr::Lam(
                BinderInfo::Default,
                Box::new(r_list_nat()),                 // ih : List Nat
                Box::new(r_cons(r_bvar(2), r_bvar(0))), // List.cons Nat head ih
            )),
        )),
    );
    // Elim head at CONCRETE levels: motive_level = Sort 1, ind_levels = [1].
    let elim = RawExpr::Elim(n("List"), one.clone(), vec![one.clone()]);
    let fold = r_apps(
        elim,
        vec![
            r_const("Nat"), // param A := Nat
            motive,
            nil_minor,
            cons_minor,
            original.clone(), // major: the concrete 2-element list
        ],
    );

    let t_fold = Term::validate_closed(&env, &fold).expect("identity-fold validates");
    let t_orig = Term::validate_closed(&env, &original).expect("original list validates");

    // (a) Soundness sanity: the fold fully recursively ι-reduces (through the
    // recursive cons minor, at concrete level 1) to the original list — def-eq.
    // This must hold on the FIXED kernel; it confirms the construction genuinely
    // exercises a recursive minor that bottoms out correctly. (On its own this is
    // NOT a tight pre-fix discriminator — this non-dependent identity fold's final
    // value is rebuilt from the minor's own concrete-level `List.cons`, so the
    // Param-level IH recursor reduces away benignly; the tight discriminator is
    // the structural witness (c) below.)
    let mut budget = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &t_fold, &t_orig, &mut budget).expect("def_eq"),
        "List.{{1}}.rec identity-fold over a 2-element list is def-eq to the original \
         (recursive ι at concrete level 1 through the cons minor)"
    );

    // (b) Soundness sanity: the fold's type infers to `List.{1} Nat`.
    let mut budget2 = Budget::default_budget();
    let inferred = clean_ck0::infer(&env, &t_fold, &mut budget2).expect("fold infers");
    let list_nat = Term::validate_closed(&env, &r_list_nat()).expect("List Nat type");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &list_nat, &mut budget2).expect("def_eq"),
        "the identity-fold's type is List.{{1}} Nat"
    );

    // (c) THE load-bearing regression guard. A single whnf step fires the cons
    // ι-rule and exposes `List.cons Nat head (ih …)`, where the IH is the embedded
    // sub-recursor `List.rec <levels> …` that the rule RHS carries. With the fix,
    // the rule RHS's generic level params are instantiated with the firing Elim's
    // CONCRETE levels before being applied, so that embedded `List.rec` carries
    // `{1, 1}` (each level a `Succ`/`Zero`, Param-FREE). PRE-FIX (the discarded
    // bug) the IH recursor kept the rule's generic `{Param(0), Param(1)}` — which
    // this test catches directly. The IH recursor appears as a recursor-named
    // `Const` (the kernel-derived RHS form; recognized via `Env::is_recursor`,
    // exactly as `whnf::try_iota` itself recognizes it) and/or an `Elim`.
    let mut budget3 = Budget::default_budget();
    let w = clean_ck0::whnf(&env, &t_fold, &mut budget3).expect("whnf");
    let (head, _args) = w.unfold_apps();
    assert!(
        matches!(head.kind(), clean_ck0::term::TermKind::Const(c) if *c.name() == n("List.cons")),
        "one ι-step of the identity-fold exposes a `List.cons` head"
    );
    // Walk the one-whnf-step term; count embedded IH recursor references and
    // assert each carries only concrete (Param-free) levels. The count guards the
    // walk against vacuously passing (it must actually FIND the IH recursor that
    // pre-fix would carry a Param).
    let mut recursor_refs = 0usize;
    walk_recursor_levels_concrete(&env, &w, &mut recursor_refs);
    assert!(
        recursor_refs >= 1,
        "the one-whnf-step fold must contain the embedded IH `List.rec` recursor \
         reference to inspect (else the level guard is vacuous)"
    );
}

/// Recursively walk `t`, and for every embedded recursor reference (a
/// recursor-named `Const` — the kernel-derived ι-rule RHS form — or an `Elim`),
/// assert its levels are Param-FREE and bump `count`. This is the structural
/// witness of the recursive-ι level-instantiation fix: pre-fix the embedded IH
/// `List.rec` carried the rule's generic `Param(_)` levels.
fn walk_recursor_levels_concrete(env: &MinimalEnv, t: &Term, count: &mut usize) {
    use clean_ck0::term::TermKind;
    match t.kind() {
        TermKind::Const(cref) if env.is_recursor(cref.name()) => {
            *count += 1;
            for lvl in cref.levels() {
                assert!(
                    !level_has_param(lvl),
                    "embedded IH recursor `{}` must carry CONCRETE levels (no Param), got {lvl:?}",
                    cref.name()
                );
            }
        }
        TermKind::Elim(eref) => {
            *count += 1;
            for lvl in eref.levels() {
                assert!(
                    !level_has_param(lvl),
                    "embedded IH recursor (Elim {}) must carry CONCRETE levels (no Param), \
                     got {lvl:?}",
                    eref.inductive()
                );
            }
        }
        TermKind::App(f, a) => {
            walk_recursor_levels_concrete(env, f, count);
            walk_recursor_levels_concrete(env, a, count);
        }
        TermKind::Lam(_, dom, body) | TermKind::Pi(_, dom, body) => {
            walk_recursor_levels_concrete(env, dom, count);
            walk_recursor_levels_concrete(env, body, count);
        }
        TermKind::Let(ty, val, body) => {
            walk_recursor_levels_concrete(env, ty, count);
            walk_recursor_levels_concrete(env, val, count);
            walk_recursor_levels_concrete(env, body, count);
        }
        TermKind::Proj(_, _, inner) => walk_recursor_levels_concrete(env, inner, count),
        _ => {}
    }
}

/// True iff `level` mentions any universe `Param`. The kernel does not expose a
/// param predicate publicly, so this test-only helper inspects the `Debug` form
/// (derived `Repr::Param(_)` renders as `Param(..)`), keeping it independent of
/// `Level`'s private representation.
fn level_has_param(level: &clean_ck0::Level) -> bool {
    format!("{level:?}").contains("Param")
}

// ===========================================================================
// Elim typing (M2)
// ===========================================================================

#[test]
fn test_elim_typing_matches_derived_recursor_type() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admitted");
    // Build a bare Elim head and infer its type; it must equal the stored
    // recursor type instantiated with the elim's derived levels (motive=Type0).
    let elim = RawExpr::Elim(n("Nat"), RawLevel::Succ(Box::new(RawLevel::Zero)), vec![]);
    let t = Term::validate_closed(&env, &elim).expect("elim validates");
    let mut budget = Budget::default_budget();
    let inferred = clean_ck0::infer(&env, &t, &mut budget).expect("Elim infers");
    // The inferred type is the recursor type with motive-level = Sort 1; it must
    // itself be a well-formed type (sort-checkable).
    clean_ck0::infer_sort_in_context(&env, &[], &inferred, &mut budget)
        .expect("inferred Elim type is well-formed");
    // Top-level it must be a Pi (the motive binder).
    assert!(
        matches!(inferred.kind(), clean_ck0::term::TermKind::Pi(_, _, _)),
        "Nat.rec type starts with the motive Pi"
    );
}

#[test]
fn test_mutual_nested_rejected_unsupported() {
    // A nested occurrence (List Self inside a ctor field) is M3 — rejected with
    // a clear Unsupported error, never a fake recursor.
    let b = boot(&[("Rose", 0), ("Rose.mk", 0), ("List", 1)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    // mk : List Rose -> Rose   (nested: Rose under List)
    let field = r_app(r_const_p("List", vec![RawLevel::Zero]), r_const("Rose"));
    let mk_ty = vlvl(&b, &r_pi(field, r_const("Rose")), 0);
    let decl = InductiveDecl {
        name: n("Rose"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Rose.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new().with_const(n("List"), 1);
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(AdmitError::Unsupported { .. })),
        "expected Unsupported (nested), got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// STRUCTURE-η registration gating (soundness): `structure_info` is populated
// (licensing structure-η in def_eq AND the recursor ι-rule) ONLY for a genuine
// η-structure — exactly 1 ctor, NO indices, NON-recursive. An indexed or
// recursive single-ctor inductive must NOT be registered, or structure-η would
// become a false-accept (`mk (proj t) ≢ t`).
// ---------------------------------------------------------------------------

/// A genuine η-structure: `Pack.{u} (α : Sort u) : Sort u` with
/// `mk : (a : α) -> Pack α`. 1 ctor, 0 indices, non-recursive (field `a : α`
/// does not mention `Pack`). num_params = 1.
fn pack_decl() -> InductiveDecl {
    let b = boot(&[("Pack", 1), ("Pack.mk", 1)]);
    // Pack : (α : Sort u) -> Sort u
    let ty = r_pi(r_sort_param(0), r_sort_param(0));
    // Pack.mk : (α : Sort u) -> (a : α) -> Pack α
    let mk_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_bvar(0), // a : α
            r_app(r_const_p("Pack", vec![RawLevel::Param(0)]), r_bvar(1)),
        ),
    );
    InductiveDecl {
        name: n("Pack"),
        num_level_params: 1,
        num_params: 1,
        type_: vlvl(&b, &ty, 1),
        constructors: vec![Constructor {
            name: n("Pack.mk"),
            type_: vlvl(&b, &mk_ty, 1),
        }],
    }
}

/// A RECURSIVE single-ctor, non-indexed inductive: `Wrap : Type` with
/// `Wrap.mk : Wrap -> Wrap` (strictly positive, admitted). It is NOT an
/// η-structure — its field is recursive, so `mk (proj t) ≢ t`.
fn wrap_decl() -> InductiveDecl {
    let b = boot(&[("Wrap", 0), ("Wrap.mk", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0); // Type 0
    let mk_ty = vlvl(&b, &r_pi(r_const("Wrap"), r_const("Wrap")), 0);
    InductiveDecl {
        name: n("Wrap"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Wrap.mk"),
            type_: mk_ty,
        }],
    }
}

#[test]
fn test_structure_info_registered_for_genuine_eta_structure() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, pack_decl()).expect("Pack admitted");
    let info = env
        .structure_info(&n("Pack"))
        .expect("Pack IS a genuine η-structure (1 ctor, no indices, non-recursive)");
    assert_eq!(info.ctor, n("Pack.mk"));
    assert_eq!(info.num_params, 1);
    assert_eq!(info.num_fields, 1);
}

#[test]
fn test_structure_info_not_registered_for_indexed_single_ctor() {
    // `Eq` is a single-constructor inductive but an INDEXED family (num_indices
    // == 1). Structure-η on `Eq` would be UNSOUND, so it must NOT be registered.
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, eq_decl()).expect("Eq admitted");
    assert!(
        env.structure_info(&n("Eq")).is_none(),
        "Eq is INDEXED: structure-η must NOT be enabled (false-accept guard)"
    );
}

#[test]
fn test_structure_info_not_registered_for_recursive_single_ctor() {
    // `Wrap : Type` with `mk : Wrap -> Wrap` is a single-ctor, non-indexed, but
    // RECURSIVE inductive. Its field is not projection-recoverable in the η sense
    // (`mk (proj t) ≢ t`), so it must NOT be registered as a structure.
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, wrap_decl()).expect("Wrap admitted");
    assert!(
        env.structure_info(&n("Wrap")).is_none(),
        "Wrap is RECURSIVE: structure-η must NOT be enabled (false-accept guard)"
    );
}

#[test]
fn test_structure_info_not_registered_for_multi_ctor() {
    // A 2-constructor inductive (`Or`) is never a structure: structure-η would
    // collapse distinct injections. Must NOT be registered.
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, or_decl()).expect("Or admitted");
    assert!(
        env.structure_info(&n("Or")).is_none(),
        "Or has 2 ctors: structure-η must NOT be enabled"
    );
}

#[test]
fn test_structure_eta_holds_for_pack_and_function_over_it() {
    // POSITIVE structure-η through the real admission path: for a neutral
    // `s : Pack Nat`, `s ≡ Pack.mk Nat s.0`, and a function applied to `s` equals
    // the function applied to its η-expansion.
    let mut env = MinimalEnv::new();
    // `Nat : Type 0` as a plain const so `Pack Nat` types (we only need a closed
    // element type for the structure, not Nat's inductive machinery).
    let nat_ty = vlvl(&MinimalEnv::new(), &r_sort(1), 0);
    env = env.with_const_typed(n("Nat"), 0, nat_ty);
    add_inductive(&mut env, pack_decl()).expect("Pack admitted");
    // s : Pack Nat (opaque const). (Pack Nat : Type 0 since Nat : Type 0.)
    let pack_nat = r_app(r_const_p("Pack", vec![RawLevel::Zero]), r_const("Nat"));
    let pack_nat_t = vlvl(&env, &pack_nat, 0);
    env = env.with_const_typed(n("s"), 0, pack_nat_t);
    // f : Pack Nat -> Nat (opaque).
    let f_ty = r_pi(pack_nat.clone(), r_const("Nat"));
    let f_ty_t = vlvl(&env, &f_ty, 0);
    env = env.with_const_typed(n("f"), 0, f_ty_t);

    let s = vlvl(&env, &r_const("s"), 0);
    let s_eta = r_apps(
        r_const_p("Pack.mk", vec![RawLevel::Zero]),
        vec![r_const("Nat"), r_proj("Pack", 0, r_const("s"))],
    );
    let s_eta_t = vlvl(&env, &s_eta, 0);
    let mut b = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &s, &s_eta_t, &mut b).expect("deq"),
        "structure-η: s ≡ Pack.mk Nat s.0"
    );

    // f s ≡ f (Pack.mk Nat s.0).
    let f_s = vlvl(&env, &r_app(r_const("f"), r_const("s")), 0);
    let f_s_eta = vlvl(&env, &r_app(r_const("f"), s_eta), 0);
    let mut b2 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &f_s, &f_s_eta, &mut b2).expect("deq"),
        "structure-η under application: f s ≡ f (Pack.mk Nat s.0)"
    );
}

#[test]
fn test_indexed_distinct_terms_stay_distinct_no_eta_overaccept() {
    // NEGATIVE / over-accept guard: with `Eq` admitted (and NOT registered as a
    // structure), two genuinely different proof terms of DIFFERENT Eq types stay
    // distinct — structure-η does not fire to wrongly equate them. We use two
    // Eq.refl at different types: `Eq.refl Nat Nat.zero` vs a Nat literal — they
    // have different types and are not def-eq.
    let mut env = MinimalEnv::new();
    // `Nat : Type 0` and `Nat.zero : Nat` as plain consts (element + index).
    let nat_ty = vlvl(&MinimalEnv::new(), &r_sort(1), 0);
    env = env.with_const_typed(n("Nat"), 0, nat_ty);
    let nat_const_ty = vlvl(&env, &r_const("Nat"), 0);
    env = env.with_const_typed(n("Nat.zero"), 0, nat_const_ty);
    add_inductive(&mut env, eq_decl()).expect("Eq admitted");
    // refl0 : Eq Nat 0 0  (a proof term, type `Eq Nat 0 0 : Prop`).
    let refl0 = vlvl(
        &env,
        &r_apps(
            r_const_p("Eq.refl", vec![RawLevel::Zero]),
            vec![r_const("Nat"), r_const("Nat.zero")],
        ),
        0,
    );
    // `Nat.zero` — a term of a DIFFERENT type (Nat, not an Eq). With Eq NOT a
    // registered structure, structure-η cannot fire to equate these.
    let zero = vlvl(&env, &r_const("Nat.zero"), 0);
    let mut b = Budget::default_budget();
    assert!(
        !clean_ck0::is_def_eq(&env, &refl0, &zero, &mut b).expect("deq"),
        "no eta over-accept: a proof of Eq Nat 0 0 is not def-eq to Nat.zero"
    );
}

fn r_proj(struct_name: &str, idx: u32, inner: RawExpr) -> RawExpr {
    RawExpr::Proj(n(struct_name), idx, Box::new(inner))
}

/// A genuine 2-field η-structure: `Pair.{u} (α β : Sort u) : Sort u` with
/// `mk : (a : α) -> (b : β) -> Pair α β`. 1 ctor, 0 indices, non-recursive.
/// num_params = 2, num_fields = 2.
fn pair_decl() -> InductiveDecl {
    let b = boot(&[("Pair", 1), ("Pair.mk", 1)]);
    // Pair : (α : Sort u) -> (β : Sort u) -> Sort u
    let ty = r_pi(r_sort_param(0), r_pi(r_sort_param(0), r_sort_param(0)));
    // Pair.mk : (α β : Sort u) -> (a : α) -> (b : β) -> Pair α β
    let mk_ty = r_pi(
        r_sort_param(0), // α
        r_pi(
            r_sort_param(0), // β
            r_pi(
                r_bvar(1), // a : α
                r_pi(
                    r_bvar(1), // b : β
                    r_apps(
                        r_const_p("Pair", vec![RawLevel::Param(0)]),
                        vec![r_bvar(3), r_bvar(2)],
                    ),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("Pair"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &ty, 1),
        constructors: vec![Constructor {
            name: n("Pair.mk"),
            type_: vlvl(&b, &mk_ty, 1),
        }],
    }
}

#[test]
fn test_two_distinct_neutrals_of_eta_structure_terminate_not_overflow() {
    // ROBUSTNESS / TOTALITY REGRESSION (fail-closed, soundness-preserving).
    //
    // Comparing two genuinely DISTINCT neutral terms `p q : Pair Nat Nat` of a
    // registered η-structure must return a clean `Ok(false)` (or
    // `Err(OutOfBudget)`) — NEVER a native stack overflow / SIGABRT.
    //
    // PRE-FIX BEHAVIOUR (verified): `def_eq`'s structure-η η-expanded `p` to
    // `Pair.mk p.0 p.1` and compared field `p.0`/`p.1` against `q.0`/`q.1`, which
    // (via the `Proj` congruence) recursed back to `is_def_eq(p, q)`, building an
    // unbounded native recursion that overflowed the stack (SIGABRT) before the
    // step budget was exhausted. Lean-faithful structure-η only η-expands a side
    // to match a CONSTRUCTOR-headed other side; two neutrals need no η and are
    // compared as neutrals (which terminates). This test pins that the path is
    // now TOTAL.
    let mut env = MinimalEnv::new();
    // `Nat : Type 0` as a plain const (we only need a closed element type).
    let nat_ty = vlvl(&MinimalEnv::new(), &r_sort(1), 0);
    env = env.with_const_typed(n("Nat"), 0, nat_ty);
    add_inductive(&mut env, pair_decl()).expect("Pair admitted");
    // Confirm Pair is a registered η-structure (so structure-η is in play).
    assert!(
        env.structure_info(&n("Pair")).is_some(),
        "Pair must be a registered η-structure for this regression to exercise structure-η"
    );
    // `Pair Nat Nat : Type 0`.
    let pair_nat = r_apps(
        r_const_p("Pair", vec![RawLevel::Zero]),
        vec![r_const("Nat"), r_const("Nat")],
    );
    let pair_nat_t = vlvl(&env, &pair_nat, 0);
    // Two DISTINCT opaque neutrals `p`, `q : Pair Nat Nat`.
    env = env.with_const_typed(n("p"), 0, pair_nat_t.clone());
    env = env.with_const_typed(n("q"), 0, pair_nat_t);
    let p = vlvl(&env, &r_const("p"), 0);
    let q = vlvl(&env, &r_const("q"), 0);
    let mut b = Budget::default_budget();
    // MUST terminate. Distinct neutrals are not def-eq → clean `Ok(false)`;
    // a budget give-up (`Err(OutOfBudget)`) would also be acceptable (fail-closed).
    // What must NOT happen is a stack overflow / abort.
    match clean_ck0::is_def_eq(&env, &p, &q, &mut b) {
        Ok(false) => {}
        Err(clean_ck0::BudgetError::OutOfBudget) => {}
        Ok(true) => panic!("SOUNDNESS: distinct neutrals p, q : Pair Nat Nat must NOT be def-eq"),
    }
    // Reflexivity still holds (sanity: the neutral path didn't break trivial eq).
    let mut b2 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &p, &p, &mut b2).expect("deq p p"),
        "p ≡ p must still hold"
    );
}
