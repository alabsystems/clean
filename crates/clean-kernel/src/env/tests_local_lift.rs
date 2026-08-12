// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for nested-local lifting (`inductive_local_lift.rs`, rung 2 of
//! `designs/2026-07-29-rocq-features-into-clean.md`).
//!
//! Every acceptance test drives the REAL checked path: `add_inductive` must
//! first reject the declaration with `NestedParamsContainLocals` (pinning
//! that the lift only ever handles what Lean rejects), then the lifted block
//! must pass `add_inductive` from scratch — positivity, universes, recursors.
//! Family-count assertions pin the depth-canonical memo: a coherence miss at
//! the aux re-scan would mint a redundant duplicate family, not fail.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveError, InductiveType};

fn prop() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::zero()))
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::new())
}

/// `inductive B : Type | b : B` — the closed base type every fixture indexes by.
fn add_base(env: &mut Environment) {
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("B"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("B.b"),
                type_: cnst("B"),
            }],
        }],
    })
    .expect("base type B must register");
}

/// `inductive Wrap (P : B → Prop) : Prop | mk : P B.b → Wrap P` — the
/// higher-order Prop container whose param instantiation the fixtures make
/// capture a local.
fn add_wrap(env: &mut Environment) {
    let p_ty = Expr::pi(BinderInfo::Default, cnst("B"), prop());
    let wrap_ty = Expr::pi(BinderInfo::Default, p_ty.clone(), prop());
    // mk : (P : B → Prop) → P B.b → Wrap P
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        p_ty,
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(0), cnst("B.b")),
            Expr::app(cnst("Wrap"), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Wrap"),
            type_: wrap_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("container Wrap must register");
}

/// `inductive Bad : B → Prop | step : (n : B) → Wrap (fun (m : B) => Bad n) → Bad n`
/// — the minimized local-capturing nested inductive (Lean rejects it).
fn bad_decl() -> InductiveDecl {
    let bad = |arg: Expr| Expr::app(cnst("Bad"), arg);
    // fun (m : B) => Bad n — under the lambda binder, `n` (the step binder) is BVar(1).
    let capturing_arg = Expr::lam(BinderInfo::Default, cnst("B"), bad(Expr::bvar(1)));
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("Wrap"), capturing_arg),
            bad(Expr::bvar(1)),
        ),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bad"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.step"),
                type_: step_ty,
            }],
        }],
    }
}

#[test]
fn test_local_lift_kernel_rejects_then_lift_accepts() {
    let mut env = Environment::new();
    add_base(&mut env);
    add_wrap(&mut env);

    let err = env
        .add_inductive(bad_decl())
        .expect_err("local-capturing nested occurrence must fail closed without the lift");
    assert!(
        matches!(
            err,
            EnvError::Inductive(InductiveError::NestedParamsContainLocals)
        ),
        "expected NestedParamsContainLocals, got: {err:?}"
    );

    let lift = env
        .lift_nested_locals(&bad_decl())
        .expect("the minimized capture is inside the v1 lift fragment");
    assert_eq!(
        lift.decl.types.len(),
        2,
        "one aux family expected (a re-scan memo miss would mint a duplicate)"
    );
    assert_eq!(lift.aux_names.len(), 1, "exactly one lifted family");
    assert_eq!(lift.aux_names[0].to_string(), "_lifted.Wrap_1");

    env.add_inductive(lift.decl)
        .expect("the lifted mutual block must pass the full kernel check");
    let bad = env
        .get_inductive(&Name::from_string("Bad"))
        .expect("Bad must register");
    assert_eq!(bad.all_names.len(), 2, "Bad is mutual with the aux family");
    assert!(
        env.get_inductive(&Name::from_string("_lifted.Wrap_1"))
            .is_some(),
        "the lifted family must register as a real inductive"
    );
}

#[test]
fn test_local_lift_depth_canonicalization_dedups_to_one_family() {
    let mut env = Environment::new();
    add_base(&mut env);
    add_wrap(&mut env);

    // Same capture shape at two different Pi depths: step at depth 1,
    // step2 at depth 2 (extra unused leading binder). The canonical memo
    // must collapse both to ONE aux family.
    let mut decl = bad_decl();
    let bad = |arg: Expr| Expr::app(cnst("Bad"), arg);
    // step2 : (n : B) → (k : B) → Wrap (fun (m : B) => Bad n) → Bad n
    let capturing_arg = Expr::lam(BinderInfo::Default, cnst("B"), bad(Expr::bvar(2)));
    let step2_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            cnst("B"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(cnst("Wrap"), capturing_arg),
                bad(Expr::bvar(2)),
            ),
        ),
    );
    decl.types[0].constructors.push(Constructor {
        name: Name::from_string("Bad.step2"),
        type_: step2_ty,
    });

    let lift = env
        .lift_nested_locals(&decl)
        .expect("both captures are inside the v1 fragment");
    assert_eq!(
        lift.decl.types.len(),
        2,
        "depth-canonicalization must dedup both occurrences into one family"
    );
    env.add_inductive(lift.decl)
        .expect("the deduped lifted block must pass the full kernel check");
}

#[test]
fn test_local_lift_indexed_container_accepts() {
    let mut env = Environment::new();
    add_base(&mut env);
    // WrapIdx (P : B → Prop) : B → Prop | mk : (b : B) → P b → WrapIdx P b
    let p_ty = Expr::pi(BinderInfo::Default, cnst("B"), prop());
    let former = Expr::pi(
        BinderInfo::Default,
        p_ty.clone(),
        Expr::pi(BinderInfo::Default, cnst("B"), prop()),
    );
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        p_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            cnst("B"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::bvar(1), Expr::bvar(0)),
                Expr::app(Expr::app(cnst("WrapIdx"), Expr::bvar(2)), Expr::bvar(1)),
            ),
        ),
    );
    // Second constructor with a CONSTANT result index: keeps the index from
    // being promoted to a parameter at registration, so the aux family must
    // genuinely carry it after the captured-local telescope.
    let mk2_ty = Expr::pi(
        BinderInfo::Default,
        p_ty,
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(0), cnst("B.b")),
            Expr::app(Expr::app(cnst("WrapIdx"), Expr::bvar(1)), cnst("B.b")),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("WrapIdx"),
            type_: former,
            constructors: vec![
                Constructor {
                    name: Name::from_string("WrapIdx.mk"),
                    type_: mk_ty,
                },
                Constructor {
                    name: Name::from_string("WrapIdx.mk2"),
                    type_: mk2_ty,
                },
            ],
        }],
    })
    .expect("indexed container WrapIdx must register");
    let stored = env
        .get_inductive(&Name::from_string("WrapIdx"))
        .expect("WrapIdx present");
    assert_eq!(
        (stored.num_params, stored.num_indices),
        (1, 1),
        "fixture premise: the index must not be param-promoted at registration"
    );

    // BadI : B → Prop | step : (n : B) → WrapIdx (fun (m : B) => BadI n) B.b → BadI n
    let badi = |arg: Expr| Expr::app(cnst("BadI"), arg);
    let capturing_arg = Expr::lam(BinderInfo::Default, cnst("B"), badi(Expr::bvar(1)));
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::app(cnst("WrapIdx"), capturing_arg), cnst("B.b")),
            badi(Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadI"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("BadI.step"),
                type_: step_ty,
            }],
        }],
    };

    let lift = env
        .lift_nested_locals(&decl)
        .expect("indexed capturing container is inside the v1 fragment");
    for t in &lift.decl.types {
        eprintln!("TYPE {} : {:?}", t.name, t.type_);
        for c in &t.constructors {
            eprintln!("  CTOR {} : {:?}", c.name, c.type_);
        }
    }
    assert_eq!(lift.aux_names[0].to_string(), "_lifted.WrapIdx_1");
    env.add_inductive(lift.decl)
        .expect("the lifted indexed block must pass the full kernel check");
    // The aux family keeps the container's index AFTER the captured-local
    // telescope: _lifted.WrapIdx_1 : B → B → Prop. Registration promotes the
    // uniform captured-local position to the block's shared parameter, so the
    // container's own index survives as the residual index.
    let aux = env
        .get_inductive(&Name::from_string("_lifted.WrapIdx_1"))
        .expect("aux family must register");
    assert_eq!(
        (aux.num_params, aux.num_indices),
        (1, 1),
        "captured local promotes to the shared param; the container index remains"
    );
}

#[test]
fn test_local_lift_second_round_capture_from_beta() {
    // The Forall₂-with-∧ mechanism in miniature: the capture only appears
    // AFTER the container's param is applied and beta-contracted inside the
    // first aux family's constructor. Two rounds, three families.
    let mut env = Environment::new();
    add_base(&mut env);
    add_wrap(&mut env);
    // Pair2 (Q R : Prop) : Prop | mk : Q → R → Pair2 Q R (an And clone).
    let pair2 = |q: Expr, r: Expr| Expr::app(Expr::app(cnst("Pair2"), q), r);
    let former = Expr::pi(
        BinderInfo::Default,
        prop(),
        Expr::pi(BinderInfo::Default, prop(), prop()),
    );
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        prop(),
        Expr::pi(
            BinderInfo::Default,
            prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    pair2(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("Pair2"),
            type_: former,
            constructors: vec![Constructor {
                name: Name::from_string("Pair2.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Pair2 must register");

    // Bad2 : B → Prop
    // | step : (n : B) → Wrap (fun (m : B) => Pair2 (Bad2 n) (Bad2 m)) → Bad2 n
    // Round 1 lifts the Wrap occurrence (captures n). Substituting its param
    // and beta-reducing `P B.b` inside the aux constructor produces
    // `Pair2 (Bad2 ℓ) (Bad2 B.b)` — whose Pair2 occurrence captures ℓ and is
    // only discoverable on the aux re-scan (round 2).
    let bad2 = |arg: Expr| Expr::app(cnst("Bad2"), arg);
    let capturing_arg = Expr::lam(
        BinderInfo::Default,
        cnst("B"),
        pair2(bad2(Expr::bvar(1)), bad2(Expr::bvar(0))),
    );
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("Wrap"), capturing_arg),
            bad2(Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bad2"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("Bad2.step"),
                type_: step_ty,
            }],
        }],
    };

    let lift = env
        .lift_nested_locals(&decl)
        .expect("the two-round capture chain is inside the v1 fragment");
    assert_eq!(
        lift.aux_names
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        vec!["_lifted.Wrap_1", "_lifted.Pair2_2"],
        "round 1 lifts Wrap, the aux re-scan (round 2) lifts Pair2 \
         (the fresh-name counter is shared, so suffixes are not dense)"
    );
    env.add_inductive(lift.decl)
        .expect("the three-family lifted block must pass the full kernel check");
}

#[test]
fn test_local_lift_gates_parameterized_and_polymorphic_decls() {
    let env = Environment::new();
    let mut decl = bad_decl();
    decl.num_params = 1;
    assert!(
        matches!(
            env.lift_nested_locals(&decl),
            Err(LocalLiftError::Unsupported { .. })
        ),
        "num_params > 0 must be refused in v1"
    );
    let mut decl = bad_decl();
    decl.level_params = vec![Name::from_string("u")];
    assert!(
        matches!(
            env.lift_nested_locals(&decl),
            Err(LocalLiftError::Unsupported { .. })
        ),
        "universe-polymorphic declarations must be refused in v1"
    );
}

#[test]
fn test_local_lift_nothing_to_lift_on_plain_decl() {
    let mut env = Environment::new();
    add_base(&mut env);
    // A perfectly ordinary declaration with no nested occurrence at all.
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Plain"),
            type_: prop(),
            constructors: vec![Constructor {
                name: Name::from_string("Plain.mk"),
                type_: cnst("Plain"),
            }],
        }],
    };
    assert!(
        matches!(
            env.lift_nested_locals(&decl),
            Err(LocalLiftError::NothingToLift)
        ),
        "no capturing occurrence ⇒ the caller must surface its original error"
    );
}

#[test]
fn test_local_lift_gates_non_prop_container() {
    let mut env = Environment::new();
    add_base(&mut env);
    // WrapT (P : B → Type) : Type | mk : P B.b → WrapT P — a Type-valued
    // container; the v1 lift is Prop-only.
    let p_ty = Expr::pi(BinderInfo::Default, cnst("B"), Expr::type_());
    let former = Expr::pi(BinderInfo::Default, p_ty.clone(), Expr::type_());
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        p_ty,
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(0), cnst("B.b")),
            Expr::app(cnst("WrapT"), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("WrapT"),
            type_: former,
            constructors: vec![Constructor {
                name: Name::from_string("WrapT.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("WrapT must register");

    let badt = |arg: Expr| Expr::app(cnst("BadT"), arg);
    let capturing_arg = Expr::lam(BinderInfo::Default, cnst("B"), badt(Expr::bvar(1)));
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("WrapT"), capturing_arg),
            badt(Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadT"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("BadT.step"),
                type_: step_ty,
            }],
        }],
    };
    assert!(
        matches!(
            env.lift_nested_locals(&decl),
            Err(LocalLiftError::Unsupported { .. })
        ),
        "Type-valued specialization must be refused in v1"
    );
}

#[test]
fn test_local_lift_gates_dependent_captured_local_type() {
    let mut env = Environment::new();
    add_base(&mut env);
    add_wrap(&mut env);
    // step : (n : B) → (x : W n) → Wrap (fun (m : B) => BadD x) → BadD n
    // The captured local `x` has a type with a loose bvar (`W n`), which the
    // v1 lift cannot transplant into the aux index telescope. The lift is
    // purely syntactic, so `W` need not exist for the gate to be exercised.
    let badd = |arg: Expr| Expr::app(cnst("BadD"), arg);
    // Under the lambda binder: m = BVar(0), x = BVar(1), n = BVar(2).
    let capturing_arg = Expr::lam(BinderInfo::Default, cnst("B"), badd(Expr::bvar(1)));
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("W"), Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(cnst("Wrap"), capturing_arg),
                badd(Expr::bvar(2)),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadD"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("BadD.step"),
                type_: step_ty,
            }],
        }],
    };
    assert!(
        matches!(
            env.lift_nested_locals(&decl),
            Err(LocalLiftError::Unsupported { .. })
        ),
        "a captured local with a dependent type must be refused in v1"
    );
}
// Regression for the mutual-sibling residual-index IH fix in
// `build_recursor_rule_rhs` (2026-08-04, found via the indexed-container
// fixture above): a hand-written mutual block — no lift involved — where a
// recursive field targets a SIBLING carrying a residual (unpromoted) index.
// The old rule builder gated IH index application on the CURRENT type's
// num_indices (0 for BadIH below), dropping the sibling's index and minting
// an IH the subject-reduction validator rejected.
#[test]
fn test_mutual_sibling_residual_index_ih_regression() {
    let mut env = Environment::new();
    add_base(&mut env);
    // mutual
    //   BadIH : B → Prop     | step : (n : B) → W n B.b → BadIH n
    //   W : B → B → Prop     | mk  : (l : B) → (b : B) → BadIH l → W l b
    //                        | mk2 : (l : B) → BadIH l → W l B.b
    let badih_ty = Expr::pi(BinderInfo::Default, cnst("B"), prop());
    let w_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(BinderInfo::Default, cnst("B"), prop()),
    );
    let step = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::app(cnst("W"), Expr::bvar(0)), cnst("B.b")),
            Expr::app(cnst("BadIH"), Expr::bvar(1)),
        ),
    );
    let mk = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            cnst("B"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(cnst("BadIH"), Expr::bvar(1)),
                Expr::app(Expr::app(cnst("W"), Expr::bvar(2)), Expr::bvar(1)),
            ),
        ),
    );
    let mk2 = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("BadIH"), Expr::bvar(0)),
            Expr::app(Expr::app(cnst("W"), Expr::bvar(1)), cnst("B.b")),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: Name::from_string("BadIH"),
                type_: badih_ty,
                constructors: vec![Constructor {
                    name: Name::from_string("BadIH.step"),
                    type_: step,
                }],
            },
            InductiveType {
                name: Name::from_string("W"),
                type_: w_ty,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("W.mk"),
                        type_: mk,
                    },
                    Constructor {
                        name: Name::from_string("W.mk2"),
                        type_: mk2,
                    },
                ],
            },
        ],
    };
    env.add_inductive(decl)
        .expect("indexed mutual block with sibling-index IH must register");
    let w = env
        .get_inductive(&Name::from_string("W"))
        .expect("W must register");
    assert_eq!(
        (w.num_params, w.num_indices),
        (1, 1),
        "the shared first index promotes; the second stays a residual index"
    );
}

// Regression for the minor-premise residual-index remap fix in
// `remap_residual_index_bvars_for_minor` (2026-08-05, found via the lift's
// Forall2 flagship): with num_motives > 1 the param branch hardcoded a
// 1-motive shift, so a residual index referencing the promoted shared param
// pointed at a MOTIVE inside the minor premise — the recursor type itself
// was malformed and the subject-reduction validator rejected the block.
// Hand-written (no lift involved), mirroring the lifted Forall2 shape:
// the sibling field `W l l` repeats the promoted local as its residual index.
#[test]
fn test_mutual_repeated_residual_index_minor_premise_regression() {
    let mut env = Environment::new();
    add_base(&mut env);
    // mutual
    //   V : B → Prop       | mk : (l : B) → W l l → V l
    //   W : B → B → Prop   | nil : (l : B) → W l l
    //                      | consish : (l : B) → (r : B) → V l → W l r → W l r
    let v_ty = Expr::pi(BinderInfo::Default, cnst("B"), prop());
    let w_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(BinderInfo::Default, cnst("B"), prop()),
    );
    let w = |a: Expr, b: Expr| Expr::app(Expr::app(cnst("W"), a), b);
    let mk = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            w(Expr::bvar(0), Expr::bvar(0)),
            Expr::app(cnst("V"), Expr::bvar(1)),
        ),
    );
    let nil = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        w(Expr::bvar(0), Expr::bvar(0)),
    );
    let consish = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            cnst("B"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(cnst("V"), Expr::bvar(1)),
                Expr::pi(
                    BinderInfo::Default,
                    w(Expr::bvar(2), Expr::bvar(1)),
                    w(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: Name::from_string("V"),
                type_: v_ty,
                constructors: vec![Constructor {
                    name: Name::from_string("V.mk"),
                    type_: mk,
                }],
            },
            InductiveType {
                name: Name::from_string("W"),
                type_: w_ty,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("W.nil"),
                        type_: nil,
                    },
                    Constructor {
                        name: Name::from_string("W.consish"),
                        type_: consish,
                    },
                ],
            },
        ],
    };
    env.add_inductive(decl)
        .expect("repeated-residual-index mutual block must register");
    let w = env
        .get_inductive(&Name::from_string("W"))
        .expect("W must register");
    assert_eq!(
        (w.num_params, w.num_indices),
        (1, 1),
        "the repeated first position promotes; the second stays a residual index"
    );
}

#[test]
fn test_local_lift_round_trip_guard_green_and_sealed() {
    let mut env = Environment::new();
    add_base(&mut env);
    add_wrap(&mut env);
    let lift = env
        .lift_nested_locals(&bad_decl())
        .expect("lift succeeds on the minimized fixture");
    assert_eq!(lift.families.len(), 1, "one synthesis record per family");
    let f = &lift.families[0];
    assert_eq!(f.aux_name.to_string(), "_lifted.Wrap_1");
    assert_eq!(f.container.to_string(), "Wrap");
    assert_eq!(f.captured_tys.len(), 1, "one captured local (n : B)");
    assert_eq!(f.ctor_map.len(), 1, "Wrap has one constructor");
    env.add_inductive(lift.decl)
        .expect("lifted block registers");
    env.verify_local_lift_anchor(&bad_decl(), &lift.families)
        .expect("guard must be green on an untampered record");

    // Tamper: a swapped canonical arg must trip the guard at ctor level.
    let mut bad = lift.families.clone();
    bad[0].canonical_args[0] = cnst("B.b");
    let err = env
        .verify_local_lift_anchor(&bad_decl(), &bad)
        .expect_err("tampered record must fail the round-trip guard");
    assert!(
        matches!(err, LocalLiftError::RoundTrip { .. }),
        "expected RoundTrip, got: {err:?}"
    );
    // The sealed guard must not have minted anything.
    assert!(
        env.get_inductive(&Name::from_string("_lifted.Wrap_2"))
            .is_none(),
        "sealed guard must never synthesize a fresh family"
    );
}
