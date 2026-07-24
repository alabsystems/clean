// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R1 fail-closed pins: recursor eliminations OUTSIDE the synthesized
//! structural-recursion fragment must keep their structured refusals all the
//! way through the pipeline — never a silent lowering.
//!
//! The synthesized path (`to_lcnf::lower::rec_apply_parts`) only accepts
//! single-motive, non-indexed, non-mutual, non-reflexive, non-nested
//! inductives whose recursive fields are non-erased DIRECT occurrences (so
//! every self-call recurses on a projected constructor component —
//! structural termination by construction). Everything else falls through to
//! the extern constant path, where `verify_recursor_calls_certifiable`
//! refuses any surviving reference to a valueless kernel recursor.

use clean_compiler::pass_manager::{compile_lcnf_decls, PipelineConfig};
use clean_compiler::to_lcnf::constant_to_decl;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Environment, Expr, Name};

fn prelude_env() -> Environment {
    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    env
}

/// Rung B positive pin: `Acc.recOn` now lowers through the dedicated
/// value-recursive well-founded-recursion path. It is not structural recursion
/// over the function-typed `Acc` field, so this must never regress to either
/// the generic structural recognizer or the old valueless-recursor refusal.
#[test]
fn test_well_founded_elimination_lowers_through_pipeline() {
    let env = prelude_env();
    let pipeline = PipelineConfig::default();
    let info = env.get_const(&Name::from_string("Acc.recOn")).unwrap();
    let decl = constant_to_decl(&env, info)
        .expect("stage 1 lowers")
        .expect("definition with a value");
    compile_lcnf_decls(std::slice::from_ref(&decl), &env, &pipeline)
        .expect("Acc.recOn must lower through the well-founded recursion path");
}

/// Rung 3 positive pin: the subsingleton transports (`Eq.rec` / `HEq.rec`,
/// whose sole 0-field constructor makes the recursor identity-on-minor) COMPILE
/// — the normalization rewrites the elimination to its minor, so no valueless
/// recursor survives to the fail-closed guard. `Eq.recOn` / `Eq.ndrec` /
/// `HEq.recOn` / `HEq.ndrec` each collapse to the identity function on the
/// transported value.
#[test]
fn test_subsingleton_transport_lowers_to_identity() {
    let env = prelude_env();
    let pipeline = PipelineConfig::default();
    for root in ["Eq.recOn", "Eq.ndrec", "HEq.recOn", "HEq.ndrec"] {
        let info = env.get_const(&Name::from_string(root)).unwrap();
        let decl = constant_to_decl(&env, info)
            .expect("stage 1 lowers")
            .expect("definition with a value");
        compile_lcnf_decls(std::slice::from_ref(&decl), &env, &pipeline).unwrap_or_else(|e| {
            panic!("{root}: subsingleton transport must compile (identity-on-minor), got: {e}")
        });
    }
}

/// Register a one-constructor record whose minor receives `field_count`
/// ordinary runtime fields. This gives the refusal test a frontier probe that
/// cannot become stale merely because the prelude gains wider structures.
fn add_wide_record(env: &mut Environment, name: &str, field_count: usize) {
    let type_name = Name::from_string(name);
    let mut constructor_type = Expr::const_(type_name.clone(), vec![]);
    for _ in 0..field_count {
        constructor_type = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            constructor_type,
        );
    }
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: type_name,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(&format!("{name}.mk")),
                type_: constructor_type,
            }],
        }],
    })
    .expect("wide frontier record must register");
}

/// `MAX_RUNTIME_APPLY_ARGS` is kept in lockstep with the runtime's
/// `clean_invoke` positional ceiling (32). `Semiring.recOn` (15 fields),
/// `DivisionRing.recOn` (20), and `Field.recOn` (21) are inside that frontier
/// and lower. A synthetic 33-field record stays refused fail-closed: otherwise
/// its saturated minor application would reach `clean_invoke` and panic.
#[test]
fn test_wide_apply_frontier_lowers_through_32_and_refuses_33() {
    let mut env = prelude_env();
    let pipeline = PipelineConfig::default();

    for (root, fields) in [
        ("Semiring.recOn", 15),
        ("DivisionRing.recOn", 20),
        ("Field.recOn", 21),
    ] {
        let info = env.get_const(&Name::from_string(root)).unwrap();
        let decl = constant_to_decl(&env, info)
            .expect("stage 1 lowers")
            .expect("definition with a value");
        compile_lcnf_decls(std::slice::from_ref(&decl), &env, &pipeline).unwrap_or_else(|error| {
            panic!("{root} ({fields} fields, <= 32) must lower, got: {error}")
        });
    }

    add_wide_record(&mut env, "Wide32", 32);
    let info = env.get_const(&Name::from_string("Wide32.recOn")).unwrap();
    let decl = constant_to_decl(&env, info)
        .expect("stage 1 lowers")
        .expect("definition with a value");
    compile_lcnf_decls(std::slice::from_ref(&decl), &env, &pipeline)
        .expect("a 32-field Apply arm at the exact ceiling must lower");

    add_wide_record(&mut env, "Wide33", 33);
    let info = env.get_const(&Name::from_string("Wide33.recOn")).unwrap();
    let decl = constant_to_decl(&env, info)
        .expect("stage 1 lowers")
        .expect("definition with a value");
    let error = compile_lcnf_decls(std::slice::from_ref(&decl), &env, &pipeline)
        .expect_err("a 33-field Apply arm must retain the valueless-rec refusal");
    assert!(
        error.to_string().contains("Wide33.rec"),
        "expected the Wide33.rec valueless-recursor refusal, got: {error}"
    );
}

/// THE ADVERSARIAL-REVIEW PIN (R2): a bespoke recursor whose rules pair with
/// the constructors BY NAME AND ORDER but are NOT their structural
/// elimination rules must decline. The Cubical-mode prop-truncation HIT
/// recursor is the concrete shape: `∥A∥.rec`'s minors are
/// `[isProp-witness, f]` against rules `[in, squash]` — `minors[0]` is not
/// `in`'s method, and `squash` is a PATH constructor (its codomain is a
/// `Path`, not the inductive; its `recursive_fields = [false, false]` belie
/// its two `Trunc`-typed fields). Pairing minors positionally would compile
/// the `in` arm to apply the isProp witness — a silent behavioral
/// miscompile (this exact spine LOWERED before the
/// `recursor_rules_pair_with_constructors` guard).
#[test]
fn test_hit_truncation_recursor_declines_to_recursor_refusal() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::{BinderInfo, CleanMode, ConstantInfo, Expr, ExprKind, Level};
    use std::sync::Arc;

    let cst = |name: &str| Expr::const_(Name::from_string(name), vec![]);

    let mut env = Environment::with_mode(CleanMode::Cubical);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);
    let in_ctor = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(cst("Trunc"), Expr::bvar(1)),
        ),
    );
    let line = Expr::lam(
        BinderInfo::Default,
        interval,
        Expr::app(cst("Trunc"), Expr::bvar(3)),
    );
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(Expr::bvar(1)),
        right: Arc::new(Expr::bvar(0)),
    });
    let squash_ctor = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cst("Trunc"), Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(cst("Trunc"), Expr::bvar(1)),
                path,
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Trunc"),
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Trunc.in"),
                    type_: in_ctor,
                },
                Constructor {
                    name: Name::from_string("Trunc.squash"),
                    type_: squash_ctor,
                },
            ],
        }],
    })
    .expect("prop-truncation HIT declares in Cubical mode");

    // The trap this pin guards: the shape passes every SHALLOW gate. The
    // inductive is recursive but neither reflexive nor nested, and the
    // bespoke recursor's rule NAMES align 1:1, in order, with the
    // constructors — only the deeper pairing verification can refuse it.
    let ind = env.get_inductive(&Name::from_string("Trunc")).unwrap();
    assert!(ind.is_recursive && !ind.is_reflexive && !ind.is_nested);
    let rec = env.get_recursor(&Name::from_string("Trunc.rec")).unwrap();
    assert_eq!(rec.num_motives, 1);
    assert_eq!(rec.num_indices, 0);
    assert_eq!(
        rec.rules
            .iter()
            .map(|r| r.constructor_name.clone())
            .collect::<Vec<_>>(),
        ind.constructor_names,
        "rule names align with constructors — the OLD name-only check passes"
    );

    // Eta-expanded probe `fun x1..xN => Trunc.rec x1..xN` (every arg an open
    // bvar, so arg classification is fail-open Normal and only the
    // structural guards can refuse) — the reviewer's probe shape.
    let info = env.get_const(&Name::from_string("Trunc.rec")).unwrap();
    let levels: Vec<Level> = info
        .level_params
        .iter()
        .map(|n| Level::param(n.clone()))
        .collect();
    let mut domains: Vec<(clean_kernel::BinderData, Expr)> = Vec::new();
    let mut cur = info.type_.clone();
    while let ExprKind::Pi(bi, dom, cod) = cur.kind() {
        domains.push((*bi, dom.as_ref().clone()));
        cur = cod.as_ref().clone();
    }
    let n = domains.len();
    let mut body = Expr::const_(Name::from_string("Trunc.rec"), levels);
    for i in 0..n {
        body = Expr::app(body, Expr::bvar((n - 1 - i) as u32));
    }
    for (bi, dom) in domains.into_iter().rev() {
        body = Expr::lam(bi, dom, body);
    }
    let probe = ConstantInfo::new(
        Name::from_string("probe_Trunc_rec"),
        info.level_params.clone(),
        info.type_.clone(),
        Some(body),
        false,
    );

    let decl = constant_to_decl(&env, &probe)
        .expect("stage 1 lowers (recursor spelled as extern const)")
        .expect("probe has a value");
    let err = compile_lcnf_decls(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default(),
    )
    .expect_err("the bespoke HIT recursor must decline fail-closed");
    let msg = err.to_string();
    assert!(
        msg.contains("Trunc.rec") && msg.contains("no runtime value"),
        "expected the valueless-recursor refusal naming `Trunc.rec`, got: {msg}"
    );
}
