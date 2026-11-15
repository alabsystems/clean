// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The binding fingerprint erases `MData` from an ordinary constant, and
//! nothing else (Q4 residuals, 2026-11-14).
//!
//! lean4export strips every `MData` node, and `.olean` files keep them, so the
//! same Lean `Nat.add` had two fingerprints and the export's was refused
//! (`reports/self-proof-q4-unanimity-2026-11-13/clean-init-roots/`). The kernel
//! reads an ordinary constant through its wrappers (`fingerprint_mdata_lean_tests.rs`
//! measures that on the real cones, judgment by judgment), so the fingerprint now does too.
//!
//! The controls below pin both directions on one key, `Nat.pred`, whose bound
//! body holds every node kind the erasure must leave alone: a constant, a
//! literal, binders with domains and a bound variable, and a universe level.
//! The same body with `MData` around any node, or around all of them, binds;
//! a body that differs in one non-`MData` node is refused with
//! `ExtensionBindingMismatch` by the replay, before the kernel reads it.

use super::super::super::fingerprint::Fingerprinter;
use super::super::super::{
    recheck_closed, ClosedRecheck, ClosedRecheckOptions, ClosedRecheckRefusal,
};
use super::super::{check_binding, BindingVerdict, ExtensionBindings};
use super::{arrow, base_env, definition, import_structurally, konst, n, one, targets};
use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, MDataValue};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveError, InductiveType};
use clean_kernel::level::{Level, LevelArc};
use clean_kernel::name::Name;
use clean_kernel::KernelEnvError;

/// One way a body can differ from the bound one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Edit {
    /// The bound body itself.
    None,
    /// `Nat.succ k` becomes `V.succ k` (`V.succ := Nat.succ`): a constant.
    Constant,
    /// The base case `0` becomes `1`: a literal.
    Literal,
    /// `Nat.succ k` becomes `Nat.succ ih`: which binder a variable names.
    BoundVariable,
    /// The motive's binder `(_ : Nat)` becomes `(_ : Bool)`: a binder domain.
    BinderDomain,
    /// `Nat.rec.{1}` becomes `Nat.rec.{max 0 1}`: a level (the same universe,
    /// spelled differently, so the gate stays structural on levels: erasure
    /// widens nothing but `MData`).
    Level,
}

const EDITS: [Edit; 5] = [
    Edit::Constant,
    Edit::Literal,
    Edit::BoundVariable,
    Edit::BinderDomain,
    Edit::Level,
];

/// `fun (n : Nat) => Nat.rec.{1} (fun (_ : Nat) => Nat) 0
///   (fun (k : Nat) (ih : Nat) => Nat.succ k) n`, with `edit` applied.
fn pred_body(edit: Edit) -> Expr {
    let level = match edit {
        Edit::Level => Level::Max(LevelArc::from(Level::zero()), LevelArc::from(one())),
        _ => one(),
    };
    let motive_domain = match edit {
        Edit::BinderDomain => konst("Bool"),
        _ => konst("Nat"),
    };
    let zero = Expr::nat_lit(u64::from(edit == Edit::Literal));
    let succ = match edit {
        Edit::Constant => konst("V.succ"),
        _ => konst("Nat.succ"),
    };
    let field = Expr::bvar(if edit == Edit::BoundVariable { 0 } else { 1 });
    let step = Expr::lam(
        BinderInfo::Default,
        konst("Nat"),
        Expr::lam(BinderInfo::Default, konst("Nat"), Expr::app(succ, field)),
    );
    let motive = Expr::lam(BinderInfo::Default, motive_domain, konst("Nat"));
    let rec = Expr::const_(n("Nat.rec"), vec![level]);
    Expr::lam(
        BinderInfo::Default,
        konst("Nat"),
        Expr::apps(rec, [motive, zero, step, Expr::bvar(0)]),
    )
}

fn mark() -> Vec<(Name, MDataValue)> {
    vec![(n("q4.residuals"), MDataValue::Bool(true))]
}

/// The nodes of `e` in pre-order, counted.
fn node_count(e: &Expr) -> usize {
    1 + children(e).into_iter().map(node_count).sum::<usize>()
}

fn children(e: &Expr) -> Vec<&Expr> {
    match e.kind() {
        ExprKind::App(f, a) => vec![f.as_ref(), a.as_ref()],
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => vec![t.as_ref(), b.as_ref()],
        ExprKind::MData(_, b) => vec![b.as_ref()],
        _ => Vec::new(),
    }
}

/// `e` with an `MData` wrapper around the node at pre-order position `at`
/// (`None`: around every node).
fn wrap(e: &Expr, at: Option<usize>) -> Expr {
    fn go(e: &Expr, at: Option<usize>, next: &mut usize) -> Expr {
        let here = *next;
        *next += 1;
        let rebuilt = match e.kind() {
            ExprKind::App(f, a) => {
                let f = go(f, at, next);
                Expr::app(f, go(a, at, next))
            }
            ExprKind::Lam(bd, t, b) => {
                let t = go(t, at, next);
                Expr::lam(*bd, t, go(b, at, next))
            }
            ExprKind::Pi(bd, t, b) => {
                let t = go(t, at, next);
                Expr::pi(*bd, t, go(b, at, next))
            }
            _ => e.clone(),
        };
        if at.is_none_or(|i| i == here) {
            Expr::mdata(mark(), rebuilt)
        } else {
            rebuilt
        }
    }
    go(e, at, &mut 0)
}

/// `base_env` plus `V.succ := Nat.succ` and `Nat.pred := body`, and the
/// client `V.p := Nat.pred 3` that the replay targets.
fn pred_env(body: Expr) -> Environment {
    let mut env = base_env(false);
    import_structurally(
        &mut env,
        definition(
            "V.succ",
            arrow(konst("Nat"), konst("Nat")),
            konst("Nat.succ"),
        ),
    );
    import_structurally(
        &mut env,
        definition("Nat.pred", arrow(konst("Nat"), konst("Nat")), body),
    );
    import_structurally(
        &mut env,
        definition(
            "V.p",
            konst("Nat"),
            Expr::app(konst("Nat.pred"), Expr::nat_lit(3)),
        ),
    );
    env
}

fn fingerprint(env: &Environment, name: &str) -> [u8; 32] {
    Fingerprinter::new(env).constant(&n(name))
}

fn honest_table() -> ExtensionBindings {
    ExtensionBindings::derive_from(&pred_env(pred_body(Edit::None)), "test: bound Nat.pred")
}

fn replay(env: &Environment) -> ClosedRecheck {
    recheck_closed(
        env,
        &targets(&["V.p"]),
        &ClosedRecheckOptions {
            extension_bindings: honest_table(),
            ..ClosedRecheckOptions::default()
        },
    )
}

/// Control 1: the bound body with `MData` around any one node, around every
/// node, or twice around the root, has the bound fingerprint, binds, and is
/// admitted by the replay.
#[test]
fn test_binding_mdata_wrapped_body_binds_as_the_bound_body() {
    let bound = pred_body(Edit::None);
    let want = fingerprint(&pred_env(bound.clone()), "Nat.pred");
    let table = honest_table();
    let mut variants: Vec<Expr> = (0..node_count(&bound))
        .map(|i| wrap(&bound, Some(i)))
        .collect();
    variants.push(wrap(&bound, None));
    variants.push(Expr::mdata(mark(), Expr::mdata(mark(), bound.clone())));
    assert_eq!(variants.len(), node_count(&bound) + 2);
    for (i, body) in variants.into_iter().enumerate() {
        assert_ne!(body, bound, "variant {i} must carry MData");
        let env = pred_env(body);
        let got = fingerprint(&env, "Nat.pred");
        assert_eq!(got, want, "variant {i}: MData changed the fingerprint");
        assert!(
            matches!(
                check_binding(&table, &n("Nat.pred"), &got),
                BindingVerdict::Bound
            ),
            "variant {i} must bind"
        );
        let run = replay(&env);
        assert!(
            run.report.passed(),
            "variant {i}: {:?}",
            run.report.refusals
        );
        assert!(run
            .report
            .extension_keys_bound
            .contains(&"Nat.pred".to_string()));
    }
}

/// Control 2: a body that differs from the bound one in one non-`MData` node
/// is refused by the replay with `ExtensionBindingMismatch` on `Nat.pred`,
/// with or without `MData` around it.
#[test]
fn test_binding_non_mdata_difference_is_an_extension_binding_mismatch() {
    let want = fingerprint(&pred_env(pred_body(Edit::None)), "Nat.pred");
    for edit in EDITS {
        for body in [pred_body(edit), wrap(&pred_body(edit), None)] {
            let env = pred_env(body);
            assert_ne!(
                fingerprint(&env, "Nat.pred"),
                want,
                "{edit:?}: a non-MData difference must change the fingerprint"
            );
            let run = replay(&env);
            assert!(!run.report.passed(), "{edit:?}");
            assert!(
                run.report.refusals.iter().any(|r| matches!(
                    r,
                    ClosedRecheckRefusal::ExtensionBindingMismatch { name, .. } if name == "Nat.pred"
                )),
                "{edit:?}: the refusal must be the binding's: {:?}",
                run.report.refusals
            );
            assert!(run.replayed.get_const(&n("Nat.pred")).is_none(), "{edit:?}");
        }
    }
}

/// Family inputs keep their wrappers. Admission reads a constructor's
/// telescope syntactically: Lean's `check_positivity` whnfs a field (reading
/// through `MData`), Clean's strict occurrence check contracts β only, so a
/// recursive field behind `MData` is refused as an invalid occurrence — the
/// wrapper changes what admission decides, and the fingerprint of a family
/// hashes it.
#[test]
fn test_binding_family_inputs_keep_their_mdata() {
    let wrapped = |e: Expr| Expr::mdata(mark(), e);
    let nat = |succ_field: Expr| InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("Nat"),
            type_: Expr::sort(one()),
            constructors: vec![
                Constructor {
                    name: n("Nat.zero"),
                    type_: konst("Nat"),
                },
                Constructor {
                    name: n("Nat.succ"),
                    type_: arrow(succ_field, konst("Nat")),
                },
            ],
        }],
    };
    Environment::default()
        .add_inductive_core(nat(konst("Nat")))
        .expect("the unwrapped family is admissible");
    let hidden = Environment::default().add_inductive_core(nat(wrapped(konst("Nat"))));
    assert!(
        matches!(
            hidden,
            Err(KernelEnvError::Inductive(
                InductiveError::InvalidInductiveOccurrence { .. }
            ))
        ),
        "a recursive field behind MData is refused by admission today: {hidden:?}"
    );

    // A wrapper on a non-recursive field is admitted, and the family's
    // fingerprint keeps it.
    let boxed = |field: Expr| {
        let mut env = base_env(false);
        env.add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: n("V.Box"),
                type_: Expr::sort(one()),
                constructors: vec![Constructor {
                    name: n("V.Box.mk"),
                    type_: arrow(field, konst("V.Box")),
                }],
            }],
        })
        .expect("a non-recursive wrapped field is admissible");
        fingerprint(&env, "V.Box")
    };
    assert_ne!(boxed(wrapped(konst("Nat"))), boxed(konst("Nat")));
}
