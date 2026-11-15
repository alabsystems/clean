// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the declaration-boundary half of `let rec` lifting: reading
//! a lifted helper back off a finished term. The production path is pinned
//! end to end in `crates/clean-elab/tests/let_rec_aux_lift_e2e.rs`.

use super::*;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// `(fun (x : Nat → Nat) => x) (fun y => y)` applied to `args`.
fn lifted(args: Vec<Expr>) -> Expr {
    let ty = Expr::pi(BinderInfo::Default, nat(), nat());
    let val = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0));
    Expr::apps(ascribe_closed(ty, val), args)
}

/// What one rewrite found: the helpers registered, the names bound by two
/// different helpers, and the names whose binding stayed inline.
struct Rewritten {
    found: Vec<(Name, Expr, Expr)>,
    conflicts: Vec<Name>,
    inline: HashSet<Name>,
    out: Expr,
}

fn rewrite(names: &[&str], e: &Expr) -> Rewritten {
    let names: HashSet<Name> = names.iter().map(|n| Name::from_string(n)).collect();
    let us: Vec<Level> = Vec::new();
    let mut rewriter = LiftRewriter {
        names: &names,
        us: &us,
        found: Vec::new(),
        seen: HashMap::new(),
        memo: HashMap::new(),
        conflicts: Vec::new(),
        inline: HashSet::new(),
    };
    let out = rewriter.rewrite(e);
    Rewritten {
        found: rewriter.found,
        conflicts: rewriter.conflicts,
        inline: rewriter.inline,
        out,
    }
}

#[test]
fn test_read_lifted_value_returns_closed_parts_and_arguments_in_order() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let value = lifted(vec![a.clone(), b.clone()]);
    let (ty, val, args) = read_lifted_value(&value).expect("lifted form is recognised");
    assert_eq!(ty, &Expr::pi(BinderInfo::Default, nat(), nat()));
    assert_eq!(val, &Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)));
    assert_eq!(args, vec![&a, &b]);
}

#[test]
fn test_read_lifted_value_plain_application_is_not_lifted() {
    let value = Expr::app(Expr::const_(Name::from_string("f"), vec![]), nat());
    assert!(read_lifted_value(&value).is_none());
}

/// `let p.go : … := lifted c; body[go]` becomes `body[p.go c]`, and `p.go`
/// is reported with its closed type and value.
#[test]
fn test_lift_rewriter_replaces_marker_let_with_constant_application() {
    let c = Expr::fvar(FVarId::new(7));
    let marker = Expr::let_named(
        Name::from_string("p.go"),
        nat(),
        lifted(vec![c.clone()]),
        Expr::app(Expr::bvar(0), nat()),
        false,
    );
    let Rewritten {
        found,
        conflicts,
        inline,
        out,
    } = rewrite(&["p.go"], &marker);
    assert!(conflicts.is_empty() && inline.is_empty());
    assert_eq!(found.len(), 1, "one helper registered");
    assert_eq!(found[0].0, Name::from_string("p.go"));
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("p.go"), vec![]), c),
        nat(),
    );
    assert_eq!(out, expected);
}

/// A `let` with an ordinary name is never touched, even in lifted form.
#[test]
fn test_lift_rewriter_ignores_lets_not_named_by_the_scope() {
    let ordinary = Expr::let_named(
        Name::from_string("x"),
        nat(),
        lifted(vec![]),
        Expr::bvar(0),
        false,
    );
    let Rewritten {
        found, inline, out, ..
    } = rewrite(&["p.go"], &ordinary);
    assert!(found.is_empty());
    assert!(inline.is_empty(), "`x` is not a helper name");
    assert_eq!(out, ordinary);
}

/// Two different helpers under one name: Lean refuses the second (`'p.go'
/// has already been declared`), so the rewrite reports the name as a
/// conflict — which `finish_let_rec_lifts` turns into the refusal — and never
/// replaces the second by a constant whose value differs from its own.
#[test]
fn test_lift_rewriter_reports_a_conflicting_second_helper() {
    let first = Expr::let_named(
        Name::from_string("p.go"),
        nat(),
        lifted(vec![]),
        Expr::bvar(0),
        false,
    );
    let other_ty = Expr::pi(BinderInfo::Default, nat(), nat());
    let other_val = Expr::lam(BinderInfo::Default, nat(), nat());
    let second = Expr::let_named(
        Name::from_string("p.go"),
        nat(),
        ascribe_closed(other_ty, other_val),
        Expr::bvar(0),
        false,
    );
    let pair = Expr::app(first, second.clone());
    let Rewritten {
        found,
        conflicts,
        out,
        ..
    } = rewrite(&["p.go"], &pair);
    assert_eq!(found.len(), 1, "only the first helper is read off");
    assert_eq!(conflicts, vec![Name::from_string("p.go")]);
    let ExprKind::App(_, kept) = out.kind() else {
        panic!("rewritten pair must stay an application, got {out}");
    };
    assert_eq!(
        kept.as_ref(),
        &second,
        "the conflicting helper is never replaced by the first's constant"
    );
}

/// The same helper read twice (one binding reached along two paths, or the
/// value elaborator's retry): one registration, no conflict.
#[test]
fn test_lift_rewriter_identical_helper_twice_is_one() {
    let marker = |body: Expr| {
        Expr::let_named(
            Name::from_string("p.go"),
            nat(),
            lifted(vec![]),
            body,
            false,
        )
    };
    let pair = Expr::app(marker(Expr::bvar(0)), marker(Expr::bvar(0)));
    let Rewritten {
        found, conflicts, ..
    } = rewrite(&["p.go"], &pair);
    assert_eq!(found.len(), 1);
    assert!(conflicts.is_empty());
}

/// A helper-named binding whose value is not in lifted form stays inline and
/// is reported as such (for a `partial` parent's recursive helper, that is a
/// refusal).
#[test]
fn test_lift_rewriter_reports_an_unrecognisable_helper_inline() {
    let plain = Expr::let_named(
        Name::from_string("p.go"),
        nat(),
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), nat()),
        Expr::bvar(0),
        false,
    );
    let Rewritten {
        found, inline, out, ..
    } = rewrite(&["p.go"], &plain);
    assert!(found.is_empty());
    assert!(inline.contains(&Name::from_string("p.go")));
    assert_eq!(out, plain);
}

fn definition(name: &str) -> ElabResult {
    ElabResult::Definition {
        name: Name::from_string(name),
        universe_params: Vec::new(),
        ty: nat(),
        val: nat(),
        modifiers: DeclModifiers::default(),
    }
}

/// `parent` with its lifted helpers reads as `parent` — for the callers that
/// ask about the declaration (parameter names, editor info, staged header) —
/// while a block of siblings is about no one declaration.
#[test]
fn test_primary_leaf_of_lifted_helpers_is_the_parent() {
    let lifted = ElabResult::Multiple(vec![
        definition("p.go"),
        definition("p.go.inner"),
        definition("p"),
    ]);
    let primary = lifted.primary_leaf().and_then(ElabResult::declaration_name);
    assert_eq!(primary, Some(&Name::from_string("p")));
    assert_eq!(lifted.declaration_name(), Some(&Name::from_string("p")));

    // A namespace block's members are siblings: no primary declaration, and
    // `declaration_name` keeps naming the first member.
    let block = ElabResult::Multiple(vec![definition("N.a"), definition("N.b")]);
    assert!(block.primary_leaf().is_none());
    assert_eq!(block.declaration_name(), Some(&Name::from_string("N.a")));

    // A helper that is NOT under the last declaration's name is no helper.
    let unrelated = ElabResult::Multiple(vec![definition("q.go"), definition("p")]);
    assert!(unrelated.primary_leaf().is_none());
    assert_eq!(
        unrelated.declaration_name(),
        Some(&Name::from_string("q.go"))
    );
}

/// A type with failed `deriving` classes beside it reads as the type.
#[test]
fn test_primary_leaf_of_type_with_failed_deriving_is_the_type() {
    let decl = clean_parser::parse_decl("def x : Nat := 1").expect("parses");
    let failed = ElabResult::Failed {
        name: "instReprT".to_string(),
        decl: Box::new(decl),
        error: Box::new(ElabError::CannotInfer),
    };
    let result = ElabResult::Multiple(vec![definition("T"), failed]);
    let primary = result.primary_leaf().and_then(ElabResult::declaration_name);
    assert_eq!(primary, Some(&Name::from_string("T")));
}

/// A finished scope that lifted `p.go`: recursive or not, under a `partial`
/// parent or not.
fn scope_with_helper(parent_partial: bool, recursive: bool) -> LetRecLiftScope {
    let go = Name::from_string("p.go");
    LetRecLiftScope {
        decl_names: vec![Name::from_string("p")],
        lifted: vec![go.clone()],
        parent_partial,
        recursive: if recursive {
            HashSet::from([go])
        } else {
            HashSet::new()
        },
        ..LetRecLiftScope::default()
    }
}

fn partial_modifiers() -> DeclModifiers {
    DeclModifiers {
        is_partial: true,
        ..DeclModifiers::default()
    }
}

/// A recursive helper of a `partial` declaration that reaches the
/// declaration boundary in NEITHER form — not lifted, not inline: a
/// finishing pass dropped its binding — registers nothing, so `p.go` could
/// not be the opaque Lean declares (pinned v4.8.0: `opaque pu.go : Nat → Nat`
/// even when `pu` never calls it). Refused, fail-closed, like the inline form.
#[test]
fn test_finish_partial_recursive_helper_missing_at_boundary_refused() {
    let env = clean_kernel::Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let body = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), nat());
    let error = ctx
        .finish_let_rec_lifts(
            Some(scope_with_helper(true, true)),
            &[],
            &partial_modifiers(),
            body,
        )
        .expect_err("a missing recursive helper of a partial parent is refused");
    match error {
        ElabError::WhereLetRecUnsupported { name, .. } => assert_eq!(name, "p.go"),
        other => panic!("expected WhereLetRecUnsupported for p.go, got {other:?}"),
    }
}

/// Controls for the refusal above: a missing helper that is NOT a recursive
/// helper of a `partial` parent stays the historical no-op (nothing
/// registers, the value is unchanged), and a recursive helper of a `partial`
/// parent that DOES arrive in lifted form registers as an opaque.
#[test]
fn test_finish_partial_boundary_check_controls_pass() {
    let env = clean_kernel::Environment::with_prelude();
    let body = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), nat());
    for (parent_partial, recursive) in [(false, true), (true, false)] {
        let mut ctx = ElabCtx::new(&env);
        let (auxiliaries, val) = ctx
            .finish_let_rec_lifts(
                Some(scope_with_helper(parent_partial, recursive)),
                &[],
                &DeclModifiers {
                    is_partial: parent_partial,
                    ..DeclModifiers::default()
                },
                body.clone(),
            )
            .unwrap_or_else(|e| panic!("partial={parent_partial} recursive={recursive}: {e:?}"));
        assert!(auxiliaries.is_empty());
        assert_eq!(val, body);
    }

    // `let p.go : Nat → Nat := (fun x => x) (fun y => y); p.go Nat.zero`.
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let marked = Expr::let_named(
        Name::from_string("p.go"),
        Expr::pi(BinderInfo::Default, nat(), nat()),
        lifted(Vec::new()),
        Expr::app(Expr::bvar(0), zero.clone()),
        false,
    );
    let mut ctx = ElabCtx::new(&env);
    let (auxiliaries, val) = ctx
        .finish_let_rec_lifts(
            Some(scope_with_helper(true, true)),
            &[],
            &partial_modifiers(),
            marked,
        )
        .expect("a lifted recursive helper of a partial parent registers");
    assert!(
        matches!(auxiliaries.as_slice(), [ElabResult::Opaque { name, .. }] if name == &Name::from_string("p.go")),
        "{auxiliaries:?}"
    );
    assert_eq!(
        val,
        Expr::app(Expr::const_(Name::from_string("p.go"), vec![]), zero)
    );
}
