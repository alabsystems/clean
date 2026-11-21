// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Brick 88: dependent type-family second domains in multi-argument equation
//! defs.
//!
//! ```text
//! def T9 : Nat → Type | 0 => Bool | _+1 => Nat
//! def f7 : (n : Nat) → T9 n → Nat
//!   | 0, true  => 1
//!   | 0, false => 0
//!   | _+1, k   => (k : Nat)
//! ```
//!
//! The multiarg normalizer's per-COLUMN nullary-ctor rewrite (B83) cannot see
//! through the type family: the second domain is `T9 n`, not a bare inductive
//! ident, so `true`/`false` stay `SurfacePattern::Var`, the shared-name check
//! sees three different "names" and bails, and the curried fallback descopes
//! loudly (B86). The fix here refines the family PER ROW with a kernel `whnf`
//! probe built from the row's first-column pattern, rewrites that row's
//! second-column leaf against the refined inductive, and re-emits the def as
//!
//! ```text
//! def f7 (n : Nat) : T9 n → Nat :=
//!   match n with
//!   | 0   => fun (_x_dep0 : Bool) => match _x_dep0 with | true => 1 | false => 0
//!   | _+1 => fun (k : Nat) => (k : Nat)
//! ```
//!
//! keeping the dependent domain in the RETURN type, so the existing
//! expected-type-dependent motive machinery (`elab_match`, `!use_rec` only)
//! supplies each arm's refined expected type `T9 ctor_i → Nat`. The kernel
//! re-checks the final term as always.
//!
//! SOUNDNESS OF THE PROBE: a row's refinement is accepted only when
//! `whnf (F probe)` is a BARE inductive head. For literal/nullary-ctor probes
//! the probe IS the matched value. For an `inner+k` succ-tower probe the tower
//! wraps an opaque fresh fvar, so a bare-inductive whnf result proves the
//! reduction went through uniformly for EVERY instance of the pattern — a
//! family discriminating deeper than the pattern (`| 0 | 1 | _+2` probed at
//! depth 1) or compiled through `ite` leaves the probe stuck and the row bails.
//!
//! ENGAGEMENT GATE: everything is all-or-nothing. Any gate failure returns
//! `None` and the caller's `arm_leaves` are untouched (per-row rewrites happen
//! on a scratch copy), so every shape outside the slice takes today's path
//! byte-identically.
//!
//! EXPLICITLY DEFERRED: recursive f7-class (dependent motive is `!use_rec`
//! only); arity > 2 and multiple dependent columns; parameterized /
//! universe-polymorphic families (`F : Nat → Type u`, applied whnf heads like
//! `Option Nat`); namespaced family references (inherits B83's bare-name
//! resolution); all-pass-through dependent columns (no structural leaf — those
//! keep today's path, whatever it does).

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, LocalContext, TypeChecker};
use clean_parser::{
    SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceLit, SurfaceMatchArm, SurfaceName,
    SurfacePattern,
};

use super::elab_decl_value::{is_structural_pattern, peel_n_domains};

/// The detected `(d : I) → F d → R` shape of a two-argument equation def.
#[derive(Clone, PartialEq, Eq)]
enum DispatchKey {
    Literal(u64),
    Tower,
    Constructor(Name),
}

struct DepFamily {
    /// The type-family constant (`T9`).
    family: Name,
    /// The column-0 domain inductive's surface name (`Nat`).
    col0_ind: SurfaceName,
    /// The DECLARED Pi binder name for column 0 (`n`).
    binder: SurfaceName,
}

/// Strip surface parens.
fn unwrap_paren(e: &SurfaceExpr) -> &SurfaceExpr {
    let mut cur = e;
    while let SurfaceExpr::Paren(_, inner) = cur {
        cur = inner;
    }
    cur
}

/// Honest-slice shape gate: arity 2; `domains[1]` is `App(Ident F, [Ident d])`
/// with `d` the DECLARED binder name of `domains[0]`; `domains[0]` is a bare
/// ident naming a registered inductive; `F` is a registered level-free
/// definition WITH a value (so the kernel probe can delta-unfold it).
fn detect_dependent_domain(
    env: &Environment,
    domains: &[(SurfaceExpr, Option<SurfaceName>, SurfaceBinderInfo)],
) -> Option<DepFamily> {
    let [(d0, d0_name, _), (d1, _, _)] = domains else {
        return None;
    };
    let binder = d0_name.clone()?;
    let SurfaceExpr::Ident(_, col0_ind) = unwrap_paren(d0) else {
        return None;
    };
    env.get_inductive(&col0_ind.name().clone())?;
    let SurfaceExpr::App(_, f, args) = unwrap_paren(d1) else {
        return None;
    };
    let SurfaceExpr::Ident(_, family_name) = unwrap_paren(f) else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    if arg.name.is_some() {
        return None;
    }
    let SurfaceExpr::Ident(_, dep_arg) = unwrap_paren(&arg.expr) else {
        return None;
    };
    if *dep_arg != binder {
        return None;
    }
    let family = family_name.name().clone();
    let ci = env.get_const(&family)?;
    if ci.value.is_none() || !ci.level_params.is_empty() {
        return None;
    }
    Some(DepFamily {
        family,
        col0_ind: col0_ind.clone(),
        binder,
    })
}

/// Resolve `cname` (bare `true` or qualified `Bool.true`) as a NULLARY,
/// parameter-free, level-free constructor of `ind_name`. Parameter/level
/// freedom keeps the `Expr::const_str` probe term well-formed.
fn resolve_nullary_ctor(
    env: &Environment,
    ind_name: &SurfaceName,
    cname: &SurfaceName,
) -> Option<Name> {
    let candidates = [cname.clone(), ind_name.append(cname)];
    candidates.into_iter().find_map(|cand| {
        let name = cand.into_name();
        let cv = env.get_constructor(&name)?;
        (&cv.inductive_name == ind_name.name()
            && cv.num_fields == 0
            && cv.num_params == 0
            && cv.level_params.is_empty())
        .then_some(name)
    })
}

/// Kernel-probe the family at a row's first-column pattern. Returns the
/// refined domain inductive (`Bool` for a `0` row of `T9`, `Nat` for a `_+1`
/// row) or `None` when the pattern is outside the probe envelope or the whnf
/// is stuck / not a bare level-free inductive head.
fn probe_row_refined_domain(
    env: &Environment,
    dep: &DepFamily,
    col0_leaf: &SurfacePattern,
) -> Option<Name> {
    let mut lctx = LocalContext::new();
    let probe = match col0_leaf {
        SurfacePattern::Lit(SurfaceLit::Nat(v))
            if dep.col0_ind == SurfaceName::generated_path("Nat") =>
        {
            Expr::nat_lit(*v)
        }
        SurfacePattern::NumeralAdd(inner, k)
            if dep.col0_ind == SurfaceName::generated_path("Nat")
                && *k >= 1
                && matches!(**inner, SurfacePattern::Var(_) | SurfacePattern::Wildcard) =>
        {
            let fv = lctx.push(
                Name::from_string("_probe"),
                Expr::const_str("Nat"),
                BinderInfo::Default,
            );
            let mut e = Expr::fvar(fv);
            for _ in 0..*k {
                e = Expr::app(Expr::const_str("Nat.succ"), e);
            }
            e
        }
        SurfacePattern::Ctor(cname, sub) if sub.is_empty() => {
            let resolved = resolve_nullary_ctor(env, &dep.col0_ind, cname)?;
            Expr::const_(resolved, vec![])
        }
        _ => return None,
    };
    let tc = TypeChecker::with_context(env, lctx);
    let reduced = tc.whnf(&Expr::app(Expr::const_(dep.family.clone(), vec![]), probe));
    match reduced.kind() {
        ExprKind::Const(ind, levels) if levels.is_empty() && env.get_inductive(ind).is_some() => {
            Some(ind.clone())
        }
        _ => None,
    }
}

/// Per-ROW check of the second column against the row's REFINED inductive.
/// Constructors that ordinary name resolution gives were already rewritten by
/// the caller (`PatternIdents`); a `Var` leaf left that names a nullary
/// constructor of the refined inductive only through its namespace
/// (`Refined.name`) is ambiguous — Lean 4 binds it — so the lane declines
/// (`None`) and the def goes to the typed path, which refuses it.
fn check_leaf_for(env: &Environment, refined: &Name, leaf: &SurfacePattern) -> Option<()> {
    if let SurfacePattern::Var(name) = leaf {
        let shorthand = crate::namespace::append_names(refined, name.name());
        if name.parent().is_anonymous()
            && env
                .get_constructor(&shorthand)
                .is_some_and(|cv| cv.inductive_name == *refined && cv.num_fields == 0)
        {
            return None;
        }
    }
    Some(())
}

/// The possible first-column heads in a dependent match on an enumeration.
pub(super) fn enum_constructors<'env>(env: &'env Environment, name: &Name) -> Option<&'env [Name]> {
    let family = env.get_inductive(name)?;
    (family.num_indices == 0
        && family.constructor_names.iter().all(|name| {
            env.get_constructor(name)
                .is_some_and(|ctor| ctor.num_fields == 0)
        }))
    .then_some(&family.constructor_names)
}

/// A named, nonrecursive two-column family can also have an applied result
/// like `And P Q`. When its first column consists only of enum constructors,
/// the typed pattern-lambda path specializes the full domain in each branch.
pub(super) fn has_dependent_enum_patterns(
    env: &Environment,
    domains: &[(SurfaceExpr, Option<SurfaceName>, SurfaceBinderInfo)],
    arm_leaves: &[Vec<SurfacePattern>],
) -> bool {
    let Some(dep) = detect_dependent_domain(env, domains) else {
        return false;
    };
    enum_constructors(env, dep.col0_ind.name()).is_some()
        && arm_leaves.iter().any(|row| is_structural_pattern(&row[1]))
        && arm_leaves.iter().all(|row| {
            matches!(&row[0], SurfacePattern::Ctor(ctor, fields)
                if fields.is_empty() && resolve_nullary_ctor(env, &dep.col0_ind, ctor).is_some())
        })
}

/// The Brick-88 lowering. All-or-nothing: `None` leaves the caller's state
/// untouched and the def on today's path byte-identically.
pub(super) fn try_emit_dependent_family(
    env: &Environment,
    ty: &SurfaceExpr,
    domains: &[(SurfaceExpr, Option<SurfaceName>, SurfaceBinderInfo)],
    arm_leaves: &[Vec<SurfacePattern>],
    arms: &[SurfaceMatchArm],
    is_recursive: bool,
) -> Option<(Vec<SurfaceBinder>, Option<SurfaceExpr>, SurfaceExpr)> {
    // The expected-type-dependent motive this emission relies on is
    // `!use_rec` only (elab_match); recursive f7-class is deferred.
    if is_recursive {
        return None;
    }
    let dep = detect_dependent_domain(env, domains)?;

    // Probe EVERY row (all-or-nothing).
    let refined: Vec<Name> = arm_leaves
        .iter()
        .map(|leaves| probe_row_refined_domain(env, &dep, &leaves[0]))
        .collect::<Option<_>>()?;

    // Column-0 disjointness gates + per-row dispatch keys: never mix ctor
    // dispatch with Nat lit/tower dispatch; at most ONE succ-tower shape (two
    // different towers overlap), textually identical across its rows; every
    // lit value below the tower depth. Distinct keys are then pairwise
    // DISJOINT, so regrouping rows by key preserves first-match-wins.
    let mut tower: Option<(Option<SurfaceName>, u64)> = None;
    let mut lit_vals: Vec<u64> = Vec::new();
    let mut saw_ctor = false;
    let mut keys: Vec<DispatchKey> = Vec::with_capacity(arm_leaves.len());
    for leaves in arm_leaves {
        match &leaves[0] {
            SurfacePattern::Lit(SurfaceLit::Nat(v)) => {
                lit_vals.push(*v);
                keys.push(DispatchKey::Literal(*v));
            }
            SurfacePattern::NumeralAdd(inner, k) => {
                let key = match inner.as_ref() {
                    SurfacePattern::Var(name) => Some(name.clone()),
                    SurfacePattern::Wildcard => None,
                    _ => return None,
                };
                match &tower {
                    None => tower = Some((key, *k)),
                    Some((prev, depth)) if *prev == key && *depth == *k => {}
                    Some(_) => return None,
                }
                keys.push(DispatchKey::Tower);
            }
            // Key nullary ctors by their RESOLVED name, so `true` and
            // `Bool.true` rows group together instead of forming two
            // overlapping arms.
            SurfacePattern::Ctor(cname, _) => {
                saw_ctor = true;
                keys.push(DispatchKey::Constructor(resolve_nullary_ctor(
                    env,
                    &dep.col0_ind,
                    cname,
                )?));
            }
            _ => return None,
        }
    }
    if saw_ctor && (tower.is_some() || !lit_vals.is_empty()) {
        return None;
    }
    if let Some((_, depth)) = &tower {
        if lit_vals.iter().any(|v| *v >= *depth) {
            return None;
        }
    }

    // Per-row check of the SECOND column against the row's refined inductive
    // (its constructors were resolved by the caller).
    for (leaves, r) in arm_leaves.iter().zip(&refined) {
        check_leaf_for(env, r, &leaves[1])?;
    }
    let rewritten: Vec<SurfacePattern> =
        arm_leaves.iter().map(|leaves| leaves[1].clone()).collect();

    // ENGAGEMENT GATE: at least one row's second column must be structural
    // after the rewrite. All-pass-through dependent columns already route
    // through the slice-2 normalizer today; leave them byte-identical.
    if !rewritten.iter().any(is_structural_pattern) {
        return None;
    }

    // Group rows by dispatch key, preserving first-appearance order (groups
    // are pairwise disjoint; within a group row order is kept).
    let mut group_keys: Vec<DispatchKey> = Vec::new();
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for (i, key) in keys.iter().enumerate() {
        match group_keys.iter().position(|k| k == key) {
            Some(g) => groups[g].push(i),
            None => {
                group_keys.push(key.clone());
                groups.push(vec![i]);
            }
        }
    }

    // Lift ONLY column 0 as a declaration binder under its DECLARED name; the
    // residual tail (`T9 n → Nat`) becomes the return type, converting
    // hypothesis-dependence (unsupported) into expected-type dependence
    // (supported: the dependent motive instantiates it per arm).
    let (_, tail) = peel_n_domains(ty, 1)?;
    let lifted = SurfaceBinder::new_typed(
        dep.binder.clone(),
        Some(domains[0].0.clone()),
        SurfaceBinderInfo::Explicit,
    );

    let span = arms.first()?.span;
    let mut match_arms: Vec<SurfaceMatchArm> = Vec::with_capacity(groups.len());
    for (gi, rows) in groups.iter().enumerate() {
        let first = rows[0];
        let refined_ident =
            SurfaceExpr::Ident(span, SurfaceName::from_name(refined[first].clone()));
        // The λ binder is deliberately ANNOTATED with the refined inductive:
        // the arm's expected type is `T9 ctor_i → Nat` and the annotation is
        // kernel-defeq to its domain (delta + iota) — checked, loud on
        // mismatch.
        let body = match (rows.as_slice(), &rewritten[first]) {
            // Single pass-through row: bind the second argument directly
            // under its surface name (or `_`).
            (
                [ri],
                SurfacePattern::Var(_) | SurfacePattern::Wildcard | SurfacePattern::Ellipsis,
            ) => {
                let name = match &rewritten[first] {
                    SurfacePattern::Var(v) => v.clone(),
                    _ => SurfaceName::generated_path("_"),
                };
                SurfaceExpr::Lambda(
                    span,
                    vec![SurfaceBinder::new_typed(
                        name,
                        Some(refined_ident),
                        SurfaceBinderInfo::Explicit,
                    )],
                    Box::new(arms[*ri].body.clone()),
                )
            }
            _ => {
                // Unspellable: this binder encloses the arm bodies, so a
                // spellable `_x_dep<n>` captured a body's reference to a global
                // of that spelling.
                let scrut_name = SurfaceName::unspellable("_x_dep", gi as u64);
                let inner_arms: Vec<SurfaceMatchArm> = rows
                    .iter()
                    .map(|&ri| SurfaceMatchArm {
                        span: arms[ri].span,
                        pattern: rewritten[ri].clone(),
                        body: arms[ri].body.clone(),
                    })
                    .collect();
                SurfaceExpr::Lambda(
                    span,
                    vec![SurfaceBinder::new_typed(
                        scrut_name.clone(),
                        Some(refined_ident),
                        SurfaceBinderInfo::Explicit,
                    )],
                    Box::new(SurfaceExpr::Match(
                        span,
                        None,
                        Box::new(SurfaceExpr::Ident(span, scrut_name)),
                        inner_arms,
                    )),
                )
            }
        };
        match_arms.push(SurfaceMatchArm {
            span: arms[first].span,
            pattern: arm_leaves[first][0].clone(),
            body,
        });
    }

    let match_body = SurfaceExpr::Match(
        span,
        None,
        Box::new(SurfaceExpr::Ident(span, dep.binder.clone())),
        match_arms,
    );
    Some((vec![lifted], Some(tail), match_body))
}
