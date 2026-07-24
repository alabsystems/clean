// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shadow faithfulness — the fail-closed guard behind graduation v3.2.
//!
//! Dependency resolution short-circuits on recheck-environment presence:
//! a referenced constant that already exists in the recheck environment is
//! silently *substituted* for the source spelling. That substitution is only
//! honest when the two names denote the SAME kernel object. The 2026-06-12
//! kernel-parity sweep proved they often do not: Clean's prelude overlay
//! `Monoid` (5 unbundled fields) shadowed mathlib's `Monoid` (subobject
//! parent `toSemigroup`), typing the carried parent projection at the
//! flattened field-function type, and the prelude's Opaque `Nat.mod`
//! placeholder shadowed Lean core's pattern-matching definition, killing
//! `Nat.mod_lt`'s replay (33 distinct shadow mismatches in a single small
//! mathlib module's closure).
//!
//! [`shadow_guard`] re-checks every silently-substituted dependency: the
//! recheck spelling must match the source spelling up to kernel-meaningless
//! metadata (binder info, `MData`, elaborator annotations, level-parameter
//! alpha-renaming). Anything else fails closed with
//! `prelude-shadow-mismatch` — never substituted, never downgraded. The
//! shadow-free fix is [`super::intake::RecheckBase::LeanCore`], which leaves
//! (almost) nothing in the recheck base to shadow in the first place.

use std::collections::HashMap;

use clean_kernel::expr::ExprKind;
use clean_kernel::{ConstantKind, Environment, Expr, Level, Name};

use super::intake_family::consume_telescope_annotations;

/// Memo of completed shadow checks: name (family ROOT for family members)
/// -> `None` (faithful) or `Some(reason)` (mismatch; cached fail-closed).
#[derive(Debug, Default)]
pub(super) struct ShadowChecks {
    checked: HashMap<String, Option<String>>,
}

/// Structural expression equality ignoring binder info AND `MData` wrappers
/// (kernel-meaningless metadata: the `.olean` import preserves `@[mdata]`
/// nodes on some toolchain types that locally-built spellings lack; the
/// kernel's own checking looks through both). Everything kernel-meaningful —
/// de Bruijn structure, constants, literals, universe levels, projections,
/// let-binder names, QTT multiplicity — must match exactly.
pub(super) fn exprs_equal_ignoring_binder_info_and_mdata(a: &Expr, b: &Expr) -> bool {
    fn peel(mut e: &Expr) -> &Expr {
        while let ExprKind::MData(_, inner) = e.kind() {
            e = inner;
        }
        e
    }
    let mut stack: Vec<(&Expr, &Expr)> = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        let (a, b) = (peel(a), peel(b));
        match (a.kind(), b.kind()) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                stack.push((f1, f2));
                stack.push((a1, a2));
            }
            (ExprKind::Lam(d1, t1, b1), ExprKind::Lam(d2, t2, b2))
            | (ExprKind::Pi(d1, t1, b1), ExprKind::Pi(d2, t2, b2)) => {
                if d1.mult != d2.mult {
                    return false;
                }
                stack.push((t1, t2));
                stack.push((b1, b2));
            }
            (ExprKind::Let(n1, t1, v1, b1, nd1), ExprKind::Let(n2, t2, v2, b2, nd2)) => {
                if n1 != n2 || nd1 != nd2 {
                    return false;
                }
                stack.push((t1, t2));
                stack.push((v1, v2));
                stack.push((b1, b2));
            }
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                if n1 != n2 || i1 != i2 {
                    return false;
                }
                stack.push((e1, e2));
            }
            (ka, kb) => {
                if ka != kb {
                    return false;
                }
            }
        }
    }
    true
}

/// Compare two spellings of one constant's type or value: source level
/// params are alpha-renamed (positionally) to the recheck names, elaborator
/// annotations consumed on the source telescope, binder info and `MData`
/// ignored.
pub(super) fn shadow_exprs_equal(
    src_levels: &[Name],
    src_expr: &Expr,
    rc_levels: &[Name],
    rc_expr: &Expr,
) -> bool {
    if src_levels.len() != rc_levels.len() {
        return false;
    }
    let src_expr = consume_telescope_annotations(src_expr);
    let renamed;
    let src_cmp = if src_levels == rc_levels {
        &src_expr
    } else {
        let target: Vec<Level> = rc_levels.iter().map(|n| Level::param(n.clone())).collect();
        renamed = src_expr.instantiate_level_params_direct(src_levels, &target);
        &renamed
    };
    exprs_equal_ignoring_binder_info_and_mdata(src_cmp, rc_expr)
}

impl ShadowChecks {
    /// Fail-closed faithfulness check for a dependency about to be silently
    /// satisfied by a recheck-environment constant of the same name.
    ///
    /// Returns `Ok(())` when the source environment has no constant of that
    /// name (nothing was shadowed), or when the two spellings denote the
    /// same kernel object. Returns the audit-ready reject reason otherwise.
    /// Results are memoized per name (family members memoize their root).
    pub(super) fn guard(
        &mut self,
        source: &Environment,
        recheck: &Environment,
        dep: &str,
    ) -> Result<(), String> {
        let dep_name = Name::from_string(dep);
        // Family members (and roots) are diagnosed at their root: the
        // recheck object a member reference resolves against is determined
        // by the family.
        let family_root = super::intake_family::inductive_family_root(source, &dep_name);
        let key = family_root
            .as_ref()
            .map_or_else(|| dep.to_string(), Name::to_string);
        if let Some(cached) = self.checked.get(&key) {
            return match cached {
                None => Ok(()),
                Some(reason) => Err(reason.clone()),
            };
        }
        let verdict = match &family_root {
            Some(root) => check_family(source, recheck, root),
            None => check_constant(source, recheck, &dep_name),
        };
        self.checked.insert(key, verdict.clone().err());
        verdict
    }
}

fn mismatch(name: &Name, detail: String) -> Result<(), String> {
    Err(format!(
        "prelude-shadow-mismatch: recheck-environment `{name}` silently shadows the source \
         spelling but is not the same kernel object ({detail}) — the substitution would not \
         be Lean-faithful, so the dependency fails closed"
    ))
}

/// Plain-constant shadow check: kind, level-param arity, type, and (for
/// definitions, whose values are delta-relevant) value must agree. Theorem
/// proof values are proof-irrelevant and not compared.
fn check_constant(source: &Environment, recheck: &Environment, name: &Name) -> Result<(), String> {
    let (Some(src), Some(rc)) = (source.get_const(name), recheck.get_const(name)) else {
        return Ok(());
    };
    if src.kind != rc.kind {
        return mismatch(name, format!("kind {:?} vs {:?}", src.kind, rc.kind));
    }
    if !shadow_exprs_equal(&src.level_params, &src.type_, &rc.level_params, &rc.type_) {
        return mismatch(name, format!("type `{}` vs `{}`", src.type_, rc.type_));
    }
    if src.kind == ConstantKind::Definition {
        match (&src.value, &rc.value) {
            (Some(a), Some(b)) if shadow_exprs_equal(&src.level_params, a, &rc.level_params, b) => {
            }
            (None, None) => {}
            _ => return mismatch(name, "definition values differ".to_string()),
        }
    }
    Ok(())
}

/// Family shadow check: the source family's root type, parameter count,
/// level-param arity, and constructor names/types must agree with the
/// recheck family of the same name.
fn check_family(source: &Environment, recheck: &Environment, root: &Name) -> Result<(), String> {
    let Some(src) = source.get_inductive(root) else {
        return Ok(());
    };
    let Some(rc) = recheck.get_inductive(root) else {
        if recheck.get_const(root).is_some() {
            return mismatch(
                root,
                "source family root is shadowed by a non-inductive constant".to_string(),
            );
        }
        return Ok(());
    };
    if src.num_params != rc.num_params {
        return mismatch(
            root,
            format!("num_params {} vs {}", src.num_params, rc.num_params),
        );
    }
    if !shadow_exprs_equal(&src.level_params, &src.type_, &rc.level_params, &rc.type_) {
        return mismatch(root, "family root types differ".to_string());
    }
    if src.constructor_names != rc.constructor_names {
        return mismatch(
            root,
            format!(
                "constructor names {:?} vs {:?}",
                src.constructor_names, rc.constructor_names
            ),
        );
    }
    for ctor in &src.constructor_names {
        let (Some(s), Some(r)) = (source.get_constructor(ctor), recheck.get_constructor(ctor))
        else {
            return mismatch(root, format!("constructor `{ctor}` missing on one side"));
        };
        if !shadow_exprs_equal(&s.level_params, &s.type_, &r.level_params, &r.type_) {
            return mismatch(
                root,
                format!("constructor `{ctor}` type `{}` vs `{}`", s.type_, r.type_),
            );
        }
    }
    Ok(())
}
