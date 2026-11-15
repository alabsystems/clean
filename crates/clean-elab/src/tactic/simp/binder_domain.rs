// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type discipline on simp's matched pattern bindings.
//!
//! # Why this guard exists
//!
//! Simp's matcher mints one metavariable per lemma binder
//! ([`super::pattern::convert_bvars_to_metas`]) with the PLACEHOLDER type
//! `Expr::type_()` — the lemma binder's declared domain is discarded there —
//! and `MetaState::assign` performs an occurs check and an undo record but no
//! type check. Between them, nothing stops a lemma binder declared
//! `(p : Prop)` from capturing a goal subterm of type `Sort v`.
//!
//! Nothing downstream catches it either, and each miss is for its own reason.
//! `lhs_inst ≡ expr` is satisfied — the reconstructed LHS IS the same term.
//! `proof_matches_rewrite` runs `ProofState::infer_type`, the kernel's
//! `infer_only` fast path, which never checks an application argument against
//! its binder domain. `template_has_unsolved_level` looks for the lemma's own
//! *unsolved universe parameters*, whereas here every level is solved and the
//! EXPRESSION is the ill-typed part. So the first thing to object is
//! `close_goal`'s `infer_type_strict`, by which point the ill-typed proof is
//! already the tactic's output and the whole declaration dies with
//! `TypeMismatch { expected: Sort(Zero), inferred: Sort(Param(..)) }`.
//!
//! Measured shape (`reports/source-elab/universe-binder-domain-2026-08-31.json`):
//! `capRhs : ∀ (p : Prop), (p → True) = p` against
//! `{γ : Sort v} : (γ → True) ↔ True` kills the declaration, and it does so
//! EVEN WHEN the correct universe-polymorphic lemma is also in the simp set —
//! the `Prop`-binder lemma is tried first, matches, and the honest candidate
//! never runs. Refusing the ill-typed match turns a declaration-killing kernel
//! error into an ordinary "this lemma did not apply" and lets the next
//! candidate fire, which is where the recovered declarations come from.
//!
//! # Why it refuses only what it can prove wrong
//!
//! Every uncertainty is fail-OPEN (skip the binder, or return `false`), so the
//! guard is purely restrictive on matches it can positively refute:
//!
//! * a rule minted from a LOCAL hypothesis whose name happens to collide with
//!   an environment constant — reading that constant's telescope would describe
//!   a completely different lemma, so the whole check is skipped (the same
//!   shadowing rule `bind_undetermined_binders` and `lemmas::resolve_unfold_defs`
//!   apply);
//! * a lemma with no environment entry at all (Clean's hand-written builtin
//!   patterns have no declared telescope to read);
//! * a lemma whose stored pattern the declaration's own type does NOT
//!   re-derive — a SYNTHESIZED lemma registered under an existing name, whose
//!   BVar layout the declaration says nothing about. `rec_equations.rs`
//!   registers a per-constructor equation for a rec-compiled `def f` under the
//!   name `f`, whose declared type is `f`'s function type; without this clause
//!   the walk paired every key with the wrong domain and refused a good
//!   rewrite (measured: `test_b7_rec_iota_simp_equations_close` went red with
//!   `NoProgress { tactic: "simp" }`);
//! * a binder whose argument the LHS match never bound — a conditional lemma's
//!   premise, discharged later by `bind_undetermined_binders`;
//! * a domain still mentioning one of this attempt's UNSOLVED fresh universe
//!   levels ([`super::lemma_levels::LemmaLevels`]) — comparing `Sort ?u`
//!   against a concrete `Sort 1` here would be a false refusal; the levels the
//!   match and the bound arguments' types did solve are instantiated first;
//! * a domain or argument carrying loose `BVar`s, or either side still holding
//!   an unassigned metavariable — `infer_type` is not meaningful for those;
//! * an argument whose type cannot be inferred at all.
//!
//! # Indexing
//!
//! `bvar_to_meta`'s keys are the conclusion's de Bruijn indices — innermost
//! binder is `0` — which is exactly how
//! [`super::expr::collect_binder_types_in_conclusion`] returns the domains. So
//! key `i` pairs with `binder_types[i]` ABSOLUTELY, with no dependence on how
//! many keys happen to be present. That is what makes a sparse `bvar_to_meta`
//! (the normal state before `bind_undetermined_binders` runs) safe here: a
//! missing key skips its binder instead of shifting every later pairing.

use clean_kernel::Expr;

use crate::tactic::{Goal, ProofState};
use crate::unify::MetaState;

use super::expr::{
    collect_binder_types_in_conclusion, extract_equality_full, extract_iff_with_binders,
};
use super::lemma_levels::{is_local_rule, LemmaLevels};
use super::pattern::substitute_bvars_with_metas;
use super::types::SimpLemma;

/// Whether the match bound a pattern variable to a term the lemma's OWN binder
/// cannot accept.
///
/// # Contract
///
/// REQUIRES: unification has succeeded, so `metas` carries the match's bindings
/// ENSURES: `true` only when some bound argument's INFERRED type is
///   demonstrably not def-eq to its binder's declared domain, with both sides
///   free of loose BVars, unassigned metas and unsolved lemma universe
///   levels
/// ENSURES: `false` whenever the lemma's declared telescope cannot be read, or
///   for any individual binder the walk cannot judge
pub(super) fn binding_violates_declared_domain(
    state: &ProofState,
    goal: &Goal,
    lemma: &SimpLemma,
    levels: &LemmaLevels,
    metas: &MetaState,
    bvar_to_meta: &hashbrown::HashMap<u32, Expr>,
) -> bool {
    // A rule minted from a LOCAL hypothesis carries that hypothesis' name,
    // which may coincide with an environment constant whose telescope belongs
    // to a different lemma entirely. Same shadowing rule as
    // `bind_undetermined_binders`.
    if is_local_rule(lemma) {
        return false;
    }
    let Some(info) = state.env.get_const(&lemma.name) else {
        return false;
    };
    // The declaration's telescope describes THIS pattern only when the pattern
    // was lifted verbatim out of the declaration's own type. A SYNTHESIZED
    // lemma carries a `name` whose environment entry says nothing about its
    // BVar layout, and reading it pairs every key with the wrong domain.
    //
    // Measured, not hypothetical: `simp/rec_equations.rs` registers a
    // per-constructor equation for a rec-compiled `def f` under the name `f`,
    // whose declared type is `f`'s FUNCTION type — so this guard read
    // `MyList → MyList → MyList`'s binders against the equation's pattern
    // variables and refused a perfectly good rewrite. `simp
    // [MyList.append, ih]` then reported `NoProgress` and
    // `test_b7_rec_iota_simp_equations_close` went red. Requiring the
    // declaration to REPRODUCE `lemma.lhs` is the exact precondition the walk
    // below needs, and it also excludes Clean's hand-written builtin patterns
    // (whose `Const` heads spell `u_simp`, a name no declaration has).
    if !statement_yields_pattern(&info.type_, &lemma.lhs) {
        return false;
    }
    // The telescope in this attempt's fresh levels, so the levels the match
    // solved are instantiated into each domain below.
    let binder_types = collect_binder_types_in_conclusion(&levels.rename(&info.type_));

    for (index, raw_domain) in binder_types.iter().enumerate() {
        let Some(meta_expr) = bvar_to_meta.get(&(index as u32)) else {
            continue;
        };
        let domain = substitute_bvars_with_metas(raw_domain, bvar_to_meta);
        let domain = metas.instantiate_levels(&metas.instantiate(&domain));
        let arg = metas.instantiate_levels(&metas.instantiate(meta_expr));
        if !judgeable(&arg, &domain, levels) {
            continue;
        }
        if state
            .infer_type(goal, &arg)
            .is_ok_and(|arg_ty| !state.is_def_eq(goal, &arg_ty, &domain))
        {
            if std::env::var_os("CLEAN_SIMP_BINDER_DOMAIN_TRACE").is_some() {
                eprintln!(
                    "simp-binder-domain: refused lemma={} binder#{index} \
                     domain={domain:?} arg={arg:?}",
                    lemma.name
                );
            }
            return true;
        }
    }
    false
}

/// Whether the declaration's own type re-derives `pattern` as its rewrite LHS.
///
/// This is the precondition for reading `info.type_`'s Pi telescope as a
/// description of `bvar_to_meta`'s keys. Both env-lemma constructors in
/// `lemmas.rs` build the pattern this way — `extract_equality_full(&decl.type_)`
/// for an `Eq` conclusion, `extract_iff_with_binders` for an `Iff` one — so a
/// genuine registry / `simp only [X]` lemma reproduces exactly, while a
/// synthesized one does not.
pub(super) fn statement_yields_pattern(declared_type: &Expr, pattern: &Expr) -> bool {
    if extract_equality_full(declared_type).is_some_and(|(_, lhs, _)| lhs == *pattern) {
        return true;
    }
    if extract_iff_with_binders(declared_type).is_some_and(|(_, lhs, _)| lhs == *pattern) {
        return true;
    }
    // The rules `prop_lemmas` makes of any other statement — Lean's
    // `preprocess` — share the statement's telescope too.
    let mut body = declared_type;
    while let clean_kernel::ExprKind::Pi(_, _, codomain) = body.kind() {
        body = codomain;
    }
    preprocess_yields_pattern(body, pattern)
}

/// Whether one of the rules Lean's `preprocess` makes of the conclusion
/// `body` has `pattern` as its left-hand side (see `super::prop_lemmas`).
fn preprocess_yields_pattern(body: &Expr, pattern: &Expr) -> bool {
    if body == pattern {
        return true;
    }
    let clean_kernel::ExprKind::Const(head, _) = body.get_app_fn().kind() else {
        return false;
    };
    let args = body.get_app_args();
    let eq_lhs = |e: &Expr| {
        matches!(e.get_app_fn().kind(), clean_kernel::ExprKind::Const(n, _) if n.to_string() == "Eq")
            && e.get_app_args().get(1).is_some_and(|lhs| *lhs == pattern)
    };
    match (head.to_string().as_str(), args.as_slice()) {
        ("Not", [p]) => *p == pattern || eq_lhs(p),
        ("Ne", [ty, a, b]) => {
            *a == pattern
                || (matches!(pattern.get_app_fn().kind(), clean_kernel::ExprKind::Const(n, _) if n.to_string() == "Eq")
                    && pattern.get_app_args().as_slice() == [*ty, *a, *b])
        }
        ("And", [p, q]) => {
            preprocess_yields_pattern(p, pattern) || preprocess_yields_pattern(q, pattern)
        }
        ("Eq", [_, lhs, _]) | ("Iff", [lhs, _]) => *lhs == pattern,
        _ => false,
    }
}

/// Whether this (argument, declared domain) pair can be judged at all.
///
/// See the module docs for why each clause is a fail-open skip rather than a
/// refusal.
fn judgeable(arg: &Expr, domain: &Expr, levels: &LemmaLevels) -> bool {
    !arg.has_loose_bvars()
        && !domain.has_loose_bvars()
        && !contains_unassigned_meta(arg)
        && !contains_unassigned_meta(domain)
        && !levels.mentions_unsolved(domain)
}

/// Whether `expr` still carries an unassigned pattern metavariable.
///
/// Mirrors `expr.rs`'s check of the same name; metas are represented as
/// high-bit-tagged `FVar`s (`MetaState::to_fvar`).
fn contains_unassigned_meta(expr: &Expr) -> bool {
    struct V {
        found: bool,
    }
    impl clean_kernel::ExprVisitor for V {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: clean_kernel::FVarId) {
            if MetaState::from_fvar(id).is_some() {
                self.found = true;
            }
        }
    }
    let mut v = V { found: false };
    clean_kernel::ExprVisitor::visit_expr(&mut v, expr);
    v.found
}
