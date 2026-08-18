// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value-bearing declaration elaboration: Definition, Theorem, Axiom, Opaque
//!
//! Extracted from `elaborate_decl.rs` to keep files under 500 lines.
//! Each method is called from the corresponding match arm in
//! `ElabCtx::elab_decl_inner`.

use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolder, ExprVisitor, FVarId, Level, LevelVec};
use clean_parser::{
    Attribute, DeclModifiers, SurfaceBinder, SurfaceExpr, SurfacePattern, TerminationHints,
    WhereLocalDef,
};
use std::collections::HashMap;

use super::{convert_binder_info, ElabCtx, ElabResult, RecursiveDefContext, RecursiveExtraParam};

/// Normalize an equation-form declaration into the equivalent named-binder +
/// explicit-`match` shape, so the already-working structural-recursion lowering
/// (which resolves the decreasing argument against the declaration's *binders*)
/// fires for equation defs like:
///
/// ```text
/// def factorial : Nat → Nat
///   | 0 => 1
///   | Nat.succ n => (Nat.succ n) * factorial n
/// ```
///
/// The parser (`def_match_body`) desugars the equation arms into a value
/// `PatternMatchLambda([_x], Match(_x, arms))` with an **empty** declaration
/// `binders` list — the `Nat → Nat` lives in `ty`. Recursion *detection* still
/// works, but `setup_recursion` resolves the decreasing-arg position against
/// `binders`, which is empty, so no `RecursiveDefContext` is installed and the
/// self-name `factorial` is left as a placeholder typed `Nat`; `factorial n`
/// then over-applies and surfaces as `TooManyArguments`.
///
/// This helper lifts the synthetic `_x` lambda binder into a real declaration
/// binder by peeling one domain off the declaration arrow/Pi type, turning the
/// equation def into exactly the named-binder + `match` form that already
/// elaborates to a genuine `T.rec` application and kernel-checks.
///
/// Returns `Some((lifted_binders, new_return_ty, match_body))` when the
/// equation-form shape is recognized, or `None` to leave the declaration
/// untouched (the common, non-equation path).
///
/// SCOPE (slice 1): single decreasing argument. The parser always emits exactly
/// one synthetic `_x` binder, so multi-arg equation defs (parsed as a single
/// `_x` scrutinee matched against a `Prod.mk` tuple pattern) are intentionally
/// left alone: peeling a single domain off the type would not match the tuple
/// scrutinee, and tuple-`.rec` lowering is a separate follow-up. Multi-binder
/// pattern lambdas (which the def parser never produces) are likewise skipped.
///
/// Also reused by `try_elab_let_rec_lifted` (`infer/elab_core.rs`) to lift an
/// equation-form `where`/`let rec` helper's hidden `_x` scrutinee binder, so
/// such a helper routes through the identical structural-recursion lowering.
pub(in crate::infer) fn normalize_equation_def(
    env: &clean_kernel::Environment,
    def_name: &str,
    binders: &[SurfaceBinder],
    ty: Option<&SurfaceExpr>,
    val: &SurfaceExpr,
) -> Option<(Vec<SurfaceBinder>, Option<SurfaceExpr>, SurfaceExpr)> {
    // Trigger for the equation-def signature the parser emits: a
    // `PatternMatchLambda` value. Leading declaration binders (`def f (op : T)
    // (width : Nat) : A → B → C | …`) are allowed — they are kept in front of
    // the lifted equation-arg binders. This is exactly the `semVectorIntBinOp`
    // shape: explicit parameters before the multi-argument equation arrow.
    let SurfaceExpr::PatternMatchLambda(_span, lam_binders, lam_body) = val else {
        return None;
    };

    // Slice 1: arity-1 equation defs. The def parser always emits a single
    // synthetic `_x` binder regardless of arity (arity-N uses a tuple pattern
    // inside the single match), so gate on exactly one synthetic binder. This
    // keeps us conservative: it never fires for a user-written `fun | ...` with
    // its own binders, and defers multi-arg/tuple forms.
    let [lam_binder] = lam_binders.as_slice() else {
        return None;
    };
    if lam_binder.name != "_x" {
        return None;
    }

    // Multi-arg equation defs (`def f : A → B → C | a, b => ...`) are also
    // emitted by the parser as a single `_x` binder, but with arms whose
    // top-level pattern is a right-nested `Prod.mk` tuple over the multiple
    // arguments. Slices 2/3 lift that single `_x` into N named binders and
    // rewrite the tuple match into a single (or nested) single-scrutinee match,
    // so the *existing* sound single-arg `.rec` lowering fires.
    //
    // `normalize_equation_def_multiarg` recognizes the tuple shape and returns
    // the lifted form when it can do so soundly. When the shape is outside that
    // conservative envelope it returns `None`, and we fall back to the existing
    // (non-normalized) path — which still handles non-recursive multi-arg defs
    // like `addCases` via tuple `casesOn`. Any leading declaration binders are
    // prepended to the lifted equation-arg binders so they stay in scope (and so
    // the decreasing-arg position the recursion lowers on is offset past them).
    if let SurfaceExpr::Match(_, _, scrut, arms) = &**lam_body {
        if arms
            .iter()
            .any(|arm| matches!(&arm.pattern, SurfacePattern::Ctor(name, _) if name == "Prod.mk"))
        {
            let is_recursive =
                !def_name.is_empty() && super::structural::body_mentions_call(val, def_name);
            let (lifted, ret_ty, body) =
                normalize_equation_def_multiarg(env, ty, scrut, arms, is_recursive)?;
            let mut all_binders = binders.to_vec();
            all_binders.extend(lifted);
            return Some((all_binders, ret_ty, body));
        }
    }

    // Slice 1 (single-arg equation def): conservatively keep the historical
    // gate of *no* leading declaration binders. Single-arg defs with leading
    // binders already elaborate through other paths; routing them here too is
    // out of scope for this change and risks regressing them.
    if !binders.is_empty() {
        return None;
    }

    // Peel exactly one domain off the declaration type for the single binder.
    // The remaining tail becomes the new return type.
    //
    // - `Arrow(from, to)`: non-dependent (the `Nat → Nat` equation-def case).
    //   The binder gets type `from`; the return type becomes `to`.
    // - `Pi([p, ...], body)`: dependent. Peel the first Pi binder's type for
    //   `_x`; the remaining Pi binders (if any) re-wrap `body` as the return
    //   type, otherwise the return type is `body`.
    // `dep_name`: for a DEPENDENT `Pi` peel, the declared binder's name. The
    // residual return type may reference it (`def g : (b : Bool) → W b | …` —
    // the tail is `W b`). Lifting the value binder as the synthetic `_x` while
    // the return type still says `b` silently breaks the dependency: `b` no
    // longer resolves to the value binder, gets auto-bound as a FRESH fvar, and
    // every downstream consumer (the k=0 dependent-motive gate, the final
    // def-level check) sees two distinct fvars for the same parameter —
    // surfacing as MatchArmTypeMismatch on the second arm. Lift under the
    // DECLARED name instead (exactly Lean's equation-def semantics) and rename
    // the synthetic match scrutinee to match. Anonymous/`_` Pi binders keep
    // `_x` (nothing can reference them).
    let (binder_ty, new_return_ty, dep_name): (
        Option<SurfaceExpr>,
        Option<SurfaceExpr>,
        Option<String>,
    ) = match ty {
        Some(SurfaceExpr::Arrow(_, from, to)) => {
            (Some((**from).clone()), Some((**to).clone()), None)
        }
        Some(SurfaceExpr::Pi(span, pi_binders, body)) => {
            let (first, rest) = pi_binders.split_first()?;
            let from = first.ty.as_ref().map(|t| (**t).clone());
            let tail = if rest.is_empty() {
                (**body).clone()
            } else {
                SurfaceExpr::Pi(*span, rest.to_vec(), body.clone())
            };
            let name = (!first.name.is_empty() && first.name != "_").then(|| first.name.clone());
            (from, Some(tail), name)
        }
        // Unannotated (`None`) or a non-arrow type is not an equation def we can
        // soundly lift here — leave it for the existing paths.
        _ => return None,
    };

    let lifted_name = dep_name.unwrap_or_else(|| lam_binder.name.clone());
    let lifted_binder = SurfaceBinder::new(lifted_name.clone(), binder_ty, lam_binder.info);

    // Rename the parser's synthetic scrutinee (`match _x with …`) to the lifted
    // binder name. `_x` is parser-generated and appears ONLY as the scrutinee
    // ident — user code cannot contain it — so a targeted scrutinee rebuild is
    // exact. Any other body shape is left untouched (then `lifted_name` must be
    // `_x`, since only the Match shape reaches the dependent peel).
    let new_body = match (&**lam_body, lifted_name != lam_binder.name) {
        (SurfaceExpr::Match(sp, h, scrut, arms), true) if matches!(scrut.as_ref(), SurfaceExpr::Ident(_, n) if n == &lam_binder.name) =>
        {
            let scrut_span = scrut.span();
            SurfaceExpr::Match(
                *sp,
                h.clone(),
                Box::new(SurfaceExpr::Ident(scrut_span, lifted_name.clone())),
                arms.clone(),
            )
        }
        _ => (**lam_body).clone(),
    };

    let mut all_binders = binders.to_vec();
    all_binders.push(lifted_binder);
    Some((all_binders, new_return_ty, new_body))
}

/// Peel exactly `n` domains off a declaration arrow/Pi type, returning the
/// `n` peeled domain types (in order) and the residual return type.
///
/// Mirrors the single-domain peel in `normalize_equation_def` but for the
/// multi-argument equation-def case. Returns `None` if the type does not have
/// at least `n` arrow/Pi domains, or is unannotated/non-arrow (which we never
/// lift — the binder types must be recoverable from the declaration type).
pub(super) fn peel_n_domains(
    ty: &SurfaceExpr,
    n: usize,
) -> Option<(Vec<(SurfaceExpr, Option<String>)>, SurfaceExpr)> {
    // Each peeled domain carries the DECLARED Pi binder name (when named). A
    // dependent residual return type (`def f6 : (a : Nat) → (b : Bool) → W6 b
    // | …` — the tail is `W6 b`) references those names; lifting the equation
    // binders under synthetic `_x`/`_x_arg{pos}` names leaves them dangling,
    // to be auto-bound as FRESH fvars — the exact single-arg name-drop fixed
    // in `normalize_equation_def`, in its multiarg form. `Arrow` domains are
    // anonymous (nothing can reference them): `None`.
    let mut domains = Vec::with_capacity(n);
    let mut current = ty.clone();
    for _ in 0..n {
        match current {
            SurfaceExpr::Arrow(_, from, to) => {
                domains.push((*from, None));
                current = *to;
            }
            SurfaceExpr::Pi(span, pi_binders, body) => {
                let (first, rest) = pi_binders.split_first()?;
                let declared =
                    (!first.name.is_empty() && first.name != "_").then(|| first.name.clone());
                // A Pi binder without an explicit type cannot supply a binder
                // type; bail rather than fabricate one.
                domains.push(((**first.ty.as_ref()?).clone(), declared));
                current = if rest.is_empty() {
                    *body
                } else {
                    SurfaceExpr::Pi(span, rest.to_vec(), body)
                };
            }
            _ => return None,
        }
    }
    Some((domains, current))
}

/// Flatten a right-nested `Prod.mk(p0, Prod.mk(p1, ... p_{n-1}))` tuple pattern
/// into the flat leaf list `[p0, p1, ..., p_{n-1}]`.
///
/// The def-equation parser builds multi-argument arm patterns by right-folding
/// `Prod.mk` over the per-argument patterns (`def_match_body`), so a 2-arg arm
/// is `Prod.mk(p0, p1)` and a 3-arg arm is `Prod.mk(p0, Prod.mk(p1, p2))`. A
/// pattern that is not a `Prod.mk` is a single leaf.
fn flatten_prod_pattern(pat: &SurfacePattern) -> Vec<SurfacePattern> {
    let mut leaves = Vec::new();
    let mut current = pat.clone();
    loop {
        match current {
            SurfacePattern::Ctor(ref name, ref sub) if name == "Prod.mk" && sub.len() == 2 => {
                leaves.push(sub[0].clone());
                current = sub[1].clone();
            }
            other => {
                leaves.push(other);
                break;
            }
        }
    }
    leaves
}

/// Whether a pattern leaf is a structural (constructor / literal / `n+k`)
/// matched position, as opposed to a pass-through variable or wildcard.
pub(super) fn is_structural_pattern(pat: &SurfacePattern) -> bool {
    matches!(
        pat,
        SurfacePattern::Ctor(..)
            | SurfacePattern::Lit(_)
            | SurfacePattern::NumeralAdd(..)
            | SurfacePattern::As(..)
            | SurfacePattern::Or(..)
    )
}

/// Collect every identifier name appearing in a surface expression. Used to
/// decide whether a residual multiarg return type references a declared Pi
/// binder name (the dependent case) — over-approximation is safe (worst case a
/// declared name is adopted where synthetic would also have worked).
fn collect_free_idents_of(e: &SurfaceExpr) -> std::collections::HashSet<String> {
    fn walk(e: &SurfaceExpr, out: &mut std::collections::HashSet<String>) {
        match e {
            SurfaceExpr::Ident(_, n) => {
                out.insert(n.clone());
            }
            SurfaceExpr::App(_, f, args) => {
                walk(f, out);
                for a in args {
                    walk(&a.expr, out);
                }
            }
            SurfaceExpr::Arrow(_, l, r) | SurfaceExpr::Ascription(_, l, r) => {
                walk(l, out);
                walk(r, out);
            }
            SurfaceExpr::Paren(_, i)
            | SurfaceExpr::Proj(_, i, _)
            | SurfaceExpr::Explicit(_, i)
            | SurfaceExpr::NamedArg(_, _, i) => walk(i, out),
            SurfaceExpr::Pi(_, binders, body) | SurfaceExpr::Lambda(_, binders, body) => {
                for b in binders {
                    if let Some(t) = &b.ty {
                        walk(t, out);
                    }
                }
                walk(body, out);
            }
            _ => {}
        }
    }
    let mut out = std::collections::HashSet::new();
    walk(e, &mut out);
    out
}

/// Lower a multi-argument equation def (parsed as a single `_x` binder matched
/// against a right-nested `Prod.mk` tuple) into the named-binder + single
/// scrutinee (or *nested* single-scrutinee) `match` shape that the existing
/// single-argument structural recursion path already lowers soundly through the
/// inductive's `.rec`.
///
/// SCOPE (conservative, sound envelope):
/// - The declaration type must expose `N` arrow/Pi domains (`N` = tuple arity).
/// - At least one position is structurally matched (constructor / literal /
///   `n+k` patterns) across the arms. The *first* structurally-matched position
///   becomes the decreasing argument the recursion lowers on.
/// - **Slice 2 (single structural position):** every other position is, in
///   every arm, the same variable name, or a wildcard in every arm. This lets us
///   name the lifted binder after that shared variable (no surface renaming
///   needed) so the arm bodies' references resolve unchanged. We emit a single
///   `match <dec_binder> with | <dec pattern> => <arm body> | …`.
/// - **Slice 3 (multiple structural positions — the `semVectorIntBinOp`
///   shape):** more than one position is structurally matched (e.g. a
///   simultaneous match on two `List`s). We compile the structural columns into
///   a *nested* single-scrutinee match decision tree (outer match on the
///   decreasing position, inner matches on the remaining structural positions),
///   which the kernel re-checks exactly like a hand-written nested `match`. The
///   nested form is the textbook ML pattern-matrix compilation; the recursion
///   still decreases on the outer (first) structural binder, so the existing
///   `.rec` lowering with trailing binders folded into the motive fires.
///
/// On success returns `(lifted_binders, Some(return_ty), match_body)`.
/// The non-decreasing binders surround it as ordinary declaration binders, so
/// they are in scope inside the arm bodies exactly as the surface program wrote
/// them, and `setup_recursion` resolves the decreasing-arg position against the
/// lifted binders — installing the genuine `.rec` lowering with the trailing
/// binders folded into the motive (the existing extra-param machinery).
fn normalize_equation_def_multiarg(
    env: &clean_kernel::Environment,
    ty: Option<&SurfaceExpr>,
    scrut: &SurfaceExpr,
    arms: &[clean_parser::SurfaceMatchArm],
    is_recursive: bool,
) -> Option<(Vec<SurfaceBinder>, Option<SurfaceExpr>, SurfaceExpr)> {
    // The synthetic scrutinee must be the parser's `_x` binder; anything else
    // is not the def-equation tuple shape we recognize.
    if !matches!(scrut, SurfaceExpr::Ident(_, name) if name == "_x") {
        return None;
    }
    let ty = ty?;
    if arms.is_empty() {
        return None;
    }

    // Flatten every arm's tuple pattern into per-position leaves and require a
    // consistent arity across all arms.
    let mut arm_leaves: Vec<Vec<SurfacePattern>> = arms
        .iter()
        .map(|arm| flatten_prod_pattern(&arm.pattern))
        .collect();
    let arity = arm_leaves[0].len();
    if arity < 2 || arm_leaves.iter().any(|leaves| leaves.len() != arity) {
        return None;
    }

    // Peel the declaration domains up front (moved before classification): the
    // nullary-constructor rewrite below needs each column's domain type.
    let (domains, return_ty) = peel_n_domains(ty, arity)?;

    // Nullary-constructor ident rewrite. A bare constructor ident pattern
    // (`true`, `false`, a user inductive's nullary ctor) parses as
    // `SurfacePattern::Var`, which mis-classifies its column as pass-through:
    // the normalizer then either bails (differing "names" across arms) or
    // lifts a binder that shadows nothing — both leaving the def to the
    // fallback path, where dependent returns dangle and recursion loses its
    // self-name. When a column's domain type is a bare Ident naming a
    // registered inductive, rewrite each `Var(name)` leaf in that column to
    // `Ctor(name, [])` IFF `name` (or its `Type.name` qualification) is a
    // NULLARY constructor of that inductive — exactly the resolution the
    // single-scrutinee match elaborator performs downstream. Anything else is
    // left untouched (a Var that is not a registered nullary ctor remains a
    // genuine binder).
    for pos in 0..arity {
        let SurfaceExpr::Ident(_, type_name) = &domains[pos].0 else {
            continue;
        };
        let Some(ind) = env.get_inductive(&Name::from_string(type_name)) else {
            continue;
        };
        let nullary: Vec<String> = ind
            .constructor_names
            .iter()
            .filter(|c| env.get_constructor(c).is_some_and(|ci| ci.num_fields == 0))
            .map(|c| c.to_string())
            .collect();
        for leaves in arm_leaves.iter_mut() {
            if let SurfacePattern::Var(name) = &leaves[pos] {
                let qualified = format!("{type_name}.{name}");
                if nullary
                    .iter()
                    .any(|c| c == name.as_str() || c == qualified.as_str())
                {
                    leaves[pos] = SurfacePattern::Ctor(name.clone(), Vec::new());
                }
            }
        }
    }

    // Brick 88: dependent type-family second domain (`(n : Nat) → T9 n → R`).
    // The per-column rewrite above cannot see through `T9 n`, so `true`/
    // `false` leaves stay `Var`, the shared-name check below bails, and the
    // curried fallback descopes loudly. Refine the family PER ROW with a
    // kernel whnf probe and re-emit with the dependent domain kept in the
    // RETURN type (dependent-motive lane). All-or-nothing: on any gate
    // failure `arm_leaves` is untouched and everything below runs
    // byte-identically.
    if let Some(lifted) = super::equation_dep_family::try_emit_dependent_family(
        env,
        ty,
        &domains,
        &arm_leaves,
        arms,
        is_recursive,
    ) {
        return Some(lifted);
    }

    // Identify the structurally-matched positions (those constructor/literal-
    // matched in some arm), in order. The first is the decreasing argument the
    // recursion lowers on; any additional ones drive the nested-match compile.
    let mut structural_positions: Vec<usize> = Vec::new();
    for pos in 0..arity {
        if arm_leaves
            .iter()
            .any(|leaves| is_structural_pattern(&leaves[pos]))
        {
            structural_positions.push(pos);
        }
    }
    let dec_pos = *structural_positions.first()?;
    let is_structural_col: Vec<bool> = (0..arity)
        .map(|pos| structural_positions.contains(&pos))
        .collect();

    // Resolve a binder name for each NON-structural (pass-through) position: all
    // *named* occurrences must agree on a single variable name; wildcard
    // occurrences impose no constraint (a `_` binds nothing, so the arm body
    // never references that position). A column that mixes a named var in one
    // arm and `_` in another therefore lifts soundly under the named var — the
    // wildcard arm simply ignores the extra binding. Only genuinely *different*
    // names across arms (which would require per-arm surface renaming) bail.
    //
    // The prior implementation treated `Wildcard` as a distinct `None` name and
    // bailed on any wildcard/named mix; that dropped the whole def back to the
    // non-normalized path, which does NOT lower multi-arg structural recursion
    // and so left the self-call as a placeholder constant typed at the return
    // type ("Too many arguments: function type … is not a function type" —
    // trust-ir `maskBitsAux`'s `| [], _, acc => …` base arm). (Track G)
    let mut binder_names: Vec<Option<String>> = vec![None; arity];
    for pos in 0..arity {
        if is_structural_col[pos] {
            continue;
        }
        let mut shared_name: Option<String> = None;
        for leaves in &arm_leaves {
            let this = match &leaves[pos] {
                SurfacePattern::Var(name) => Some(name.clone()),
                SurfacePattern::Wildcard => None,
                // A structural pattern in a non-structural column would
                // contradict the column classification; reject for safety.
                _ => return None,
            };
            match (&shared_name, this) {
                // Wildcard arm: no constraint, keep whatever name we have.
                (_, None) => {}
                // First named occurrence sets the column's binder name.
                (None, Some(name)) => shared_name = Some(name),
                // Subsequent named occurrence must match the established name;
                // a different name would require per-arm renaming, so bail.
                (Some(prev), Some(name)) if *prev == name => {}
                (Some(_), Some(_)) => return None,
            }
        }
        binder_names[pos] = shared_name;
    }

    // Build the lifted declaration binders. Structural positions prefer the
    // DECLARED Pi binder name (so a dependent residual return type like `W6 b`
    // resolves to the lifted binder — the multiarg form of the single-arg
    // name-drop fix in `normalize_equation_def`), falling back to synthetic
    // `_x`/`_x_arg{pos}` for anonymous domains. Pass-through positions reuse
    // the shared surface variable name, then the declared name, then a fresh
    // `_`-name (all-wildcard columns, never referenced). COLLISION GUARD: a
    // declared name is only used for a structural position when no OTHER
    // lifted binder takes the same name — otherwise the emitted `match <name>`
    // scrutinee ident could resolve to a different column's binder via
    // shadowing. On collision the position keeps its synthetic name (the
    // dangling-name behavior is then no worse than before this fix).
    let declared_names: Vec<Option<String>> = domains.iter().map(|(_, n)| n.clone()).collect();
    let synthetic_name = |pos: usize| -> String {
        if pos == dec_pos {
            "_x".to_string()
        } else {
            format!("_x_arg{pos}")
        }
    };
    // A declared name is only adopted when the residual return type actually
    // REFERENCES it (the dependent case, which previously failed with the name
    // dangling). Otherwise every position keeps its pre-existing name choice
    // (pass-through pattern name / synthetic), so non-dependent defs lift
    // byte-identically to before.
    let return_ty_idents = collect_free_idents_of(&return_ty);
    let mut chosen_names: Vec<String> = Vec::with_capacity(arity);
    for pos in 0..arity {
        let declared_if_referenced = declared_names[pos]
            .clone()
            .filter(|n| return_ty_idents.contains(n));
        let candidate = if is_structural_col[pos] {
            declared_if_referenced
        } else {
            binder_names[pos].clone().or(declared_if_referenced)
        };
        chosen_names.push(candidate.unwrap_or_else(|| synthetic_name(pos)));
    }
    // Resolve duplicates: keep the FIRST occurrence of a name, demote later
    // ones to their synthetic name (pass-through pattern names must win over a
    // structural declared name, and pattern names were already validated
    // unique per column).
    for pos in 0..arity {
        let dup = chosen_names[..pos].contains(&chosen_names[pos]);
        if dup {
            chosen_names[pos] = synthetic_name(pos);
        }
    }
    let scrut_binder_name = |pos: usize| -> String { chosen_names[pos].clone() };
    let mut lifted_binders = Vec::with_capacity(arity);
    for (pos, (domain, _)) in domains.into_iter().enumerate() {
        lifted_binders.push(SurfaceBinder::new(
            chosen_names[pos].clone(),
            Some(domain),
            clean_parser::SurfaceBinderInfo::Explicit,
        ));
    }

    let dec_span = scrut.span();

    if structural_positions.len() == 1 {
        // Slice 2: single structural position. Scrutinize only the decreasing
        // position. The arm body is unchanged — pass-through binders are already
        // in scope under their original surface names, and the decreasing
        // pattern's bound variables are re-bound by the single-scrutinee match.
        let new_arms: Vec<clean_parser::SurfaceMatchArm> = arms
            .iter()
            .zip(arm_leaves.iter())
            .map(|(arm, leaves)| clean_parser::SurfaceMatchArm {
                span: arm.span,
                pattern: leaves[dec_pos].clone(),
                body: arm.body.clone(),
            })
            .collect();
        let match_body = SurfaceExpr::Match(
            dec_span,
            None,
            Box::new(SurfaceExpr::Ident(dec_span, scrut_binder_name(dec_pos))),
            new_arms,
        );
        return Some((lifted_binders, Some(return_ty), match_body));
    }

    // Slice 3: multiple structural positions. Compile the structural columns
    // into a nested single-scrutinee match via textbook pattern-matrix
    // compilation. Each structural column's top-level leaf must be a constructor,
    // literal, or wildcard (variable / as / or / n+k patterns at a structural
    // top level are outside the envelope and bail) so the column always reduces
    // to "match this scrutinee against these head patterns".
    let scrut_names: Vec<String> = structural_positions
        .iter()
        .map(|&pos| scrut_binder_name(pos))
        .collect();
    let rows: Vec<MatrixRow> = arm_leaves
        .iter()
        .zip(arms.iter())
        .map(|(leaves, arm)| MatrixRow {
            pats: structural_positions
                .iter()
                .map(|&pos| leaves[pos].clone())
                .collect(),
            body: arm.body.clone(),
            span: arm.span,
        })
        .collect();
    let match_body = compile_pattern_matrix(&scrut_names, &rows, dec_span, is_recursive)?;
    Some((lifted_binders, Some(return_ty), match_body))
}

/// Unpack the parser's multi-discriminant scrutinee — a RIGHT-nested
/// `Prod.mk a (Prod.mk b c)` application spine (`match a, b, c with`,
/// `expr_match.rs::match_body`) — into its component expressions. Returns
/// `None` unless the top level is a positional two-argument application of the
/// bare ident `Prod.mk` (i.e. at least two packed discriminants).
fn unpack_prod_mk_scrutinee(scrut: &SurfaceExpr) -> Option<Vec<&SurfaceExpr>> {
    let mut components = Vec::new();
    let mut current = scrut;
    loop {
        match current {
            SurfaceExpr::App(_, f, args)
                if matches!(&**f, SurfaceExpr::Ident(_, n) if n == "Prod.mk")
                    && args.len() == 2
                    && args.iter().all(|a| a.name.is_none()) =>
            {
                components.push(&args[0].expr);
                current = &args[1].expr;
            }
            other => {
                components.push(other);
                break;
            }
        }
    }
    (components.len() >= 2).then_some(components)
}

/// Brick 84: normalize a RECURSIVE def whose whole body is a multi-scrutinee
/// `match a, b with` over the def's own binders into the equivalent nested
/// single-scrutinee form, compiled through the same equation pattern matrix
/// as multi-argument equation defs (bricks B81/B83).
///
/// The parser packs `match a, b with` into ONE right-nested `Prod.mk`
/// scrutinee with `Prod.mk` tuple arm patterns. That tuple is never the bare
/// decreasing-arg ident, so `is_match_on_decreasing_arg` cannot fire, the
/// match lowers via `casesOn` with no induction hypothesis, and the self-call
/// dies `UnknownIdent` (the constant is not yet registered while its own body
/// elaborates). Rewriting to `match a with … match b with …` BEFORE
/// `setup_recursion` lets the existing `use_rec` + IH machinery work
/// unchanged.
///
/// ENGAGEMENT GATE (B81 lesson): only fires for defs whose body mentions a
/// self-call — the previously-FAILING class. Non-recursive multi-scrutinee
/// matches work today via the tuple-`casesOn` path and keep byte-identical
/// behavior. Every other shape check (`None` return) also falls back to that
/// pre-existing path, so nothing that elaborated before is rerouted.
fn normalize_multi_scrutinee_match_body(
    env: &clean_kernel::Environment,
    def_name: &str,
    binders: &[SurfaceBinder],
    val: &SurfaceExpr,
) -> Option<SurfaceExpr> {
    if def_name.is_empty() || binders.is_empty() {
        return None;
    }
    // The whole body must be a plain match (no `h :` discriminant hypothesis —
    // the parser rejects `h :` on multi-discriminant matches anyway).
    let SurfaceExpr::Match(span, None, scrut, arms) = val else {
        return None;
    };
    if arms.is_empty() {
        return None;
    }
    // The packed scrutinee must unpack to >= 2 BARE idents naming PAIRWISE
    // DISTINCT def binders (distinctness keeps the nested rebinding
    // shadow-free; a repeated component would re-match a name the outer match
    // may have re-bound).
    let components = unpack_prod_mk_scrutinee(scrut)?;
    let mut names: Vec<String> = Vec::with_capacity(components.len());
    for component in components {
        let SurfaceExpr::Ident(_, n) = component else {
            return None;
        };
        if !binders.iter().any(|b| b.name == *n) || names.contains(n) {
            return None;
        }
        names.push(n.clone());
    }
    // ENGAGEMENT GATE: recursive defs only (see doc comment).
    if !super::structural::body_mentions_call(val, def_name) {
        return None;
    }
    // Every arm's tuple pattern must flatten to exactly one leaf per
    // scrutinee component.
    let mut arm_leaves: Vec<Vec<SurfacePattern>> = arms
        .iter()
        .map(|arm| flatten_prod_pattern(&arm.pattern))
        .collect();
    if arm_leaves.iter().any(|leaves| leaves.len() != names.len()) {
        return None;
    }
    // B83 nullary-ctor ident rewrite, keyed on the BINDER type (the multiarg
    // path keys on the peeled declaration domain): a bare `true`/`false`/…
    // pattern parses as `SurfacePattern::Var`, which the matrix compiler's
    // variable rule would silently treat as a catch-all — an always-first-arm
    // WRONG compile. Resolving registered nullary constructors up front keeps
    // those columns genuine constructor dispatches.
    for (pos, comp_name) in names.iter().enumerate() {
        let Some(SurfaceExpr::Ident(_, type_name)) = binders
            .iter()
            .find(|b| b.name == *comp_name)
            .and_then(|b| b.ty.as_deref())
        else {
            continue;
        };
        let Some(ind) = env.get_inductive(&Name::from_string(type_name)) else {
            continue;
        };
        let nullary: Vec<String> = ind
            .constructor_names
            .iter()
            .filter(|c| env.get_constructor(c).is_some_and(|ci| ci.num_fields == 0))
            .map(|c| c.to_string())
            .collect();
        for leaves in arm_leaves.iter_mut() {
            if let SurfacePattern::Var(name) = &leaves[pos] {
                let qualified = format!("{type_name}.{name}");
                if nullary
                    .iter()
                    .any(|c| c == name.as_str() || c == qualified.as_str())
                {
                    leaves[pos] = SurfacePattern::Ctor(name.clone(), Vec::new());
                }
            }
        }
    }
    let rows: Vec<MatrixRow> = arm_leaves
        .into_iter()
        .zip(arms.iter())
        .map(|(pats, arm)| MatrixRow {
            pats,
            body: arm.body.clone(),
            span: arm.span,
        })
        .collect();
    // `extended: true` — the gate above already restricted us to the
    // recursive (previously-failing) class the B81 extensions target.
    compile_pattern_matrix(&names, &rows, *span, /*extended=*/ true)
}

/// One row of the structural pattern matrix: the per-structural-column patterns
/// plus the arm body and source span.
struct MatrixRow {
    pats: Vec<SurfacePattern>,
    body: SurfaceExpr,
    span: clean_parser::Span,
}

/// The head shape a structural column's top-level pattern dispatches on. Two
/// patterns share a column "head" iff they would select the same `match` arm.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ColHead {
    /// Constructor `name` applied to `arity` sub-patterns.
    Ctor(String, usize),
    /// A literal pattern, keyed by its surface rendering.
    Lit(String),
}

/// Whether a column pattern is a "pass-through" (binds the whole scrutinee or
/// ignores it) rather than dispatching on a constructor/literal head: a plain
/// variable, a wildcard, or the constructor-field ellipsis marker.
fn is_passthrough_pattern(pat: &SurfacePattern) -> bool {
    matches!(
        pat,
        SurfacePattern::Var(_) | SurfacePattern::Wildcard | SurfacePattern::Ellipsis
    )
}

/// Classify a structural column's top-level pattern's dispatch head. Returns
/// `Ok(None)` for a pass-through pattern (variable / wildcard / ellipsis — these
/// match every head and form the default rows) and bails the whole compile
/// (`Err(())`) for patterns outside the envelope (as / or / inaccessible / n+k /
/// q-pattern at a structural top level), which would need richer handling.
fn col_head(pat: &SurfacePattern) -> Result<Option<ColHead>, ()> {
    match pat {
        SurfacePattern::Var(_) | SurfacePattern::Wildcard | SurfacePattern::Ellipsis => Ok(None),
        SurfacePattern::Ctor(name, sub) => Ok(Some(ColHead::Ctor(name.clone(), sub.len()))),
        SurfacePattern::Lit(lit) => Ok(Some(ColHead::Lit(format!("{lit:?}")))),
        _ => Err(()),
    }
}

/// Textbook ML pattern-matrix compiler specialized for the structural columns
/// of a multi-argument equation def. Produces a nested single-scrutinee
/// `SurfaceExpr::Match` decision tree that is semantically equivalent to the
/// simultaneous match the surface program wrote, and that the kernel re-checks
/// like any hand-written nested match.
///
/// `scruts[i]` is the binder name scrutinized for matrix column `i`. Each row's
/// `pats[i]` is that row's pattern for column `i`. Rows are tried top-to-bottom
/// (first-match-wins), exactly as Lean's equation compiler orders arms.
///
/// Binding faithfulness: rather than alpha-renaming arm bodies (which would
/// require a full surface substitution pass), we preserve a column pattern's
/// *variable* bindings by re-emitting the original pattern as a single-arm
/// `match scrut with | <pat> => …` (the variable rule). A constructor column
/// peels into fresh field-scrutinee columns bound by fresh names in the arm
/// pattern; each row's original sub-patterns then flow into those fresh columns,
/// so a sub-pattern like a list tail `xs` re-binds via the variable rule exactly
/// where the surface program expects it.
///
/// Returns `None` (bailing the whole lowering) when any column pattern is
/// outside `col_head`'s envelope, so we never emit a term that silently
/// reorders or drops a binding.
fn compile_pattern_matrix(
    scruts: &[String],
    rows: &[MatrixRow],
    span: clean_parser::Span,
    extended: bool,
) -> Option<SurfaceExpr> {
    // No columns left: every structural position matched. The first remaining
    // row wins (first-match-wins arm ordering).
    if scruts.is_empty() {
        return rows.first().map(|r| r.body.clone());
    }
    if rows.is_empty() {
        return None;
    }

    // Column-head normalization pass, run BEFORE head classification:
    //
    // (1) NumeralAdd expansion: an `inner + k` pattern is `k` nested
    //     `Nat.succ` constructor applications around `inner`. `col_head` has
    //     no numeral-add head (two different `+k`s OVERLAP, so they are not
    //     disjoint dispatch heads) — expanding to `Nat.succ` towers makes the
    //     column a uniform constructor dispatch, exactly how Lean's equation
    //     compiler treats `n+1` rows.
    // (2) Variable-row rewrite (the Maranget variable rule for a MIXED
    //     column): a row binding the WHOLE scrutinee to `x` alongside
    //     constructor heads matches every head. The scrutinee is a named
    //     lifted def binder that stays in scope inside the emitted match arms,
    //     so `x`'s binding is preserved by opening the row body with
    //     `let x := <scrutinee>` and demoting the row's head to a wildcard
    //     pass-through — included in every constructor arm AND the default
    //     arm by the specialization below. (The prior mixed-column guard
    //     bailed the whole lowering here, dropping everyday defs like
    //     `| 0, m => m | n+1, m+1 => f n m + 1` back to the non-normalized
    //     path — where multi-arg structural recursion never installs the
    //     self-name and the recursive call fails UnknownIdent.)
    fn expand_numeral_add(pat: &SurfacePattern) -> SurfacePattern {
        match pat {
            SurfacePattern::NumeralAdd(inner, k) => {
                let mut expanded = (**inner).clone();
                for _ in 0..*k {
                    expanded = SurfacePattern::Ctor("Nat.succ".to_string(), vec![expanded]);
                }
                expanded
            }
            other => other.clone(),
        }
    }
    // ENGAGEMENT GATE: the two extensions below only fire for defs the OLD
    // envelope could not lower at all (recursive multiarg equation defs, which
    // previously died UnknownIdent on their own name). For every other def the
    // old semantics are restored EXACTLY — non-extended rows pass through
    // unchanged, and the old mixed-column guard below bails as before — so
    // previously-working defs take a byte-identical path.
    let rewritten_rows: Vec<MatrixRow> = rows
        .iter()
        .map(|r| {
            if !extended {
                return MatrixRow {
                    pats: r.pats.clone(),
                    body: r.body.clone(),
                    span: r.span,
                };
            }
            let mut pats = r.pats.clone();
            pats[0] = expand_numeral_add(&pats[0]);
            match pats[0].clone() {
                SurfacePattern::Var(x) => {
                    pats[0] = SurfacePattern::Wildcard;
                    MatrixRow {
                        pats,
                        body: SurfaceExpr::Let(
                            r.span,
                            SurfaceBinder::new(x, None, clean_parser::SurfaceBinderInfo::Explicit),
                            Box::new(SurfaceExpr::Ident(r.span, scruts[0].clone())),
                            Box::new(r.body.clone()),
                        ),
                        span: r.span,
                    }
                }
                _ => MatrixRow {
                    pats,
                    body: r.body.clone(),
                    span: r.span,
                },
            }
        })
        .collect();
    let rows = &rewritten_rows[..];

    // Old mixed-column guard, kept verbatim for the non-extended path: a
    // constructor column with a whole-scrutinee `Var` row bails the lowering
    // (the extended path rewrote such rows to let-bound wildcards above).
    if !extended
        && rows
            .iter()
            .any(|r| matches!(&r.pats[0], SurfacePattern::Var(_)))
    {
        return None;
    }

    let heads: Vec<Option<ColHead>> = rows
        .iter()
        .map(|r| col_head(&r.pats[0]))
        .collect::<Result<_, _>>()
        .ok()?;

    // Variable rule: the first column dispatches on no constructor — every row
    // is a pass-through (variable / wildcard) there. The column binds (or
    // ignores) the scrutinee but does not branch. If *any* row binds a real
    // variable, re-emit that binding via a single-arm `match scrut with | x => …`
    // so the body's reference to `x` resolves to the scrutinee. We use the first
    // row's binder (rows are tried in order; for a pure variable column they all
    // succeed, so binding the first row's name and continuing with the remaining
    // columns is faithful). A pure wildcard/ellipsis column is simply dropped.
    if heads.iter().all(Option::is_none) {
        let rest_scruts = &scruts[1..];
        let rest_rows: Vec<MatrixRow> = rows
            .iter()
            .map(|r| MatrixRow {
                pats: r.pats[1..].to_vec(),
                body: r.body.clone(),
                span: r.span,
            })
            .collect();
        let inner = compile_pattern_matrix(rest_scruts, &rest_rows, span, extended)?;
        // Bind the first row's variable (if it is one) to the scrutinee.
        if let SurfacePattern::Var(name) = &rows[0].pats[0] {
            return Some(SurfaceExpr::Match(
                span,
                None,
                Box::new(SurfaceExpr::Ident(span, scruts[0].clone())),
                vec![clean_parser::SurfaceMatchArm {
                    span,
                    pattern: SurfacePattern::Var(name.clone()),
                    body: inner,
                }],
            ));
        }
        return Some(inner);
    }

    // Constructor rule: build a `match scruts[0] with` whose arms are the
    // distinct heads (in first-appearance order). For each head we *specialize*
    // the matrix: keep rows whose first pattern is that head (decomposing its
    // sub-patterns into fresh leading columns) or a pass-through (which
    // decomposes into wildcards for the head's fields). The remaining structural
    // columns follow. Fresh scrutinee names back the head's field columns.
    let mut head_order: Vec<ColHead> = Vec::new();
    for h in heads.iter().flatten() {
        if !head_order.contains(h) {
            head_order.push(h.clone());
        }
    }

    let mut match_arms: Vec<clean_parser::SurfaceMatchArm> = Vec::new();
    for head in &head_order {
        let (head_ctor_name, field_count) = match head {
            ColHead::Ctor(name, n) => (Some(name.clone()), *n),
            ColHead::Lit(_) => (None, 0),
        };

        // Per-field binding decision. For each of the head's fields we look at
        // how every row matching this head fills it. If every such row uses the
        // *same* variable name (wildcards are compatible — they bind nothing),
        // we bind the field directly to that surface name in the arm pattern and
        // do NOT spawn an inner column for it. This is what keeps a recursive
        // list-tail like `lhsRest` bound under its original name, so the IH
        // (keyed on the arm's pattern-variable name) matches the self-call's
        // decreasing argument. Otherwise we bind the field to a fresh name and
        // re-match the differing sub-patterns as a fresh inner column.
        let mut field_names: Vec<String> = Vec::with_capacity(field_count);
        let mut field_is_inner: Vec<bool> = Vec::with_capacity(field_count);
        for fi in 0..field_count {
            // `chosen` is the single surface variable name every matching row
            // uses for this field (wildcards bind nothing, so they impose no
            // constraint and stay compatible with any chosen name). `decomposable`
            // stays true only while all matching rows are a `Var`/wildcard that
            // agree on at most one name.
            let mut chosen: Option<String> = None;
            let mut decomposable = true;
            for r in rows {
                if let SurfacePattern::Ctor(name, sub) = &r.pats[0] {
                    if head_ctor_name.as_deref() == Some(name.as_str()) && sub.len() == field_count
                    {
                        match &sub[fi] {
                            SurfacePattern::Wildcard | SurfacePattern::Ellipsis => {
                                // No constraint.
                            }
                            SurfacePattern::Var(n) => match &chosen {
                                None => chosen = Some(n.clone()),
                                Some(prev) if prev == n => {}
                                Some(_) => {
                                    // Two different variable names for the same
                                    // field across arms: cannot bind one name.
                                    decomposable = false;
                                    break;
                                }
                            },
                            _ => {
                                // A non-variable sub-pattern (constructor/literal/…):
                                // this field must be re-matched as an inner column.
                                decomposable = false;
                                break;
                            }
                        }
                    }
                }
            }
            if decomposable {
                // All matching rows agree on a single variable (or only wildcards)
                // for this field: bind it directly, no inner column.
                let name = chosen.unwrap_or_else(|| format!("{}_f{fi}", scruts[0]));
                field_names.push(name);
                field_is_inner.push(false);
            } else {
                // Differing sub-patterns: bind a fresh name, re-match inner.
                field_names.push(format!("{}_f{fi}", scruts[0]));
                field_is_inner.push(true);
            }
        }

        // Inner scrutinee columns are exactly the fields we did NOT bind by a
        // shared name, in order, followed by the remaining structural columns.
        let inner_field_scruts: Vec<String> = (0..field_count)
            .filter(|&fi| field_is_inner[fi])
            .map(|fi| field_names[fi].clone())
            .collect();
        let mut sub_scruts: Vec<String> = inner_field_scruts;
        sub_scruts.extend_from_slice(&scruts[1..]);

        // Specialize: rows whose first pattern is this head contribute their
        // re-match (inner-column) sub-patterns; pass-through rows contribute
        // wildcards for each inner column (they match every head).
        let inner_field_indices: Vec<usize> =
            (0..field_count).filter(|&fi| field_is_inner[fi]).collect();
        let mut sub_rows: Vec<MatrixRow> = Vec::new();
        for r in rows {
            match &r.pats[0] {
                SurfacePattern::Ctor(name, sub)
                    if head_ctor_name.as_deref() == Some(name.as_str())
                        && sub.len() == field_count =>
                {
                    let mut new_pats: Vec<SurfacePattern> = inner_field_indices
                        .iter()
                        .map(|&fi| sub[fi].clone())
                        .collect();
                    new_pats.extend_from_slice(&r.pats[1..]);
                    sub_rows.push(MatrixRow {
                        pats: new_pats,
                        body: r.body.clone(),
                        span: r.span,
                    });
                }
                p @ SurfacePattern::Lit(_) if col_head(p).ok().flatten().as_ref() == Some(head) => {
                    sub_rows.push(MatrixRow {
                        pats: r.pats[1..].to_vec(),
                        body: r.body.clone(),
                        span: r.span,
                    });
                }
                p if is_passthrough_pattern(p) => {
                    let mut new_pats: Vec<SurfacePattern> =
                        vec![SurfacePattern::Wildcard; inner_field_indices.len()];
                    new_pats.extend_from_slice(&r.pats[1..]);
                    sub_rows.push(MatrixRow {
                        pats: new_pats,
                        body: r.body.clone(),
                        span: r.span,
                    });
                }
                _ => { /* row's head differs from this arm: skip */ }
            }
        }

        let body = compile_pattern_matrix(&sub_scruts, &sub_rows, span, extended)?;
        // Arm pattern: reconstruct the head, binding fields either to their
        // shared surface name (so the body / IH refers to them unchanged) or to
        // the fresh re-match name. A literal head re-emits the literal verbatim.
        let arm_pattern = match head {
            ColHead::Ctor(name, _) => SurfacePattern::Ctor(
                name.clone(),
                field_names
                    .iter()
                    .map(|n| SurfacePattern::Var(n.clone()))
                    .collect(),
            ),
            ColHead::Lit(_) => rows.iter().find_map(|r| match &r.pats[0] {
                p @ SurfacePattern::Lit(_) if col_head(p).ok().flatten().as_ref() == Some(head) => {
                    Some(p.clone())
                }
                _ => None,
            })?,
        };
        match_arms.push(clean_parser::SurfaceMatchArm {
            span,
            pattern: arm_pattern,
            body,
        });
    }

    // Default arm: pass-through rows also apply when the scrutinee matches none
    // of the explicit heads. Emit a trailing arm dropping this column. If the
    // first such pass-through row binds a variable, the wildcard arm rebinds it.
    if heads.iter().any(Option::is_none) {
        let default_rows: Vec<MatrixRow> = rows
            .iter()
            .zip(heads.iter())
            .filter(|(_, h)| h.is_none())
            .map(|(r, _)| MatrixRow {
                pats: r.pats[1..].to_vec(),
                body: r.body.clone(),
                span: r.span,
            })
            .collect();
        if let Some(default_body) =
            compile_pattern_matrix(&scruts[1..], &default_rows, span, extended)
        {
            // Top-level `Var` rows were rewritten to wildcard rows whose
            // bodies rebind the variable via `let` (variable-row rewrite
            // above), so the only pass-through heads here are wildcard /
            // ellipsis — a wildcard arm is faithful.
            match_arms.push(clean_parser::SurfaceMatchArm {
                span,
                pattern: SurfacePattern::Wildcard,
                body: default_body,
            });
        }
    }

    Some(SurfaceExpr::Match(
        span,
        None,
        Box::new(SurfaceExpr::Ident(span, scruts[0].clone())),
        match_arms,
    ))
}

/// Collect all `Level::Param` names that appear in an expression's `Sort` and
/// `Const` nodes. Used to filter `universe_params` down to only those levels
/// that actually survive after `instantiate_levels` resolves concrete assignments.
///
/// Without this filtering, definitions like `abbrev MySem (a : Type) := StateT ...`
/// carry universe params (e.g., `u_0, u_1, u_2`) that were unified to concrete
/// levels during elaboration but still appear in `level_params`. This causes
/// level count mismatches when the definition is later unfolded, because the
/// definition's value has concrete levels but `unfold_definition` substitutes
/// the (now-unused) params with fresh levels that are never constrained.
/// Part of #3396.
struct DefLevelParamCollector<'a> {
    params: &'a mut Vec<Name>,
}

impl ExprVisitor for DefLevelParamCollector<'_> {
    type Result = ();

    fn combine(&self, _: Self::Result, _: Self::Result) -> Self::Result {}

    fn visit_sort(&mut self, level: &Level) -> Self::Result {
        level.collect_params(self.params);
    }

    fn visit_const(&mut self, _name: &Name, levels: &LevelVec) -> Self::Result {
        for level in levels {
            level.collect_params(self.params);
        }
    }
}

fn collect_def_level_params(expr: &Expr, params: &mut Vec<Name>) {
    if !expr.has_level_param_quick() {
        return;
    }
    let mut collector = DefLevelParamCollector { params };
    collector.visit_expr(expr);
}

impl ElabCtx<'_> {
    /// Lean parity for `def f := e` (no ascribed type): residual UNASSIGNED
    /// metavariables are generalized into fresh leading implicit binders —
    /// exactly how Lean gives `def comp := Function.comp` (and every
    /// `alias`-desugared def, e.g. `alias ⟨And.rotate, _⟩ := and_rotate`) its
    /// signature via abstractMVars. Ascribed defs and theorems keep the
    /// strict fail-closed guard; user-written `_` holes (span-carrying metas)
    /// are excluded — those belong to the hole-feedback contract.
    ///
    /// Binding order: dependency-first (a meta mentioned in another meta's
    /// TYPE binds further out), then first occurrence in (ty, val). The
    /// innermost binder is abstracted first, so outer metas still present as
    /// tagged FVars inside inner binder types are de Bruijn-adjusted by
    /// `abstract_fvar` when their own turn comes.
    fn generalize_residual_metas(&self, ty: Expr, val: Expr) -> (Expr, Expr) {
        use crate::unify::MetaState;

        fn collect_meta_fvars(e: &Expr, out: &mut Vec<FVarId>) {
            use clean_kernel::expr::visitor::ExprVisitor;
            struct C<'v>(&'v mut Vec<FVarId>);
            impl ExprVisitor for C<'_> {
                type Result = ();
                fn combine(&self, _a: (), _b: ()) {}
                fn visit_fvar(&mut self, id: FVarId) {
                    if MetaState::from_fvar(id).is_some() && !self.0.contains(&id) {
                        self.0.push(id);
                    }
                }
            }
            if e.has_fvar_quick() {
                C(out).visit_expr(e);
            }
        }

        // Occurrence-ordered residual metas over (ty, val), holes excluded.
        let mut occurrence: Vec<FVarId> = Vec::new();
        collect_meta_fvars(&ty, &mut occurrence);
        collect_meta_fvars(&val, &mut occurrence);
        occurrence.retain(|fv| {
            MetaState::from_fvar(*fv)
                .and_then(|mid| self.metas.get(mid))
                .is_some_and(|meta| meta.span.is_none())
        });
        if occurrence.is_empty() {
            return (ty, val);
        }

        // Dependency expansion + ordering: a meta appearing in another meta's
        // type must bind further out. Bounded passes (the sets are tiny).
        let meta_ty = |fv: FVarId| -> Option<Expr> {
            let mid = MetaState::from_fvar(fv)?;
            let m = self.metas.get(mid)?;
            Some(
                self.metas
                    .instantiate_levels(&self.metas.instantiate(&m.ty)),
            )
        };
        let mut ordered = occurrence;
        for _ in 0..16 {
            let mut changed = false;
            let mut i = 0;
            while i < ordered.len() {
                let Some(mty) = meta_ty(ordered[i]) else {
                    i += 1;
                    continue;
                };
                let mut deps = Vec::new();
                collect_meta_fvars(&mty, &mut deps);
                for dep in deps {
                    let dep_pos = ordered.iter().position(|x| *x == dep);
                    match dep_pos {
                        Some(p) if p > i => {
                            ordered.remove(p);
                            ordered.insert(i, dep);
                            changed = true;
                        }
                        Some(_) => {}
                        None => {
                            // A dep only reachable through a type: include it
                            // (holes stay excluded — a hole dep leaves this
                            // meta for the guard, which is the honest outcome).
                            let is_hole = MetaState::from_fvar(dep)
                                .and_then(|mid| self.metas.get(mid))
                                .is_none_or(|meta| meta.span.is_some());
                            if !is_hole {
                                ordered.insert(i, dep);
                                changed = true;
                            }
                        }
                    }
                }
                i += 1;
            }
            if !changed {
                break;
            }
        }

        // Abstract innermost-first (reverse of the outermost-first `ordered`).
        let mut ty_acc = ty;
        let mut val_acc = val;
        for fv in ordered.iter().rev() {
            let Some(mty) = meta_ty(*fv) else { continue };
            let ty_body = ty_acc.abstract_fvar(*fv);
            let val_body = val_acc.abstract_fvar(*fv);
            ty_acc = Expr::pi(clean_kernel::BinderInfo::Implicit, mty.clone(), ty_body);
            val_acc = Expr::lam(clean_kernel::BinderInfo::Implicit, mty, val_body);
        }
        (ty_acc, val_acc)
    }

    /// Fail-closed residual guard for finalized declarations.
    ///
    /// This elaborator encodes unassigned metavariables as FVars with bit 63
    /// set (`MetaState` meta-tag), so the kernel's "contains free variables"
    /// rejection conflates two distinct completeness failures. Catch both
    /// here, classified: meta-tagged ids are implicit arguments nothing could
    /// ever constrain (phantom section binders, an untyped alias desugar, a
    /// failed instance-synthesis fallback); low ids are genuine locals that
    /// escaped abstraction (e.g. a dropped section variable). Zero soundness
    /// effect — every declaration this rejects, the kernel already rejects —
    /// but the error becomes typed, named, and actionable.
    pub(super) fn ensure_no_residual_fvars(
        &self,
        decl_kind: &str,
        name: &str,
        ty: &Expr,
        val: Option<&Expr>,
    ) -> Result<(), ElabError> {
        const META_TAG: u64 = 1u64 << 63;
        let mut exprs: Vec<&Expr> = vec![ty];
        if let Some(v) = val {
            exprs.push(v);
        }
        let ids = clean_kernel::env::collect_fvar_ids_for_diagnostics(&exprs);
        if ids.is_empty() {
            return Ok(());
        }
        // User-written `_` holes are metas that carry a source span; they are
        // EXPECTED to survive finalization — the hole machinery reports their
        // goal as agent feedback and registration handles them downstream.
        // The guard is for metas nothing will ever report or resolve.
        let hole_ids: std::collections::HashSet<u64> = self
            .metas
            .iter()
            .filter_map(|(id, meta)| meta.span.map(|_| id.as_u64()))
            .collect();
        let metas: Vec<u64> = ids
            .iter()
            .filter(|id| **id & META_TAG != 0)
            .map(|id| *id & !META_TAG)
            .filter(|raw| !hole_ids.contains(raw))
            .collect();
        let locals: Vec<u64> = ids
            .iter()
            .filter(|id| **id & META_TAG == 0)
            .copied()
            .collect();
        if metas.is_empty() && locals.is_empty() {
            return Ok(());
        }
        let mut parts = Vec::new();
        if !metas.is_empty() {
            parts.push(format!("unsolved metavariables ?{metas:?}"));
        }
        if !locals.is_empty() {
            parts.push(format!("escaped local fvars {locals:?}"));
        }
        Err(ElabError::ResidualFreeVariables {
            decl_kind: decl_kind.to_owned(),
            name: name.to_owned(),
            detail: parts.join("; "),
        })
    }

    /// U2 rung 4 — the `levelMVarToParam` analog, run once at declaration
    /// close. Splits the surviving universe params into the DECLARED (rigid)
    /// head and the FRESH (auto-generalized) tail, orders the tail by first
    /// use (traversal order: type before value — Lean's ordering), renames it
    /// contiguously `u_1..u_k` (no gaps; mint-index gaps like `t5.{u_0,u_2}`
    /// were the measured naming divergence), substitutes the renames into the
    /// declaration, and — when the declaration carried an explicit `.{...}`
    /// list — REFUSES leftover fresh levels loudly instead of appending them
    /// (an explicit list is closed in Lean).
    pub(super) fn finalize_level_params(
        &mut self,
        ty: Expr,
        val: Expr,
    ) -> Result<(Vec<Name>, Expr, Expr), ElabError> {
        // Canonicalize FIRST: the decl-close canonicalize pass
        // (`canonicalize_levels_in_elab_result`) resolves every level through
        // the union-find, so a rename applied to un-canonicalized exprs would
        // be clobbered when a resurrected mint-name flows back. After this,
        // whatever params remain are genuinely unsolved.
        // U2: DRAIN THE DEFERRED LEVEL QUEUE FIRST, and fail closed.
        //
        // The solver defers undetermined level equations (some side still
        // mentions a solvable parameter) instead of failing them, so a later
        // assignment can settle them. This is the boundary where "later" runs
        // out. Anything still unsolved here was ACCEPTED BY THE SOLVER AND
        // NEVER DISCHARGED, which is exactly the hole postponement would
        // otherwise open — so it is an error, not a warning.
        //
        // Drained BEFORE canonicalization on purpose: draining can assign
        // parameters, and canonicalize must see those assignments.
        if let Err(msg) = self.metas.drain_postponed_levels() {
            return Err(ElabError::Unsupported { feature: msg });
        }
        let ty = self.metas.canonicalize_levels_in_expr(&ty);
        let val = self.metas.canonicalize_levels_in_expr(&val);
        let mut used = Vec::new();
        collect_def_level_params(&ty, &mut used);
        collect_def_level_params(&val, &mut used);
        let mut declared: Vec<Name> = Vec::new();
        let mut fresh: Vec<Name> = Vec::new();
        for s in &self.universe_params {
            let n = Name::from_string(s);
            if !used.contains(&n) {
                continue;
            }
            if self.metas.is_rigid_level_param(&n) {
                declared.push(n);
            } else {
                fresh.push(n);
            }
        }
        if fresh.is_empty() {
            return Ok((declared, ty, val));
        }
        // NOTE (rung-4 scope cut): Lean treats an explicit `.{...}` list as
        // CLOSED (leftover fresh levels error). Clean cannot yet distinguish
        // a declared `.{u}` from `universe u`-merged params at this layer —
        // the file-context preprocessor folds both into `universe_params`
        // (test_issue168_param_to_param_canonical is exactly the merged
        // case) — so enforcement waits on a real explicitness channel
        // through preprocess.rs; until then explicit lists still
        // auto-extend (pinned as the p21 divergence fixture).
        fresh.sort_by_key(|n| used.iter().position(|u| u == n));
        // Rename targets are freshly MINTED param names (`fresh_universe_param`):
        // guaranteed absent from the metas' union-find, so the decl-close
        // canonicalize pass cannot rewrite them back into a solved mint-name.
        // The tail is a contiguous block in first-use order (the measured
        // divergence was mint-index GAPS like `t5.{u_0,u_2}`; 1-based
        // Lean-exact numbering is a cosmetic follow-up).
        let mut subst: Vec<(Name, Level)> = Vec::new();
        let mut renamed: Vec<Name> = Vec::new();
        for f in &fresh {
            let tname = match self.fresh_universe_param() {
                Level::Param(n) => n,
                _ => unreachable!("fresh_universe_param mints a Param"),
            };
            subst.push((f.clone(), Level::param(tname.clone())));
            renamed.push(tname);
        }
        let (ty, val) = if subst.is_empty() {
            (ty, val)
        } else {
            (
                ty.instantiate_level_params(&subst),
                val.instantiate_level_params(&subst),
            )
        };
        declared.extend(renamed);
        Ok((declared, ty, val))
    }

    /// Type-only variant of [`Self::finalize_level_params`] (axioms/opaque
    /// declarations with no value expression).
    pub(super) fn finalize_level_params_ty(
        &mut self,
        ty: Expr,
    ) -> Result<(Vec<Name>, Expr), ElabError> {
        let (params, ty, _) = self.finalize_level_params(ty, Expr::sort(Level::zero()))?;
        Ok((params, ty))
    }
}

/// Replace every occurrence of the forward-declaration free variable `fvar`
/// with `Const(name)` (no universe args — the course-of-values auxiliary is
/// universe-monomorphic at `Nat → R × R`). Mirrors `replace_mutual_fvars` but
/// for the single auxiliary the pair-threading transform forward-declares.
fn replace_fvar_with_const(expr: Expr, fvar: FVarId, name: &Name) -> Expr {
    struct FvarToConst<'b> {
        fvar: FVarId,
        name: &'b Name,
    }
    impl ExprFolder for FvarToConst<'_> {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if id == self.fvar {
                Expr::const_(self.name.clone(), Vec::new())
            } else {
                Expr::fvar(id)
            }
        }
    }
    let mut folder = FvarToConst { fvar, name };
    folder.fold_expr(&expr)
}

impl<'a> ElabCtx<'a> {
    /// Course-of-values recursion via the pair-threading transform.
    ///
    /// Recognizes the two-prior `fib`-shape (`def f : Nat → R | 0 => .. | 1 =>
    /// .. | n + 2 => .. f (n+1) .. f n ..`) and lowers it to two ordinary
    /// declarations the existing single-step `Nat.rec` lowering already handles:
    ///
    /// - `f.cov : Nat → R × R` — the pair-threading auxiliary, single-step
    ///   structural recursion on the immediate predecessor.
    /// - `f (n : Nat) : R := Prod.fst (f.cov n)` — the projecting wrapper that
    ///   keeps the original surface name.
    ///
    /// Both are elaborated here and returned as an [`ElabResult::Multiple`] so
    /// the caller registers each into the kernel (which re-checks them — no
    /// `add_decl_unchecked`, no new axioms). Returns `Ok(None)` for every shape
    /// the transform does not recognize, leaving the standard path untouched.
    ///
    /// The wrapper references `f.cov`, which is not yet in the environment when
    /// its body elaborates (registration is deferred until this method returns).
    /// We bridge that exactly as the `mutual` path does: push `f.cov` as a
    /// forward local so the wrapper body resolves it, then rewrite that local
    /// fvar back to a `Const` in the final wrapper value.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_elab_course_of_values(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<Option<ElabResult>, ElabError> {
        let Some(plan) = super::course_of_values::try_pair_thread(name, binders, ty, val) else {
            return Ok(None);
        };

        // ---- Elaborate the auxiliary def `f.cov : Nat → R × R` ----
        // Route it through the ordinary definition path: `normalize_equation_def`
        // lifts its `_x` lambda to a binder, `setup_recursion` installs the
        // single-step IH, and `Nat.rec` lowering fires — the working k==1 path.
        self.set_decl_universe_params(universe_params);
        let aux_result = self.elab_definition_inner(
            &plan.aux_name,
            universe_params,
            &[],
            Some(&plan.aux_ty),
            &plan.aux_val,
            &[],
            &TerminationHints::default(),
            modifiers,
            &[],
        )?;

        // Recover the auxiliary's elaborated type so the forward local for the
        // wrapper carries the right signature.
        let aux_ty_expr = aux_result
            .declaration_type()
            .ok_or_else(|| ElabError::Unsupported {
                feature: "course-of-values: auxiliary def produced no type".to_string(),
            })?
            .clone();

        // ---- Elaborate the wrapper with `f.cov` pushed as a forward local ----
        self.set_decl_universe_params(universe_params);
        let aux_fvar: FVarId = self.push_local(plan.aux_name.clone(), aux_ty_expr);
        let aux_qualified = Name::from_string(&self.qualify_name(&plan.aux_name));

        // The wrapper value is `fun (n : Nat) => Prod.fst (f.cov n)`; it already
        // carries its own binder, so elaborate it with an empty binder list and
        // the signature `Nat → R` reconstructed as an arrow.
        let wrapper_ty = SurfaceExpr::Arrow(
            clean_parser::Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                clean_parser::Span::dummy(),
                "Nat".to_string(),
            )),
            Box::new(plan.wrapper_ret_ty.clone()),
        );
        let wrapper_outcome = self.elab_def_body(&[], Some(&wrapper_ty), &plan.wrapper_val);
        self.pop_local();
        let (wrapper_ty_expr, wrapper_val_expr) = wrapper_outcome?;

        let wrapper_ty_expr = self.metas.instantiate(&wrapper_ty_expr);
        let wrapper_val_expr = self.metas.instantiate(&wrapper_val_expr);
        let wrapper_ty_expr = self.metas.instantiate_levels(&wrapper_ty_expr);
        let wrapper_val_expr = self.metas.instantiate_levels(&wrapper_val_expr);

        // Rewrite the forward-local fvar `f.cov` back to a `Const` reference.
        let wrapper_val_expr = replace_fvar_with_const(wrapper_val_expr, aux_fvar, &aux_qualified);
        let wrapper_ty_expr = replace_fvar_with_const(wrapper_ty_expr, aux_fvar, &aux_qualified);

        let auto_implicits = self.take_auto_implicits();
        let (wrapper_ty_expr, wrapper_val_expr) =
            Self::wrap_with_auto_implicits(wrapper_ty_expr, wrapper_val_expr, &auto_implicits);

        let decl_name = Name::from_string(&self.qualify_name(name));
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        let (surviving_universe_params, wrapper_ty_expr, wrapper_val_expr) =
            self.finalize_level_params(wrapper_ty_expr, wrapper_val_expr)?;

        let wrapper_result = ElabResult::Definition {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: wrapper_ty_expr,
            val: wrapper_val_expr,
            modifiers: *modifiers,
        };

        Ok(Some(ElabResult::Multiple(vec![aux_result, wrapper_result])))
    }

    /// Set up recursion handling shared by `def` and `theorem` elaboration (#1132).
    ///
    /// Detects whether the body recurses on `name`, applies any explicit
    /// `termination_by` hint, and then does one of two things:
    ///
    /// - **Well-founded recursion** (an explicit `termination_by <measure>` with
    ///   no resolvable structural decreasing argument): fully elaborates the
    ///   declaration through the WF lowering path and returns the resulting
    ///   `(type, value)` pair. The caller wraps this in the appropriate
    ///   `ElabResult` variant.
    /// - **Structural recursion**: installs `self.recursive_def_ctx` so the
    ///   subsequent `elab_def_body` call substitutes recursive calls with the
    ///   induction hypothesis, and returns `None`.
    ///
    /// Non-recursive declarations also return `None` without touching
    /// `recursive_def_ctx`, so the common (non-recursive) path is unchanged.
    pub(super) fn setup_recursion(
        &mut self,
        name: &str,
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        termination: &TerminationHints,
    ) -> Result<Option<(Expr, Expr)>, ElabError> {
        let param_names: Vec<String> = binders.iter().map(|b| b.name.clone()).collect();
        let mut recursion_info =
            super::structural::detect_recursion_with_params(name, val, &param_names);

        // Track AA: a fused nested-mutual fold's primary def (`Tree.size`) often
        // contains NO literal self-call — its only recursion is the SIBLING call
        // (`Tree.sizeList ts`), which the auto-detector does not see. But it IS
        // genuinely recursive: the sibling call becomes an induction hypothesis
        // of the fused `Tree.rec` application, so it must lower through `T.rec`
        // (not `T.casesOn`). When the aux-arm source is installed and a sibling
        // call appears in the body, force structural recursion on the sole/first
        // binder (the scrutinee). The kernel re-checks the recursor application,
        // so this never escapes soundness — it only routes to the right lowering.
        if !recursion_info.is_recursive {
            let forced = self.nested_mutual_aux_arms.as_ref().is_some_and(|aux| {
                !param_names.is_empty()
                    && aux
                        .sibling_func_names
                        .iter()
                        .any(|sib| super::structural::body_mentions_call(val, sib))
            });
            if forced {
                recursion_info.is_recursive = true;
                recursion_info.decreasing_arg = Some(0);
            }
        }

        if !recursion_info.is_recursive {
            return Ok(None);
        }

        // Check for explicit termination hints (#1132).
        // If `termination_by structural <param>` is specified, use that param
        // instead of the auto-detected decreasing argument.
        let explicit_dec_arg = termination
            .termination_by
            .as_ref()
            .map(|tb| match &tb.kind {
                clean_parser::TerminationKind::Structural(param_name) => {
                    if param_name.is_empty() {
                        Ok(None)
                    } else if let Some(pos) = param_names.iter().position(|p| p == param_name) {
                        Ok(Some((pos, param_name.clone())))
                    } else {
                        Err(ElabError::Unsupported {
                            feature: format!(
                                "termination_by structural {} (unknown parameter)",
                                param_name
                            ),
                        })
                    }
                }
                // WellFounded and Query don't specify a structural param,
                // so fall back to auto-detection.
                clean_parser::TerminationKind::WellFounded
                | clean_parser::TerminationKind::Query => Ok(None),
            });

        // Use explicit hint if provided, otherwise use auto-detected position.
        let dec_arg = explicit_dec_arg.transpose()?.flatten().or_else(|| {
            recursion_info
                .decreasing_arg
                .and_then(|pos| binders.get(pos).map(|b| (pos, b.name.clone())))
        });

        if let Some((dec_pos, dec_name)) = dec_arg {
            // Collect names of parameters after the decreasing argument (#1386).
            // These are folded into the motive so IHs can handle varying
            // parameter values in recursive calls.
            let extra_params: Vec<RecursiveExtraParam> = binders[(dec_pos + 1)..]
                .iter()
                .map(|binder| RecursiveExtraParam {
                    name: binder.name.clone(),
                    binder_info: convert_binder_info(binder.info),
                })
                .collect();

            // Extract well-founded measure if present (#1132).
            let wf_measure = termination
                .termination_by
                .as_ref()
                .and_then(|tb| match &tb.kind {
                    clean_parser::TerminationKind::WellFounded => tb.measure.clone(),
                    _ => None,
                });

            // Set up recursive definition context. Store the *qualified* name
            // (e.g. `TrustIr.Ty.bitWidth` inside `namespace TrustIr`) so the
            // call-site IH substitution can recognise namespace-qualified and
            // method-dot-notation self-references that resolve to the fully
            // qualified constant (Track R, Basic.lean `Ty.bitWidth`).
            self.recursive_def_ctx = Some(RecursiveDefContext {
                func_name: self.qualify_name(name),
                decreasing_arg_pos: dec_pos,
                decreasing_arg_name: dec_name,
                inductive_type_name: None, // Will be set during elaboration
                ih_fvar: None,
                ih_type: None,
                ih_map: HashMap::new(),
                // Track AA: a fused nested-mutual fold installs the sibling
                // function names on `nested_mutual_aux_arms`; copy them here so a
                // sibling self-call inside a minor body is recognized. Empty for
                // ordinary recursion (no aux-arm source installed).
                sibling_names: self
                    .nested_mutual_aux_arms
                    .as_ref()
                    .map(|a| a.sibling_func_names.clone())
                    .unwrap_or_default(),
                extra_params,
                wf_measure,
            });
            Ok(None)
        } else if let Some(tb) = termination.termination_by.as_ref() {
            if matches!(tb.kind, clean_parser::TerminationKind::WellFounded) && tb.measure.is_some()
            {
                // Well-founded recursion with explicit measure.
                // Use the WF elaboration path instead of structural recursion.
                let measure = super::wf_recursion::pre_definition::TerminationMeasure {
                    params: tb.params.clone(),
                    measure_expr: tb
                        .measure
                        .clone()
                        .expect("invariant: measure presence checked above"),
                    decreasing_by: termination
                        .decreasing_by
                        .as_ref()
                        .map(|db| db.tactic.clone()),
                };

                let (ty_expr, val_expr) =
                    self.elab_wf_recursion(name, binders, ty, val, &measure)?;

                // Substitute metavariables.
                let ty_expr = self.metas.instantiate(&ty_expr);
                let val_expr = self.metas.instantiate(&val_expr);
                let ty_expr = self.metas.instantiate_levels(&ty_expr);
                let val_expr = self.metas.instantiate_levels(&val_expr);

                return Ok(Some((ty_expr, val_expr)));
            }
            Ok(None)
        } else {
            Ok(None)
        }
    }

    /// Elaborate a `def` declaration.
    ///
    /// Handles recursive definition detection, termination hints,
    /// auto-implicits, and metavariable instantiation.
    pub(super) fn elab_definition_inner(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        attrs: &[Attribute],
        termination: &TerminationHints,
        modifiers: &DeclModifiers,
        where_decls: &[WhereLocalDef],
    ) -> Result<ElabResult, ElabError> {
        // A SELF-RECURSIVE `partial def name : T := … name …`: Lean treats a
        // partial def as an opaque/unsafe constant — its body is NOT
        // termination-checked and the constant does not reduce in the kernel.
        // Register `name : T` as an OPAQUE declaration so the body's
        // self-reference — the whole reason such a partial def exists, and the
        // reason the ordinary recursion path can't elaborate it — resolves
        // against the signature, and discard the body. SOUNDNESS: an opaque
        // `name : T` is, kernel-wise, an axiom, so `T` MUST be inhabited —
        // otherwise `partial def f : False := f` would register an unsound
        // `f : False`. Lean requires `Inhabited T`; we FAIL LOUD otherwise.
        //
        // A NON-recursive partial def (`partial def p : Nat := 0`) has a valid
        // body and keeps the ordinary `Definition` path (carrying `is_partial`);
        // only the self-referencing case, which that path can't resolve, is
        // rerouted. Requires an explicit result type.
        if modifiers.is_partial {
            if let Some(ty) = ty {
                if super::course_of_values::body_calls(val, name) {
                    return self.elab_partial_def_opaque(
                        name,
                        universe_params,
                        binders,
                        ty,
                        attrs,
                        modifiers,
                    );
                }
            }
        }

        // Desugar where-clause local defs into let-rec wrapping the body.
        // Dependency-ordered (Lean's `where` decls form ONE mutually visible
        // `let rec` group — Lean/Elab/Binders.lean:472-476 expandWhereDecls,
        // Lean/Elab/LetRec.lean:87 withAuxLocalDecls — so acyclic forward
        // references must still resolve). Duplicate names and genuinely
        // mutual (cyclic) groups FAIL LOUD; they are never lowered to a
        // shape that would register with a placeholder.
        let val = if where_decls.is_empty() {
            val.clone()
        } else {
            crate::where_desugar_ext::desugar_where_from_parsed_ordered(val, where_decls).map_err(
                |e| ElabError::WhereLetRecUnsupported {
                    name: name.to_string(),
                    shape: format!("`where` block rejected: {e}"),
                },
            )?
        };
        let val = &val;

        // Course-of-values recursion (the `fib`-shape `n + 2 => f (n+1) + f n`).
        // Bare `Nat.rec` gives the succ minor exactly one immediate IH, so a
        // two-prior recurrence cannot lower directly. We rewrite it into the
        // fast-`fib` pair-threading form — a single-step auxiliary over `R × R`
        // plus a projecting wrapper — which reuses the existing `Nat.rec` (#20)
        // and `Prod` matcher (#21) lowering. Returns `None` for every other
        // shape, leaving the path below unchanged. This runs BEFORE
        // `normalize_equation_def` so the un-normalized `PatternMatchLambda`
        // shape (which the detector keys on) is still intact.
        if let Some(result) = self.try_elab_course_of_values(
            name,
            universe_params,
            binders,
            ty,
            val,
            attrs,
            modifiers,
        )? {
            return Ok(result);
        }

        // Normalize equation-form defs (`def f : A → B | pat => ...`) into the
        // named-binder + `match` shape so structural recursion lowers via the
        // inductive's `.rec` (Task 3, slice 1). Returns `None` for non-equation
        // declarations, leaving the common path unchanged.
        let normalized = normalize_equation_def(self.env, name, binders, ty, val);
        let (binders, ty, val): (&[SurfaceBinder], Option<&SurfaceExpr>, &SurfaceExpr) =
            match &normalized {
                Some((lifted_binders, new_ty, match_body)) => {
                    (lifted_binders, new_ty.as_ref(), match_body)
                }
                None => (binders, ty, val),
            };

        // Brick 84: a RECURSIVE def whose body is a multi-scrutinee
        // `match a, b with` over its own binders. The parser packed the
        // scrutinees into ONE right-nested `Prod.mk` tuple, which never
        // matches the decreasing-arg ident, so `use_rec` cannot fire and the
        // self-call dies UnknownIdent. Rewrite to the nested single-scrutinee
        // form BEFORE `setup_recursion` so the existing IH machinery works
        // unchanged. Engagement-gated on recursion: non-recursive
        // multi-scrutinee matches keep the tuple-`casesOn` path untouched.
        let multi_scrut = normalize_multi_scrutinee_match_body(self.env, name, binders, val);
        let val: &SurfaceExpr = multi_scrut.as_ref().unwrap_or(val);

        // Set universe params
        self.set_decl_universe_params(universe_params);

        // Detect recursion and apply termination hints (#378, #1132).
        // Returns Some((ty, val)) only for the well-founded lowering early-return
        // path; otherwise installs the structural recursion context (if any) and
        // returns None so the standard body path runs below.
        if let Some((ty_expr, val_expr)) =
            self.setup_recursion(name, binders, ty, val, termination)?
        {
            // Wrap with auto-implicit binders.
            let auto_implicits = self.take_auto_implicits();
            let (ty_expr, val_expr) =
                Self::wrap_with_auto_implicits(ty_expr, val_expr, &auto_implicits);

            let decl_name = Name::from_string(&self.qualify_name(name));
            self.ensure_known_attributes(attrs)?;
            self.collect_attributes(&decl_name, attrs);

            // Filter to surviving params only (#3396).
            let (surviving_universe_params, ty_expr, val_expr) =
                self.finalize_level_params(ty_expr, val_expr)?;

            return Ok(ElabResult::Definition {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                val: val_expr,
                modifiers: *modifiers,
            });
        }

        // Elaborate binders as pi types around the type, lambdas around the value
        // Use a closure to ensure recursive context is cleared even on error
        let result = self.elab_def_body(binders, ty, val);

        // Clear recursive context after elaboration (must happen even on error)
        self.recursive_def_ctx = None;

        let (ty_expr, val_expr) = result?;

        // Substitute metavariables (#163: unsolved metavariables from typeclass
        // resolution would otherwise leak as FVars to the kernel type checker)
        let ty_expr = self.metas.instantiate(&ty_expr);
        let val_expr = self.metas.instantiate(&val_expr);

        // Substitute level constraints collected during unification
        let ty_expr = self.metas.instantiate_levels(&ty_expr);
        let val_expr = self.metas.instantiate_levels(&val_expr);

        // Wrap with auto-implicit binders (#164)
        // Auto-implicits are added in order of first occurrence (reversed for Pi/Lambda)
        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, val_expr) =
            Self::wrap_with_auto_implicits(ty_expr, val_expr, &auto_implicits);

        // Collect all attributes for later registration
        let decl_name = Name::from_string(&self.qualify_name(name));
        // B21: reject unknown attributes loudly before honoring the rest.
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // Use self.universe_params which includes auto-bound params from
        // fresh_universe_param() during elaboration (e.g., auto-implicit
        // `def f (x : A) : A := x` auto-binds u_0 for A : Sort(u_0)).
        // Fix for #1324: previously used parser's explicit universe_params
        // which is empty when universe params are auto-bound.
        //
        // Fix for #3396: filter universe_params to only those that actually
        // appear in the final type/value expressions. When an abbrev like
        // `abbrev MySem (a : Type) := StateT MyState (Except MyError) a`
        // is applied to concrete types, `instantiate_levels` resolves the
        // auto-generated params (u_0, u_1, ...) to concrete levels (Zero),
        // but they remain in `universe_params`. This causes level count
        // mismatches when the definition is later unfolded.
        // Same pattern as #3390 fix for structures (see elab_structure.rs).
        // Lean parity: a def with NO ascribed type generalizes residual
        // unassigned metas into implicit binders (abstractMVars) — the alias
        // desugar and `def f := Function.comp`-style definitions depend on it.
        let (ty_expr, val_expr) = if ty.is_none() {
            self.generalize_residual_metas(ty_expr, val_expr)
        } else {
            (ty_expr, val_expr)
        };

        let (surviving_universe_params, ty_expr, val_expr) =
            self.finalize_level_params(ty_expr, val_expr)?;

        self.ensure_no_residual_fvars("def", name, &ty_expr, Some(&val_expr))?;

        Ok(ElabResult::Definition {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            val: val_expr,
            modifiers: *modifiers,
        })
    }

    /// Elaborate a `theorem` declaration.
    ///
    /// Similar to `elab_definition_inner` but produces `ElabResult::Theorem`.
    pub(super) fn elab_theorem_inner(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
        attrs: &[Attribute],
        termination: &TerminationHints,
        modifiers: &DeclModifiers,
        where_decls: &[WhereLocalDef],
    ) -> Result<ElabResult, ElabError> {
        // Desugar where-clause local defs for theorems. Same contract as the
        // `def` path above: dependency-ordered, duplicate/cyclic groups fail
        // loud, no placeholder registration.
        let proof = if where_decls.is_empty() {
            proof.clone()
        } else {
            crate::where_desugar_ext::desugar_where_from_parsed_ordered(proof, where_decls)
                .map_err(|e| ElabError::WhereLetRecUnsupported {
                    name: name.to_string(),
                    shape: format!("`where` block rejected: {e}"),
                })?
        };
        let proof = &proof;

        // Normalize equation-form theorems (`theorem t : A → B | pat => ...`)
        // into named-binder + `match` shape, mirroring the definition path so
        // structural recursion lowers via `.rec` (Task 3, slice 1).
        let normalized = normalize_equation_def(self.env, name, binders, Some(ty), proof);
        let (binders, ty, proof): (&[SurfaceBinder], &SurfaceExpr, &SurfaceExpr) = match &normalized
        {
            // A normalized equation theorem must have a peeled return type;
            // if normalization somehow produced `None` for the type, fall
            // back to the original shape rather than fabricate one.
            Some((lifted_binders, Some(new_ty), match_body)) => {
                (lifted_binders, new_ty, match_body)
            }
            _ => (binders, ty, proof),
        };

        self.set_decl_universe_params(universe_params);

        // Handle termination hints for recursive theorems (#1132).
        // Most theorems are not recursive, in which case `setup_recursion`
        // returns `None` without touching `recursive_def_ctx`, leaving the
        // common non-recursive path below unchanged. A recursive theorem with
        // an explicit `termination_by <measure>` is lowered through the
        // well-founded path; structural recursion installs the IH context for
        // the `elab_def_body` call.
        if let Some((ty_expr, proof_expr)) =
            self.setup_recursion(name, binders, Some(ty), proof, termination)?
        {
            // Well-founded lowering early-return path.
            let auto_implicits = self.take_auto_implicits();
            let (ty_expr, proof_expr) =
                Self::wrap_with_auto_implicits(ty_expr, proof_expr, &auto_implicits);

            let decl_name = Name::from_string(&self.qualify_name(name));
            self.ensure_known_attributes(attrs)?;
            self.collect_attributes(&decl_name, attrs);

            let (surviving_universe_params, ty_expr, proof_expr) =
                self.finalize_level_params(ty_expr, proof_expr)?;

            self.ensure_no_residual_fvars("theorem", name, &ty_expr, Some(&proof_expr))?;

            return Ok(ElabResult::Theorem {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                proof: proof_expr,
                modifiers: *modifiers,
            });
        }

        // Elaborate binders/body. The structural recursion context (if installed
        // by `setup_recursion`) is consumed here and must be cleared afterward,
        // even on error.
        let result = self.elab_def_body(binders, Some(ty), proof);
        self.recursive_def_ctx = None;
        let (ty_expr, proof_expr) = result?;

        // Substitute metavariables (#163)
        let ty_expr = self.metas.instantiate(&ty_expr);
        let proof_expr = self.metas.instantiate(&proof_expr);

        // Substitute level constraints collected during unification
        let ty_expr = self.metas.instantiate_levels(&ty_expr);
        let proof_expr = self.metas.instantiate_levels(&proof_expr);

        // Wrap with auto-implicit binders (#164)
        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, proof_expr) =
            Self::wrap_with_auto_implicits(ty_expr, proof_expr, &auto_implicits);

        // Collect all attributes for later registration
        let decl_name = Name::from_string(&self.qualify_name(name));
        // B21: reject unknown attributes loudly before honoring the rest.
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // Use self.universe_params which includes auto-bound params
        // (same fix as Definition, see #1324)
        // Filter to surviving params only (#3396, same as Definition).
        let (surviving_universe_params, ty_expr, proof_expr) =
            self.finalize_level_params(ty_expr, proof_expr)?;

        self.ensure_no_residual_fvars("theorem", name, &ty_expr, Some(&proof_expr))?;

        Ok(ElabResult::Theorem {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            proof: proof_expr,
            modifiers: *modifiers,
        })
    }

    /// Elaborate an `axiom` declaration.
    ///
    /// Axioms have a type but no value expression.
    pub(super) fn elab_axiom_inner(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        self.set_decl_universe_params(universe_params);
        let ty_expr = self.elab_axiom_type(binders, ty)?;

        // Substitute metavariables (#163)
        let ty_expr = self.metas.instantiate(&ty_expr);

        // Substitute level constraints collected during unification
        let ty_expr = self.metas.instantiate_levels(&ty_expr);

        // Wrap with auto-implicit binders (#164)
        let auto_implicits = self.take_auto_implicits();
        let ty_expr = Self::wrap_type_with_auto_implicits(ty_expr, &auto_implicits);

        // Collect all attributes for later registration
        let decl_name = Name::from_string(&self.qualify_name(name));
        // B21: reject unknown attributes loudly before honoring the rest.
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // Use self.universe_params which includes auto-bound params
        // (same fix as Definition, see #1324)
        // Filter to surviving params only (#3396, same as Definition).
        let (surviving_universe_params, ty_expr) = self.finalize_level_params_ty(ty_expr)?;

        Ok(ElabResult::Axiom {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            modifiers: *modifiers,
        })
    }

    /// Elaborate ONLY a declaration's SIGNATURE into a header: its
    /// namespace-qualified name, its surviving universe parameters, and its
    /// type. The body/proof is not elaborated and nothing is registered.
    ///
    /// This is the primitive that header-first, two-phase checking is built on
    /// (Trust I1): every declaration's header is elaborated before ANY body is,
    /// so name resolution sees the whole symbol table and stops depending on
    /// source order. It is deliberately the SAME computation `elab_axiom_inner`
    /// already performs for the signature of an `axiom` — an axiom *is* a
    /// header — minus attribute collection, which belongs to the authoritative
    /// pass that registers the real declaration.
    ///
    /// SOUNDNESS — a header is a TYPE, never a proof. Installing one as a
    /// constant is indistinguishable, to everything downstream, from asserting
    /// an axiom the user never wrote. A caller may therefore install headers
    /// ONLY in a non-authoritative staging environment, and owes two things
    /// this function cannot check for it:
    ///
    ///   1. elaborate a body only once every declaration it actually depends on
    ///      is a real, kernel-checked definition — never against the header of
    ///      something still unproved; and
    ///   2. verify, after registration, that the registered term mentions no
    ///      still-staged header.
    ///
    /// Without (2) a dependency scan that misses an edge silently upgrades a
    /// header into an assumption backing a kernel-certified proof. With it, a
    /// missed edge can only cause a spurious rejection.
    pub(crate) fn elab_decl_header_inner(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
    ) -> Result<(Name, Vec<Name>, Expr), ElabError> {
        self.set_decl_universe_params(universe_params);
        let ty_expr = self.elab_axiom_type(binders, ty)?;

        // Same normalization the axiom path applies: metavariables and level
        // constraints solved during signature unification must be substituted
        // before the type is used as a header, or the staged constant carries
        // unsolved holes the kernel would reject.
        let ty_expr = self.metas.instantiate(&ty_expr);
        let ty_expr = self.metas.instantiate_levels(&ty_expr);

        let auto_implicits = self.take_auto_implicits();
        let ty_expr = Self::wrap_type_with_auto_implicits(ty_expr, &auto_implicits);

        let decl_name = Name::from_string(&self.qualify_name(name));

        // Filter to surviving params only (#3396, as Definition/Axiom do).
        let mut used_level_params = Vec::new();
        collect_def_level_params(&ty_expr, &mut used_level_params);
        let surviving_universe_params: Vec<Name> = self
            .universe_params
            .iter()
            .map(|s| Name::from_string(s))
            .filter(|name| used_level_params.contains(name))
            .collect();

        Ok((decl_name, surviving_universe_params, ty_expr))
    }

    /// Elaborate an `opaque` declaration.
    ///
    /// Opaque declarations may have an optional body:
    /// - `opaque name : ty := val` -- body-bearing: elaborate both type and value
    /// - `opaque name : ty` -- body-less: elaborate type only (sort-only lane)
    ///
    /// Fixes #2552: previously collapsed all opaque to ElabResult::Axiom.
    pub(super) fn elab_opaque_inner(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        val: Option<&SurfaceExpr>,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        self.set_decl_universe_params(universe_params);

        let decl_name = Name::from_string(&self.qualify_name(name));
        if attrs.iter().any(|attr| {
            matches!(attr, Attribute::ImplementedBy(impl_name) if impl_name == name || impl_name == &decl_name.to_string())
        }) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "invalid implemented_by argument {name}: definition cannot be implemented by itself"
                ),
            });
        }
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        if let Some(val_expr) = val {
            // Body-bearing opaque: elaborate like a definition
            let (ty_expr, val_expr) = self.elab_def_body(binders, Some(ty), val_expr)?;

            let ty_expr = self.metas.instantiate(&ty_expr);
            let val_expr = self.metas.instantiate(&val_expr);

            let ty_expr = self.metas.instantiate_levels(&ty_expr);
            let val_expr = self.metas.instantiate_levels(&val_expr);

            let auto_implicits = self.take_auto_implicits();
            let (ty_expr, val_expr) =
                Self::wrap_with_auto_implicits(ty_expr, val_expr, &auto_implicits);

            // Filter to surviving params only (#3396, same as Definition).
            let (surviving_universe_params, ty_expr, val_expr) =
                self.finalize_level_params(ty_expr, val_expr)?;

            Ok(ElabResult::Opaque {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                val: Some(val_expr),
                modifiers: *modifiers,
            })
        } else {
            // Body-less opaque: type-only elaboration (like axiom)
            let ty_expr = self.elab_axiom_type(binders, ty)?;

            let ty_expr = self.metas.instantiate(&ty_expr);
            let ty_expr = self.metas.instantiate_levels(&ty_expr);

            let auto_implicits = self.take_auto_implicits();
            let ty_expr = Self::wrap_type_with_auto_implicits(ty_expr, &auto_implicits);

            // Filter to surviving params only (#3396, same as Definition).
            let (surviving_universe_params, ty_expr) = self.finalize_level_params_ty(ty_expr)?;

            Ok(ElabResult::Opaque {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                val: None,
                modifiers: *modifiers,
            })
        }
    }

    /// Elaborate a `partial def name : T := body` as a sound opaque constant.
    ///
    /// The body is deliberately DISCARDED: Lean compiles a partial def to an
    /// opaque declaration plus an unsafe implementation, so kernel-wise it is a
    /// non-reducing constant of type `T`. Registering `name : T` opaquely lets
    /// the body's self-reference resolve (its only purpose here) while the
    /// non-terminating body is never kernel-checked — matching Lean.
    ///
    /// SOUNDNESS: an opaque `name : T` is an axiom `name : T` to the kernel, so
    /// `T` must be inhabited or the declaration is a false witness (`partial def
    /// f : False := f`). We require `Inhabited T` — Lean's own requirement — and
    /// FAIL LOUD if it cannot be synthesized. No `add_decl_unchecked` / bypass is
    /// used: the opaque type itself is kernel-checked.
    pub(super) fn elab_partial_def_opaque(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        self.set_decl_universe_params(universe_params);
        let decl_name = Name::from_string(&self.qualify_name(name));
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // The full signature type `T = (binders) → ty` (like an axiom / body-less
        // opaque).
        let ty_expr = self.elab_axiom_type(binders, ty)?;
        let ty_expr = self.metas.instantiate(&ty_expr);
        let ty_expr = self.metas.instantiate_levels(&ty_expr);

        // SOUNDNESS GUARD: require `Inhabited` of the RESULT type — the type
        // after stripping the parameter binders (Lean's partial fixpoint needs a
        // default of the result type). This is sufficient: if `retTy` is
        // inhabited then so is `(binders) → retTy`, so the opaque `name : T` is a
        // genuine witness. Checking the result type (a base type like `Nat`)
        // also resolves against the concrete `Inhabited Nat` instance, whereas
        // `Inhabited (Nat → Nat)` would need an `Inhabited`-forall instance.
        let mut ret_ty = &ty_expr;
        for _ in 0..binders.len() {
            match ret_ty.kind() {
                clean_kernel::ExprKind::Pi(_, _, body) => ret_ty = body,
                _ => break,
            }
        }
        let ret_ty = ret_ty.clone();
        // A dependent result type (`partial def f (n : Nat) : Fin n`) leaves
        // loose bvars we cannot instantiate to check inhabitedness — and such a
        // type may genuinely be uninhabited (`Fin 0`). Reject conservatively.
        if ret_ty.has_loose_bvars() {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "`partial def {name}` with a dependent result type is not yet supported"
                ),
            });
        }
        let u = self
            .infer_sort(&ret_ty)
            .unwrap_or_else(|_| Level::succ(Level::zero()));
        let inhabited_goal = Expr::app(
            Expr::const_(Name::from_string("Inhabited"), vec![u]),
            ret_ty.clone(),
        );
        if self.resolve_instance(&inhabited_goal).is_none() {
            return Err(ElabError::FailedToSynthesizeInstance {
                goal: format!(
                    "Inhabited <result type of `partial def {name}`> \
                     (required to register the partial def's opaque signature soundly)"
                ),
            });
        }

        let auto_implicits = self.take_auto_implicits();
        let ty_expr = Self::wrap_type_with_auto_implicits(ty_expr, &auto_implicits);

        let (surviving_universe_params, ty_expr) = self.finalize_level_params_ty(ty_expr)?;

        Ok(ElabResult::Opaque {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            val: None,
            modifiers: *modifiers,
        })
    }
}
