// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in tactic registration for the [`TacticRegistry`].
//!
//! Wires existing tactic implementations into registry dispatch via
//! `SurfaceTactic::Named`. Design: `designs/2026-02-28-1839-tactic-dispatch.md`.

use std::sync::Arc;

use clean_kernel::{Expr, ExprKind};
use clean_parser::{Projection, SurfaceExpr, SurfaceName};

use super::registry::{TacticArgPattern, TacticEntry, TacticRegistry};
use super::{ProofState, TacticError, TacticResult};

#[cfg(test)]
mod typed_name_tests;

/// Extract a hypothesis name from an elaborated `Expr` argument.
///
/// Handles two common forms:
/// - `FVar(id)` → retain the exact local name and its lexical annotation
/// - typed name-slot metadata → validate and recover the authored SurfaceName
/// - legacy `Const(name, _)` → retain its exact kernel Name as generated syntax
///
/// REQUIRES: If `expr` is an `FVar`, the current goal local context contains that fvar when callers expect success.
/// ENSURES: On Ok, returns the user-facing hypothesis/constant name encoded by `expr`.
/// ENSURES: On Err, proof state is unchanged.
pub(crate) fn expr_to_hyp_name(ps: &ProofState, expr: &Expr) -> Result<SurfaceName, TacticError> {
    if let Some(name) = super::registry::decode_name_argument(expr)? {
        return ordinary_hyp_name(name);
    }
    match expr.kind() {
        ExprKind::FVar(id) => {
            if let Some(goal) = ps.current_goal() {
                for decl in &goal.local_ctx {
                    if &decl.fvar == id {
                        return ordinary_hyp_name(decl.name.clone());
                    }
                }
            }
            // NAME the variable rather than asserting one is missing. The
            // payload of `HypothesisNotFound` is meant to be the name the user
            // wrote; there is none here, so this said nothing and said it in
            // the wrong variant — the same category error the `assumption`
            // split fixed. `error_render::fvar` also decodes a metavariable,
            // which is what an unsolved `?m` in this position actually is.
            Err(TacticError::InvalidTarget {
                tactic: "resolve_ident".into(),
                detail: format!(
                    "{} is not a hypothesis in the current goal",
                    crate::error_render::fvar(*id, None)
                ),
            })
        }
        ExprKind::Const(name, _) => ordinary_hyp_name(SurfaceName::from_name(name.clone())),
        // `resolve_ident` is this helper, not a tactic anybody typed — but it
        // fronts ~30 call sites and `builtins_handlers.rs` asserts the string,
        // so threading the real tactic name is a separate change. What is fixed
        // here is the detail, which withheld the expression it was holding.
        _ => Err(TacticError::InvalidTarget {
            tactic: "resolve_ident".into(),
            detail: format!(
                "expected an identifier argument, got {} ({})",
                crate::error_render::term(expr),
                crate::error_render::kind_name(expr)
            ),
        }),
    }
}

/// The hypothesis a TERM argument denotes (`specialize h a`, `injection h`):
/// what [`expr_to_hyp_name`] reads, except that a global constant is never a
/// hypothesis — Lean elaborates the argument and requires a local of the
/// goal. A notation template's free name elaborates to the global it named
/// where the template was declared, and a use-site hypothesis spelled like
/// that global must not be what the tactic acts on (`specialize kz 0` in a
/// template over a global `kz`, used where a local `kz` is in scope, fails
/// in Lean).
pub(crate) fn term_hyp_name(ps: &ProofState, expr: &Expr) -> Result<SurfaceName, TacticError> {
    if let ExprKind::Const(name, _) = expr.kind() {
        return Err(TacticError::InvalidTarget {
            tactic: "resolve_ident".into(),
            detail: format!("the global constant `{name}` is not a hypothesis of the goal"),
        });
    }
    expr_to_hyp_name(ps, expr)
}

fn ordinary_hyp_name(name: SurfaceName) -> Result<SurfaceName, TacticError> {
    if name.is_anonymous() || name.is_relative_constructor() {
        Err(TacticError::InvalidTarget {
            tactic: "resolve_ident".into(),
            detail: "expected an ordinary hypothesis or binder name, not an anonymous or relative constructor selector".into(),
        })
    } else {
        Ok(name)
    }
}

/// Create a [`TacticEntry`] for a nullary tactic (takes no arguments).
/// REQUIRES: `f` implements the tactic semantics without inspecting elaborated args.
/// ENSURES: Returned entry uses `TacticArgPattern::Nullary`.
/// ENSURES: Invoking the handler forwards directly to `f(ps)`.
pub(crate) fn nullary(name: &str, f: fn(&mut ProofState) -> TacticResult) -> TacticEntry {
    TacticEntry {
        name: name.to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(move |ps, _args| f(ps)),
    }
}

/// Read `grind`'s parameter list and its `only` flag back out of its
/// elaborated arguments.
///
/// An identifier parameter arrives through the name-argument protocol (the
/// dispatch site treats this pattern like an ident list, because a lemma NAME
/// is not a term to elaborate against the goal). A parameter that really is a
/// term — Lean allows one — contributes the head constant of its application
/// spine, which is the name grind would key it on; anything with no constant
/// head contributes nothing rather than failing the tactic.
///
/// The leading [`clean_parser::GRIND_ONLY_MARKER`] argument, if present, is
/// the parser's record of `grind only`. It is matched with `same_syntax`, not
/// `==`: `SurfaceName` equality is structural, so a user lemma literally named
/// `_grind_only` would compare equal, while its component's origin is `Plain`
/// and the marker's is `Generated`.
fn grind_params_from_args(args: &[Expr]) -> Result<(Vec<SurfaceName>, bool), TacticError> {
    let only_marker = SurfaceName::generated_path(clean_parser::GRIND_ONLY_MARKER);
    let mut params = Vec::new();
    let mut only = false;
    for arg in args {
        if let Some(name) = super::registry::decode_name_argument(arg)? {
            if name.same_syntax(&only_marker) {
                only = true;
                continue;
            }
            params.push(name);
            continue;
        }
        if let ExprKind::Const(name, _) = arg.get_app_fn().kind() {
            params.push(SurfaceName::from_name(name.clone()));
        }
    }
    Ok((params, only))
}

/// Create a [`TacticEntry`] for a tactic taking a single elaborated term argument.
fn term_arg(name: &str, f: fn(&mut ProofState, Expr) -> TacticResult) -> TacticEntry {
    let owned_name = name.to_string();
    TacticEntry {
        name: name.to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(move |ps, args| {
            let arg = args.first().ok_or_else(|| TacticError::MissingArgument {
                tactic: owned_name.clone(),
                expected: "an argument".into(),
            })?;
            f(ps, arg.clone())
        }),
    }
}

/// Create a [`TacticEntry`] for a tactic taking exactly two elaborated term
/// arguments (parser pattern [`TacticArgPattern::TwoTerms`]).
///
/// The parser guarantees two argument-level terms reach the handler; both are
/// elaborated separately by the tactic dispatcher before the handler runs.
/// A missing argument (defensive — the parser already rejects fewer than two)
/// yields a [`TacticError::MissingArgument`] rather than a panic.
fn two_term(name: &str, f: fn(&mut ProofState, Expr, Expr) -> TacticResult) -> TacticEntry {
    let owned_name = name.to_string();
    TacticEntry {
        name: name.to_string(),
        pattern: TacticArgPattern::TwoTerms,
        handler: Arc::new(move |ps, args| {
            let first = args.first().ok_or_else(|| TacticError::MissingArgument {
                tactic: owned_name.clone(),
                expected: "two term arguments".into(),
            })?;
            let second = args.get(1).ok_or_else(|| TacticError::MissingArgument {
                tactic: owned_name.clone(),
                expected: "a second term argument".into(),
            })?;
            f(ps, first.clone(), second.clone())
        }),
    }
}

/// Create a [`TacticEntry`] for a tactic taking a single hypothesis name.
fn hyp_arg(name: &str, f: fn(&mut ProofState, &SurfaceName) -> TacticResult) -> TacticEntry {
    let owned_name = name.to_string();
    TacticEntry {
        name: name.to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(move |ps, args| {
            let hyp = if let Some(arg) = args.first() {
                term_hyp_name(ps, arg)?
            } else {
                return Err(TacticError::MissingArgument {
                    tactic: owned_name.clone(),
                    expected: "a hypothesis argument".into(),
                });
            };
            f(ps, &hyp)
        }),
    }
}

/// Register all built-in tactics into the registry.
///
/// Called during `ElabCtx::new()` initialization. Delegates to batch
/// registration helpers to stay within function-size limits.
///
/// Registers both simple (Named-dispatched) and compound (variant-dispatched)
/// tactics in a single entry point. Callers should not need to register
/// additional tactic batches separately.
///
/// ENSURES: Core, search, ay, and phase-3D migrated tactic names are inserted into `registry`.
/// ENSURES: Compound handlers for all migrated SurfaceTactic variants are inserted.
/// ENSURES: Existing entries with matching names are overwritten by the built-in registrations.
pub fn register_builtin_tactics(registry: &mut TacticRegistry) {
    // Simple (Named-dispatched) tactics
    register_core_nullary(registry);
    register_nullary_p1(registry);
    register_nullary_p2_p3(registry);
    register_hyp_arg_tactics(registry);
    register_complex_arg_tactics(registry);
    register_ay_tactics(registry);
    super::builtins_phase3d_loc::register_phase3d_location(registry);

    // Compound (variant-dispatched) tactics — consolidated from elab_init.rs
    // Phase 3D Wave 5: compound combinator tactics (#2440)
    super::builtins_compound::register_compound_tactics(registry);
    // Phase 3D Wave 6: expression-dependent compound tactics (#2440)
    super::builtins_phase3d_elab::register_phase3d_elab_tactics(registry);
    // Phase 3D Wave 4: conv tactics (#2440)
    super::builtins_phase3d_conv::register_phase3d_conv(registry);
    // Phase 3D Wave 3: rewrite/simp tactics (#2440)
    super::builtins_phase3d_rewrite::register_phase3d_rewrite(registry);
    // Phase 3D Wave 4: cases/induction tactics (#2440)
    super::builtins_phase3d_intro::register_phase3d_intro(registry);
}

/// Build the built-in tactic argument pattern table for the parser.
/// Callers with an `ElabCtx` should use `ctx.tactic_registry.tactic_patterns()` instead.
#[must_use]
/// ENSURES: Result matches `tactic_patterns()` on a fresh registry after `register_builtin_tactics`.
pub fn builtin_tactic_patterns() -> super::registry::TacticPatterns {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    registry.tactic_patterns()
}

/// Register core Lean 4 nullary tactics (migrated from hardcoded SurfaceTactic variants).
/// Phase 3B of #1886 — these were previously dispatched via dedicated enum variants;
/// now they flow through the TacticRegistry via SurfaceTactic::Named.
fn register_core_nullary(registry: &mut TacticRegistry) {
    let entries = [
        nullary("assumption", super::assumption),
        nullary("constructor", super::constructor),
        nullary("and_intros", super::and_intros),
        nullary("left", super::left_),
        nullary("right", super::right_),
        nullary("split", super::split_),
        nullary("exfalso", super::exfalso),
        nullary("omega", super::omega),
        // Lean's procedure (`decide_lean`): free variables and metavariables
        // refused first, default transparency, `of_decide_eq_true`. The
        // `eval_decide` ladder stays the internal rung of omega/norm_num/….
        nullary("decide", super::decide_lean::decide),
        nullary("contradiction", super::contradiction),
        nullary("trivial", super::trivial),
        // Wave 2: 10 more nullary tactics
        nullary("aesop", super::aesop),
        nullary("tauto", super::tauto),
        nullary("cert_simp", super::cert_simp),
        nullary("norm_num", super::norm_num),
        nullary("ring", super::ring),
        nullary("ring_nf", super::ring_nf),
        nullary("symm", super::symm),
        nullary("native_decide", super::decide_lean::native_decide),
        nullary("delta", super::delta),
        // `whnf`: reduce the goal (or conv focus) to weak-head normal form.
        // Works inside `conv => whnf` via the generic conv-body evaluator.
        nullary("whnf", super::whnf),
        // `reduce`: head + argument-position normalization (`conv => reduce`).
        nullary("reduce", super::reduce),
        // `subst_eqs`: substitute every equality hypothesis. Clean's `subst_vars`
        // already repeatedly substs all variable-equalities, which is exactly the
        // core of Lean's `subst_eqs`, so it serves as the handler.
        nullary("subst_eqs", super::subst_vars),
        nullary("admit", super::sorry),
        // `classical`: make classical reasoning available for the rest of the
        // block. A structural no-op in Clean (classical primitives are always
        // in the env; `by_cases`/`by_contra` use `Classical.em` directly), so it
        // recognizes Mathlib's single most common block opener and lets those
        // proofs elaborate instead of aborting on an unknown tactic. See
        // `existential::classical` for the honest scope (no Decidable fallback).
        nullary("classical", super::classical),
        nullary("auto_cascade", super::auto_cascade),
        // `infer_instance`: synthesize a type-class instance for the goal
        // (e.g. `Decidable True`, `Inhabited Nat`). Closes the goal via the
        // kernel-checked `exact` with the synthesized instance term, so a
        // wrong synthesis is rejected by the kernel rather than trusted.
        nullary("infer_instance", super::infer_instance),
    ];
    for entry in entries {
        registry.register(entry);
    }

    // `grind [f, g]` / `grind only [f]`: Lean's grind takes an optional
    // parameter list whose entries feed the same E-matching machinery
    // `@[grind]` registers into. Registered `Nullary` the list was parsed and
    // DISCARDED — `grind [no_such_lemma_xyzzy]` failed byte-identically to a
    // bare `grind`, which is how the diagnosis established it was dropped
    // rather than merely unhelpful.
    registry.register(TacticEntry {
        name: "grind".to_string(),
        pattern: TacticArgPattern::BracketedParamList,
        handler: Arc::new(|ps, args| {
            let (params, only) = grind_params_from_args(args)?;
            super::grind::grind_with_params(ps, &params, only)
        }),
    });

    // mathverse_use / mathverse_suggest: Mathverse Library premise selection tactics
    registry.register(TacticEntry {
        name: "mathverse_use".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(super::mathverse_use::eval_mathverse_use),
    });
    registry.register(TacticEntry {
        name: "mathverse_suggest".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(super::mathverse_use::eval_mathverse_suggest),
    });
    // mathverse_apply <name> — cite a library lemma BY NAME and apply it to the
    // goal, synthesizing its arguments. This is the `exact add_comm a b` shape;
    // `mathverse_use` above is nullary SEARCH and cannot express "I know which
    // lemma I want". NonemptyIdentList because the argument is a constant NAME
    // that is not yet in the environment (the tactic is what loads it), so it
    // cannot be pre-elaborated as a term.
    registry.register(TacticEntry {
        name: "mathverse_apply".to_string(),
        pattern: TacticArgPattern::NonemptyIdentList,
        handler: Arc::new(super::mathverse_use::eval_mathverse_apply),
    });

    // Phase 3C Wave 1: 5 remaining nullary + 2 conv-nullary (#2430)
    register_phase3c_nullary(registry);
    // Phase 3C Wave 2: term-arg + expr-list + opt-nat (#2430)
    register_phase3c_wave2(registry);
    // Phase 3C Wave 3: ident-list + nonempty-ident + compound + search (#2430)
    super::builtins_wave3::register_phase3c_wave3(registry);
}

/// Phase 3C Wave 1: nullary tactics migrated from dedicated SurfaceTactic variants.
/// `linarith` and `norm_cast` are already registered in `register_nullary_p1`.
fn register_phase3c_nullary(registry: &mut TacticRegistry) {
    // Phase 3D.6 keyword-to-Named registrations (#2440)
    super::builtins_phase3d::register_phase3d_keyword(registry);

    // intros — bare, introduce ALL binders (loop intro until failure); with
    // names, `intros a b` introduces exactly those, like `intro a b` (Lean's
    // `Lean.Parser.Tactic.intros` takes `(ppSpace colGt (ident <|> hole))*`).
    // As a nullary entry the names were parsed as the NEXT tactics
    // (`IsPartialInv.comp`'s `intros a b`: "unknown tactic 'a'", measured
    // 2026-09-12).
    registry.register(TacticEntry {
        name: "intros".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            if args.is_empty() {
                let mut count = 0;
                while super::intro(
                    ps,
                    &SurfaceName::from_name(clean_kernel::Name::anon().str(format!("h_{count}"))),
                )
                .is_ok()
                {
                    count += 1;
                }
                return Ok(());
            }
            for name in super::builtins_wave3::args_to_names(ps, args)? {
                super::intro(ps, &name)?;
            }
            Ok(())
        }),
    });

    // skip — no-op
    registry.register(TacticEntry {
        name: "skip".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|_ps, _args| Ok(())),
    });

    // trace_state — diagnostic tactic that prints the goal state for debugging
    // and leaves the proof unchanged. Faithful for proof-checking as a no-op:
    // the trace output is a side-effect, so the goal (and the assembled proof
    // term) is identical with or without it. Previously an UnknownTactic that
    // rejected otherwise-valid debug/test proofs.
    registry.register(TacticEntry {
        name: "trace_state".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|_ps, _args| Ok(())),
    });

    // done — assert no goals remain
    registry.register(TacticEntry {
        name: "done".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| {
            if ps.goals().is_empty() {
                Ok(())
            } else {
                Err(TacticError::UnsolvedGoals {
                    count: ps.goals().len(),
                    detail: String::new(),
                })
            }
        }),
    });

    // lhs — conv navigation: focus on LHS of equality/relation
    registry.register(TacticEntry {
        name: "lhs".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| conv_nav(ps, super::conv::ConvPosition::EqLhs)),
    });

    // rhs — conv navigation: focus on RHS of equality/relation
    registry.register(TacticEntry {
        name: "rhs".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| conv_nav(ps, super::conv::ConvPosition::EqRhs)),
    });
}

/// Conv navigation handler extracted from ElabCtx::conv_navigate.
///
/// Shared by simple conv tactics (`lhs`, `rhs`) in phase 3C and
/// compound conv tactics (`conv_arg`) in phase 3D.
///
/// Part of #2477: stores the original expression and accumulated navigation
/// path on `ps.conv_nav_original` / `ps.conv_nav_path` so that
/// `eval_conv_goal` can reconstruct the full expression after body rewrites.
///
/// REQUIRES: `ps` has a current goal whose target supports navigation at `pos`.
/// ENSURES: On Ok, the current goal target is the focused subexpression at `pos`.
/// ENSURES: On Ok, `ps.conv_nav` stores `(original, accumulated_path)`.
/// ENSURES: On Err, the proof state is unchanged.
pub(crate) fn conv_nav(ps: &mut ProofState, pos: super::conv::ConvPosition) -> TacticResult {
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
    let mut conv = super::conv::ConvState::new(goal.target.clone());
    conv.go(pos.clone())?;

    match ps.conv_nav {
        Some((_, ref mut path)) => {
            // Extend existing navigation (e.g., lhs followed by enter)
            path.push(pos);
        }
        None => {
            // First navigation — store the original full expression
            ps.conv_nav = Some((goal.target.clone(), vec![pos]));
        }
    }
    // A witness accumulated for a previous focus is no longer valid after
    // changing the navigation path inside the same conv body.
    ps.conv_focus_witness = None;
    if let Some(g) = ps.current_goal_mut() {
        g.target = conv.focus;
    }
    Ok(())
}

/// Extract an exact source name for name-based tactics.
///
/// Shared by phase 3D intro (`cases`, `induction`) and rewrite (`rw`, `simp`)
/// registration handlers.
///
/// Handles:
/// - `SurfaceExpr::Ident` → preserves identity and lexical annotation.
/// - `SurfaceExpr::Proj` with a `Named` projection → appends typed components,
///   recursing into the base so `MySem.run` / `StateT.bind` /
///   `Except.ok.injEq` resolve to their fully-qualified kernel names. This is
///   the form produced by the parser for any dotted identifier used in a
///   tactic argument list (e.g. `simp only [StateT.bind, Except.ok.injEq] at
///   h`). Before #3529, these collapsed to a Debug-rendered span string which
///   never matched anything in the environment, so the unfold/rewrite silently
///   dropped the lemma and reported `NoProgress`.
/// - `SurfaceExpr::Paren` → strips redundant parentheses (`(foo)` ≡ `foo`).
///
/// Non-name expressions and relative constructor selectors are rejected;
/// diagnostics cannot mint a name that happens to resolve downstream.
pub(crate) fn surface_expr_to_name(expr: &SurfaceExpr) -> Result<SurfaceName, TacticError> {
    match expr {
        SurfaceExpr::Ident(_, name) if !name.is_anonymous() && !name.is_relative_constructor() => {
            Ok(name.clone())
        }
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            if field.is_anonymous() || field.is_relative_constructor() {
                return Err(TacticError::InvalidTarget {
                    tactic: "resolve_ident".into(),
                    detail: "expected an ordinary named projection".into(),
                });
            }
            Ok(surface_expr_to_name(base)?.append(field))
        }
        SurfaceExpr::Paren(_, inner) => surface_expr_to_name(inner),
        other => Err(TacticError::InvalidTarget {
            tactic: "resolve_ident".into(),
            detail: format!("expected a name, got {}", crate::error_render::shape(other)),
        }),
    }
}

/// Phase 3C Wave 2: term-arg, expr-list, and opt-nat tactics (#2430).
fn register_phase3c_wave2(registry: &mut TacticRegistry) {
    // 3C.2: term-arg tactics (elaborated Expr passed to handler)
    let term_entries = [
        term_arg("exact", super::exact),
        term_arg("apply", super::apply),
        term_arg("refine", super::term_close::refine),
        term_arg("change", super::term_close::change),
        term_arg("trans", super::trans),
        hyp_arg("injection", super::injection),
        // `absurd h hn`: given `h : a` and `hn : ¬a`, close any goal. The two
        // terms are elaborated separately and handed to the kernel-checked
        // `eval_absurd`, which builds `absurd h hn` / `False.elim (hn h)`.
        two_term("absurd", super::eval_absurd),
    ];
    for entry in term_entries {
        registry.register(entry);
    }

    // 3C.5: expr-list tactics
    registry.register(TacticEntry {
        name: "use".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(|ps, args| super::term_close::use_(ps, args.to_vec())),
    });
    registry.register(TacticEntry {
        name: "exists".to_string(),
        pattern: TacticArgPattern::ExprList,
        // Lean's core `exists e₁, …` provides the witnesses AND discharges the
        // trivial residual goal (e.g. `0 = 0` after `exists 0` on `∃ n, n = 0`),
        // so it is the same as `use` here — route through the discharging handler
        // instead of bare `existsi` (which left the residual open). A non-trivial
        // residual (e.g. a wrong witness `exists 3` on `∃ n, n = 5`) is NOT closed
        // and remains for the user / fails — fail-closed, matching Lean.
        handler: Arc::new(|ps, args| super::term_close::use_(ps, args.to_vec())),
    });

    // `congr` / `congr n` — Lean's `congrN`, depth `hugeDepth` when omitted.
    registry.register(TacticEntry {
        name: "congr".to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(|ps, args| {
            let depth = extract_opt_nat(args).unwrap_or(super::congr_n::CONGR_DEFAULT_DEPTH);
            super::congr_n::congr_n(ps, depth)
        }),
    });

    // Mathlib's `inhabit α` (`Mathlib/Tactic/Inhabit.lean`).
    registry.register(TacticEntry {
        name: "inhabit".to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(super::inhabit::inhabit),
    });

    // 3C.6: opt-nat tactics (rotate_left/rotate_right)
    registry.register(TacticEntry {
        name: "rotate_left".to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(|ps, args| {
            let count = extract_opt_nat(args).unwrap_or(1);
            for _ in 0..count {
                super::goal::rotate(ps)?;
            }
            Ok(())
        }),
    });
    registry.register(TacticEntry {
        name: "rotate_right".to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(|ps, args| {
            let count = extract_opt_nat(args).unwrap_or(1);
            for _ in 0..count {
                super::goal::rotate_back(ps)?;
            }
            Ok(())
        }),
    });
}

/// Extract an optional natural number from elaborated args.
fn extract_opt_nat(args: &[Expr]) -> Option<usize> {
    use clean_kernel::expr::Literal;
    args.first().and_then(|e| match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64().map(|v| v as usize),
        _ => None,
    })
}

/// Register nullary tactics — Priority 1 (Mathlib-critical).
fn register_nullary_p1(registry: &mut TacticRegistry) {
    let entries = [
        nullary("contrapose", super::contrapose),
        nullary("field", super::field_normalize_tactic),
        nullary("field_simp", super::field_simp),
        nullary("norm_cast", super::norm_cast),
        nullary("positivity", super::positivity),
        nullary("polyrith", super::polyrith),
        nullary("linarith", super::linarith),
        nullary("nlinarith", super::nlinarith),
        nullary("push_cast", super::push_cast),
        nullary("gcongr", super::gcongr),
        nullary("split_ifs", super::split_ifs),
    ];
    for entry in entries {
        registry.register(entry);
    }
}

/// Register nullary tactics — Priority 2-3 (library and specialized).
fn register_nullary_p2_p3(registry: &mut TacticRegistry) {
    let entries = [
        nullary("cc", super::cc),
        nullary("blast", super::blast),
        nullary("abel", super::abel),
        nullary("group", super::group),
        nullary("cert_mathverse", super::cert_mathverse),
        nullary("zify", super::zify),
        nullary("qify", super::qify),
        nullary("mono", super::mono),
        nullary("nontriviality", super::nontriviality),
        nullary("continuity", super::continuity),
        nullary("measurability", super::measurability),
        nullary("itauto", super::itauto),
    ];
    for entry in entries {
        registry.register(entry);
    }
}

/// Register tactics that take a single hypothesis name argument.
fn register_hyp_arg_tactics(registry: &mut TacticRegistry) {
    let entries = [
        hyp_arg("discriminate", super::discriminate),
        hyp_arg("peel", super::peel),
        hyp_arg("fin_cases", super::fin_cases),
        hyp_arg("interval_cases", super::interval_cases),
    ];
    for entry in entries {
        registry.register(entry);
    }
}

/// Register tactics with complex argument handling (delegated to builtins_handlers.rs, #307).
fn register_complex_arg_tactics(registry: &mut TacticRegistry) {
    super::builtins_handlers::register_complex_arg_tactics(registry);
}

/// Register ay SMT tactics (delegated to builtins_handlers.rs, #307).
fn register_ay_tactics(registry: &mut TacticRegistry) {
    super::builtins_handlers::register_ay_tactics(registry);
}
