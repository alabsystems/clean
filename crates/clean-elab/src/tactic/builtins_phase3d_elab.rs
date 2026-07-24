// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 6: expression-dependent compound tactic registrations.
//!
//! Migrates 4 compound tactics (Have, Let, Suffices, Match) from hardcoded
//! `eval_compound_tactic` dispatch to registry-based compound handlers (#2440).
//!
//! Unlike Wave 5's combinator handlers (which only need `eval`/`eval_seq`),
//! these handlers also need `elaborate` and `infer_type` from the `TacticEval`
//! trait to process type annotations and value expressions.

use std::sync::Arc;

use super::registry::{CompoundTacticEntry, TacticRegistry};
use super::{ProofState, TacticError};
use clean_kernel::Expr;
use clean_parser::SurfaceTactic;

/// Register expression-dependent compound tactics into the registry.
///
/// These 4 tactics need `TacticEval::elaborate` and/or `TacticEval::infer_type`
/// in addition to recursive tactic evaluation.
/// ENSURES: `registry` contains compound handlers for `have`, `let`, `suffices`, `obtain`, and `match`.
/// ENSURES: Existing compound entries with those names are replaced.
pub(crate) fn register_phase3d_elab_tactics(registry: &mut TacticRegistry) {
    registry.register_compound(compound_have());
    registry.register_compound(compound_let());
    registry.register_compound(compound_suffices());
    registry.register_compound(compound_obtain());
    registry.register_compound(compound_rcases());
    registry.register_compound(compound_rintro());
    registry.register_compound(super::builtins_phase3d_match::compound_match());
}

/// `have h : T := proof`, `have h : T by tacs`, or `have h := proof` — forward
/// reasoning.
///
/// Introduces an intermediate lemma. When a `: T` annotation is present,
/// elaborates the type, then either elaborates a direct proof term or runs a
/// sub-tactic to produce one. When the annotation is omitted (`have h :=
/// term`), the proof must be a direct term: it is elaborated and its inferred
/// type becomes the hypothesis type (mirrors `let`'s no-annotation path and
/// Lean's `have h := e`).
///
/// SOUNDNESS: in every branch the hypothesis is introduced via the
/// kernel-checked `have_`, which rechecks that the proof term has the recorded
/// type. The inferred-type path uses the proof term's own `infer_type`, so the
/// hypothesis can never claim a type the term does not have; a term that fails
/// to elaborate or whose type does not match a given annotation surfaces as a
/// `TacticError`, never a fabricated type or panic. A no-annotation `have` whose
/// proof is a `by`/tactic block (no type to seed the sub-goal) errors rather
/// than guessing.
fn compound_have() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "have".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Have(_, name, ty, proof_tac) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "have".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            // An anonymous `have : T := e` binds the hypothesis under `this`,
            // matching Lean's `haveIdLhs` default (`elabHaveCore`); a named
            // `have h : T := e` keeps `h`. Previously the anonymous case defaulted
            // to `h`, leaving a subsequent `exact this` unbound. (B105)
            let h = name.as_deref().unwrap_or("this");
            match ty {
                // `have h : T := proof` / `have h : T by tacs` — typed.
                Some(ty) => {
                    let ty_expr = eval.elaborate(ty)?;
                    let proof_expr = match proof_tac.as_ref() {
                        // `have h : T := e` elaborates `e` against the ascribed
                        // type `T` (Lean's `elabHaveCore` → `elabTermEnsuringType`),
                        // not bare/inferred. This is what lets a polymorphic proof
                        // term like `rfl` — whose principal type fixes neither side
                        // of the equation on its own — be solved: seeded with
                        // expected type `n + 0 = n`, `rfl` unifies both sides
                        // instead of failing with a metavariable shape mismatch.
                        // The term is still kernel-re-checked by `have_` below.
                        SurfaceTactic::Term(_, e) => Some(eval.elaborate_expected(e, &ty_expr)?),
                        other => {
                            let mut sub_ps = create_sub_proof_state(ps, ty_expr.clone());
                            // #close_fvars (nested `have := by`): the `by` block
                            // assembles an INDEPENDENT proof term that
                            // `sub_ps.closed_proof()` closes on its own. Its tactic
                            // FVars must be numbered from this sub-proof's OWN base
                            // so FVar id ↔ binder depth stays aligned — the first
                            // `fresh_fvar()` in the sub-proof (e.g. an inner
                            // `have`'s let-binder or an `intro`) has to map to
                            // BVar(0) at binder depth 1. `clone_with_fresh_goal_target`
                            // bumps `next_fvar` (+1) above the parent to avoid id
                            // collisions but left `fvar_base` inherited from the
                            // parent (often 0); the resulting off-by-one made
                            // `close_fvars` leave the sub-proof's first binder FVar
                            // unconverted (an ID-to-binder gap → the close_fvars
                            // panic on a valid nested `have := by`). Rebasing to the
                            // sub-proof's own starting `next_fvar` — the same
                            // discipline `script_runner`/`run_oracle` use for a
                            // caller-owned context — restores the correspondence.
                            // Any FVar the sub-proof inherits from the parent
                            // (id < this base, e.g. an outer `intro h`) is preserved
                            // through `closed_proof()` and abstracted by the
                            // parent's own close pass, so nothing is dropped and the
                            // assembled term is still kernel-rechecked by `have_`.
                            sub_ps.fvar_base = sub_ps.next_fvar;
                            eval.eval(&mut sub_ps, other)?;
                            sub_ps.closed_proof()
                        }
                    };
                    super::have_(ps, h, ty_expr, proof_expr)
                }
                // `have h := proof` — type inferred from the proof term. Only a
                // direct term carries a type to infer; a tactic block has no
                // seed type, so reject it (matching Lean, which requires `: T`
                // for `have h := by ...`).
                None => {
                    let SurfaceTactic::Term(_, e) = proof_tac.as_ref() else {
                        return Err(TacticError::InvalidTarget {
                            tactic: "have".into(),
                            detail: "`have` without a type annotation requires a proof term \
                                     (`have h := term`); add `: T` to use a tactic block"
                                .into(),
                        });
                    };
                    let proof_expr = eval.elaborate(e)?;
                    let inferred_ty = eval.infer_type(&proof_expr)?;
                    super::have_(ps, h, inferred_ty, Some(proof_expr))
                }
            }
        }),
    }
}

/// `let x : T := val` — introduce a let-binding.
///
/// Elaborates the optional type annotation and value. If no type annotation,
/// infers the type from the value expression.
fn compound_let() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "let".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Let(_, name, ty, val) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "let".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let ty_expr = ty.as_ref().map(|t| eval.elaborate(t)).transpose()?;
            let val_expr = eval.elaborate(val)?;
            let let_ty = match ty_expr {
                Some(t) => t,
                None => eval.infer_type(&val_expr)?,
            };
            // `let x : T := val` introduces a *local definition* whose value is
            // retained (body-visible / zeta-reducible), unlike `have` which
            // forgets the value and yields an opaque hypothesis. Route to
            // `let_` so the assembled proof term is `let x : T := val; <rest>`
            // and `x` is definitionally equal to `val`. See `have_let::let_`.
            super::let_(ps, name, let_ty, Some(val_expr))
        }),
    }
}

/// `suffices h : T by tacs` (and `suffices h : T from e`) — backward reasoning
/// from a sufficient condition.
///
/// Faithful desugaring of Lean 4's `expandSuffices`
/// (`Lean.Elab.BuiltinNotation`): `suffices h : T by tacs; body` elaborates as
/// `have h : T := body; by tacs`, i.e. `h : T` is bound to the *residual*
/// proof of `T` (supplied by the tactics that follow `suffices`), and the
/// *main* goal is closed by `by tacs` with `h : T` in scope. The `from e` form
/// shares the desugaring; the parser routes `from e` through the same
/// `tacs` channel as a single `Term(e)` tactic that closes the main goal.
///
/// Implementation: reuse the kernel-checked `have_` machinery (the obligation
/// order is the only difference between `have` and `suffices`). `have_(.., None)`
/// produces two goals — `goal[0]` = the lemma `T`, `goal[1]` = the continuation
/// (the *original* target, with `h : T` in its local context). We swap so the
/// continuation is the main goal, run `tacs` on it (which closes the original
/// goal using `h`), and leave the lemma goal `⊢ T` as the residual obligation
/// for the subsequent tactics. If `tacs` fail to close the main goal — or close
/// it with the wrong term — the kernel-checked `have_`/`close_goal`/term-tactic
/// path surfaces a `TacticError` (never a panic), and the residual `⊢ T` goal
/// remains unsolved if the user never proves it.
fn compound_suffices() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "suffices".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Suffices(_, name, ty, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "suffices".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let ty_expr = eval.elaborate(ty)?;
            let h = name.as_deref().unwrap_or("h");
            // `have_(.., None)` pushes [lemma_goal (T), cont_goal (original, h:T)].
            // The continuation goal is the one whose target is the original goal
            // and whose context carries `h : T` — that is exactly where Lean's
            // `by tacs` block runs.
            super::have_(ps, h, ty_expr, None)?;
            let goals_before = ps.goals.len();
            // Swap so the continuation (original target, h : T in scope) is the
            // current main goal; `tacs` close it using `h`.
            if ps.goals.len() >= 2 {
                ps.goals.swap(0, 1);
            } else {
                // `have_` always pushes two goals; if not, the state is
                // unexpected — refuse rather than silently mis-elaborate.
                return Err(TacticError::InvalidTarget {
                    tactic: "suffices".into(),
                    detail: "expected continuation and lemma goals after have_".into(),
                });
            }
            eval.eval_seq(ps, tacs)?;
            // `tacs` must have closed *exactly* the continuation goal, leaving
            // the residual lemma goal `⊢ T` (and any pre-existing goals) at the
            // front. If `tacs` did not close it (count unchanged) or closed more
            // than the continuation, the main goal was not properly discharged.
            if ps.goals.len() != goals_before.saturating_sub(1) {
                return Err(TacticError::InvalidTarget {
                    tactic: "suffices".into(),
                    detail: "tactic block did not close the main goal".into(),
                });
            }
            Ok(())
        }),
    }
}

/// `obtain pat (: T)? := e` — destructure a term via the pattern engine.
///
/// Faithful desugaring of Lean 4's `obtain pat := e` ≡ `have h : T := e;
/// rcases h with pat`. Elaborates the RHS scrutinee `e` (kernel-checked through
/// the normal elaborator), determines its type (the `: T` ascription if given,
/// else inferred), introduces it as a fresh anonymous hypothesis via the
/// kernel-checked `have_`, then destructures that hypothesis per `pattern` using
/// the SAME kernel-checked `cases`/`casesOn` engine that backs `rintro`/`rcases`.
///
/// SOUNDNESS: the goal is only ever transformed via `have_` (kernel-checked
/// `close_goal`) and `destruct_named_hypothesis` (kernel-checked `cases`); no
/// raw FVars are pushed and no new trust surface is introduced. A pattern/type
/// mismatch surfaces as a `TacticError`, never a panic.
fn compound_obtain() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "obtain".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Obtain {
                pattern, ty, term, ..
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "obtain".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };

            // Elaborate the scrutinee term (kernel-checked elaboration).
            let term_expr = eval.elaborate(term)?;

            // Fast path: `obtain pat := h` where `h` is a BARE existing hypothesis
            // (a local FVar) and there is no `: T` ascription is EXACTLY
            // `rcases h with pat` — Lean destructures/consumes `h` in place, with no
            // intervening copy. Route straight to the existing-hypothesis engine so
            // `h` itself is the scrutinee. This matters for the top-level `rfl`
            // pattern: `obtain rfl := h` must `subst h` directly. If instead we
            // copied `h` into `_obtain{N}` and `subst`bed the copy, the ORIGINAL
            // `h : a = b` would survive and — being an equality mentioning both `a`
            // and `b` — would mask which side is safe to eliminate (subst's motive
            // only abstracts the goal, not surviving hyps), reintroducing the
            // `fvar mismatch`. Only taken for a bare hypothesis reference with no
            // ascription; a compound RHS or a `: T` ascription still goes through
            // the kernel-checked `have_` copy below.
            if ty.is_none() {
                if let clean_kernel::ExprKind::FVar(id) = term_expr.kind() {
                    let is_local_hyp = ps
                        .current_goal()
                        .map(|g| g.local_ctx.iter().any(|d| d.fvar == *id))
                        .unwrap_or(false);
                    if is_local_hyp {
                        let hyp_name = super::builtins::expr_to_hyp_name(ps, &term_expr)?;
                        return super::destruct_named_hypothesis(ps, &hyp_name, pattern);
                    }
                }
            }

            // Determine the hypothesis type: the `: T` ascription if present,
            // otherwise the inferred type of the scrutinee. `have_` re-checks
            // that `term_expr` has this type, so an ascription mismatch errors.
            let hyp_ty = match ty {
                Some(t) => eval.elaborate(t)?,
                None => eval.infer_type(&term_expr)?,
            };

            // FAIL CLOSED on an unresolved binder-type metavariable in the
            // scrutinee's type. An untyped existential whose binder type was never
            // inferred — e.g. `∃ a, ∃ b, a = b`, where `a = b` pins no concrete
            // type (Lean 4 itself rejects this header with "don't know how to
            // synthesize implicit argument `α`") — carries an *unassigned*
            // elaborator meta encoded as an `FVar` with the high-bit tag
            // (`MetaState::to_fvar`, id `2^63 + n`). The `have_` copy below would
            // commit that meta into the outer proof term's `let h : ty := …`,
            // where it survives `close_fvars` (its id is far above `next_fvar`)
            // and `instantiate` (it is unassigned) and reaches the kernel re-check
            // as a confusing `UnknownFVar(FVarId(9223372…))`. Reject it here, at
            // the earliest leak point (before `have_`), with a clear diagnostic —
            // never a sentinel leak into the kernel, never a silent over-accept.
            // Fully-resolved (typed) scrutinees carry no meta, so this is a no-op
            // for the common `∃ a : T, …` case.
            let hyp_ty_inst = ps.metas.instantiate(&hyp_ty);
            if super::contains_unassigned_meta(&hyp_ty_inst) {
                return Err(TacticError::InvalidTarget {
                    tactic: "obtain".into(),
                    detail: "cannot destructure: the scrutinee's type still contains an \
                             unresolved metavariable (an implicit argument such as the binder \
                             type could not be inferred). Add an explicit type annotation to \
                             the binder(s) — e.g. `∃ a : T, …`"
                        .into(),
                });
            }

            // Introduce the scrutinee as a fresh anonymous hypothesis. Use a
            // name unlikely to collide with user hypotheses so the subsequent
            // destructure targets exactly this binder.
            let tmp_name = format!("_obtain{}", ps.next_fvar);
            super::have_(ps, &tmp_name, hyp_ty, Some(term_expr))?;

            // Destructure per the parsed pattern via the kernel-checked engine.
            super::destruct_named_hypothesis(ps, &tmp_name, pattern)
        }),
    }
}

/// `rcases h with ⟨hp, hq⟩` — destructure an EXISTING hypothesis in place.
///
/// Identical to the destructure half of `obtain` but WITHOUT the `have_`/copy
/// step: the scrutinee `h` is an already-introduced hypothesis, so we resolve it
/// to its binder name and feed it straight to the same kernel-checked pattern
/// engine (`destruct_named_hypothesis`) that backs `obtain`, `rintro`, and
/// `cases ... with`.
///
/// SOUNDNESS: the goal is only ever transformed via `destruct_named_hypothesis`
/// (kernel-checked `cases`); no raw FVars are pushed and no new trust surface is
/// introduced. A pattern that does not match the hypothesis's structure (e.g.
/// too many components) surfaces as a `TacticError`, never a panic, and the
/// resulting proof term is rechecked by `add_decl`.
fn compound_rcases() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rcases".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::RCases { term, pattern, .. } = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rcases".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };

            // Resolve the scrutinee to the name of an existing hypothesis.
            // Elaborate the surface term (a hypothesis reference) to a kernel
            // Expr, then map FVar/Const back to its local-context binder name —
            // the same resolution the registry `rcases_handler` performs.
            let term_expr = eval.elaborate(term)?;
            let hyp_name = super::builtins::expr_to_hyp_name(ps, &term_expr)?;

            // Destructure the EXISTING hypothesis per the parsed pattern via the
            // kernel-checked engine. No `have_` step: `h` already exists.
            super::destruct_named_hypothesis(ps, &hyp_name, pattern)
        }),
    }
}

/// `rintro pat₁ pat₂ …` — recursive intro with destructuring patterns.
///
/// Faithful desugaring of Lean 4's `rintro pat ≡ intro <fresh> ; rcases <fresh>
/// with pat`, applied left-to-right for each pattern. Each pattern first `intro`s
/// a fresh anonymous binder via the kernel-checked [`super::intro`], then —
/// crucially — re-resolves that binder BY NAME in the (now-mutated) current goal
/// and destructures it via the SAME kernel-checked `cases`/`casesOn` engine
/// (`destruct_named_hypothesis`) that backs `obtain`/`rcases`. Re-resolving by
/// name after each `intro` is what avoids the stale/dangling-FVar reference
/// (`UnknownFVar`) that the previous term-elaboration path produced: the FVar id
/// captured before `intro`/`cases` mutated the local context is never reused.
///
/// SOUNDNESS: the goal is only ever transformed via `intro` (kernel-checked
/// `close_goal`) and `destruct_named_hypothesis` (kernel-checked `cases`); no raw
/// FVars are pushed and no new trust surface is introduced. A pattern that does
/// not match the introduced hypothesis's structure (e.g. too many components, or
/// a tuple on an atomic hypothesis) surfaces as a `TacticError`, never a panic or
/// a silent over-accept, and the assembled proof term is rechecked by `add_decl`.
fn compound_rintro() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rintro".into(),
        handler: Arc::new(|_eval, ps, tac| {
            let SurfaceTactic::RIntro { patterns, .. } = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rintro".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };

            for pattern in patterns {
                let pattern = pattern.trim();

                // A bare-name (or wildcard) pattern is a plain `intro` under the
                // chosen name; routing it through the `intro` + destructure path
                // would needlessly re-resolve, so handle it directly. A `_`
                // pattern introduces a fresh anonymous binder.
                if pattern == "_" {
                    let fresh = format!("_rintro{}", ps.next_fvar);
                    super::intro(ps, &fresh)?;
                    continue;
                }
                // A pattern that destructs — an anonymous constructor `⟨...⟩`/`<...>`
                // OR a top-level `|` alternation (`rintro (hp | hq)`, captured as
                // `hp | hq` after the parser strips the grouping parens) — must
                // route through the kernel-checked `intro` + `destruct_named_hypothesis`
                // engine. A bare identifier is a plain `intro`. `has_top_level_pipe`
                // detects the alternation without splitting a `|` nested inside
                // brackets (`⟨h | h'⟩`), which is part of the field, not a
                // top-level alternation.
                if !pattern.starts_with('\u{27E8}')
                    && !pattern.starts_with('<')
                    && !has_top_level_pipe(pattern)
                {
                    // Plain identifier: intro under that exact name. `intro` itself
                    // rejects a non-Pi goal with a `TacticError`.
                    super::intro(ps, pattern)?;
                    continue;
                }

                // Destructuring pattern `⟨...⟩` / `(hp | hq)`: intro a fresh binder, then
                // re-resolve it BY NAME in the current goal and destructure. The
                // fresh name is unlikely to collide with user hypotheses so the
                // subsequent destructure targets exactly this binder.
                let fresh = format!("_rintro{}", ps.next_fvar);
                super::intro(ps, &fresh)?;

                // Re-resolve the just-introduced binder's ACTUAL name from the
                // current goal (the last decl) rather than assuming `fresh`:
                // `intro` may collision-rename, and — more importantly — reading
                // the name back from the now-current goal guarantees we never feed
                // a stale FVar/name from before the `intro` mutation. This is the
                // by-name re-resolution that fixes the `UnknownFVar` bug.
                let introduced = ps
                    .current_goal()
                    .and_then(|g| g.local_ctx.last())
                    .map(|d| d.name.clone())
                    .ok_or_else(|| {
                        TacticError::HypothesisNotFound(
                            "rintro: introduced hypothesis vanished from goal".into(),
                        )
                    })?;
                super::destruct_named_hypothesis(ps, &introduced, pattern)?;
            }

            Ok(())
        }),
    }
}

/// True iff `pattern` contains a `|` alternation at bracket depth 0.
///
/// A `|` nested inside `⟨⟩`/`<>`/`()`/`[]` belongs to an enclosed sub-pattern
/// (e.g. the `q ∨ r` field in `⟨hp, hq | hr⟩`) and is NOT a top-level
/// alternation. Used by `rintro` dispatch to decide whether a pattern needs the
/// case-split engine. Mirrors the depth-0 scan in `RIntroPattern::parse`.
fn has_top_level_pipe(pattern: &str) -> bool {
    let mut depth: i32 = 0;
    for c in pattern.chars() {
        match c {
            '\u{27E8}' | '<' | '(' | '[' => depth += 1,
            '\u{27E9}' | '>' | ')' | ']' => depth -= 1,
            '|' if depth == 0 => return true,
            _ => {}
        }
    }
    false
}

/// Create a sub-ProofState for proving an intermediate lemma.
///
/// Inherits the environment, instances, and elab_locals from the parent state.
/// Shared by `have` (phase 3D elab) and `conv` (phase 3D conv) handlers.
/// REQUIRES: `target` is a well-formed goal type in `parent.env()`.
/// ENSURES: Returned state has exactly one goal with target `target`.
/// ENSURES: Returned state reuses the parent's environment, instances, and elaborator locals.
pub(crate) fn create_sub_proof_state(parent: &ProofState, target: Expr) -> ProofState {
    parent.clone_with_fresh_goal_target(target)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::registry::{ElaboratedRefine, TacticEval};
    use crate::unify::MetaState;
    use crate::ElabError;
    use clean_kernel::Environment;
    use clean_parser::{Span, SurfaceExpr};

    struct StubEval {
        elaborate_result: Expr,
        infer_type_result: Result<Expr, TacticError>,
        meta_state: MetaState,
        elaborate_calls: usize,
        infer_type_calls: usize,
    }

    impl TacticEval for StubEval {
        fn eval(&mut self, _ps: &mut ProofState, _tac: &SurfaceTactic) -> Result<(), TacticError> {
            unreachable!("phase3d elab unit tests do not evaluate nested tactics")
        }

        fn eval_seq(
            &mut self,
            _ps: &mut ProofState,
            _tacs: &[SurfaceTactic],
        ) -> Result<(), TacticError> {
            unreachable!("phase3d elab unit tests do not evaluate tactic sequences")
        }

        fn elaborate(&mut self, _expr: &SurfaceExpr) -> Result<Expr, TacticError> {
            self.elaborate_calls += 1;
            Ok(self.elaborate_result.clone())
        }

        fn infer_type(&mut self, _expr: &Expr) -> Result<Expr, TacticError> {
            self.infer_type_calls += 1;
            self.infer_type_result.clone()
        }

        fn elaborate_refine(
            &mut self,
            _ps: &ProofState,
            _expr: &SurfaceExpr,
        ) -> Result<ElaboratedRefine, TacticError> {
            unreachable!("phase3d elab unit tests do not elaborate refine terms")
        }

        fn metas(&self) -> &MetaState {
            &self.meta_state
        }
    }

    fn stub_eval() -> StubEval {
        StubEval {
            elaborate_result: Expr::prop(),
            infer_type_result: Ok(Expr::prop()),
            meta_state: MetaState::new(),
            elaborate_calls: 0,
            infer_type_calls: 0,
        }
    }

    #[test]
    fn test_compound_let_propagates_infer_type_failure() {
        let mut eval = StubEval {
            infer_type_result: Err(TacticError::UpstreamElabError {
                source: Box::new(ElabError::CannotInfer),
            }),
            ..stub_eval()
        };
        let mut state = ProofState::new(Environment::new(), Expr::prop());
        let handler = compound_let();
        let tactic = SurfaceTactic::Let(
            Span::dummy(),
            "x".into(),
            None,
            Box::new(SurfaceExpr::Ident(Span::dummy(), "value".into())),
        );

        let result = (handler.handler)(&mut eval, &mut state, &tactic);

        assert!(
            matches!(result, Err(TacticError::UpstreamElabError { ref source })
                if matches!(source.as_ref(), ElabError::CannotInfer)),
            "expected infer_type failure to propagate without a fabricated Type, got: {result:?}"
        );
        assert_eq!(
            eval.elaborate_calls, 1,
            "value should still elaborate first"
        );
        assert_eq!(
            eval.infer_type_calls, 1,
            "compound_let should ask infer_type exactly once when no annotation is present"
        );
        assert_eq!(
            state.goals().len(),
            1,
            "failing before have_ should leave the original goal intact"
        );
    }
}
