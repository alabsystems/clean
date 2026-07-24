// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursive intro patterns (rintro) tactic.

use clean_kernel::{Expr, ExprKind, FVarId};

use crate::unify::MetaState;

use super::super::proof_manipulation::cases;
use super::super::{intro, rfl, subst, Goal, ProofState, TacticError, TacticResult};
use super::util::get_app_head;

/// Whether `expr` contains a leaked *unassigned* metavariable, represented as an
/// `FVar` whose id carries `MetaState`'s high-bit tag (`MetaState::to_fvar` /
/// `from_fvar`, i.e. `2^63 + n`).
///
/// After `MetaState::instantiate`, an `FVar` that still decodes to a `MetaId` is
/// an elaborator metavariable that was never assigned — for a destructure
/// scrutinee this is the untyped-binder case (`∃ a, ∃ b, a = b`) whose binder
/// type `?α` could not be inferred. Destructuring such a hypothesis would embed
/// the sentinel meta-FVar in the `casesOn` proof term and leak it to the kernel,
/// so the caller rejects it. Mirrors `simp`'s `contains_unassigned_meta`.
///
/// `pub(crate)` so the `obtain` surface handler can reject the same
/// unsolved-binder-type scrutinee *before* the `have_`-copy step commits the
/// meta-typed `let` into the outer proof term (the earliest leak point).
pub(crate) fn contains_unassigned_meta(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(f, a) => contains_unassigned_meta(f) || contains_unassigned_meta(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_unassigned_meta(ty) || contains_unassigned_meta(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_unassigned_meta(ty)
                || contains_unassigned_meta(val)
                || contains_unassigned_meta(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            contains_unassigned_meta(inner)
        }
        _ => false,
    }
}

/// Pattern for rintro tactic
#[derive(Debug, Clone)]
pub enum RIntroPattern {
    /// Simple name: `x`
    Name(String),
    /// Wildcard: `_`
    Wildcard,
    /// Anonymous: `<...>` for And/Exists
    Anonymous(Vec<RIntroPattern>),
    /// Or pattern: `h1 | h2`
    Or(Vec<RIntroPattern>),
    /// Recursive intro: `<a, b, c>`
    Tuple(Vec<RIntroPattern>),
    /// Equality rewrite: `rfl`
    Rfl,
}

impl RIntroPattern {
    /// Parse a pattern string into RIntroPattern
    ///
    /// # Contract
    ///
    /// REQUIRES: `s` is a non-empty, trimmed pattern string
    /// ENSURES: On Ok, returns a parsed `RIntroPattern` matching the surface syntax
    /// ENSURES: On Err(MissingArgument), `s` was empty or whitespace-only
    pub fn parse(s: &str) -> Result<Self, TacticError> {
        let s = s.trim();

        if s.is_empty() {
            return Err(TacticError::MissingArgument {
                tactic: "rintro".into(),
                expected: "non-empty pattern".into(),
            });
        }

        if s == "_" {
            return Ok(RIntroPattern::Wildcard);
        }

        if s == "rfl" {
            return Ok(RIntroPattern::Rfl);
        }

        // Or-alternation `|` binds looser than the `⟨⟩`/`<>` grouping, so it
        // must be detected FIRST and split only at bracket depth 0. Lean 4
        // parses `rintro ⟨a, b⟩ | ⟨c, d⟩` as an alternation of two
        // anonymous-constructor patterns, not a single tuple. (Bug fix:
        // previously the tuple branch fired first whenever the whole string
        // happened to start with `⟨`/`<` and end with `⟩`/`>`, mis-parsing
        // top-level alternations, and the naive `s.split('|')` also split
        // inside nested brackets.)
        let or_parts = split_top_level_or(s);
        if or_parts.len() > 1 {
            let patterns: Result<Vec<_>, _> = or_parts
                .iter()
                .map(|p| RIntroPattern::parse(p.trim()))
                .collect();
            return Ok(RIntroPattern::Or(patterns?));
        }

        // Tuple pattern `⟨a, b, c⟩` or `<a, b, c>`: only when a single bracket
        // group spans the entire string. `strip_tuple_brackets` is char-aware
        // so Unicode brackets (3 bytes each) do not panic on slicing.
        if let Some(inner) = strip_tuple_brackets(s) {
            let parts = split_pattern_args(inner);
            let patterns: Result<Vec<_>, _> = parts
                .iter()
                .map(|p| RIntroPattern::parse(p.trim()))
                .collect();
            return Ok(RIntroPattern::Tuple(patterns?));
        }

        // Simple name
        Ok(RIntroPattern::Name(s.to_string()))
    }
}

/// Split a pattern string at top-level (bracket depth 0) `|` alternation marks.
///
/// # Contract
///
/// REQUIRES: `s` is a trimmed pattern string
/// ENSURES: Returns the substrings between depth-0 `|` markers, in order
/// ENSURES: A `|` nested inside `⟨⟩`/`<>`/`()`/`[]` does NOT split (it belongs
///          to the enclosed sub-pattern)
/// ENSURES: When `s` has no top-level `|`, the result is a single element (`s`)
fn split_top_level_or(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0usize;

    for (idx, c) in s.char_indices() {
        match c {
            '\u{27E8}' | '<' | '(' | '[' => depth += 1,
            '\u{27E9}' | '>' | ')' | ']' => depth -= 1,
            '|' if depth == 0 => {
                result.push(&s[start..idx]);
                start = idx + c.len_utf8();
            }
            _ => {}
        }
    }
    result.push(&s[start..]);
    result
}

/// If `s` is a single balanced bracket group spanning the whole string, return
/// the inner contents; otherwise `None`.
///
/// # Contract
///
/// REQUIRES: `s` is a trimmed pattern string
/// ENSURES: On `Some(inner)`, `s` opened with `⟨`/`<` at index 0 and the
///          matching close bracket was the final char, with balanced nesting
///          throughout (`inner` is the slice strictly between them)
/// ENSURES: On `None`, `s` is not a single whole-string bracket group (e.g.
///          `<a> <b>` or a bare name) and must be handled some other way
/// ENSURES: Char-aware: never slices through a multi-byte Unicode bracket
fn strip_tuple_brackets(s: &str) -> Option<&str> {
    let first = s.chars().next()?;
    let close = match first {
        '\u{27E8}' => '\u{27E9}',
        '<' => '>',
        _ => return None,
    };

    let mut depth: i32 = 0;
    let mut closes_at_end = false;
    for (idx, c) in s.char_indices() {
        match c {
            '\u{27E8}' | '<' | '(' | '[' => depth += 1,
            '\u{27E9}' | '>' | ')' | ']' => {
                depth -= 1;
                if depth == 0 {
                    // The opening bracket only spans the whole string if its
                    // match is the final char (and is the right close kind).
                    let at_end = idx + c.len_utf8() == s.len();
                    if !at_end {
                        // Bracket group closes before the end (e.g. `<a> <b>`):
                        // this is not a single whole-string tuple.
                        return None;
                    }
                    closes_at_end = c == close;
                }
            }
            _ => {}
        }
    }

    if closes_at_end {
        // Strip the leading open bracket and trailing close bracket by their
        // char widths (Unicode-safe).
        Some(&s[first.len_utf8()..s.len() - close.len_utf8()])
    } else {
        None
    }
}

/// Split pattern arguments respecting nested brackets
///
/// # Contract
///
/// REQUIRES: `s` is a string of comma-separated pattern arguments (may contain nested brackets)
/// ENSURES: Returns a `Vec` of trimmed argument strings, split at top-level commas only
/// ENSURES: Nested brackets (`<>`, `()`, `[]`, `⟨⟩`) are respected — commas inside them do not split
pub(crate) fn split_pattern_args(s: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for c in s.chars() {
        match c {
            '\u{27E8}' | '<' | '(' | '[' => {
                depth += 1;
                current.push(c);
            }
            '\u{27E9}' | '>' | ')' | ']' => {
                depth -= 1;
                current.push(c);
            }
            ',' if depth == 0 => {
                result.push(current.trim().to_string());
                current = String::new();
            }
            _ => current.push(c),
        }
    }

    if !current.is_empty() {
        result.push(current.trim().to_string());
    }

    result
}

/// rintro tactic: recursive intro with patterns
///
/// The `rintro` tactic extends `intro` with pattern matching on the introduced
/// hypotheses. It can destruct conjunctions, existentials, and handle
/// alternatives.
///
/// # Patterns
/// - `x` - Simple name
/// - `_` - Wildcard (anonymous hypothesis)
/// - `<a, b>` - Destruct And/Exists/Sigma
/// - `h1 | h2` - Case split on Or
/// - `rfl` - Rewrite with reflexivity
///
/// # Example
/// ```text
/// -- Goal: (P /\ Q) -> R
/// rintro <hp, hq>
/// -- Now have: hp : P, hq : Q, Goal: R
///
/// -- Goal: (exists x, P x) -> Q
/// rintro <x, hx>
/// -- Now have: x : alpha, hx : P x, Goal: Q
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty (the goal target is a Pi/forall or has destructible head)
/// REQUIRES: Each element of `patterns` is a valid rintro pattern string
/// ENSURES: On Ok, one intro step per pattern has been applied, possibly with destructuring
/// ENSURES: On Err(MissingArgument), a pattern string was empty
/// ENSURES: On Err(NoGoals), the goal queue was empty before intro
pub fn rintro(state: &mut ProofState, patterns: Vec<String>) -> TacticResult {
    let parsed_patterns: Result<Vec<_>, _> =
        patterns.iter().map(|s| RIntroPattern::parse(s)).collect();
    rintro_patterns(state, parsed_patterns?)
}

/// rintro with parsed patterns
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, each pattern in `patterns` has been applied sequentially via `apply_rintro_pattern`
/// ENSURES: On Err, patterns applied before the failing one remain in effect (partial mutation)
pub fn rintro_patterns(state: &mut ProofState, patterns: Vec<RIntroPattern>) -> TacticResult {
    for pattern in patterns {
        apply_rintro_pattern(state, pattern)?;
    }
    Ok(())
}

/// Destructure an existing named hypothesis according to a pattern string.
///
/// This is the engine behind `obtain pat := e`: the caller first introduces the
/// elaborated scrutinee `e` as a hypothesis `hyp_name` (via the kernel-checked
/// `have_`), then this function destructs it per `pattern`. Reuses the SAME
/// kernel-checked `cases`/`casesOn` path as `rintro`/`rcases` — no raw FVars are
/// pushed; nested patterns (`⟨⟨a, b⟩, c⟩`) compose `casesOn` eliminators.
///
/// A single-name pattern renames the hypothesis; a `⟨...⟩` tuple destructs it; a
/// top-level `rfl` pattern on an equality hypothesis substitutes it away via the
/// kernel-checked `subst` tactic (the `rcases h with rfl` / `obtain rfl := h`
/// idiom). A pattern/type mismatch (e.g. destructuring a non-inductive
/// hypothesis with a tuple of more than one field, or a `rfl` pattern on a
/// non-equality hypothesis) surfaces as a [`TacticError`], never a panic.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the current goal's local context
/// REQUIRES: `pattern` is a valid rintro pattern string (`⟨a, b⟩`, a name, `_`,
///           `rfl`)
/// ENSURES: On Ok, the hypothesis is renamed (Name pattern), destructured into
///          kernel-bound fields (Tuple/Anonymous pattern, recursing on nesting),
///          or — for a `rfl` pattern on an equality — substituted away via a
///          kernel-checked `Eq.ndrec` proof (`subst`)
/// ENSURES: On Err, returns a `TacticError` describing the pattern/type or
///          parse failure (including a `rfl` pattern on a non-equality or
///          non-substitutable hypothesis); the goal is only ever transformed via
///          the kernel-checked `cases`/`subst` path
pub fn destruct_named_hypothesis(
    state: &mut ProofState,
    hyp_name: &str,
    pattern: &str,
) -> TacticResult {
    match RIntroPattern::parse(pattern)? {
        RIntroPattern::Name(name) => rename_hypothesis(state, hyp_name, &name),
        RIntroPattern::Wildcard => Ok(()),
        // A TOP-LEVEL `rfl` pattern (`rcases h with rfl` / `obtain rfl := h`)
        // applied to an already-bound equality hypothesis IS `subst h`: the
        // hypothesis `h : a = b` is substituted away, rewriting one side of the
        // equation throughout the goal and context. Route to the same
        // kernel-checked `subst` tactic that the `subst` tactic, the in-a-tuple
        // `⟨rfl, _⟩` field pattern (`substitute_field`), and `cases`-on-`Eq` all
        // use — reusing subst's `Eq.ndrec` proof construction and FVar-id↔binder
        // discipline rather than hand-rolling any substitution. `subst` itself
        // FAILS CLOSED: if `h` is not an equality (e.g. `h : p ∧ q`), or neither
        // side is a substitutable local variable (e.g. `h : 5 = 3`), its
        // `TacticError` is surfaced verbatim — never a panic and never a silent
        // over-accept. (A `rfl` field WITHIN a tuple is handled separately by
        // `substitute_field`; a top-level `rfl` in the `rintro` intro-and-close
        // context is a distinct construct handled in `apply_rintro_pattern`.)
        RIntroPattern::Rfl => subst(state, hyp_name),
        RIntroPattern::Tuple(sub) | RIntroPattern::Anonymous(sub) => {
            destruct_hypothesis(state, hyp_name, &sub)
        }
        RIntroPattern::Or(sub) => {
            // Top-level alternation in `obtain`/`rcases` (e.g. `rcases h with hp |
            // hq` on an `Or`): case-split the hypothesis into one goal per
            // constructor and apply each alternative's sub-pattern to that
            // branch's field. This is the canonical disjunction-splitting idiom.
            split_or_hypothesis(state, hyp_name, &sub)
        }
    }
}

/// Case-split a hypothesis on its inductive constructors (the `|` alternation),
/// applying one sub-pattern per constructor branch.
///
/// This backs the `pat₁ | pat₂` rcases/obtain/rintro pattern. `pat₁ | pat₂`
/// means: `hyp_name` is an inductive with ≥2 constructors (canonically `Or`:
/// `Or.inl`/`Or.inr`), so case-split it — produce one goal per branch, applying
/// `pat₁` to the first constructor's field(s) and `pat₂` to the second.
///
/// Reuses the SAME kernel-checked `cases`/`casesOn` engine as `cases`/`rcases`:
/// `cases` removes the front goal, builds a real `T.casesOn motive (λ field =>
/// ?branchᵢ) h` term, and pushes one branch goal per constructor to the back of
/// the goal queue with the constructor's field FVars genuinely bound. We then
/// focus each branch goal in turn and apply its alternative's sub-pattern to the
/// freshly bound field via the same `apply_subpattern_to_field` path used for
/// `⟨...⟩` fields — so a branch's `Name` renames the disjunct, a `⟨...⟩` further
/// destructs it, and a nested `|` recurses. No raw FVars are pushed; the
/// assembled proof term is kernel-rechecked by `add_decl`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty and `hyp_name` is in the current goal's
///           local context
/// ENSURES: On Ok, the goal is replaced by one goal per constructor of
///           `hyp_name`'s inductive type, each carrying the branch field named /
///           recursed per the corresponding `alternatives` entry
/// ENSURES: On Err(InvalidTarget), the number of `alternatives` does not match
///           the constructor count, or `hyp_name`'s type is not a splittable
///           inductive — surfaced as a `TacticError`, never a panic or
///           silent over-accept
fn split_or_hypothesis(
    state: &mut ProofState,
    hyp_name: &str,
    alternatives: &[RIntroPattern],
) -> TacticResult {
    // Determine the constructor count up front so an `|` pattern on a
    // non-splittable (or mis-sized) hypothesis ERRORS before mutating the goal,
    // never silently over-accepts. The type is WHNF-reduced first: a recursively
    // destructured field (a branch of a nested `⟨_, _ | _⟩`) can arrive as a
    // not-yet-reduced application.
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let hyp_ty = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .map(|d| d.ty.clone())
        .ok_or_else(|| {
            TacticError::HypothesisNotFound(
                "rcases: could not find hypothesis to case-split".into(),
            )
        })?;
    // Instantiate metavariables before WHNF: a field type produced by a previous
    // `casesOn` motive instantiation can still carry unsolved metas, which `whnf`
    // alone does not reduce. `cases` itself instantiates the scrutinee type the
    // same way, so mirror it here to classify the head reliably.
    let hyp_ty = state.metas.instantiate(&hyp_ty);
    let hyp_ty = state.whnf(goal, &hyp_ty);
    let head = get_app_head(&hyp_ty);
    let num_ctors = match head.kind() {
        ExprKind::Const(name, _) => state
            .env
            .get_inductive(name)
            .map(|i| i.constructor_names.len()),
        _ => None,
    };
    let Some(num_ctors) = num_ctors else {
        return Err(TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: format!(
                "the `|` alternation pattern requires hypothesis '{hyp_name}' to be an \
                 inductive type (e.g. `Or`), but its type is not a case-splittable inductive"
            ),
        });
    };
    // A `|` split needs one alternative per constructor. There are two valid
    // shapes:
    //   * exactly one alternative per constructor (the common 2-way `Or`); or
    //   * MORE alternatives than constructors, which Lean reads right-nested:
    //     `rcases h with hp | hq | hr` on `p ∨ q ∨ r` (= `Or p (Or q r)`) maps
    //     `hp` to `Or.inl`'s field and groups the trailing `hq | hr` into a
    //     nested `Or` applied to `Or.inr`'s field (which is itself an `Or`). This
    //     mirrors the tuple-flattening rule in `destruct_hypothesis`.
    // Too FEW alternatives, or a flat over-long pattern whose grouped tail lands
    // on a non-splittable field, ERRORS downstream (no over-accept).
    if alternatives.len() < num_ctors {
        return Err(TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: format!(
                "the `|` alternation has {} branch(es) but hypothesis '{hyp_name}' has {} \
                 constructor(s); supply exactly one pattern per constructor",
                alternatives.len(),
                num_ctors
            ),
        });
    }

    // Group an over-long flat alternation into [p_0, .., p_{M-2}, Or(p_{M-1}..)]
    // so the trailing patterns recurse on the last constructor's field. When the
    // counts already match, use the alternatives as-is.
    let grouped: Vec<RIntroPattern>;
    let effective: &[RIntroPattern] = if alternatives.len() > num_ctors && num_ctors >= 1 {
        grouped = alternatives[..num_ctors - 1]
            .iter()
            .cloned()
            .chain(std::iter::once(RIntroPattern::Or(
                alternatives[num_ctors - 1..].to_vec(),
            )))
            .collect();
        &grouped
    } else {
        alternatives
    };

    // Snapshot the goal-queue length so we can locate the branch goals `cases`
    // appends at the back: `cases` pops the front goal and pushes `num_ctors`
    // branch goals, so they occupy `[goals_before - 1 .. goals_after)`.
    let goals_before = state.goals().len();
    cases(state, hyp_name)?;
    let goals_after = state.goals().len();
    // Net new goals = goals_after - (goals_before - 1).
    let num_new = goals_after.saturating_sub(goals_before.saturating_sub(1));
    let new_goal_start = goals_after.saturating_sub(num_new);

    // First pass: apply the SIMPLE (in-place) sub-patterns to each branch's field
    // by direct index, exactly like `eval_rcases_inner`. `Name` renames the field,
    // `Wildcard`/`Rfl` are handled in place, and any sub-pattern needing a further
    // case-split (`Tuple`/`Anonymous`/`Or`) is DEFERRED to a second pass that
    // focuses the branch goal — mirroring `apply_field_patterns`, which never
    // reorders goals during the in-place rename phase. This avoids disturbing the
    // goal queue (and the assembled `casesOn` proof term's branch metas) while
    // names are assigned. The deferred targets are recorded by the field's
    // generated name so they can be re-resolved after focusing. (A NAME, not the
    // FVar id: sibling `Or` branches reset `next_fvar` to the same base in
    // `cases`, so `Or.inl`'s and `Or.inr`'s field FVars share an id — only their
    // auto-generated names, `inl_0` vs `inr_0`, distinguish the branches.)
    let mut deferred: Vec<(String, RIntroPattern)> = Vec::new();
    for (alt_idx, branch_pos) in (new_goal_start..goals_after).enumerate() {
        if branch_pos >= state.goals().len() {
            break;
        }
        let Some(pattern) = effective.get(alt_idx) else {
            break;
        };
        // The constructor field (the disjunct hypothesis) is the LAST decl that
        // `cases` appended to this branch goal's context.
        let Some(field_decl) = state.goals()[branch_pos].local_ctx.last() else {
            return Err(TacticError::HypothesisNotFound(
                "rcases: case-split branch produced no field hypothesis".into(),
            ));
        };
        let field_idx = state.goals()[branch_pos].local_ctx.len() - 1;
        let field_name = field_decl.name.clone();

        match pattern {
            RIntroPattern::Wildcard => {
                // Keep the auto-generated field name; nothing to do.
            }
            RIntroPattern::Name(new_name) => {
                state.goals[branch_pos].local_ctx[field_idx].name = new_name.clone();
            }
            // Anything that further destructs the field (nested tuple, nested
            // alternation, or a `rfl` substitution) is deferred so it can run with
            // the branch goal focused as the front goal.
            other => {
                deferred.push((field_name, other.clone()));
            }
        }
    }

    // Second pass: run the deferred destructuring sub-patterns. Each branch's
    // field is located by its (unique) generated name, EXTRACTED into an ISOLATED
    // single-goal sub-state, destructured there, and merged back in place.
    //
    // The isolation is essential for correctness, not just tidiness. The field
    // engine (`destruct_hypothesis` → `cases`) reads the FRONT goal to locate the
    // fields it just introduced, and `cases` pushes the new branch to the BACK of
    // the queue while popping the front. If the destructure ran against the shared
    // goal queue while a SIBLING alternation branch was still queued behind the
    // one being destructured (e.g. the untouched `Or.inr` `hr` branch while the
    // `Or.inl` `⟨hp, hq⟩` arm is split), that "front goal after cases" assumption
    // breaks: after `cases` pops the `inl` goal and pushes its `And` branch to the
    // back, the sibling `inr` goal surfaces as the new front, and the field engine
    // mis-reads ITS context — applying the tuple sub-pattern to the wrong disjunct
    // (`hr : r`) and failing (bug #14: `rcases h with ⟨hp, hq⟩ | hr`). Extracting
    // exactly the target branch into a one-goal sub-state restores the invariant.
    //
    // Each isolated branch's binder FVars must be allocated from a SHARED base so
    // the FVar-id ↔ binder-depth correspondence `close_fvars` relies on holds
    // across sibling branches (the same discipline `all_goals`/`<;>` and
    // `apply_subpattern_to_field_all_goals` use). Reset `next_fvar` to that base
    // before running each branch; restore the running max afterward so later
    // allocations never collide with any branch's fields. Without this, the second
    // `⟨…⟩` arm's fields start from a higher id than the first, breaking the
    // correspondence and yielding a dangling proof term (`ProofNotProduced`) — the
    // `⟨hp, hq⟩ | ⟨hr, hs⟩` case.
    let branch_fvar_base = state.next_fvar;
    let mut branch_fvar_max = branch_fvar_base;
    for (field_name, pattern) in deferred {
        let branch_pos = state
            .goals()
            .iter()
            .position(|g| g.local_ctx.iter().any(|d| d.name == field_name))
            .ok_or_else(|| {
                TacticError::HypothesisNotFound(
                    "rcases: deferred alternation branch goal not found".into(),
                )
            })?;
        let field_fvar = state.goals()[branch_pos]
            .local_ctx
            .iter()
            .find(|d| d.name == field_name)
            .map(|d| d.fvar)
            .ok_or_else(|| {
                TacticError::HypothesisNotFound(
                    "rcases: deferred alternation field vanished before focus".into(),
                )
            })?;
        // Pull the single target branch out of the queue and run the sub-pattern
        // on it in isolation, so the field engine's `cases` never observes a
        // sibling branch as the front goal.
        let branch = state.goals.remove(branch_pos).ok_or(TacticError::NoGoals)?;
        state.next_fvar = branch_fvar_base;
        let mut focused = state.clone_with_goal(branch);
        apply_subpattern_to_field(&mut focused, field_fvar, &pattern)?;
        branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
        state.merge_meta_state(&focused);
        // Re-insert the (possibly multiplied) result goals at the branch's
        // original position, preserving source order for downstream `·` bullets.
        for (offset, g) in focused.goals.into_iter().enumerate() {
            state.goals.insert(branch_pos + offset, g);
        }
    }
    state.next_fvar = branch_fvar_max;

    Ok(())
}

/// Apply a single rintro pattern
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok(Name), one hypothesis is introduced with the given name
/// ENSURES: On Ok(Wildcard), one hypothesis is introduced with a generated anonymous name
/// ENSURES: On Ok(Tuple), the introduced hypothesis is destructured (And/Exists/Sigma) or renamed
/// ENSURES: On Ok(Rfl), the introduced hypothesis is used to attempt reflexivity closure
/// ENSURES: On Ok(Or), the introduced hypothesis is renamed to the first alternative name
fn apply_rintro_pattern(state: &mut ProofState, pattern: RIntroPattern) -> TacticResult {
    match pattern {
        RIntroPattern::Name(name) => intro(state, &name),
        RIntroPattern::Wildcard => {
            // Generate a fresh anonymous name
            let name = format!("_h{}", state.next_fvar);
            intro(state, &name)
        }
        RIntroPattern::Tuple(sub_patterns) => {
            // First intro to get the hypothesis
            let temp_name = format!("_temp{}", state.next_fvar);
            intro(state, &temp_name)?;

            // Now destruct the just-introduced hypothesis by name.
            destruct_hypothesis(state, &temp_name, &sub_patterns)
        }
        RIntroPattern::Or(sub_patterns) => {
            // `rintro hp | hq` desugars to `intro h; rcases h with hp | hq`:
            // intro the hypothesis, then case-split it on its constructors,
            // applying each alternative's sub-pattern to that branch's field.
            let temp_name = format!("_temp{}", state.next_fvar);
            intro(state, &temp_name)?;
            // Re-resolve the actual binder name from the current goal (intro may
            // collision-rename) before feeding it to the case-split engine.
            let introduced = state
                .current_goal()
                .and_then(|g| g.local_ctx.last())
                .map(|d| d.name.clone())
                .unwrap_or(temp_name);
            split_or_hypothesis(state, &introduced, &sub_patterns)
        }
        RIntroPattern::Rfl => {
            // Intro and then try to apply reflexivity
            let temp_name = format!("_temp{}", state.next_fvar);
            intro(state, &temp_name)?;
            // Try to close goal with rfl
            rfl(state).or(Ok(()))
        }
        RIntroPattern::Anonymous(sub_patterns) => {
            // Same as Tuple
            apply_rintro_pattern(state, RIntroPattern::Tuple(sub_patterns))
        }
    }
}

/// Destruct a hypothesis by delegating to the sound `cases` engine.
///
/// This routes And/Exists/Sigma (and any one-constructor inductive)
/// single-level destructuring through the SAME `T.casesOn` builder that the
/// `cases`/`rcases` tactics use. Concretely, `cases` assigns the current goal's
/// metavariable to `T.casesOn motive (λ fields => ?continuation) h` with the
/// field FVars abstracted into the branch lambda — so the introduced fields are
/// genuinely bound by a real lambda and the assembled proof term is accepted by
/// the kernel. (Previously this pushed raw, unbound FVars into `local_ctx`,
/// producing a dangling-FVar proof term that the kernel rejected and that
/// panicked the `close_fvars` debug assertion in test builds.)
///
/// After `cases` runs, the new branch goal (for a single-constructor type there
/// is exactly one) is at the front of the goal queue and its `local_ctx` holds
/// the freshly bound field FVars as its final `num_fields` declarations. We then
/// apply each sub-pattern to the corresponding field: `Name` renames it,
/// `Wildcard` leaves the generated name, and nested `Tuple`/`Anonymous`
/// recursively destructs it (composing the `casesOn` eliminators).
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the current goal whose type has an
///           inductive head with a single constructor (And/Exists/Sigma/etc.)
/// ENSURES: On Ok, the goal's metavariable is closed with a kernel-checked
///          `casesOn` eliminator term and the continuation goal carries the
///          destructured fields, named/recursed per `sub_patterns`
/// ENSURES: On Err(GoalMismatch/EnvironmentMissing), the hypothesis type was not
///          a destructible one-constructor inductive (mirrors `cases`)
fn destruct_hypothesis(
    state: &mut ProofState,
    hyp_name: &str,
    sub_patterns: &[RIntroPattern],
) -> TacticResult {
    // Snapshot the hypothesis type head BEFORE running cases so we can decide
    // whether to delegate. If it is not a destructible inductive, fall back to
    // renaming with the first name pattern (preserving prior lenient behavior).
    //
    // The type is WHNF-reduced first: a recursively-destructed field's type
    // (the right field of `a ∧ (b ∧ c)`, say) can arrive as a not-yet-reduced
    // application coming out of the `casesOn` motive instantiation, so a raw
    // structural head peek would mis-classify the nested `And` as atomic and
    // wrongly bail (the cause of explicit-nested `⟨a, ⟨b, c⟩⟩` failing through
    // the full surface `∧` path even though it works on bare `And` constants).
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let hyp_ty = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .map(|d| d.ty.clone())
        .ok_or_else(|| {
            TacticError::HypothesisNotFound("rintro: could not find introduced hypothesis".into())
        })?;
    let hyp_ty = state.whnf(goal, &hyp_ty);
    let head = get_app_head(&hyp_ty);
    let destructible = matches!(head.kind(), ExprKind::Const(name, _) if {
        // Match by the short (final) name component so namespaced or
        // `_root_`-qualified forms of the connective still classify correctly.
        let n = name.last_component().unwrap_or_default();
        // Delegate for these one-constructor inductives. (Or/disjunctions have
        // multiple constructors and are handled by the Or pattern, not here.)
        n == "And" || n == "Exists" || n == "Sigma" || n == "Prod" || n == "PProd"
            // …and for ANY native structure — a user `structure`, or `Subtype`
            // etc. — recognized by its field-name table. Such a type is a
            // single-constructor inductive that `cases` already destructures via
            // its own `casesOn` (a named `| mk … =>` pattern works), so
            // `⟨a, b, c⟩` must too; the field-mapping below binds one sub-pattern
            // per field (or flattens an over-long pattern into the last field).
            // Before this, `rcases`/`obtain`/`rintro ⟨a, b, c⟩` on a user
            // structure wrongly reported it "not destructurable". `And`/`Exists`
            // have no field table, so they keep the explicit name check; `Eq` and
            // other non-structure specials remain non-destructible as before.
            || state.env.get_structure_field_names(name).is_some()
    });

    if !destructible {
        // Not a destructible single-constructor inductive. A single sub-pattern
        // is still a valid (degenerate) destructure: a one-name `⟨x⟩` simply
        // renames the hypothesis, and a wildcard/`rfl`/`or` leaf is a no-op. But
        // asking to bind MORE than one field name to an atomic, non-destructible
        // hypothesis (e.g. `⟨a, b⟩` on `h : Atom`, or the grouped trailing
        // patterns of an over-long flat tuple landing on an atomic last field)
        // has no sound `casesOn` fields to bind to — it must surface as a
        // `TacticError`, never a silent success (which would let a wrong /
        // over-long pattern close the goal with a false `proved`).
        return match sub_patterns {
            [] => Ok(()),
            [RIntroPattern::Name(new_name)] => rename_hypothesis(state, hyp_name, new_name),
            [RIntroPattern::Wildcard | RIntroPattern::Rfl | RIntroPattern::Or(_)] => Ok(()),
            _ => Err(TacticError::InvalidTarget {
                tactic: "rcases".into(),
                detail: format!(
                    "pattern has {} components but hypothesis '{hyp_name}' is not destructurable \
                     (its type is not a single-constructor inductive)",
                    sub_patterns.len()
                ),
            }),
        };
    }

    // FAIL CLOSED on an unsolved binder-type metavariable in the scrutinee.
    //
    // A hypothesis whose type still contains an *unassigned* elaborator
    // metavariable — e.g. the untyped `∃ a, ∃ b, a = b`, where the binder type
    // `?α` is never pinned because `a = b` supplies no concrete type (Lean 4
    // rejects this same header: "don't know how to synthesize implicit argument
    // `α`") — cannot be soundly destructured. `cases` would build a
    // `T.casesOn motive …` term that embeds the meta-FVar (`MetaState::to_fvar`,
    // id `2^63 + n`); because that id is far above `next_fvar`, `close_fvars`
    // leaves it untouched and `instantiate` cannot resolve it (it is unassigned),
    // so the raw sentinel FVar survives into the assembled proof term and the
    // kernel re-check reports a confusing `UnknownFVar(FVarId(9223372…))`.
    //
    // Detect the residual meta up front (after `instantiate`, which resolves any
    // metas that WERE solved) and surface a clear `TacticError` instead — never a
    // sentinel leak into the kernel, and never a silent over-accept. This mirrors
    // the `contains_unassigned_meta` reject used by `simp`/`rw?`. Fully-resolved
    // hypothesis types (the common typed case, `∃ a : Nat, …`) carry no meta, so
    // this guard is a no-op for them.
    let hyp_ty_inst = state.metas.instantiate(&hyp_ty);
    if contains_unassigned_meta(&hyp_ty_inst) {
        return Err(TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: format!(
                "cannot destructure hypothesis '{hyp_name}': its type still contains an \
                 unresolved metavariable (an implicit argument such as the binder type could \
                 not be inferred). Add an explicit type annotation to the binder(s) \
                 (e.g. `∃ a : T, …`)"
            ),
        });
    }

    // Count fields currently in context so we can locate the new field decls
    // after cases() pushes them. cases() removes the scrutinee hyp and appends
    // the constructor's field FVars (properly bound by the casesOn branch
    // lambda) to the new front goal's local_ctx.
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let ctx_len_before = goal.local_ctx.len();

    // Delegate to the sound cases engine. This builds and kernel-closes
    // `T.casesOn motive (λ fields => ?meta) h` via close_goal.
    cases(state, hyp_name)?;

    // The branch goal (single constructor ⇒ exactly one) is now at the front.
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    // Removing the scrutinee dropped one decl; the appended fields are the tail.
    // new_len = (ctx_len_before - 1) + num_fields ⇒ num_fields = new_len - (ctx_len_before - 1).
    let new_len = goal.local_ctx.len();
    let removed = ctx_len_before.saturating_sub(1);
    let num_fields = new_len.saturating_sub(removed);

    // Collect the field FVars in order (these align with the constructor's
    // field order: And ⇒ [left, right], Exists/Sigma ⇒ [witness, proof]).
    let field_fvars: Vec<FVarId> = goal
        .local_ctx
        .iter()
        .skip(removed)
        .take(num_fields)
        .map(|d| d.fvar)
        .collect();

    // Lean's `rcases` flattening rule: when there are MORE flat patterns than
    // the constructor has fields (N > M), the first M-1 patterns map to the
    // first M-1 fields and the REMAINING patterns (indices M-1..N) group into a
    // single `Tuple` applied recursively to the LAST field. So `⟨a, b, c⟩` on
    // `a ∧ (b ∧ c)` (And has 2 fields) becomes `⟨a, ⟨b, c⟩⟩`: `a` binds the
    // left field, `⟨b, c⟩` recursively destructs the right field. If that last
    // field is itself a one-constructor inductive the recursion succeeds; if it
    // is atomic (e.g. `⟨a, b, c⟩` on `p ∧ q` with `q : Prop`) the grouped tuple
    // of >1 patterns hits the non-destructible arm above and ERRORS — a wrong /
    // over-long pattern can never silently succeed.
    let grouped_last: Vec<RIntroPattern>;
    let effective: &[RIntroPattern] = if num_fields >= 1 && sub_patterns.len() > num_fields {
        // Build [p_0, .., p_{M-2}, Tuple(p_{M-1}, .., p_{N-1})].
        grouped_last = sub_patterns[..num_fields - 1]
            .iter()
            .cloned()
            .chain(std::iter::once(RIntroPattern::Tuple(
                sub_patterns[num_fields - 1..].to_vec(),
            )))
            .collect();
        &grouped_last
    } else {
        sub_patterns
    };

    // Apply each (possibly re-grouped) sub-pattern to the corresponding field in
    // TWO passes, so that a field whose pattern CASE-SPLITS the goal (`Or`, or a
    // nested `Tuple`/`Anonymous` that recurses into a further split) does not
    // strand LATER sibling fields in only one branch.
    //
    // The subtle bug this guards against: `cases` on an earlier field replaces the
    // single branch goal with one goal per constructor, and it CLONES the branch's
    // `local_ctx` (including the still-unprocessed later sibling fields, with their
    // FVar ids preserved) into every new branch. A later field must therefore be
    // renamed/destructed in EVERY resulting branch, not just the one that happens
    // to be at the front after the split. Applying its pattern to the front goal
    // alone leaves the other branches carrying the field under its original
    // generated name — so a closer like `exact hr` cannot find `hr` there and the
    // proof term dangles an unbound FVar (`UnknownFVar`). See the non-last-field
    // `⟨hp | hq, hr⟩` case.
    //
    // Pass 1 applies the in-place patterns (`Name`/`Wildcard`) to every goal that
    // still carries the field's FVar — these never split the goal, so ordering is
    // irrelevant and doing them first means the renamed sibling is already present
    // in the context that a subsequent split CLONES into each branch. Pass 2 runs
    // the splitting patterns; each is applied to all goals still carrying the
    // field (a prior split may have multiplied the goals), focusing each in turn.
    let mut deferred: Vec<(FVarId, RIntroPattern)> = Vec::new();
    for (idx, fvar) in field_fvars.iter().enumerate() {
        let Some(pattern) = effective.get(idx) else {
            break;
        };
        match pattern {
            RIntroPattern::Name(new_name) => {
                rename_field_in_all_goals(state, *fvar, new_name);
            }
            RIntroPattern::Wildcard => {
                // Keep the generated field name in every branch; nothing to do.
            }
            other => deferred.push((*fvar, other.clone())),
        }
    }

    // Pass 2: run the deferred, goal-splitting sub-patterns. Each field's FVar is
    // shared (by id) across every branch a prior split produced, so we resolve and
    // apply to ALL goals that still carry it, focusing each to the front in turn.
    for (fvar, pattern) in deferred {
        apply_subpattern_to_field_all_goals(state, fvar, &pattern)?;
    }

    Ok(())
}

/// Rename a field hypothesis (identified by FVar) in EVERY goal that carries it.
///
/// After an earlier field's `Or`/tuple split multiplies the goal into sibling
/// branches, a later field's FVar is present (under its generated name) in each
/// branch. Renaming it in only the front goal strands it in the others. This
/// renames it wherever it appears so all branches agree.
fn rename_field_in_all_goals(state: &mut ProofState, field_fvar: FVarId, new_name: &str) {
    state.invalidate_tc_cache();
    for goal in &mut state.goals {
        for decl in &mut goal.local_ctx {
            if decl.fvar == field_fvar {
                decl.name = new_name.to_string();
            }
        }
    }
}

/// Apply a goal-splitting sub-pattern to a field FVar across ALL goals that carry
/// it, running each in an ISOLATED single-goal sub-state.
///
/// A field FVar is shared by id across every branch produced by an earlier
/// field's case-split (`cases` clones the branch `local_ctx`). A splitting
/// sub-pattern (`Or`, or a `Tuple`/`Anonymous`/`Rfl` that recurses into a split)
/// must therefore be applied to each such branch, not just one.
///
/// Each branch is processed in a single-goal sub-state (`clone_with_goal`), for
/// two reasons:
///
///  1. The shared kernel field engine (`cases`) pushes newly created branch goals
///     to the BACK of the goal queue and then the callee re-reads the FRONT goal
///     to locate the fields it just introduced. When OTHER sibling goals from an
///     earlier field's split are already queued, that "front goal after cases"
///     assumption breaks — the callee would read a foreign branch's context and
///     mis-collect its fields. Isolating one goal restores the invariant.
///  2. Sibling branches must allocate their binder FVars from a SHARED base so the
///     FVar-id ↔ binder-depth correspondence `close_fvars` relies on holds (the
///     same discipline `all_goals`/`<;>` use). Resetting `next_fvar` to a common
///     base before each isolated branch keeps every branch's fields numbered from
///     the same id.
///
/// After each branch runs, its meta assignments are merged back and the goals it
/// produced are collected. The relative order of goals is preserved so downstream
/// bullets (`·`) and `<;>` see the branches in source order.
fn apply_subpattern_to_field_all_goals(
    state: &mut ProofState,
    field_fvar: FVarId,
    pattern: &RIntroPattern,
) -> TacticResult {
    // Partition the current goals into those carrying this field's FVar (the
    // branches an earlier split produced) and those that do not (untouched goals,
    // e.g. from an outer tactic). Process the carriers in isolation; leave the
    // rest in place at their original positions.
    let original: Vec<Goal> = state.goals.iter().cloned().collect();

    // Shared per-branch FVar base so parallel branches number their binder FVars
    // from the same id (keeps the id↔depth correspondence for `close_fvars`).
    let branch_fvar_base = state.next_fvar;
    let mut branch_fvar_max = branch_fvar_base;

    let mut rebuilt: std::collections::VecDeque<Goal> = std::collections::VecDeque::new();
    for goal in original {
        let carries_field = goal.local_ctx.iter().any(|d| d.fvar == field_fvar);
        if !carries_field {
            rebuilt.push_back(goal);
            continue;
        }
        // Reset to the shared base so this branch's fields start from the same id
        // as its siblings, then run the sub-pattern on the isolated goal.
        state.next_fvar = branch_fvar_base;
        let mut focused = state.clone_with_goal(goal);
        apply_subpattern_to_field(&mut focused, field_fvar, pattern)?;
        branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
        state.merge_meta_state(&focused);
        rebuilt.extend(focused.goals);
    }

    state.next_fvar = branch_fvar_max;
    state.goals = rebuilt;
    Ok(())
}

/// Apply a single rintro sub-pattern to an already-bound field FVar.
///
/// The field FVar is already genuinely bound by the enclosing `casesOn` branch
/// lambda (created by `destruct_hypothesis` → `cases`). This only adjusts the
/// surface name, substitutes, or recursively destructs:
/// - `Name(n)`: rename the field's local decl to `n`.
/// - `Wildcard`: leave the generated name in place.
/// - `Rfl`: the field is an equation `lhs = rhs`; substitute it away via the
///   kernel-checked `subst` tactic (eliminating the local variable and the
///   equation). This is the `⟨x, rfl⟩` idiom.
/// - `Tuple`/`Anonymous`: recursively destruct the field via `cases`.
/// - `Or`: treated as a no-op (best effort), matching the prior lenient surface
///   behavior.
fn apply_subpattern_to_field(
    state: &mut ProofState,
    field_fvar: FVarId,
    pattern: &RIntroPattern,
) -> TacticResult {
    match pattern {
        RIntroPattern::Name(name) => {
            rename_field_by_fvar(state, field_fvar, name)?;
            Ok(())
        }
        RIntroPattern::Rfl => substitute_field(state, field_fvar),
        RIntroPattern::Wildcard => {
            // Keep the generated field name; no further destructuring.
            Ok(())
        }
        RIntroPattern::Or(alternatives) => {
            // Nested alternation, e.g. the `hq | hr` field of `⟨hp, hq | hr⟩`
            // destructuring `p ∧ (q ∨ r)`. Resolve the field's current name and
            // case-split it on its constructors via the shared engine.
            let field_name = current_field_name(state, field_fvar).ok_or_else(|| {
                TacticError::HypothesisNotFound(
                    "rcases: nested alternation field hypothesis not found".into(),
                )
            })?;
            split_or_hypothesis(state, &field_name, alternatives)
        }
        RIntroPattern::Tuple(sub) | RIntroPattern::Anonymous(sub) => {
            // Recurse: destruct this field by its current generated name so the
            // nested casesOn composes with the outer one.
            let field_name = current_field_name(state, field_fvar).ok_or_else(|| {
                TacticError::HypothesisNotFound("rintro: nested field hypothesis not found".into())
            })?;
            destruct_hypothesis(state, &field_name, sub)
        }
    }
}

/// Apply the `rfl` pattern to a destructured field: substitute the field's
/// equation away.
///
/// The `⟨x, rfl⟩` idiom binds the second field to an equation (`a = x` or
/// `x = a`) and then `subst`s it, replacing the local variable by the other side
/// and dropping both the variable and the equation from the context. This routes
/// through the existing kernel-checked [`subst`] tactic — which builds a genuine
/// `Eq.ndrec` proof term and re-closes the goal via `close_goal` — so no new
/// trust surface is introduced and the result is rechecked by `add_decl`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty and `field_fvar` is a field hypothesis
///           in the current goal's local context
/// ENSURES: On Ok, the field's equation has been substituted away (one side, a
///          local FVar, eliminated) via a kernel-checked `Eq.ndrec` proof
/// ENSURES: On Err(GoalMismatch), the field's type was not an equality, or
///          neither side is a substitutable local FVar — surfaced as a
///          `TacticError`, never a panic or silent over-accept
fn substitute_field(state: &mut ProofState, field_fvar: FVarId) -> TacticResult {
    let field_name = current_field_name(state, field_fvar).ok_or_else(|| {
        TacticError::HypothesisNotFound("rintro: rfl-pattern field hypothesis not found".into())
    })?;
    subst(state, &field_name)
}

/// Look up a field hypothesis's current name by its FVar in the front goal.
fn current_field_name(state: &ProofState, field_fvar: FVarId) -> Option<String> {
    state
        .current_goal()?
        .local_ctx
        .iter()
        .find(|d| d.fvar == field_fvar)
        .map(|d| d.name.clone())
}

/// Rename a field hypothesis (identified by FVar) in the current goal.
fn rename_field_by_fvar(
    state: &mut ProofState,
    field_fvar: FVarId,
    new_name: &str,
) -> TacticResult {
    state.invalidate_tc_cache();
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    for decl in &mut goal.local_ctx {
        if decl.fvar == field_fvar {
            decl.name = new_name.to_string();
            return Ok(());
        }
    }
    Err(TacticError::HypothesisNotFound(
        "rintro: field hypothesis not found for rename".into(),
    ))
}

/// Rename a hypothesis in the current goal
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `old_name` names a hypothesis in `state.goals[0].local_ctx`
/// ENSURES: On Ok, the hypothesis formerly named `old_name` is renamed to `new_name`
/// ENSURES: On Err(HypothesisNotFound), no hypothesis with `old_name` exists in the current goal
pub(crate) fn rename_hypothesis(
    state: &mut ProofState,
    old_name: &str,
    new_name: &str,
) -> TacticResult {
    state.invalidate_tc_cache();
    let goal = &mut state.goals[0];
    for decl in &mut goal.local_ctx {
        if decl.name == old_name {
            decl.name = new_name.to_string();
            return Ok(());
        }
    }
    Err(TacticError::HypothesisNotFound(format!(
        "rintro: hypothesis '{old_name}' not found"
    )))
}
