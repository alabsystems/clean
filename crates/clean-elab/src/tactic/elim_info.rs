// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Eliminator shape analysis — Clean's equivalent of Lean's `getElimExprInfo`.
//!
//! An *eliminator* is any constant whose type ends in an application of one of
//! its own binders (the **motive**). Kernel recursors (`Nat.rec`) are the
//! canonical instance, but Lean also lets a plain `def` play the role — that is
//! what `@[elab_as_elim]` marks (`Nat.strongRecOn`, `Nat.caseStrongRecOn`, and
//! ~430 Mathlib declarations). Those are *not* in the kernel recursor table, so
//! `induction … using` cannot reach them through `Environment::get_recursor`.
//!
//! This module recovers, from the eliminator's **type alone**, everything the
//! `induction` tactic needs:
//!
//! - which binder is the motive (`motive_pos`),
//! - which binders are the targets / major premises (`targets_pos`),
//! - which binders are the alternatives (minor premises), and for each, how
//!   many fields it binds and whether it proves the motive (`alts_info`).
//!
//! # Why de Bruijn rather than a free-variable telescope
//!
//! Lean's `getElimExprInfo` opens the eliminator type with
//! `forallTelescopeReducing` and compares *free variables* by identity. Clean's
//! kernel [`ExprKind::Pi`] stores only [`BinderData`] (binder info +
//! multiplicity) and **no binder name**, and opening a telescope here would
//! have to allocate tactic FVars — perturbing `ProofState::next_fvar`, which
//! `close_fvars` depends on. So the whole analysis is done directly on de
//! Bruijn indices: inside the body of an `n`-binder telescope, binder `p` is
//! `BVar(n - 1 - p)`. This is pure, allocation-free and unit-testable without a
//! `ProofState`.
//!
//! # The binder-name limitation
//!
//! Because `Pi` carries no name, [`ElimAltInfo`] deliberately has **no `name`
//! field** (Lean's has one, taken from `xDecl.userName`). Alternative *tags*
//! therefore cannot be recovered from the environment; the `induction … using`
//! driver assigns them positionally from the user's `with` block. See
//! `induction_elim.rs` for that contract.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

/// One alternative (minor premise) of an eliminator.
///
/// Deliberately nameless — see the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ElimAltInfo {
    /// Position of this alternative among the eliminator's telescope binders.
    pub(crate) binder_pos: usize,
    /// Number of binders (`∀` / `let`) this alternative's own type introduces.
    ///
    /// Lean calls this `numFields`; it is what `altArity` counts.
    pub(crate) num_fields: usize,
    /// Whether this alternative's conclusion is an application of the motive.
    ///
    /// Lean only introduces reverted hypotheses into motive-proving
    /// alternatives; Clean uses it the same way (and to reject shapes it cannot
    /// yet serve).
    pub(crate) proves_motive: bool,
}

/// The shape of an eliminator, recovered from its type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ElimInfo {
    /// Total number of telescope binders in the eliminator's type.
    pub(crate) num_binders: usize,
    /// Telescope binder position of the motive.
    pub(crate) motive_pos: usize,
    /// Telescope binder positions of the targets (major premises), in order.
    ///
    /// These are exactly the leading motive arguments that are themselves
    /// telescope binders — Lean's `motiveArgs.takeWhile (·.isFVar)`.
    pub(crate) targets_pos: Vec<usize>,
    /// Motive arguments beyond the targets (Lean's `numComplexMotiveArgs`).
    ///
    /// Non-zero means the motive is applied to a computed expression, which
    /// this brick does not serve.
    pub(crate) num_complex_motive_args: usize,
    /// The alternatives, in telescope order.
    pub(crate) alts_info: Vec<ElimAltInfo>,
}

/// Why a constant could not be read as an eliminator.
///
/// Every variant is a *shape* rejection: the analysis never guesses, so the
/// `induction … using` driver can fail closed with a diagnostic that names the
/// construct rather than degrading to a silent sorry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ElimInfoError {
    /// The conclusion's head is not one of the eliminator's own binders.
    ConclusionNotMotiveApplication,
    /// The conclusion's head binder is not applied to anything.
    MotiveNotApplied,
    /// The motive binder's own type is not a telescope ending in a sort, or its
    /// arity does not match the number of motive arguments in the conclusion.
    MotiveTypeMismatch {
        /// Arity of the motive binder's own `∀` telescope.
        motive_params: usize,
        /// Number of arguments the conclusion applies the motive to.
        motive_args: usize,
    },
}

impl std::fmt::Display for ElimInfoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConclusionNotMotiveApplication => write!(
                f,
                "the eliminator's result type is not an application of one of its own parameters (the motive)"
            ),
            Self::MotiveNotApplied => write!(
                f,
                "the eliminator's motive is not applied to any argument in its result type"
            ),
            Self::MotiveTypeMismatch {
                motive_params,
                motive_args,
            } => write!(
                f,
                "the eliminator's motive takes {motive_params} parameter(s) but its result type applies it to {motive_args} argument(s)"
            ),
        }
    }
}

/// Peel a `∀` / `let` telescope, returning each binder's `(info, type)` in
/// order together with the conclusion.
///
/// Each returned binder type is expressed in the scope of the binders *before*
/// it, i.e. binder `p`'s type may mention binder `q < p` as `BVar(p - 1 - q)`.
/// The conclusion is in the scope of all `n` binders, where binder `p` is
/// `BVar(n - 1 - p)`.
///
/// Only `∀` binders are peeled — Lean's `forallTelescopeReducing` likewise
/// stops at anything that is not a `forallE` (its `whnf` step zeta-reduces a
/// leading `let` away rather than binding it). A `let` therefore ends the
/// telescope and the caller fails closed on the resulting non-motive
/// conclusion. `altArity` *does* count `let`s; that is a separate walk.
///
/// ENSURES: the returned conclusion is not a `Pi`
pub(crate) fn telescope(ty: &Expr) -> (Vec<(BinderInfo, Expr)>, Expr) {
    let mut binders = Vec::new();
    let mut current = ty.clone();
    loop {
        match current.strip_mdata().kind() {
            ExprKind::Pi(bd, domain, codomain) => {
                binders.push((bd.info, domain.as_ref().clone()));
                current = codomain.as_ref().clone();
            }
            _ => return (binders, current),
        }
    }
}

/// Lean's `altArity`: count the binders an alternative's type introduces and
/// report whether its conclusion is a motive application.
///
/// `motive_idx` is the de Bruijn index that refers to the motive **at the outer
/// level of `ty`**, or `None` when this binder *precedes* the motive and so
/// cannot mention it at all. It is incremented as the walk descends under
/// binders — saturating, because a pathological type could otherwise overflow
/// it (a real eliminator's telescope is far shallower than `u32::MAX`, and a
/// saturated index can only make `proves_motive` false, never true).
fn alt_arity(motive_idx: Option<u32>, ty: &Expr) -> (usize, bool) {
    let mut idx = motive_idx;
    let mut count = 0usize;
    let mut current = ty.clone();
    loop {
        match current.strip_mdata().kind() {
            ExprKind::Pi(_, _, codomain) => {
                current = codomain.as_ref().clone();
            }
            ExprKind::Let(_, _, _, body, _) => {
                current = body.as_ref().clone();
            }
            _ => {
                let head = current.get_app_fn();
                let proves = match (head.strip_mdata().kind(), idx) {
                    (ExprKind::BVar(i), Some(m)) => *i == m,
                    _ => false,
                };
                return (count, proves);
            }
        }
        idx = idx.map(|i| i.saturating_add(1));
        count += 1;
    }
}

/// Analyse an eliminator's type — the port of Lean's `getElimExprInfo`.
///
/// Mirrors Lean step for step:
/// 1. telescope the type; the conclusion must be `motive args…` with `motive` a
///    telescope binder (Lean: `motive.isFVar`);
/// 2. the targets are the leading `args` that are themselves telescope binders
///    (Lean: `motiveArgs.takeWhile (·.isFVar)`), the rest are "complex";
/// 3. the motive's own type must be a telescope of exactly `args.len()`
///    parameters ending in a sort;
/// 4. every remaining **explicit** binder is an alternative, with `alt_arity`
///    giving its field count and whether it proves the motive.
///
/// REQUIRES: `elim_type` is a closed (level-instantiated or not) constant type
/// ENSURES: On Ok, `motive_pos < num_binders` and every `targets_pos` entry is
///   `< num_binders`
/// ENSURES: On Ok, no position appears in more than one of `motive_pos`,
///   `targets_pos`, `alts_info`
pub(crate) fn get_elim_info(elim_type: &Expr) -> Result<ElimInfo, ElimInfoError> {
    let (binders, conclusion) = telescope(elim_type);
    let num_binders = binders.len();

    // Step 1: conclusion must be `motive args…` with `motive` a telescope binder.
    let head = conclusion.get_app_fn().strip_mdata().clone();
    let ExprKind::BVar(head_idx) = head.kind() else {
        return Err(ElimInfoError::ConclusionNotMotiveApplication);
    };
    let head_idx = *head_idx as usize;
    if head_idx >= num_binders {
        // A loose BVar escaping the telescope: not a well-formed eliminator type.
        return Err(ElimInfoError::ConclusionNotMotiveApplication);
    }
    let motive_pos = num_binders - 1 - head_idx;

    let motive_args: Vec<Expr> = conclusion.get_app_args().into_iter().cloned().collect();
    if motive_args.is_empty() {
        return Err(ElimInfoError::MotiveNotApplied);
    }

    // Step 2: leading motive args that are telescope binders are the targets.
    let mut targets_pos = Vec::new();
    for arg in &motive_args {
        match arg.strip_mdata().kind() {
            ExprKind::BVar(i) if (*i as usize) < num_binders => {
                targets_pos.push(num_binders - 1 - *i as usize);
            }
            _ => break,
        }
    }
    let num_complex_motive_args = motive_args.len() - targets_pos.len();

    // Step 3: the motive's own type is a telescope of `motive_args.len()`
    // parameters ending in a sort.
    let (motive_params, motive_result) = telescope(&binders[motive_pos].1);
    if motive_params.len() != motive_args.len() || !motive_result.strip_mdata().is_sort() {
        return Err(ElimInfoError::MotiveTypeMismatch {
            motive_params: motive_params.len(),
            motive_args: motive_args.len(),
        });
    }

    // Step 4: every other explicit binder is an alternative.
    let mut alts_info = Vec::new();
    for (pos, (info, binder_ty)) in binders.iter().enumerate() {
        if pos == motive_pos || targets_pos.contains(&pos) {
            continue;
        }
        if *info != BinderInfo::Default {
            continue;
        }
        // Inside binder `pos`'s type the motive is `BVar(pos - 1 - motive_pos)`.
        // A binder that PRECEDES the motive cannot mention it at all — `None`,
        // so `proves_motive` is false without inventing an index.
        let motive_idx = if pos > motive_pos {
            u32::try_from(pos - 1 - motive_pos).ok()
        } else {
            None
        };
        let (num_fields, proves_motive) = alt_arity(motive_idx, binder_ty);
        alts_info.push(ElimAltInfo {
            binder_pos: pos,
            num_fields,
            proves_motive,
        });
    }

    Ok(ElimInfo {
        num_binders,
        motive_pos,
        targets_pos,
        num_complex_motive_args,
        alts_info,
    })
}

// ---------------------------------------------------------------------------
// First-order matching: recover the eliminator's implicit arguments and
// universe levels from the goal.
// ---------------------------------------------------------------------------

/// Solutions recovered by matching an eliminator's declared types against the
/// actual goal.
///
/// Clean's [`Level`] has **no metavariable constructor**, so universe
/// instantiation cannot be deferred to a unifier the way Lean does it
/// (`mkConstWithFreshMVarLevels`). Levels are instead solved by first-order
/// matching, here.
#[derive(Debug, Default, Clone)]
pub(crate) struct ElimSolution {
    /// Telescope binder position → solved argument value.
    pub(crate) binder_values: Vec<(usize, Expr)>,
    /// Eliminator level parameter → solved level.
    pub(crate) levels: Vec<(Name, Level)>,
}

impl ElimSolution {
    fn set_binder(&mut self, pos: usize, value: Expr) {
        if !self.binder_values.iter().any(|(p, _)| *p == pos) {
            self.binder_values.push((pos, value));
        }
    }

    pub(crate) fn binder(&self, pos: usize) -> Option<&Expr> {
        self.binder_values
            .iter()
            .find(|(p, _)| *p == pos)
            .map(|(_, v)| v)
    }

    fn set_level(&mut self, param: &Name, level: Level) {
        if !self.levels.iter().any(|(p, _)| p == param) {
            self.levels.push((param.clone(), level));
        }
    }
}

/// Match a level *pattern* (over the eliminator's level params) against an
/// actual level, recording assignments.
///
/// Conservative and structural: `Param` binds, identical shapes recurse,
/// anything else is simply not solved here (a later unsolved-parameter check
/// fails closed).
fn match_level(pattern: &Level, actual: &Level, params: &[Name], sol: &mut ElimSolution) {
    match (pattern, actual) {
        (Level::Param(p), _) if params.contains(p) => sol.set_level(p, actual.clone()),
        (Level::Succ(a), Level::Succ(b)) => match_level(a, b, params, sol),
        (Level::Max(a1, a2), Level::Max(b1, b2)) | (Level::IMax(a1, a2), Level::IMax(b1, b2)) => {
            match_level(a1, b1, params, sol);
            match_level(a2, b2, params, sol);
        }
        _ => {}
    }
}

/// First-order match of an eliminator binder type (`pattern`, in the scope of
/// the binders before position `depth`) against a concrete expression.
///
/// Records both binder values (a `BVar` in the pattern is a preceding
/// eliminator binder) and universe-level assignments. Structural mismatches are
/// *ignored* rather than reported: this is a best-effort solver whose output is
/// validated downstream by the kernel re-check, and whose unsolved parameters
/// are rejected explicitly by the caller.
///
/// `depth` is the number of telescope binders in scope at `pattern`; `local`
/// counts the binders the walk has itself descended under. A pattern
/// `BVar(i)` denotes a *local* binder when `i < local`, and telescope binder
/// `depth - 1 - (i - local)` otherwise.
pub(crate) fn match_pattern(
    pattern: &Expr,
    actual: &Expr,
    depth: usize,
    params: &[Name],
    sol: &mut ElimSolution,
) {
    match_pattern_at(pattern, actual, depth, 0, params, sol);
}

fn match_pattern_at(
    pattern: &Expr,
    actual: &Expr,
    depth: usize,
    local: usize,
    params: &[Name],
    sol: &mut ElimSolution,
) {
    let pattern = pattern.strip_mdata();
    let actual = actual.strip_mdata();
    match (pattern.kind(), actual.kind()) {
        (ExprKind::BVar(i), _) => {
            let i = *i as usize;
            // A binder the walk descended under is not an eliminator parameter.
            if i < local {
                return;
            }
            let telescope_idx = i - local;
            // Only a closed actual can instantiate an eliminator parameter: a
            // term mentioning a locally-bound variable would escape its scope.
            if telescope_idx < depth && !actual.has_loose_bvars() {
                sol.set_binder(depth - 1 - telescope_idx, actual.clone());
            }
        }
        (ExprKind::Sort(lp), ExprKind::Sort(la)) => match_level(lp, la, params, sol),
        (ExprKind::Const(np, lp), ExprKind::Const(na, la)) if np == na => {
            for (p, a) in lp.iter().zip(la.iter()) {
                match_level(p, a, params, sol);
            }
        }
        (ExprKind::App(fp, ap), ExprKind::App(fa, aa)) => {
            match_pattern_at(fp, fa, depth, local, params, sol);
            match_pattern_at(ap, aa, depth, local, params, sol);
        }
        (ExprKind::Pi(_, dp, cp), ExprKind::Pi(_, da, ca))
        | (ExprKind::Lam(_, dp, cp), ExprKind::Lam(_, da, ca)) => {
            match_pattern_at(dp, da, depth, local, params, sol);
            match_pattern_at(cp, ca, depth, local + 1, params, sol);
        }
        (ExprKind::Proj(_, ip, ep), ExprKind::Proj(_, ia, ea)) if ip == ia => {
            match_pattern_at(ep, ea, depth, local, params, sol);
        }
        _ => {}
    }
}
