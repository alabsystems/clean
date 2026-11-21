// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The normalised form a goal subterm is matched against by the simp lemma
//! matcher, and the two normalisation steps that build it.
//!
//! These steps are pure functions of `(state, goal, expr)` — none reads the
//! candidate lemma — so a candidate loop computes a [`MatchTarget`] ONCE per
//! subterm and matches every candidate against it. See [`MatchTarget`] for the
//! measurement that motivated hoisting them out of the per-candidate path.

use std::sync::LazyLock;

use clean_kernel::expr::Literal;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

mod numerals;
pub(crate) use numerals::as_nat_ofnat_literal;
pub(super) use numerals::collapse_nat_ofnat_literals;

use crate::tactic::core::{Goal, ProofState};
use crate::tactic::op_projection::reduce_op_projection_head;

use super::budget::SimpBudget;

static NAT_ADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.add"));
static NAT_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.succ"));
static HADD_ADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("HAdd.hAdd"));

/// The expression a simp candidate's LHS pattern is unified against.
///
/// # Why this exists
///
/// `try_apply_simp_lemma_with_proof` used to derive the match target from
/// `expr` itself, on every call — i.e. once per CANDIDATE LEMMA at every
/// subterm simp visits — even though neither derivation step looks at the
/// lemma. The `OfNat` collapse rebuilds the entire target tree, so a subterm
/// with `n` candidates allocated and immediately dropped `n` full copies of
/// it. Measured on `Mathlib/Logic/Basic.lean` (1 ms `sample(1)` windows on the
/// `clean-check` thread, release binary): the collapse fold was 7.7–32.5% of
/// the thread and the `Expr` drop glue it fed inside
/// `try_apply_simp_lemma_with_proof` a further 6.0–25.8% — together
/// 13.7–56.5% across four windows, the largest single component of
/// `simp_expr`.
///
/// Hoisting is behaviour-preserving by construction: `ProofState` exposes no
/// interior mutability that either step reads (`metas`, `elab_locals` and the
/// goal are plain fields behind `&self`; the only `Mutex` is the `TypeChecker`
/// cache), so consecutive calls with the same `(state, goal, expr)` are
/// obliged to produce the same target — this type just stops asking twice.
///
/// # Normalization steps
///
/// 1. **Hetero-operator projection peel.** When `expr` is a typeclass
///    projection (`@HMul.hMul Nat … n 0`), bare-head builtin/library lemmas
///    (`Nat.mul ?n 0`) cannot unify head-to-head against the projection spine:
///    the first-order unifier mis-binds `?n` to a partial `HMul.hMul …`
///    application, assembling a malformed proof that only the kernel
///    `add_decl` rejects (after which simp has already lost the chance to fall
///    through to another candidate). Peel EXACTLY the projection layer —
///    exposing `Nat.mul n 0` WITHOUT ι-reducing the operands — and unify the
///    pattern against THAT. The unifier then binds `?n ↦ n` correctly.
///    `reduce_op_projection_head` returns `None` for non-projection heads, so
///    the common case is untouched.
/// 2. **`OfNat` literal collapse.** Collapse
///    `@OfNat.ofNat Nat k (instOfNatNat k)` operand leaves to the raw
///    `Lit(Nat k)` (B102). The surface elaborator spells a Nat numeral as the
///    `OfNat` projection form; builtin literal-operand patterns
///    (`Nat.add ?n 0`, `Nat.mul ?n 1`) carry the bare `Nat.zero`/`Lit 1` leaf,
///    and the reducible-transparency unifier cannot bridge the two (the
///    `OfNat` instance does not unfold at `withReducible`).
/// 3. **Lambda argument contraction.** When an argument's body reduces to
///    `f x` with no `x` in `f`, pass `f` to the alternate index lookup and
///    to the matcher. Both see the same candidate shape.
///
/// # Soundness
///
/// The steps are definitional, and nothing
/// downstream is restated over the normalised form: the `lhs_inst ≡ expr`
/// guard is still stated over the ORIGINAL `expr`, the assembled proof still
/// goes through `proof_matches_rewrite`, and the kernel `add_decl` re-check
/// remains the backstop. This only decides which candidate is *selected*.
///
/// The subterm it was built from travels WITH it ([`MatchTarget::source`]), so
/// the matcher takes one argument instead of two and a caller cannot pair a
/// normalised target with a different expression.
pub(crate) struct MatchTarget {
    /// The subterm this target was built from — the expression every guard in
    /// the matcher is still stated over.
    source: Expr,
    /// The target after eta contraction and operator projection peeling.
    base: Expr,
    /// Numeral folding can traverse the entire subterm. Candidate selection
    /// only needs the source and eta forms, so fold after it offers a lemma.
    collapsed_numerals: std::cell::OnceCell<Option<Expr>>,
    eta_index_target: Option<Expr>,
    /// The goal universe parameters `source` and `target` mention — rigid for
    /// every universe-polymorphic candidate matched against them — computed
    /// on first use and shared by every candidate, for the reason this type
    /// exists at all.
    level_params: std::cell::OnceCell<Vec<Name>>,
}

impl MatchTarget {
    /// Normalise `expr` for lemma matching.
    ///
    /// REQUIRES: `expr` is a subterm of `goal`'s target or hypotheses.
    /// ENSURES: `self.expr()` is definitionally equal to `self.source()`.
    pub(crate) fn new(state: &ProofState, goal: &Goal, expr: &Expr) -> Self {
        let eta_index_target = eta_arguments(state, goal, expr);
        let eta_shape = eta_index_target.as_ref().unwrap_or(expr);
        let peeled = reduce_op_projection_head(state, goal, eta_shape);
        let base = peeled.unwrap_or_else(|| eta_shape.clone());
        MatchTarget {
            source: expr.clone(),
            base,
            collapsed_numerals: std::cell::OnceCell::new(),
            eta_index_target,
            level_params: std::cell::OnceCell::new(),
        }
    }

    /// The goal's universe parameters this subterm mentions, which a match
    /// may never assign (see `super::lemma_levels::goal_level_params`).
    pub(crate) fn level_params(&self) -> &[Name] {
        self.level_params.get_or_init(|| {
            let mut out = super::lemma_levels::goal_level_params(self.expr());
            for name in super::lemma_levels::goal_level_params(&self.source) {
                if !out.contains(&name) {
                    out.push(name);
                }
            }
            out
        })
    }

    /// The subterm being rewritten — what a rewrite must be stated over.
    pub(crate) fn source(&self) -> &Expr {
        &self.source
    }

    /// The expression candidate patterns are unified against.
    pub(crate) fn expr(&self) -> &Expr {
        self.collapsed_numerals
            .get_or_init(|| collapse_nat_ofnat_literals(&self.base))
            .as_ref()
            .unwrap_or(&self.base)
    }

    /// Numeral folding changes the application head only when that head is
    /// `OfNat.ofNat`. Other heads can reject unrelated lemmas before a fold.
    pub(super) fn head_guard_target(&self) -> &Expr {
        if matches!(
            self.base.get_app_fn().kind(),
            ExprKind::Const(name, _) if *name == *numerals::OFNAT_NAME
        ) {
            self.expr()
        } else {
            &self.base
        }
    }

    pub(super) fn eta_index_target(&self) -> Option<&Expr> {
        self.eta_index_target.as_ref()
    }
}

/// A matcher in a lambda may reduce to `f x`, making `f` a usable key and match target.
/// A successful broad tree hit can otherwise hide a rule keyed by `f`.
/// The simplifier still checks every candidate against the original target.
fn eta_arguments(state: &ProofState, goal: &Goal, target: &Expr) -> Option<Expr> {
    let args = target.get_app_args();
    if !args
        .iter()
        .any(|arg| matches!(arg.kind(), ExprKind::Lam(..)))
    {
        return None;
    }
    let mut changed = false;
    let adjusted = args.into_iter().map(|argument| {
        if let ExprKind::Lam(_, _, body) = argument.kind() {
            let body = state.whnf_indexing(goal, body);
            if let Some(contracted) = super::reduce::eta_contract_body(&body) {
                changed = true;
                return contracted;
            }
        }
        argument.clone()
    });
    let contracted = Expr::apps(target.get_app_fn().clone(), adjusted);
    changed.then_some(contracted)
}

/// Expose a successor written as addition when a compatible constructor
/// equation already requires that argument. The existing match guards still
/// compare the instantiated lemma to the original goal expression.
pub(super) fn match_successor_arguments(
    state: &ProofState,
    goal: &Goal,
    pattern: &Expr,
    candidate: &Expr,
    budget: &SimpBudget,
) -> Option<Expr> {
    let (ExprKind::Const(pattern_head, _), ExprKind::Const(candidate_head, _)) =
        (pattern.get_app_fn().kind(), candidate.get_app_fn().kind())
    else {
        return None;
    };
    if pattern_head != candidate_head {
        return None;
    }
    let patterns = pattern.get_app_args();
    let arguments = candidate.get_app_args();
    if patterns.len() != arguments.len() {
        return None;
    }
    let mut normalized = None;
    for (index, (pattern, argument)) in patterns.iter().zip(&arguments).enumerate() {
        if !matches!(pattern.get_app_fn().kind(), ExprKind::Const(name, _) if *name == *NAT_SUCC) {
            continue;
        }
        if let Some(reduced) =
            successor_from_addition(state, goal, argument, budget, reduce_op_projection_head)
        {
            normalized
                .get_or_insert_with(|| arguments.iter().copied().cloned().collect::<Vec<_>>())
                [index] = reduced;
        }
    }
    normalized.map(|arguments| Expr::apps(candidate.get_app_fn().clone(), arguments))
}

pub(super) fn successor_from_addition(
    state: &ProofState,
    goal: &Goal,
    argument: &Expr,
    budget: &SimpBudget,
    peel_projection: fn(&ProofState, &Goal, &Expr) -> Option<Expr>,
) -> Option<Expr> {
    let ExprKind::Const(head, _) = argument.get_app_fn().kind() else {
        return None;
    };
    let addition = if *head == *NAT_ADD {
        argument.clone()
    } else if *head == *HADD_ADD {
        peel_projection(state, goal, argument)?
    } else {
        return None;
    };
    if !matches!(addition.get_app_fn().kind(), ExprKind::Const(name, _) if *name == *NAT_ADD) {
        return None;
    }
    let arguments = addition.get_app_args();
    let [left, amount] = arguments.as_slice() else {
        return None;
    };
    let literal = as_nat_ofnat_literal(amount);
    let ExprKind::Lit(Literal::Nat(amount)) = literal.as_ref().unwrap_or(amount).kind() else {
        return None;
    };
    let predecessor = amount.pred()?;
    if !budget.charge_attempt() {
        return None;
    }
    let inner = if predecessor.is_zero() {
        (*left).clone()
    } else {
        Expr::apps(
            addition.get_app_fn().clone(),
            [(*left).clone(), Expr::bignat_lit(predecessor)],
        )
    };
    let reduced = Expr::app(Expr::const_(NAT_SUCC.clone(), vec![]), inner);
    (budget.admit(&reduced, "matching a successor argument")
        && state.is_def_eq(goal, argument, &reduced))
    .then_some(reduced)
}

#[cfg(test)]
mod tests {
    use clean_kernel::{BinderInfo, Environment};
    use clean_parser::SurfaceName;

    use super::*;
    use crate::tactic::intro;

    #[test]
    fn only_an_attempted_match_needs_the_full_numeral_fold() {
        let state = ProofState::new(Environment::with_prelude(), Expr::const_str("True"));
        let goal = state.goals().front().unwrap();
        let numeral = Expr::nat_lit(7);
        let wrapper = Expr::apps(
            Expr::const_str("OfNat.ofNat"),
            [
                Expr::const_str("Nat"),
                numeral.clone(),
                Expr::app(Expr::const_str("instOfNatNat"), numeral.clone()),
            ],
        );
        let wrapped_argument = Expr::app(Expr::const_str("unrelated"), wrapper.clone());
        let target = MatchTarget::new(&state, goal, &wrapped_argument);
        let lemmas = super::super::SimpLemmaSet::without_index(Vec::new());
        assert!(lemmas
            .candidates_for_target(&state, goal, &target)
            .is_empty());
        assert_eq!(target.head_guard_target(), &wrapped_argument);
        assert!(target.collapsed_numerals.get().is_none());
        let collapsed = Expr::app(Expr::const_str("unrelated"), numeral.clone());
        assert_eq!(target.expr(), &collapsed);
        assert_eq!(target.collapsed_numerals.get(), Some(&Some(collapsed)));

        let headed = MatchTarget::new(&state, goal, &wrapper);
        assert_eq!(headed.head_guard_target(), &numeral);
        assert_eq!(headed.collapsed_numerals.get(), Some(&Some(numeral)));
    }

    #[test]
    fn successor_equations_match_compact_open_nat_additions() {
        let nat = Expr::const_str("Nat");
        let proposition = Expr::pi(BinderInfo::Default, nat, Expr::const_str("True"));
        let mut state = ProofState::new(Environment::with_prelude(), proposition);
        intro(&mut state, &SurfaceName::generated_path("n")).unwrap();
        let goal = state.goals().front().unwrap();
        let local = Expr::fvar(goal.local_ctx[0].fvar);
        let succ = |argument| Expr::app(Expr::const_(NAT_SUCC.clone(), vec![]), argument);
        let add = |amount| {
            Expr::apps(
                Expr::const_(NAT_ADD.clone(), vec![]),
                [local.clone(), Expr::nat_lit(amount)],
            )
        };
        let pattern = succ(succ(local.clone()));
        let candidate = succ(add(2));
        let budget = SimpBudget::for_target(&candidate);
        let expected = succ(succ(add(1)));
        assert_eq!(
            match_successor_arguments(&state, goal, &pattern, &candidate, &budget),
            Some(expected)
        );
        assert_eq!(
            match_successor_arguments(&state, goal, &pattern, &succ(add(0)), &budget),
            None
        );
    }
}
