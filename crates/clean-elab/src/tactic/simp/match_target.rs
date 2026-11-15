// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The normalised form a goal subterm is matched against by the simp lemma
//! matcher, and the two normalisation steps that build it.
//!
//! Both steps are pure functions of `(state, goal, expr)` — neither reads the
//! candidate lemma — so a candidate loop computes a [`MatchTarget`] ONCE per
//! subterm and matches every candidate against it. See [`MatchTarget`] for the
//! measurement that motivated hoisting them out of the per-candidate path.

use std::sync::LazyLock;

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolder, ExprKind};

use crate::stack_safe;
use crate::tactic::core::{Goal, ProofState};
use crate::tactic::op_projection::reduce_op_projection_head;

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
/// # The two steps
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
///
/// # Soundness
///
/// Both steps are definitional (the instance's own ι/δ-reduction), and nothing
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
    /// The normalised target. Equal to `source` when neither step fired, which
    /// is the overwhelmingly common case.
    target: Expr,
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
        let peeled = reduce_op_projection_head(state, goal, expr);
        let base = peeled.unwrap_or_else(|| expr.clone());
        let target = collapse_nat_ofnat_literals(&base).unwrap_or(base);
        MatchTarget {
            source: expr.clone(),
            target,
            level_params: std::cell::OnceCell::new(),
        }
    }

    /// The goal's universe parameters this subterm mentions, which a match
    /// may never assign (see `super::lemma_levels::goal_level_params`).
    pub(crate) fn level_params(&self) -> &[Name] {
        self.level_params.get_or_init(|| {
            let mut out = super::lemma_levels::goal_level_params(&self.target);
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
        &self.target
    }
}

/// If `e` is exactly the Nat-numeral projection form
/// `@OfNat.ofNat Nat (Lit k) (instOfNatNat (Lit k))`, return the raw literal
/// `Lit(Nat k)`; otherwise `None`.
///
/// SOUNDNESS: `instOfNatNat k` is the structure literal storing `k`, so the
/// projection ι/δ-reduces to `k` — the two spellings are definitionally equal
/// (the kernel's `add_decl` re-check enforces exactly this equivalence).
pub(crate) fn as_nat_ofnat_literal(e: &Expr) -> Option<Expr> {
    let head = e.get_app_fn();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    if *head_name != *OFNAT_NAME {
        return None;
    }
    let args = e.get_app_args();
    let [ty, lit, inst] = args.as_slice() else {
        return None;
    };
    if !matches!(ty.kind(), ExprKind::Const(n, _) if *n == *NAT_NAME) {
        return None;
    }
    if !matches!(lit.kind(), ExprKind::Lit(clean_kernel::Literal::Nat(_))) {
        return None;
    }
    let inst_head = inst.get_app_fn();
    if !matches!(inst_head.kind(), ExprKind::Const(n, _) if *n == *INST_OFNAT_NAT_NAME) {
        return None;
    }
    // Read the instance's stored field: that is the value the genuine
    // `OfNat.ofNat` projection produces. Requiring it to be the same literal
    // as the class index also makes this helper fail closed on an internally
    // inconsistent (and therefore ill-typed) wrapper.
    let inst_args = inst.get_app_args();
    let [inst_lit] = inst_args.as_slice() else {
        return None;
    };
    let (
        ExprKind::Lit(clean_kernel::Literal::Nat(k_inst)),
        ExprKind::Lit(clean_kernel::Literal::Nat(k_idx)),
    ) = (inst_lit.kind(), lit.kind())
    else {
        return None;
    };
    if k_inst != k_idx {
        return None;
    }
    Some((*inst_lit).clone())
}

static OFNAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("OfNat.ofNat"));
static NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static INST_OFNAT_NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("instOfNatNat"));

/// Whether any `OfNat.ofNat` constant occurs anywhere in `e`.
///
/// [`as_nat_ofnat_literal`] fires only on a node whose application head is
/// `Const("OfNat.ofNat")`, and a collapse only ever replaces a subtree with a
/// `Lit` — it can never introduce that head. So a tree without the constant
/// cannot collapse, at any node, before or after any other collapse, and the
/// rebuild below can be skipped outright. Read-only: allocates nothing.
fn mentions_ofnat(e: &Expr) -> bool {
    stack_safe(|| match e.kind() {
        ExprKind::Const(name, _) => *name == *OFNAT_NAME,
        ExprKind::App(f, a) => mentions_ofnat(f) || mentions_ofnat(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_ofnat(ty) || mentions_ofnat(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_ofnat(ty) || mentions_ofnat(val) || mentions_ofnat(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            mentions_ofnat(inner)
        }
        _ => false,
    })
}

/// Rewrite every `@OfNat.ofNat Nat k (instOfNatNat k)` subterm of `e` to the
/// raw `Lit(Nat k)`. Returns `None` when nothing collapsed (the common case),
/// so callers keep the original expression without an extra clone.
///
/// The [`mentions_ofnat`] pre-scan makes the no-op case allocation-free: the
/// fold below rebuilds EVERY node it visits (that is what `ExprFolder` does),
/// so without the guard a call that collapses nothing still built a complete
/// copy of the tree and then dropped it. The guard cannot change the result —
/// see its doc comment.
pub(super) fn collapse_nat_ofnat_literals(e: &Expr) -> Option<Expr> {
    if !mentions_ofnat(e) {
        return None;
    }

    struct OfNatCollapser {
        changed: bool,
    }
    impl ExprFolder for OfNatCollapser {
        fn fold_app(&mut self, f: &Expr, arg: &Expr) -> Expr {
            let rebuilt = Expr::app(self.fold_expr(f), self.fold_expr(arg));
            if let Some(lit) = as_nat_ofnat_literal(&rebuilt) {
                self.changed = true;
                lit
            } else {
                rebuilt
            }
        }
    }
    let mut collapser = OfNatCollapser { changed: false };
    let folded = collapser.fold_expr(e);
    collapser.changed.then_some(folded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Literal;

    /// The fold WITHOUT the [`mentions_ofnat`] pre-scan — the exact body this
    /// module shipped before the guard was added. Every test below asserts the
    /// guarded and unguarded forms agree, so the guard is pinned as a pure
    /// performance change and cannot silently start refusing a collapse.
    fn collapse_unguarded(e: &Expr) -> Option<Expr> {
        struct OfNatCollapser {
            changed: bool,
        }
        impl ExprFolder for OfNatCollapser {
            fn fold_app(&mut self, f: &Expr, arg: &Expr) -> Expr {
                let rebuilt = Expr::app(self.fold_expr(f), self.fold_expr(arg));
                if let Some(lit) = as_nat_ofnat_literal(&rebuilt) {
                    self.changed = true;
                    lit
                } else {
                    rebuilt
                }
            }
        }
        let mut collapser = OfNatCollapser { changed: false };
        let folded = collapser.fold_expr(e);
        collapser.changed.then_some(folded)
    }

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), clean_kernel::LevelVec::new())
    }

    fn nat_lit(k: u64) -> Expr {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(k.into())))
    }

    /// `@OfNat.ofNat Nat (Lit k) (instOfNatNat (Lit k))`.
    fn ofnat(k: u64) -> Expr {
        Expr::app(
            Expr::app(Expr::app(c("OfNat.ofNat"), c("Nat")), nat_lit(k)),
            Expr::app(c("instOfNatNat"), nat_lit(k)),
        )
    }

    fn assert_agrees(e: &Expr) -> Option<Expr> {
        let guarded = collapse_nat_ofnat_literals(e);
        let unguarded = collapse_unguarded(e);
        assert_eq!(
            guarded, unguarded,
            "the mentions_ofnat pre-scan changed the result of the collapse"
        );
        guarded
    }

    #[test]
    fn test_collapse_no_ofnat_returns_none_and_agrees_with_unguarded() {
        let e = Expr::app(Expr::app(c("Nat.add"), c("n")), nat_lit(0));
        assert!(assert_agrees(&e).is_none());
    }

    #[test]
    fn test_collapse_ofnat_leaf_becomes_literal() {
        let e = Expr::app(Expr::app(c("Nat.add"), c("n")), ofnat(7));
        let got = assert_agrees(&e).expect("the OfNat operand must collapse");
        assert_eq!(got, Expr::app(Expr::app(c("Nat.add"), c("n")), nat_lit(7)));
    }

    /// A child collapse can EXPOSE a parent collapse: the outer node's literal
    /// slot is itself spelled as `OfNat.ofNat`, so it only matches
    /// [`as_nat_ofnat_literal`] once the inner one has been replaced. This is
    /// the case that forces the pre-scan to be a superset test ("does the
    /// constant occur anywhere") rather than a top-node test.
    #[test]
    fn test_collapse_is_iterated_through_nested_ofnat() {
        let nested = Expr::app(
            Expr::app(Expr::app(c("OfNat.ofNat"), c("Nat")), ofnat(3)),
            Expr::app(c("instOfNatNat"), nat_lit(3)),
        );
        let got = assert_agrees(&nested).expect("the nested OfNat must collapse");
        assert_eq!(got, nat_lit(3));
    }

    #[test]
    fn test_collapse_reaches_under_binders_and_projections() {
        let under_lam = Expr::lam(
            clean_kernel::BinderInfo::Default,
            c("Nat"),
            Expr::app(Expr::app(c("Nat.add"), Expr::bvar(0)), ofnat(1)),
        );
        assert!(assert_agrees(&under_lam).is_some());

        let under_proj = Expr::proj(Name::from_string("S"), 0, ofnat(2));
        assert_eq!(
            assert_agrees(&under_proj),
            Some(Expr::proj(Name::from_string("S"), 0, nat_lit(2),))
        );
    }

    /// A near-miss must NOT collapse: the instance argument is not
    /// `instOfNatNat`, so the two spellings are not the same numeral.
    #[test]
    fn test_collapse_refuses_foreign_ofnat_instance() {
        let e = Expr::app(
            Expr::app(Expr::app(c("OfNat.ofNat"), c("Nat")), nat_lit(5)),
            c("someOtherInstance"),
        );
        assert!(assert_agrees(&e).is_none());
    }

    #[test]
    fn test_collapse_refuses_mismatched_ofnat_index_and_instance_value() {
        let e = Expr::app(
            Expr::app(Expr::app(c("OfNat.ofNat"), c("Nat")), nat_lit(5)),
            Expr::app(c("instOfNatNat"), nat_lit(6)),
        );
        assert!(assert_agrees(&e).is_none());
    }
}
