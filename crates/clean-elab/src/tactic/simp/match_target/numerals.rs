// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, LazyLock};

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolderOpt, ExprKind, ExprVisitor};

/// If `e` is exactly the Nat-numeral projection form
/// `@OfNat.ofNat Nat (Lit k) (instOfNatNat (Lit k))`, return the raw literal
/// `Lit(Nat k)`; otherwise `None`.
///
/// SOUNDNESS: `instOfNatNat k` is the structure literal storing `k`, so the
/// projection ι/δ-reduces to `k` — the two spellings are definitionally equal
/// (the kernel's `add_decl` re-check enforces exactly this equivalence).
pub(crate) fn as_nat_ofnat_literal(e: &Expr) -> Option<Expr> {
    let ExprKind::App(with_index, inst) = e.kind() else {
        return None;
    };
    let ExprKind::App(with_type, lit) = with_index.kind() else {
        return None;
    };
    let ExprKind::App(head, ty) = with_type.kind() else {
        return None;
    };
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    if *head_name != *OFNAT_NAME {
        return None;
    }
    if !matches!(ty.kind(), ExprKind::Const(n, _) if *n == *NAT_NAME) {
        return None;
    }
    if !matches!(lit.kind(), ExprKind::Lit(clean_kernel::Literal::Nat(_))) {
        return None;
    }
    let ExprKind::App(inst_head, inst_lit) = inst.kind() else {
        return None;
    };
    if !matches!(inst_head.kind(), ExprKind::Const(n, _) if *n == *INST_OFNAT_NAT_NAME) {
        return None;
    }
    // Read the instance's stored field: that is the value the genuine
    // `OfNat.ofNat` projection produces. Requiring it to be the same literal
    // as the class index also makes this helper fail closed on an internally
    // inconsistent (and therefore ill-typed) wrapper.
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
    Some(inst_lit.as_ref().clone())
}

pub(super) static OFNAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("OfNat.ofNat"));
static NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static INST_OFNAT_NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("instOfNatNat"));

/// The simp target pre-scan follows the ordinary term forms used for numeral
/// matching. Its answer is independent of binder depth. Skip repeated nodes
/// and stop inspecting descendants once a suitable constant has been seen.
fn mentions_ofnat(expr: &Expr) -> bool {
    #[derive(Default)]
    struct Search {
        seen: HashSet<*const Expr>,
        found: bool,
    }
    impl ExprVisitor for Search {
        type Result = ();
        fn combine(&self, _: (), _: ()) {}

        fn should_visit(&mut self, expr: &Expr) -> bool {
            if self.found {
                return false;
            }
            match expr.kind() {
                ExprKind::Const(name, _) => {
                    self.found = *name == *OFNAT_NAME;
                    false
                }
                ExprKind::App(..)
                | ExprKind::Lam(..)
                | ExprKind::Pi(..)
                | ExprKind::Let(..)
                | ExprKind::Proj(..)
                | ExprKind::MData(..)
                | ExprKind::Squash(..) => self.seen.insert(std::ptr::from_ref(expr)),
                _ => false,
            }
        }
    }
    let mut search = Search::default();
    search.visit_expr(expr);
    search.found
}

/// Rewrite every genuine Nat numeral projection under this target. A shared
/// child has the same replacement at every occurrence, including under a
/// binder. Keep the changed Arc itself so later walks retain that sharing.
pub(crate) fn collapse_nat_ofnat_literals(expr: &Expr) -> Option<Expr> {
    if !mentions_ofnat(expr) {
        return None;
    }
    #[derive(Default)]
    struct Collapser {
        shared: HashMap<*const Expr, Option<Arc<Expr>>>,
    }
    impl ExprFolderOpt for Collapser {
        fn fold_expr_opt_inner(&mut self, expr: &Expr) -> Option<Expr> {
            // Every edge runs the kernel's metered fold dispatch before this
            // lookup. The Arc hook supplies the cached value on a hit.
            if self.shared.contains_key(&std::ptr::from_ref(expr)) {
                return None;
            }
            #[cfg(kani)]
            let updated = self.fold_expr_opt_inner_core(expr);
            #[cfg(not(kani))]
            let updated = self.fold_expr_opt_inner_full(expr);
            if matches!(expr.kind(), ExprKind::App(..)) {
                if let Some(literal) = as_nat_ofnat_literal(updated.as_ref().unwrap_or(expr)) {
                    return Some(literal);
                }
            }
            updated
        }

        fn fold_expr_arc_opt(&mut self, child: &Arc<Expr>) -> Option<Arc<Expr>> {
            let updated = self.fold_expr_opt(child).map(Arc::new);
            if Arc::strong_count(child) == 1 {
                return updated;
            }
            self.shared
                .entry(Arc::as_ptr(child))
                .or_insert(updated)
                .clone()
        }

        fn fold_binder_body_arc_opt(&mut self, child: &Arc<Expr>) -> Option<Arc<Expr>> {
            self.fold_expr_arc_opt(child)
        }
    }
    Collapser::default().fold_expr_opt(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{ExprFolder, Literal};

    /// The original rebuilding fold, used as the reference for ordinary
    /// targets on which the numeral pre-scan is defined.
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

    #[test]
    fn shared_input_keeps_one_replacement_and_the_original_unchanged_child() {
        let unchanged = Arc::new(c("untouched"));
        let mut shared = Arc::new(Expr::app_arc(Arc::clone(&unchanged), Arc::new(ofnat(7))));
        for _ in 0..18 {
            shared = Arc::new(Expr::app_arc(Arc::clone(&shared), shared));
        }
        let replacement = collapse_nat_ofnat_literals(&shared).unwrap();
        let mut node = &replacement;
        for _ in 0..18 {
            let ExprKind::App(left, right) = node.kind() else {
                panic!("expected application")
            };
            assert!(Arc::ptr_eq(left, right));
            node = left;
        }
        let ExprKind::App(left, right) = node.kind() else {
            panic!("expected original application")
        };
        assert!(Arc::ptr_eq(left, &unchanged));
        assert_eq!(**right, nat_lit(7));
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

    #[test]
    fn the_numeral_head_and_instance_require_exact_arity() {
        let valid = ofnat(5);
        assert!(as_nat_ofnat_literal(&Expr::app(valid, c("extra"))).is_none());
        let wrong_instance = Expr::app(Expr::app(c("instOfNatNat"), nat_lit(5)), nat_lit(5));
        let wrong = Expr::app(
            Expr::app(Expr::app(c("OfNat.ofNat"), c("Nat")), nat_lit(5)),
            wrong_instance,
        );
        assert!(collapse_nat_ofnat_literals(&wrong).is_none());
    }

    #[test]
    fn a_cubical_child_preserves_the_original_prescan_scope() {
        let inside = Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(ofnat(2)),
        });
        assert!(collapse_nat_ofnat_literals(&inside).is_none());
        // Once an ordinary branch triggers the fold, its original visitor
        // also inspects cubical children, irrespective of branch order.
        assert!(assert_agrees(&Expr::app(inside, ofnat(3))).is_some());
    }
}
