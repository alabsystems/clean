// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExprKind and ZFCSetExpr enums with metadata computation.
//!
//! Contains the structural variants of expressions, their metadata computation,
//! and the ZFC set expression type with its de Bruijn operations.

use super::*;
use crate::level::Level;
use crate::name::Name;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// Compute metadata for a ZFCSetExpr by combining child expression metadata.
///
/// Each ZFCSetExpr variant gets a distinct hash seed (primes 73-89) to avoid
/// collisions between different set constructions with the same children.
fn zfc_set_expr_meta(set_expr: &ZFCSetExpr) -> ExprMeta {
    match set_expr {
        ZFCSetExpr::Empty => {
            ExprMeta::pack(mix_hash(73, 0) as u32, 0, 0, false, false, false, false)
        }
        ZFCSetExpr::Infinity => {
            ExprMeta::pack(mix_hash(79, 0) as u32, 0, 0, false, false, false, false)
        }
        ZFCSetExpr::Singleton(e) => ExprMeta::mk_wrapper_meta(e.meta(), 83),
        ZFCSetExpr::Pair(a, b) => {
            let (am, bm) = (a.meta(), b.meta());
            let depth = (am.approx_depth().max(bm.approx_depth()) as u32 + 1).min(255);
            let range = am.loose_bvar_range().max(bm.loose_bvar_range());
            let h = mix_hash(89, mix_hash(am.hash() as u64, bm.hash() as u64)) as u32;
            ExprMeta::pack(
                h,
                range,
                depth,
                am.has_fvar() || bm.has_fvar(),
                am.has_expr_mvar() || bm.has_expr_mvar(),
                am.has_level_mvar() || bm.has_level_mvar(),
                am.has_level_param() || bm.has_level_param(),
            )
        }
        ZFCSetExpr::Union(e) => ExprMeta::mk_wrapper_meta(e.meta(), 97),
        ZFCSetExpr::PowerSet(e) => ExprMeta::mk_wrapper_meta(e.meta(), 101),
        ZFCSetExpr::Separation { set, pred } => {
            let (sm, pm) = (set.meta(), pred.meta());
            let depth = (sm.approx_depth().max(pm.approx_depth()) as u32 + 1).min(255);
            // pred is a binding construct (traversals use depth+1), so subtract 1
            // from its bvar range, matching mk_binder_meta pattern (line 464).
            let pred_range = pm.loose_bvar_range().saturating_sub(1);
            let range = sm.loose_bvar_range().max(pred_range);
            let h = mix_hash(103, mix_hash(sm.hash() as u64, pm.hash() as u64)) as u32;
            ExprMeta::pack(
                h,
                range,
                depth,
                sm.has_fvar() || pm.has_fvar(),
                sm.has_expr_mvar() || pm.has_expr_mvar(),
                sm.has_level_mvar() || pm.has_level_mvar(),
                sm.has_level_param() || pm.has_level_param(),
            )
        }
        ZFCSetExpr::Replacement { set, func } => {
            let (sm, fm) = (set.meta(), func.meta());
            let depth = (sm.approx_depth().max(fm.approx_depth()) as u32 + 1).min(255);
            // func is a binding construct (traversals use depth+1), so subtract 1
            // from its bvar range, matching mk_binder_meta pattern (line 464).
            let func_range = fm.loose_bvar_range().saturating_sub(1);
            let range = sm.loose_bvar_range().max(func_range);
            let h = mix_hash(107, mix_hash(sm.hash() as u64, fm.hash() as u64)) as u32;
            ExprMeta::pack(
                h,
                range,
                depth,
                sm.has_fvar() || fm.has_fvar(),
                sm.has_expr_mvar() || fm.has_expr_mvar(),
                sm.has_level_mvar() || fm.has_level_mvar(),
                sm.has_level_param() || fm.has_level_param(),
            )
        }
        ZFCSetExpr::Choice(e) => ExprMeta::mk_wrapper_meta(e.meta(), 109),
    }
}

/// Construct Expr from ExprKind, computing metadata. Module-internal shorthand.
#[inline(always)]
pub(crate) fn ek(kind: ExprKind) -> Expr {
    Expr::from_kind(kind)
}

/// Expression kind — the structural variants of expressions.
///
/// This enum represents the tree structure of Lean 5 expressions. It is wrapped
/// by the `Expr` struct which adds cached `ExprMeta` for O(1) hash/flags access.
///
/// # Migration Note
///
/// Previously named `Expr`. Code that pattern-matches on expressions should use:
/// ```text
/// match &expr.kind {
///     ExprKind::App(f, a) => { /* ... */ }
///     ExprKind::BVar(idx) => { /* ... */ }
///     // ...
/// }
/// ```
// Under Kani, use manual impls for Clone, PartialEq, Eq, Debug that only handle
// core variants (8-12 vs 20+). Derived impls generate match arms for all variants,
// causing CBMC to generate GOTO code and verification conditions for variants that
// harnesses never construct. This complements cfg(kani) overrides on compute_meta
// and fold_expr_opt_inner.
// ExprKind is always stored behind Arc<Expr> (heap-allocated). The size
// difference between Const(Name, SmallVec<[Level;2]>) and smaller variants
// doesn't cause stack bloat. Boxing the large variant would add a pointer
// chase on every constant lookup — unacceptable for sub-microsecond type checking.
#[cfg_attr(not(kani), derive(Clone, Eq, Debug))]
#[derive(Hash, Serialize, Deserialize)]
// The manual `PartialEq` below computes EXACTLY the derived structural relation
// (its `Arc::ptr_eq` fast path can only short-circuit pairs that are already
// structurally equal — same immutable allocation), so the derived `Hash` remains
// consistent with it (a == b ⇒ hash(a) == hash(b)); the lint's premise (manual
// eq might diverge from derived hash) does not apply.
#[allow(clippy::derived_hash_with_manual_eq)]
pub enum ExprKind {
    // ════════════════════════════════════════════════════════════════════════
    // CORE (all modes)
    // ════════════════════════════════════════════════════════════════════════
    /// Bound variable (de Bruijn index, 0 = innermost)
    BVar(u32),
    /// Free variable
    FVar(FVarId),
    /// Sort (Type u or Prop)
    Sort(Level),
    /// Constant with universe level instantiation
    Const(Name, LevelVec),
    /// Function application
    App(Arc<Expr>, Arc<Expr>),
    /// Lambda abstraction: λ (x : A), body
    Lam(BinderData, Arc<Expr>, Arc<Expr>),
    /// Pi/forall type: (x : A) → B
    Pi(BinderData, Arc<Expr>, Arc<Expr>),
    /// Let binding: let x : A := val in body
    /// Fields: (name, type, value, body, nonDep)
    /// nonDep=true means body doesn't depend on the let-bound variable (optimization hint)
    Let(Name, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool),
    /// Literal value
    Lit(Literal),
    /// Structure projection
    Proj(Name, u32, Arc<Expr>),
    /// Metadata wrapper (transparent to type checking)
    /// MData(metadata, inner_expr) - the metadata is carried but type is of inner_expr
    MData(MDataMap, Arc<Expr>),

    // ════════════════════════════════════════════════════════════════════════
    // IMPREDICATIVE MODE EXTENSIONS
    // These expressions are only valid in Impredicative mode (or Classical/SetTheoretic).
    // ════════════════════════════════════════════════════════════════════════
    /// Strict proposition sort (proof-irrelevant, no large elimination).
    /// SProp is always proof-irrelevant (unlike Prop which is only proof-irrelevant
    /// when proof irrelevance axiom is enabled).
    /// Mode: Impredicative
    SProp,

    /// Squash type (truncation to SProp).
    /// `Squash A` is a strict proposition that is inhabited iff A is inhabited.
    /// All proofs of `Squash A` are definitionally equal.
    /// Mode: Impredicative
    Squash(Arc<Expr>),

    // ════════════════════════════════════════════════════════════════════════
    // CUBICAL MODE EXTENSIONS
    // These expressions are only valid in Cubical mode.
    // ════════════════════════════════════════════════════════════════════════
    /// Interval type I with endpoints 0 and 1.
    /// Mode: Cubical
    CubicalInterval,

    /// Interval endpoint 0.
    /// Mode: Cubical
    CubicalI0,

    /// Interval endpoint 1.
    /// Mode: Cubical
    CubicalI1,

    /// Path type: Path A a b (heterogeneous equality).
    /// `ty` is `A : I -> Type`, `left` is `a : A 0`, `right` is `b : A 1`.
    /// Mode: Cubical
    CubicalPath {
        /// Type family A : I -> Type
        ty: Arc<Expr>,
        /// Left endpoint a : A 0
        left: Arc<Expr>,
        /// Right endpoint b : A 1
        right: Arc<Expr>,
    },

    /// Path lambda: `<i> e` (introduce a path by abstracting over interval).
    /// Mode: Cubical
    CubicalPathLam {
        /// Body expression with bound interval variable
        body: Arc<Expr>,
    },

    /// Path application: p @ i (apply a path to an interval point).
    /// Mode: Cubical
    CubicalPathApp {
        /// Path expression to apply
        path: Arc<Expr>,
        /// Interval argument
        arg: Arc<Expr>,
    },

    /// Homogeneous composition: hcomp {A} {φ} u base.
    /// Computes a filler for a partial element along a cofibration.
    /// Mode: Cubical
    CubicalHComp {
        /// Type to compose into
        ty: Arc<Expr>,
        /// Cofibration formula φ
        phi: Arc<Expr>,
        /// Partial element u
        u: Arc<Expr>,
        /// Base element at φ = 0
        base: Arc<Expr>,
    },

    /// Transport along a path: transp A φ base.
    /// Transports `base : A 0` to `A 1` along a line of types.
    /// Mode: Cubical
    CubicalTransp {
        /// Type family to transport along
        ty: Arc<Expr>,
        /// Cofibration where type is constant
        phi: Arc<Expr>,
        /// Element to transport
        base: Arc<Expr>,
    },

    /// Generalized coercion: coe A r s base.
    /// Coerces `base : A r` to `A s` along a line of types `A : I → Sort u`.
    /// This is the directed/parametrized generalization of `transp`
    /// (`transp A φ base` is `coe A i0 i1 base` for a line constant on `φ`).
    /// All four children are non-binders.
    /// Mode: Cubical
    CubicalCoe {
        /// Type family (line of types) `A : I → Sort u`
        ty: Arc<Expr>,
        /// Source interval endpoint `r : I`
        r: Arc<Expr>,
        /// Target interval endpoint `s : I`
        s: Arc<Expr>,
        /// Element to coerce: `base : A r`
        base: Arc<Expr>,
    },

    // ════════════════════════════════════════════════════════════════════════
    // SET-THEORETIC MODE EXTENSIONS
    // These expressions are only valid in SetTheoretic mode.
    // ════════════════════════════════════════════════════════════════════════
    /// ZFC set expression (various set constructions).
    /// Mode: SetTheoretic
    ZFCSet(ZFCSetExpr),

    /// Set membership: element ∈ set.
    /// Mode: SetTheoretic
    ZFCMem {
        /// Element to test
        element: Arc<Expr>,
        /// Set to test membership in
        set: Arc<Expr>,
    },

    /// Set comprehension: {x ∈ domain | pred x}.
    /// Mode: SetTheoretic
    ZFCComprehension {
        /// Domain set
        domain: Arc<Expr>,
        /// Predicate for inclusion
        pred: Arc<Expr>,
    },
}

/// DAG-aware structural equality of two `Arc<Expr>` children: a shared child
/// (the *same* heap allocation, common in the imported proof DAGs) resolves in
/// O(1) via `Arc::ptr_eq` instead of re-walking its whole subtree. This is
/// exactly Lean's `is_eqp` fast path (`kernel/expr.cpp`).
///
/// SOUNDNESS: `Arc::ptr_eq(a, b)` is true iff `a` and `b` are the same
/// allocation, and `Expr` is immutable after construction (`Expr::kind` is
/// `pub(crate)` precisely to forbid post-hoc mutation — issue #1397). Therefore
/// `Arc::ptr_eq(a, b) ⇒ **a == **b`, so the short-circuit returns *exactly* the
/// boolean the structural walk would return — it can never equate two
/// non-identical terms, it only skips a provably-redundant walk. `arc_eq(a, b)`
/// is thus definitionally `**a == **b`, only cheaper on shared DAGs. Pinned by
/// `test_manual_expr_kind_eq_matches_reference` (differential vs a ptr_eq-free
/// reference equality).
#[cfg(not(kani))]
#[inline]
fn arc_eq(a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    Arc::ptr_eq(a, b) || **a == **b
}

/// Manual `PartialEq` for `ExprKind` (non-Kani builds) that mirrors the derived
/// structural equality *exactly*, with the sole change that every `Arc<Expr>`
/// child is compared through [`arc_eq`] — adding the `Arc::ptr_eq` short-circuit
/// so the trusted kernel's structural equality (and hence every `whnf` /
/// `is_def_eq` structural check) walks the imported proof term as the shared DAG
/// it is, not as an exponentially-larger tree (see
/// `designs/2026-07-06-carrier-whnf-perf.md`). Non-`Arc` fields compare with
/// `==`, identical to the derived impl.
#[cfg(not(kani))]
impl PartialEq for ExprKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ExprKind::BVar(a), ExprKind::BVar(b)) => a == b,
            (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
            (ExprKind::Sort(a), ExprKind::Sort(b)) => a == b,
            (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => arc_eq(f1, f2) && arc_eq(a1, a2),
            (ExprKind::Lam(b1, t1, bo1), ExprKind::Lam(b2, t2, bo2)) => {
                b1 == b2 && arc_eq(t1, t2) && arc_eq(bo1, bo2)
            }
            (ExprKind::Pi(b1, t1, bo1), ExprKind::Pi(b2, t2, bo2)) => {
                b1 == b2 && arc_eq(t1, t2) && arc_eq(bo1, bo2)
            }
            (ExprKind::Let(n1, t1, v1, bo1, d1), ExprKind::Let(n2, t2, v2, bo2, d2)) => {
                n1 == n2 && arc_eq(t1, t2) && arc_eq(v1, v2) && arc_eq(bo1, bo2) && d1 == d2
            }
            (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && arc_eq(e1, e2)
            }
            (ExprKind::MData(m1, e1), ExprKind::MData(m2, e2)) => m1 == m2 && arc_eq(e1, e2),
            (ExprKind::SProp, ExprKind::SProp) => true,
            (ExprKind::Squash(e1), ExprKind::Squash(e2)) => arc_eq(e1, e2),
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval) => true,
            (ExprKind::CubicalI0, ExprKind::CubicalI0) => true,
            (ExprKind::CubicalI1, ExprKind::CubicalI1) => true,
            (
                ExprKind::CubicalPath {
                    ty: t1,
                    left: l1,
                    right: r1,
                },
                ExprKind::CubicalPath {
                    ty: t2,
                    left: l2,
                    right: r2,
                },
            ) => arc_eq(t1, t2) && arc_eq(l1, l2) && arc_eq(r1, r2),
            (ExprKind::CubicalPathLam { body: b1 }, ExprKind::CubicalPathLam { body: b2 }) => {
                arc_eq(b1, b2)
            }
            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => arc_eq(p1, p2) && arc_eq(a1, a2),
            (
                ExprKind::CubicalHComp {
                    ty: t1,
                    phi: p1,
                    u: u1,
                    base: ba1,
                },
                ExprKind::CubicalHComp {
                    ty: t2,
                    phi: p2,
                    u: u2,
                    base: ba2,
                },
            ) => arc_eq(t1, t2) && arc_eq(p1, p2) && arc_eq(u1, u2) && arc_eq(ba1, ba2),
            (
                ExprKind::CubicalTransp {
                    ty: t1,
                    phi: p1,
                    base: ba1,
                },
                ExprKind::CubicalTransp {
                    ty: t2,
                    phi: p2,
                    base: ba2,
                },
            ) => arc_eq(t1, t2) && arc_eq(p1, p2) && arc_eq(ba1, ba2),
            (
                ExprKind::CubicalCoe {
                    ty: t1,
                    r: r1,
                    s: s1,
                    base: ba1,
                },
                ExprKind::CubicalCoe {
                    ty: t2,
                    r: r2,
                    s: s2,
                    base: ba2,
                },
            ) => arc_eq(t1, t2) && arc_eq(r1, r2) && arc_eq(s1, s2) && arc_eq(ba1, ba2),
            (ExprKind::ZFCSet(a), ExprKind::ZFCSet(b)) => a == b,
            (
                ExprKind::ZFCMem {
                    element: e1,
                    set: s1,
                },
                ExprKind::ZFCMem {
                    element: e2,
                    set: s2,
                },
            ) => arc_eq(e1, e2) && arc_eq(s1, s2),
            (
                ExprKind::ZFCComprehension {
                    domain: d1,
                    pred: p1,
                },
                ExprKind::ZFCComprehension {
                    domain: d2,
                    pred: p2,
                },
            ) => arc_eq(d1, d2) && arc_eq(p1, p2),
            // Different variants are never equal. Enumerated tuple arms above
            // are exhaustive over same-variant pairs; any (X, Y) with X≠Y falls
            // here, matching the derived impl.
            _ => false,
        }
    }
}

/// Kani Clone: only handles variants constructed by harnesses.
/// Reduces CBMC per-clone branching from 20+ to 8 core variants.
/// Matches the variant set in fold_expr_opt_inner_core and compute_meta.
#[cfg(kani)]
impl Clone for ExprKind {
    fn clone(&self) -> Self {
        match self {
            ExprKind::BVar(idx) => ExprKind::BVar(*idx),
            ExprKind::FVar(id) => ExprKind::FVar(*id),
            ExprKind::Sort(level) => ExprKind::Sort(level.clone()),
            ExprKind::Const(name, levels) => ExprKind::Const(name.clone(), levels.clone()),
            ExprKind::App(f, a) => ExprKind::App(f.clone(), a.clone()),
            ExprKind::Lam(bi, ty, body) => ExprKind::Lam(*bi, ty.clone(), body.clone()),
            ExprKind::Pi(bi, ty, body) => ExprKind::Pi(*bi, ty.clone(), body.clone()),
            ExprKind::Lit(lit) => ExprKind::Lit(lit.clone()),
            // Trivial unit-like variants reachable via fold_expr_opt_inner_core wildcard:
            ExprKind::SProp => ExprKind::SProp,
            ExprKind::CubicalInterval => ExprKind::CubicalInterval,
            ExprKind::CubicalI0 => ExprKind::CubicalI0,
            ExprKind::CubicalI1 => ExprKind::CubicalI1,
            _ => unreachable!("Kani harnesses only construct core ExprKind variants"),
        }
    }
}

/// Kani PartialEq: only handles variants constructed by harnesses.
/// Expr::PartialEq (mod.rs) calls `self.kind == other.kind` after a metadata
/// pre-filter. The derived PartialEq matches all 20+ variants, generating CBMC
/// verification conditions for comparison paths that harnesses never exercise.
#[cfg(kani)]
impl PartialEq for ExprKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ExprKind::BVar(a), ExprKind::BVar(b)) => a == b,
            (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
            (ExprKind::Sort(a), ExprKind::Sort(b)) => a == b,
            (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => f1 == f2 && a1 == a2,
            (ExprKind::Lam(b1, t1, bo1), ExprKind::Lam(b2, t2, bo2)) => {
                b1 == b2 && t1 == t2 && bo1 == bo2
            }
            (ExprKind::Pi(b1, t1, bo1), ExprKind::Pi(b2, t2, bo2)) => {
                b1 == b2 && t1 == t2 && bo1 == bo2
            }
            (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
            (ExprKind::SProp, ExprKind::SProp) => true,
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval) => true,
            (ExprKind::CubicalI0, ExprKind::CubicalI0) => true,
            (ExprKind::CubicalI1, ExprKind::CubicalI1) => true,
            _ => false, // Different variants or unsupported under Kani
        }
    }
}

#[cfg(kani)]
impl Eq for ExprKind {}

/// Kani Debug: only handles variants constructed by harnesses.
/// The derived Debug recursively formats all 20+ variants including Arc<Expr>
/// children, which CBMC must model even if Debug is never called from harnesses.
/// Reducing to core variants shrinks the GOTO binary that --slice-formula processes.
#[cfg(kani)]
impl std::fmt::Debug for ExprKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprKind::BVar(idx) => write!(f, "BVar({idx})"),
            ExprKind::FVar(id) => write!(f, "FVar({:?})", id),
            ExprKind::Sort(level) => write!(f, "Sort({level:?})"),
            ExprKind::Const(name, levels) => write!(f, "Const({name:?}, {levels:?})"),
            ExprKind::App(func, arg) => write!(f, "App({func:?}, {arg:?})"),
            ExprKind::Lam(bi, ty, body) => write!(f, "Lam({bi:?}, {ty:?}, {body:?})"),
            ExprKind::Pi(bi, ty, body) => write!(f, "Pi({bi:?}, {ty:?}, {body:?})"),
            ExprKind::Lit(lit) => write!(f, "Lit({lit:?})"),
            ExprKind::SProp => write!(f, "SProp"),
            ExprKind::CubicalInterval => write!(f, "CubicalInterval"),
            ExprKind::CubicalI0 => write!(f, "CubicalI0"),
            ExprKind::CubicalI1 => write!(f, "CubicalI1"),
            _ => write!(f, "ExprKind(<non-core variant>)"),
        }
    }
}

/// ZFC set expressions for SetTheoretic mode.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ZFCSetExpr {
    /// Empty set: ∅
    Empty,
    /// Singleton set: {a}
    Singleton(Arc<Expr>),
    /// Unordered pair: {a, b}
    Pair(Arc<Expr>, Arc<Expr>),
    /// Union: ⋃A (union of all sets in A)
    Union(Arc<Expr>),
    /// Power set: P(A) (set of all subsets of A)
    PowerSet(Arc<Expr>),
    /// Separation: {x ∈ A | φ(x)}
    Separation {
        /// Source set A
        set: Arc<Expr>,
        /// Selection predicate φ
        pred: Arc<Expr>,
    },
    /// Replacement: {F(x) | x ∈ A}
    Replacement {
        /// Source set A
        set: Arc<Expr>,
        /// Replacement function F
        func: Arc<Expr>,
    },
    /// Infinity: ω (the first infinite ordinal)
    Infinity,
    /// Choice function application
    Choice(Arc<Expr>),
}

impl ZFCSetExpr {
    /// Check if expression has loose bound variables in range [start, end)
    pub(crate) fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
        if end != u32::MAX && start >= end {
            return false;
        }
        match self {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => false,
            ZFCSetExpr::Singleton(e) => e.has_loose_bvar_in_range(start, end),
            ZFCSetExpr::Pair(a, b) => {
                a.has_loose_bvar_in_range(start, end) || b.has_loose_bvar_in_range(start, end)
            }
            ZFCSetExpr::Union(e) | ZFCSetExpr::PowerSet(e) | ZFCSetExpr::Choice(e) => {
                e.has_loose_bvar_in_range(start, end)
            }
            ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
                let pred_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        pred.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                set.has_loose_bvar_in_range(start, end) || pred_has_loose
            }
        }
    }

    /// Collect all constant names referenced in this ZFC expression
    pub(crate) fn collect_constants_into(&self, result: &mut std::collections::HashSet<Name>) {
        match self {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
            ZFCSetExpr::Singleton(e)
            | ZFCSetExpr::Union(e)
            | ZFCSetExpr::PowerSet(e)
            | ZFCSetExpr::Choice(e) => {
                e.collect_constants_into(result);
            }
            ZFCSetExpr::Pair(a, b) => {
                a.collect_constants_into(result);
                b.collect_constants_into(result);
            }
            ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
                set.collect_constants_into(result);
                pred.collect_constants_into(result);
            }
        }
    }

    /// Abstract: replace FVar(id) with BVar(depth), shifting other bound variables up
    pub(crate) fn abstract_fvar_at(&self, id: FVarId, depth: u32) -> Self {
        match self {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => self.clone(),
            ZFCSetExpr::Singleton(e) => {
                ZFCSetExpr::Singleton(Arc::new(e.abstract_fvar_at(id, depth)))
            }
            ZFCSetExpr::Pair(a, b) => ZFCSetExpr::Pair(
                Arc::new(a.abstract_fvar_at(id, depth)),
                Arc::new(b.abstract_fvar_at(id, depth)),
            ),
            ZFCSetExpr::Union(e) => ZFCSetExpr::Union(Arc::new(e.abstract_fvar_at(id, depth))),
            ZFCSetExpr::PowerSet(e) => {
                ZFCSetExpr::PowerSet(Arc::new(e.abstract_fvar_at(id, depth)))
            }
            ZFCSetExpr::Separation { set, pred } => ZFCSetExpr::Separation {
                set: Arc::new(set.abstract_fvar_at(id, depth)),
                pred: Arc::new(
                    pred.abstract_fvar_at(id, checked_add_u32(depth, 1, "abstract_fvar depth")),
                ),
            },
            ZFCSetExpr::Replacement { set, func } => ZFCSetExpr::Replacement {
                set: Arc::new(set.abstract_fvar_at(id, depth)),
                func: Arc::new(
                    func.abstract_fvar_at(id, checked_add_u32(depth, 1, "abstract_fvar depth")),
                ),
            },
            ZFCSetExpr::Choice(e) => ZFCSetExpr::Choice(Arc::new(e.abstract_fvar_at(id, depth))),
        }
    }
}

impl ExprKind {
    /// Compute metadata for this expression kind (O(1) — reads cached meta from children).
    ///
    /// Children stored in `Arc<Expr>` already carry cached metadata, so this
    /// only combines children's metadata — no recursive tree traversal.
    ///
    /// Called by `Expr::from_kind()` at construction time.
    /// Compute expression metadata from the kind.
    ///
    /// Under Kani, only handles the 7 core ExprKind variants constructed in
    /// Kani harnesses. This eliminates CBMC's need to model metadata paths for
    /// Let, MData, Proj, Squash, Cubical, and ZFC variants — reducing per-node
    /// branching in every `ek()` / `Expr::from_kind()` call.
    pub(crate) fn compute_meta(&self) -> ExprMeta {
        #[cfg(kani)]
        {
            match self {
                ExprKind::BVar(idx) => ExprMeta::pack(
                    mix_hash(7, *idx as u64) as u32,
                    idx.saturating_add(1),
                    0,
                    false,
                    false,
                    false,
                    false,
                ),
                ExprKind::FVar(id) => {
                    ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
                }
                ExprKind::Sort(lvl) => ExprMeta::pack(
                    mix_hash(11, hash_to_u64(lvl)) as u32,
                    0,
                    0,
                    false,
                    false,
                    level_has_mvar(lvl),
                    lvl.has_params(),
                ),
                ExprKind::Const(name, levels) => {
                    let name_hash = hash_to_u64(name);
                    let levels_hash = hash_to_u64(levels);
                    let has_level_param = levels.iter().any(|l| l.has_params());
                    let has_level_mvar = levels.iter().any(level_has_mvar);
                    ExprMeta::pack(
                        mix_hash(5, mix_hash(name_hash, levels_hash)) as u32,
                        0,
                        0,
                        false,
                        false,
                        has_level_mvar,
                        has_level_param,
                    )
                }
                ExprKind::App(f, a) => ExprMeta::mk_app_meta(f.meta(), a.meta()),
                ExprKind::Lam(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 0),
                ExprKind::Pi(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 1),
                ExprKind::Lit(lit) => ExprMeta::pack(
                    mix_hash(3, hash_to_u64(lit)) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    false,
                ),
                _ => unreachable!(
                    "Kani harnesses only construct BVar/FVar/Sort/Const/App/Lam/Pi/Lit"
                ),
            }
        }
        #[cfg(not(kani))]
        {
            match self {
                ExprKind::BVar(idx) => ExprMeta::pack(
                    mix_hash(7, *idx as u64) as u32,
                    idx.saturating_add(1), // loose_bvar_range = idx + 1
                    0,
                    false,
                    false,
                    false,
                    false,
                ),
                ExprKind::FVar(id) => {
                    ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
                }
                ExprKind::Sort(lvl) => ExprMeta::pack(
                    mix_hash(11, hash_to_u64(lvl)) as u32,
                    0,
                    0,
                    false,
                    false,
                    level_has_mvar(lvl),
                    lvl.has_params(),
                ),
                ExprKind::Const(name, levels) => {
                    let name_hash = hash_to_u64(name);
                    let levels_hash = hash_to_u64(levels);
                    let has_level_param = levels.iter().any(|l| l.has_params());
                    let has_level_mvar = levels.iter().any(level_has_mvar);
                    ExprMeta::pack(
                        mix_hash(5, mix_hash(name_hash, levels_hash)) as u32,
                        0,
                        0,
                        false,
                        false,
                        has_level_mvar,
                        has_level_param,
                    )
                }
                ExprKind::App(f, a) => ExprMeta::mk_app_meta(f.meta(), a.meta()),
                ExprKind::Lam(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 0),
                ExprKind::Pi(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 1),
                ExprKind::Let(_, ty, val, body, _) => {
                    ExprMeta::mk_let_meta(ty.meta(), val.meta(), body.meta())
                }
                ExprKind::Lit(lit) => ExprMeta::pack(
                    mix_hash(3, hash_to_u64(lit)) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    false,
                ),
                ExprKind::Proj(name, idx, expr) => {
                    let inner = expr.meta();
                    let depth = (inner.approx_depth() as u32 + 1).min(255);
                    let h = mix_hash(
                        depth as u64,
                        mix_hash(
                            hash_to_u64(name),
                            mix_hash(*idx as u64, inner.hash() as u64),
                        ),
                    ) as u32;
                    ExprMeta::pack(
                        h,
                        inner.loose_bvar_range(),
                        depth,
                        inner.has_fvar(),
                        inner.has_expr_mvar(),
                        inner.has_level_mvar(),
                        inner.has_level_param(),
                    )
                }
                ExprKind::MData(_, expr) => ExprMeta::mk_wrapper_meta(expr.meta(), 0),
                // Leaf extensions: distinct hash seeds, no children so no flags.
                ExprKind::SProp => {
                    ExprMeta::pack(mix_hash(19, 0) as u32, 0, 0, false, false, false, false)
                }
                ExprKind::CubicalInterval => {
                    ExprMeta::pack(mix_hash(23, 0) as u32, 0, 0, false, false, false, false)
                }
                ExprKind::CubicalI0 => {
                    ExprMeta::pack(mix_hash(29, 0) as u32, 0, 0, false, false, false, false)
                }
                ExprKind::CubicalI1 => {
                    ExprMeta::pack(mix_hash(31, 0) as u32, 0, 0, false, false, false, false)
                }
                ExprKind::Squash(e) => ExprMeta::mk_wrapper_meta(e.meta(), 0),
                ExprKind::CubicalPath { ty, left, right } => {
                    let (tm, lm, rm) = (ty.meta(), left.meta(), right.meta());
                    let depth = (tm
                        .approx_depth()
                        .max(lm.approx_depth())
                        .max(rm.approx_depth()) as u32
                        + 1)
                    .min(255);
                    let range = tm
                        .loose_bvar_range()
                        .max(lm.loose_bvar_range())
                        .max(rm.loose_bvar_range());
                    let h = mix_hash(
                        37,
                        mix_hash(
                            tm.hash() as u64,
                            mix_hash(lm.hash() as u64, rm.hash() as u64),
                        ),
                    ) as u32;
                    ExprMeta::pack(
                        h,
                        range,
                        depth,
                        tm.has_fvar() || lm.has_fvar() || rm.has_fvar(),
                        tm.has_expr_mvar() || lm.has_expr_mvar() || rm.has_expr_mvar(),
                        tm.has_level_mvar() || lm.has_level_mvar() || rm.has_level_mvar(),
                        tm.has_level_param() || lm.has_level_param() || rm.has_level_param(),
                    )
                }
                ExprKind::CubicalPathLam { body } => {
                    // CubicalPathLam binds an interval variable, so loose_bvar_range
                    // must be decremented by 1 (matching binder semantics). Fix: #1362.
                    let bm = body.meta();
                    let depth = (bm.approx_depth() as u32 + 1).min(ExprMeta::MAX_DEPTH);
                    let h = mix_hash(depth as u64, mix_hash(bm.hash() as u64, 41)) as u32;
                    ExprMeta::pack(
                        h,
                        bm.loose_bvar_range().saturating_sub(1),
                        depth,
                        bm.has_fvar(),
                        bm.has_expr_mvar(),
                        bm.has_level_mvar(),
                        bm.has_level_param(),
                    )
                }
                ExprKind::CubicalPathApp { path, arg } => {
                    ExprMeta::mk_app_meta(path.meta(), arg.meta())
                }
                ExprKind::CubicalHComp { ty, phi, u, base } => {
                    let (tm, pm, um, bm) = (ty.meta(), phi.meta(), u.meta(), base.meta());
                    let depth = (tm
                        .approx_depth()
                        .max(pm.approx_depth())
                        .max(um.approx_depth())
                        .max(bm.approx_depth()) as u32
                        + 1)
                    .min(255);
                    let range = tm
                        .loose_bvar_range()
                        .max(pm.loose_bvar_range())
                        .max(um.loose_bvar_range())
                        .max(bm.loose_bvar_range());
                    let h = mix_hash(
                        43,
                        mix_hash(
                            tm.hash() as u64,
                            mix_hash(
                                pm.hash() as u64,
                                mix_hash(um.hash() as u64, bm.hash() as u64),
                            ),
                        ),
                    ) as u32;
                    ExprMeta::pack(
                        h,
                        range,
                        depth,
                        tm.has_fvar() || pm.has_fvar() || um.has_fvar() || bm.has_fvar(),
                        tm.has_expr_mvar()
                            || pm.has_expr_mvar()
                            || um.has_expr_mvar()
                            || bm.has_expr_mvar(),
                        tm.has_level_mvar()
                            || pm.has_level_mvar()
                            || um.has_level_mvar()
                            || bm.has_level_mvar(),
                        tm.has_level_param()
                            || pm.has_level_param()
                            || um.has_level_param()
                            || bm.has_level_param(),
                    )
                }
                ExprKind::CubicalTransp { ty, phi, base } => {
                    let (tm, pm, bm) = (ty.meta(), phi.meta(), base.meta());
                    let depth = (tm
                        .approx_depth()
                        .max(pm.approx_depth())
                        .max(bm.approx_depth()) as u32
                        + 1)
                    .min(255);
                    let range = tm
                        .loose_bvar_range()
                        .max(pm.loose_bvar_range())
                        .max(bm.loose_bvar_range());
                    let h = mix_hash(
                        47,
                        mix_hash(
                            tm.hash() as u64,
                            mix_hash(pm.hash() as u64, bm.hash() as u64),
                        ),
                    ) as u32;
                    ExprMeta::pack(
                        h,
                        range,
                        depth,
                        tm.has_fvar() || pm.has_fvar() || bm.has_fvar(),
                        tm.has_expr_mvar() || pm.has_expr_mvar() || bm.has_expr_mvar(),
                        tm.has_level_mvar() || pm.has_level_mvar() || bm.has_level_mvar(),
                        tm.has_level_param() || pm.has_level_param() || bm.has_level_param(),
                    )
                }
                ExprKind::CubicalCoe { ty, r, s, base } => {
                    let (tm, rm, sm, bm) = (ty.meta(), r.meta(), s.meta(), base.meta());
                    let depth = (tm
                        .approx_depth()
                        .max(rm.approx_depth())
                        .max(sm.approx_depth())
                        .max(bm.approx_depth()) as u32
                        + 1)
                    .min(255);
                    let range = tm
                        .loose_bvar_range()
                        .max(rm.loose_bvar_range())
                        .max(sm.loose_bvar_range())
                        .max(bm.loose_bvar_range());
                    let h = mix_hash(
                        53,
                        mix_hash(
                            tm.hash() as u64,
                            mix_hash(
                                rm.hash() as u64,
                                mix_hash(sm.hash() as u64, bm.hash() as u64),
                            ),
                        ),
                    ) as u32;
                    ExprMeta::pack(
                        h,
                        range,
                        depth,
                        tm.has_fvar() || rm.has_fvar() || sm.has_fvar() || bm.has_fvar(),
                        tm.has_expr_mvar()
                            || rm.has_expr_mvar()
                            || sm.has_expr_mvar()
                            || bm.has_expr_mvar(),
                        tm.has_level_mvar()
                            || rm.has_level_mvar()
                            || sm.has_level_mvar()
                            || bm.has_level_mvar(),
                        tm.has_level_param()
                            || rm.has_level_param()
                            || sm.has_level_param()
                            || bm.has_level_param(),
                    )
                }
                ExprKind::ZFCSet(set_expr) => zfc_set_expr_meta(set_expr),
                ExprKind::ZFCMem { element, set } => {
                    let (em, sm) = (element.meta(), set.meta());
                    let depth = (em.approx_depth().max(sm.approx_depth()) as u32 + 1).min(255);
                    let range = em.loose_bvar_range().max(sm.loose_bvar_range());
                    let h = mix_hash(67, mix_hash(em.hash() as u64, sm.hash() as u64)) as u32;
                    ExprMeta::pack(
                        h,
                        range,
                        depth,
                        em.has_fvar() || sm.has_fvar(),
                        em.has_expr_mvar() || sm.has_expr_mvar(),
                        em.has_level_mvar() || sm.has_level_mvar(),
                        em.has_level_param() || sm.has_level_param(),
                    )
                }
                ExprKind::ZFCComprehension { domain, pred } => {
                    let (dm, pm) = (domain.meta(), pred.meta());
                    let depth = (dm.approx_depth().max(pm.approx_depth()) as u32 + 1).min(255);
                    // pred is a binding construct (traversals use depth+1), so subtract 1
                    // from its bvar range, matching Separation/Replacement patterns above.
                    let pred_range = pm.loose_bvar_range().saturating_sub(1);
                    let range = dm.loose_bvar_range().max(pred_range);
                    let h = mix_hash(71, mix_hash(dm.hash() as u64, pm.hash() as u64)) as u32;
                    ExprMeta::pack(
                        h,
                        range,
                        depth,
                        dm.has_fvar() || pm.has_fvar(),
                        dm.has_expr_mvar() || pm.has_expr_mvar(),
                        dm.has_level_mvar() || pm.has_level_mvar(),
                        dm.has_level_param() || pm.has_level_param(),
                    )
                }
            }
        }
    }
}

#[cfg(all(test, not(kani)))]
mod arc_eq_tests {
    //! Differential validation of the manual `Arc::ptr_eq`-short-circuiting
    //! `PartialEq for ExprKind` (F1, `designs/2026-07-06-carrier-whnf-perf.md`).
    //! The manual impl MUST compute the identical boolean the derived structural
    //! equality would, only faster on shared DAGs. We prove this against an
    //! INDEPENDENT structural oracle — the derived `Debug` string, which encodes
    //! an expr's full structure (Arc children recurse) and is byte-equal iff two
    //! exprs are structurally equal — so it cannot share the bug being tested.

    use super::*;
    use crate::expr::types::{Literal, MDataValue};
    use crate::expr::BinderInfo;
    use crate::expr::{Expr, FVarId};
    use crate::level::Level;
    use crate::name::Name;

    fn leaf(k: u32) -> Arc<Expr> {
        Arc::new(Expr::bvar(k))
    }

    /// One representative of EVERY `ExprKind` variant, built with FRESH child
    /// allocations on each call (so two calls produce structurally-equal,
    /// pointer-DISTINCT terms — the case that exercises the structural fallback,
    /// not the `ptr_eq` fast path). Distinct bvar indices per child position so a
    /// swapped-field bug in any arm changes the structure detectably.
    fn one_of_each_variant() -> Vec<Expr> {
        let bd = BinderData::from(BinderInfo::Default);
        vec![
            Expr::bvar(0),
            Expr::fvar(FVarId::new(0)),
            Expr::sort(Level::zero()),
            Expr::const_(Name::from_string("C"), vec![Level::zero()]),
            Expr::from_kind(ExprKind::App(leaf(1), leaf(2))),
            Expr::from_kind(ExprKind::Lam(bd, leaf(3), leaf(4))),
            Expr::from_kind(ExprKind::Pi(bd, leaf(5), leaf(6))),
            Expr::from_kind(ExprKind::Let(
                Name::from_string("x"),
                leaf(7),
                leaf(8),
                leaf(9),
                false,
            )),
            Expr::from_kind(ExprKind::Lit(Literal::nat(0))),
            Expr::from_kind(ExprKind::Proj(Name::from_string("S"), 1, leaf(10))),
            Expr::from_kind(ExprKind::MData(
                vec![(Name::from_string("k"), MDataValue::Bool(true))],
                leaf(11),
            )),
            Expr::from_kind(ExprKind::SProp),
            Expr::from_kind(ExprKind::Squash(leaf(12))),
            Expr::from_kind(ExprKind::CubicalInterval),
            Expr::from_kind(ExprKind::CubicalI0),
            Expr::from_kind(ExprKind::CubicalI1),
            Expr::from_kind(ExprKind::CubicalPath {
                ty: leaf(13),
                left: leaf(14),
                right: leaf(15),
            }),
            Expr::from_kind(ExprKind::CubicalPathLam { body: leaf(16) }),
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: leaf(17),
                arg: leaf(18),
            }),
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: leaf(19),
                phi: leaf(20),
                u: leaf(21),
                base: leaf(22),
            }),
            Expr::from_kind(ExprKind::CubicalTransp {
                ty: leaf(23),
                phi: leaf(24),
                base: leaf(25),
            }),
            Expr::from_kind(ExprKind::CubicalCoe {
                ty: leaf(26),
                r: leaf(27),
                s: leaf(28),
                base: leaf(29),
            }),
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty)),
            Expr::from_kind(ExprKind::ZFCMem {
                element: leaf(30),
                set: leaf(31),
            }),
            Expr::from_kind(ExprKind::ZFCComprehension {
                domain: leaf(32),
                pred: leaf(33),
            }),
        ]
    }

    /// The manual `==` agrees with the independent `Debug`-string structural
    /// oracle on ALL pairs of an every-variant battery. A missing same-variant
    /// arm (would return `false` for equal terms), a swapped-field arm, or an
    /// over-broad arm all surface here as a disagreement.
    #[test]
    fn test_manual_expr_kind_eq_matches_reference() {
        // Two independent constructions → structurally identical, ptr-distinct.
        let a = one_of_each_variant();
        let b = one_of_each_variant();
        assert_eq!(a.len(), 25, "battery must cover every ExprKind variant");

        let oracle = |x: &Expr, y: &Expr| format!("{x:?}") == format!("{y:?}");

        for (i, ai) in a.iter().enumerate() {
            for (j, bj) in b.iter().enumerate() {
                let manual = ai == bj;
                let structural = oracle(ai, bj);
                assert_eq!(
                    manual, structural,
                    "manual ExprKind::eq disagrees with structural oracle at \
                     (variant {i} vs {j}): manual={manual} structural={structural}\n  \
                     a={ai:?}\n  b={bj:?}"
                );
                if i == j {
                    // Same variant, distinct allocations, equal structure: the
                    // structural fallback MUST return true (guards against a
                    // missing same-variant arm falling through to `_ => false`).
                    assert!(manual, "reflexive equality failed for variant {i}: {ai:?}");
                }
            }
        }
    }

    /// The `Arc::ptr_eq` fast path fires for a genuinely shared child and returns
    /// the same verdict as the structural walk. Also confirms it never
    /// over-equates: two DIFFERENT terms that SHARE a sub-Arc stay unequal.
    #[test]
    fn test_ptr_eq_shortcircuit_is_verdict_preserving() {
        let shared = leaf(99);
        // `App(shared, shared)` — the two children are the same allocation.
        let dag = Expr::from_kind(ExprKind::App(shared.clone(), shared.clone()));
        // A structural twin with DISTINCT child allocations.
        let twin = Expr::from_kind(ExprKind::App(leaf(99), leaf(99)));
        assert_eq!(
            dag, twin,
            "ptr_eq path and structural path must agree (equal)"
        );

        // Two DIFFERENT terms sharing the `shared` sub-Arc must remain unequal —
        // ptr_eq on the shared child must not leak into the parent verdict.
        let p = Expr::from_kind(ExprKind::App(shared.clone(), leaf(1)));
        let q = Expr::from_kind(ExprKind::App(shared, leaf(2)));
        assert_ne!(p, q, "shared sub-term must not force parent equality");
    }

    /// Deeply-shared DAG: a subterm reused K times must compare equal to its
    /// fully-distinct structural expansion (the exact shape F1 accelerates).
    #[test]
    fn test_deep_shared_dag_equals_expanded() {
        let mut shared = leaf(0);
        let mut expanded: Arc<Expr> = leaf(0);
        for _ in 0..6 {
            shared = Arc::new(Expr::from_kind(ExprKind::App(
                shared.clone(),
                shared.clone(),
            )));
            let e = expanded.clone();
            // Distinct allocation for each child, same structure.
            let e2 = Arc::new((*e).clone());
            expanded = Arc::new(Expr::from_kind(ExprKind::App(e, e2)));
        }
        assert_eq!(
            *shared, *expanded,
            "shared DAG must equal its tree expansion"
        );
    }
}
