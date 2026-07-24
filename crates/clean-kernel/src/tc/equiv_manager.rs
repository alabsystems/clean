// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates

//! Union-find equivalence manager for definitional equality caching.
//!
//! Lean 4 reference: `src/kernel/equiv_manager.{h,cpp}` (Leonardo de Moura, 2015)
//!
//! Unlike the HashMap-based `def_eq_cache` which stores per-call results,
//! this accumulates equivalence knowledge across `is_def_eq` calls within
//! a TypeChecker session. After proving `is_def_eq(A, B)`, any future query
//! returns in O(α(n)) — effectively O(1).

#[cfg(kani)]
use super::KaniBuildHasher;
use crate::expr::{stack_safe, Expr, ExprKind, ZFCSetExpr};
#[cfg(kani)]
use std::collections::HashMap;

type NodeRef = u32;
struct Node {
    parent: NodeRef,
    rank: u32,
}

// Kani: deterministic hasher (#982). Production: ahash for pre-hashed Expr keys (#2409).
#[cfg(not(kani))]
type EquivHashMap<K, V> = hashbrown::HashMap<K, V, ahash::RandomState>;
#[cfg(kani)]
type EquivHashMap<K, V> = HashMap<K, V, KaniBuildHasher>;

/// Union-find equivalence manager for expression equality.
///
/// Follows Lean 4's `equiv_manager` design: a union-find forest keyed by
/// expression identity, with structural equality fallback that merges nodes
/// on success.
pub(crate) struct EquivManager {
    nodes: Vec<Node>,
    /// Maps expression to node index. Uses Expr's O(1) cached hash +
    /// structural PartialEq (hash pre-filter rejects most mismatches in O(1)).
    to_node: EquivHashMap<Expr, NodeRef>,
}

impl Default for EquivManager {
    fn default() -> Self {
        Self::new()
    }
}

impl EquivManager {
    pub(crate) fn new() -> Self {
        EquivManager {
            nodes: Vec::new(),
            to_node: Default::default(),
        }
    }

    /// Check if two expressions are known-equivalent.
    ///
    /// Returns true if they are in the same equivalence class,
    /// or if they are structurally equal (recording the equivalence).
    /// Uses hash pre-filter when `use_hash` is true.
    pub(crate) fn is_equiv(&mut self, a: &Expr, b: &Expr, use_hash: bool) -> bool {
        self.is_equiv_core(a, b, use_hash)
    }

    /// Record that two expressions are definitionally equal.
    pub(crate) fn add_equiv(&mut self, a: &Expr, b: &Expr) {
        let r1 = self.get_or_insert_node(a);
        let r2 = self.get_or_insert_node(b);
        self.merge(r1, r2);
    }

    /// Clear all equivalence data. Called on context mutation.
    pub(crate) fn clear(&mut self) {
        self.nodes.clear();
        self.to_node.clear();
    }

    /// Number of tracked expressions (for diagnostics).
    pub(crate) fn len(&self) -> usize {
        self.to_node.len()
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.to_node.is_empty()
    }

    fn mk_node(&mut self) -> NodeRef {
        let r = u32::try_from(self.nodes.len())
            .expect("invariant: EquivManager node count fits in u32");
        self.nodes.push(Node { parent: r, rank: 0 });
        r
    }

    /// Find root with path compression (O(α(n)) amortized).
    fn find(&mut self, mut n: NodeRef) -> NodeRef {
        // Find root
        let mut root = n;
        while self.nodes[root as usize].parent != root {
            root = self.nodes[root as usize].parent;
        }
        // Path compression
        while self.nodes[n as usize].parent != root {
            let next = self.nodes[n as usize].parent;
            self.nodes[n as usize].parent = root;
            n = next;
        }
        root
    }

    /// Union by rank.
    fn merge(&mut self, n1: NodeRef, n2: NodeRef) {
        let r1 = self.find(n1);
        let r2 = self.find(n2);
        if r1 != r2 {
            let rank1 = self.nodes[r1 as usize].rank;
            let rank2 = self.nodes[r2 as usize].rank;
            if rank1 < rank2 {
                self.nodes[r1 as usize].parent = r2;
            } else if rank1 > rank2 {
                self.nodes[r2 as usize].parent = r1;
            } else {
                self.nodes[r2 as usize].parent = r1;
                self.nodes[r1 as usize].rank += 1;
            }
        }
    }

    /// Get or create a node for an expression.
    fn get_or_insert_node(&mut self, e: &Expr) -> NodeRef {
        if let Some(&r) = self.to_node.get(e) {
            return r;
        }
        let r = self.mk_node();
        self.to_node.insert(e.clone(), r);
        r
    }

    /// Core equivalence check following Lean 4's `is_equiv_core`.
    /// Stack-safe wrapper matching Lean 4's check_system() at recursion entry.
    fn is_equiv_core(&mut self, a: &Expr, b: &Expr, use_hash: bool) -> bool {
        // Fast paths before stack_safe to avoid overhead on trivial cases
        if std::ptr::eq(a, b) {
            return true;
        }
        if let (ExprKind::BVar(i), ExprKind::BVar(j)) = (&a.kind, &b.kind) {
            return i == j;
        }
        stack_safe(|| self.is_equiv_core_impl(a, b, use_hash))
    }

    /// Implementation of core equivalence check (called via stack_safe).
    fn is_equiv_core_impl(&mut self, a: &Expr, b: &Expr, use_hash: bool) -> bool {
        // 3. Existing union-find knowledge must win even when hashes differ.
        // add_equiv can merge structurally different expressions, so hash
        // pre-filtering before this check would incorrectly return false.
        // Probe the node map once and remember the roots: when both are already
        // tracked (the common revisit case) we reuse them at step 5 instead of
        // re-probing + re-find()ing. Nothing between here and step 5 mutates
        // `to_node`, so the captured roots stay exact.
        let tracked_roots = if let (Some(n1), Some(n2)) =
            (self.to_node.get(a).copied(), self.to_node.get(b).copied())
        {
            let r1 = self.find(n1);
            let r2 = self.find(n2);
            if r1 == r2 {
                return true;
            }
            Some((r1, r2))
        } else {
            None
        };

        // 4. Hash pre-filter (O(1) via cached metadata)
        if use_hash && a.hash_cached() != b.hash_cached() {
            return false;
        }

        // 5. Union-find lookup. Reuse the step-3 roots when both were already
        //    tracked; otherwise insert via get_or_insert_node, which coalesces
        //    structurally-equal keys onto a single node (so a==b untracked still
        //    short-circuits here exactly as before).
        let (r1, r2) = match tracked_roots {
            Some(roots) => roots,
            None => {
                let n1 = self.get_or_insert_node(a);
                let n2 = self.get_or_insert_node(b);
                (self.find(n1), self.find(n2))
            }
        };
        if r1 == r2 {
            return true;
        }

        // 6. Structural comparison fallback by kind tag
        if std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind) {
            return false;
        }

        let result = match (&a.kind, &b.kind) {
            (ExprKind::BVar(_), ExprKind::BVar(_)) => {
                unreachable!("handled above")
            }
            (ExprKind::FVar(id1), ExprKind::FVar(id2)) => id1 == id2,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.is_equiv_core(f1, f2, use_hash) && self.is_equiv_core(a1, a2, use_hash)
            }
            (ExprKind::Lam(bi1, ty1, body1), ExprKind::Lam(bi2, ty2, body2)) => {
                bi1 == bi2
                    && self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(body1, body2, use_hash)
            }
            (ExprKind::Pi(bi1, ty1, body1), ExprKind::Pi(bi2, ty2, body2)) => {
                bi1 == bi2
                    && self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(body1, body2, use_hash)
            }
            (ExprKind::Let(_, ty1, val1, body1, _), ExprKind::Let(_, ty2, val2, body2, _)) => {
                self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(val1, val2, use_hash)
                    && self.is_equiv_core(body1, body2, use_hash)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(_, i1, e1), ExprKind::Proj(_, i2, e2)) => {
                i1 == i2 && self.is_equiv_core(e1, e2, use_hash)
            }
            (ExprKind::MData(_, e1), ExprKind::MData(_, e2)) => {
                self.is_equiv_core(e1, e2, use_hash)
            }
            // Impredicative mode extensions
            (ExprKind::SProp, ExprKind::SProp) => true,
            (ExprKind::Squash(e1), ExprKind::Squash(e2)) => self.is_equiv_core(e1, e2, use_hash),
            // Cubical mode extensions
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
            | (ExprKind::CubicalI0, ExprKind::CubicalI0)
            | (ExprKind::CubicalI1, ExprKind::CubicalI1) => true,
            (
                ExprKind::CubicalPath {
                    ty: ty1,
                    left: l1,
                    right: r1,
                },
                ExprKind::CubicalPath {
                    ty: ty2,
                    left: l2,
                    right: r2,
                },
            ) => {
                self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(l1, l2, use_hash)
                    && self.is_equiv_core(r1, r2, use_hash)
            }
            (
                ExprKind::CubicalPathLam { body: body1 },
                ExprKind::CubicalPathLam { body: body2 },
            ) => self.is_equiv_core(body1, body2, use_hash),
            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => self.is_equiv_core(p1, p2, use_hash) && self.is_equiv_core(a1, a2, use_hash),
            (
                ExprKind::CubicalHComp {
                    ty: ty1,
                    phi: phi1,
                    u: u1,
                    base: base1,
                },
                ExprKind::CubicalHComp {
                    ty: ty2,
                    phi: phi2,
                    u: u2,
                    base: base2,
                },
            ) => {
                self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(phi1, phi2, use_hash)
                    && self.is_equiv_core(u1, u2, use_hash)
                    && self.is_equiv_core(base1, base2, use_hash)
            }
            (
                ExprKind::CubicalTransp {
                    ty: ty1,
                    phi: phi1,
                    base: base1,
                },
                ExprKind::CubicalTransp {
                    ty: ty2,
                    phi: phi2,
                    base: base2,
                },
            ) => {
                self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(phi1, phi2, use_hash)
                    && self.is_equiv_core(base1, base2, use_hash)
            }
            (
                ExprKind::CubicalCoe {
                    ty: ty1,
                    r: r1,
                    s: s1,
                    base: base1,
                },
                ExprKind::CubicalCoe {
                    ty: ty2,
                    r: r2,
                    s: s2,
                    base: base2,
                },
            ) => {
                self.is_equiv_core(ty1, ty2, use_hash)
                    && self.is_equiv_core(r1, r2, use_hash)
                    && self.is_equiv_core(s1, s2, use_hash)
                    && self.is_equiv_core(base1, base2, use_hash)
            }
            // Set-theoretic mode extensions
            (ExprKind::ZFCSet(s1), ExprKind::ZFCSet(s2)) => self.is_zfc_set_equiv(s1, s2, use_hash),
            (
                ExprKind::ZFCMem {
                    element: e1,
                    set: s1,
                },
                ExprKind::ZFCMem {
                    element: e2,
                    set: s2,
                },
            ) => self.is_equiv_core(e1, e2, use_hash) && self.is_equiv_core(s1, s2, use_hash),
            (
                ExprKind::ZFCComprehension {
                    domain: d1,
                    pred: p1,
                },
                ExprKind::ZFCComprehension {
                    domain: d2,
                    pred: p2,
                },
            ) => self.is_equiv_core(d1, d2, use_hash) && self.is_equiv_core(p1, p2, use_hash),
            // Discriminant mismatch already handled above
            _ => false,
        };

        if result {
            self.merge(r1, r2);
        }
        result
    }

    /// Structural equivalence check for ZFC set expressions.
    fn is_zfc_set_equiv(&mut self, a: &ZFCSetExpr, b: &ZFCSetExpr, use_hash: bool) -> bool {
        if std::mem::discriminant(a) != std::mem::discriminant(b) {
            return false;
        }
        match (a, b) {
            (ZFCSetExpr::Empty, ZFCSetExpr::Empty)
            | (ZFCSetExpr::Infinity, ZFCSetExpr::Infinity) => true,
            (ZFCSetExpr::Singleton(e1), ZFCSetExpr::Singleton(e2)) => {
                self.is_equiv_core(e1, e2, use_hash)
            }
            (ZFCSetExpr::Pair(a1, b1), ZFCSetExpr::Pair(a2, b2)) => {
                self.is_equiv_core(a1, a2, use_hash) && self.is_equiv_core(b1, b2, use_hash)
            }
            (ZFCSetExpr::Union(e1), ZFCSetExpr::Union(e2)) => self.is_equiv_core(e1, e2, use_hash),
            (ZFCSetExpr::PowerSet(e1), ZFCSetExpr::PowerSet(e2)) => {
                self.is_equiv_core(e1, e2, use_hash)
            }
            (
                ZFCSetExpr::Separation { set: s1, pred: p1 },
                ZFCSetExpr::Separation { set: s2, pred: p2 },
            ) => self.is_equiv_core(s1, s2, use_hash) && self.is_equiv_core(p1, p2, use_hash),
            (
                ZFCSetExpr::Replacement { set: s1, func: f1 },
                ZFCSetExpr::Replacement { set: s2, func: f2 },
            ) => self.is_equiv_core(s1, s2, use_hash) && self.is_equiv_core(f1, f2, use_hash),
            (ZFCSetExpr::Choice(e1), ZFCSetExpr::Choice(e2)) => {
                self.is_equiv_core(e1, e2, use_hash)
            }
            _ => false,
        }
    }
}
