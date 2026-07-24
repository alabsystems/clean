// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal READ-ONLY environment for the micro-checker.
//!
//! # Why this exists (the #3 diversity gap)
//!
//! The micro-checker is a genuinely-independent second checker (its own
//! [`MicroExpr`](super::MicroExpr) / [`MicroCert`](super::MicroCert) / its own
//! `whnf`/`def_eq`). Historically it REJECTED every [`Const`](super::MicroExpr::Const)
//! ("micro-checker has no environment"), so the kernel's stage-3 cross-check
//! returned `Ok(false)` — a SILENT SKIP — for any term with named references.
//! Every real `:= rfl` theorem reduces named defs (`Const`) via delta + native
//! Nat/Bool reductions, so the diversity cross-check covered only closed
//! pure-λ terms — NOT the corpus the soundness rests on.
//!
//! `MicroEnv` closes that gap with the SMALLEST possible addition: a read-only
//! `name -> (type, body, reducible)` map. The micro-checker consults it to
//!
//! * resolve a `Const` to its TYPE (so `App` typing works), and
//! * unfold a `@[reducible]` def to its BODY (DELTA), enabling the reductions
//!   the `:= rfl` corpus relies on.
//!
//! # Independence is preserved
//!
//! `MicroEnv` is JUST DATA. It is built ONCE from a kernel [`Environment`] by
//! translating each constant's type/body through
//! [`MicroExpr::from_kernel_env`](super::MicroExpr::from_kernel_env) (a pure
//! structural translation). The checker's reduction engine
//! ([`super::checker`]) then runs entirely on `MicroExpr` using its OWN
//! `whnf`/`def_eq`/native arithmetic — it never calls the kernel's
//! `whnf`/`is_def_eq`/`Expr`. Sharing a name→data table is not sharing a
//! reducer: the diversity value (a second, differently-written normalizer) is
//! intact.
//!
//! # Fail-closed by construction
//!
//! Any constant the translation cannot model (polymorphic type it can't
//! erase, an unsupported `ExprKind`, …) is simply ABSENT from the map. The
//! checker then reports [`MicroResult::Unsupported`](super::MicroResult) for
//! it — never a silent accept.

use std::collections::HashMap;
use std::sync::Arc;

use crate::env::{ConstantKind, Environment, Reducibility};
use crate::name::Name;

use super::types::MicroExpr;

/// A single read-only constant entry: its translated type and (optionally) its
/// translated, delta-unfoldable body.
#[derive(Debug, Clone)]
pub struct MicroConst {
    /// Translated type of the constant.
    pub ty: MicroExpr,
    /// Translated body, present iff the constant is a delta-unfoldable
    /// (`@[reducible]` / regular) `Definition`. `None` for axioms, opaque
    /// constants, inductives/constructors/recursors (whose iota is handled by
    /// the checker's native rules, not by body unfolding), and theorems.
    pub body: Option<MicroExpr>,
}

/// Read-only constant table consulted by the micro-checker for delta unfolding
/// and `Const` typing. Built once from a kernel [`Environment`]; never mutated
/// during checking.
#[derive(Debug, Clone, Default)]
pub struct MicroEnv {
    consts: HashMap<Arc<str>, MicroConst>,
}

impl MicroEnv {
    /// An empty environment (every `Const` is `Unsupported`).
    #[must_use]
    pub fn new() -> Self {
        MicroEnv {
            consts: HashMap::new(),
        }
    }

    /// Look up a constant by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&MicroConst> {
        self.consts.get(name)
    }

    /// Number of constants successfully translated into the read-only table.
    #[must_use]
    pub fn len(&self) -> usize {
        self.consts.len()
    }

    /// Whether the table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.consts.is_empty()
    }

    /// Insert (or overwrite) a constant entry. Used by [`Self::from_kernel`]
    /// and directly by tests/builders.
    pub fn insert(&mut self, name: impl Into<Arc<str>>, entry: MicroConst) {
        self.consts.insert(name.into(), entry);
    }

    /// Build a read-only micro-env by translating the **transitive constant
    /// closure** of `roots` out of the kernel [`Environment`].
    ///
    /// The closure walk seeds from each root's type and value, follows every
    /// referenced `Const`, and translates each into a [`MicroConst`]. A
    /// constant whose type or (definitional) body cannot be structurally
    /// translated is OMITTED (the checker then fails closed on it). The
    /// translation is purely structural — no kernel reduction is invoked.
    ///
    /// A `@[reducible]` or regular `Definition` keeps its body so the checker
    /// can DELTA-unfold it. All other kinds keep only their type (axioms,
    /// opaque constants, theorems, and inductive machinery — whose iota the
    /// checker handles natively for the supported Nat/Bool set).
    #[must_use]
    pub fn from_kernel(env: &Environment, roots: &[Name]) -> Self {
        let mut out = MicroEnv::new();
        let mut worklist: Vec<Name> = roots.to_vec();
        let mut seen: std::collections::HashSet<Name> = std::collections::HashSet::new();

        while let Some(name) = worklist.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let Some(info) = env.get_const(&name) else {
                continue;
            };

            // Translate the type (best-effort, structural).
            let Ok(ty) = MicroExpr::from_kernel_env(&info.type_) else {
                // Untranslatable type: omit, checker fails closed on this const.
                // Still enqueue its referenced consts so siblings translate.
                enqueue_refs(&info.type_, &seen, &mut worklist);
                if let Some(v) = &info.value {
                    enqueue_refs(v, &seen, &mut worklist);
                }
                continue;
            };

            // Keep the body only for delta-unfoldable Definitions.
            let body = match info.kind {
                ConstantKind::Definition
                    if matches!(
                        info.reducibility,
                        Reducibility::Reducible | Reducibility::Regular(_)
                    ) =>
                {
                    info.value
                        .as_ref()
                        .and_then(|v| MicroExpr::from_kernel_env(v).ok())
                }
                _ => None,
            };

            // Enqueue referenced consts (type + value) so the closure completes.
            enqueue_refs(&info.type_, &seen, &mut worklist);
            if let Some(v) = &info.value {
                enqueue_refs(v, &seen, &mut worklist);
            }

            out.insert(name.to_string(), MicroConst { ty, body });
        }

        out
    }
}

/// Push every `Const` referenced in `expr` (not already `seen`) onto the
/// worklist, so [`MicroEnv::from_kernel`] reaches the full transitive closure.
fn enqueue_refs(
    expr: &crate::expr::Expr,
    seen: &std::collections::HashSet<Name>,
    worklist: &mut Vec<Name>,
) {
    use crate::expr::ExprKind;
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) if !seen.contains(name) => {
                worklist.push(name.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) | ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::micro::{MicroChecker, MicroExpr, MicroLiteral, MicroResult};
    use std::sync::Arc;

    fn nat_const() -> MicroExpr {
        MicroExpr::Const(Arc::from("Nat"))
    }

    /// Build a tiny micro-env modeling `double a := Nat.add a a` (a reducible
    /// def) so the checker can DELTA-unfold it and IOTA-reduce the `Nat.add`.
    fn double_env() -> MicroEnv {
        let mut env = MicroEnv::new();
        // double : Nat -> Nat
        let ty = MicroExpr::Pi(Arc::new(nat_const()), Arc::new(nat_const()));
        // body: λ a => Nat.add a a   (a = BVar 0)
        let body = MicroExpr::Lam(
            Arc::new(nat_const()),
            Arc::new(MicroExpr::App(
                Arc::new(MicroExpr::App(
                    Arc::new(MicroExpr::Const(Arc::from("Nat.add"))),
                    Arc::new(MicroExpr::BVar(0)),
                )),
                Arc::new(MicroExpr::BVar(0)),
            )),
        );
        env.insert(
            "double",
            MicroConst {
                ty,
                body: Some(body),
            },
        );
        env
    }

    fn lit(n: u64) -> MicroExpr {
        MicroExpr::Lit(MicroLiteral::nat_u64(n))
    }

    #[test]
    fn test_env_delta_plus_native_iota_reduces() {
        let env = double_env();
        let checker = MicroChecker::with_env(&env);
        // double 21 ≡ 42 via delta (unfold double) + native (Nat.add 21 21).
        let lhs = MicroExpr::App(
            Arc::new(MicroExpr::Const(Arc::from("double"))),
            Arc::new(lit(21)),
        );
        match checker.check_value_eq_result(&lhs, &lit(42)) {
            MicroResult::Verified(v) => assert_eq!(v, lit(42)),
            other => panic!("expected Verified(42), got {other:?}"),
        }
    }

    #[test]
    fn test_env_delta_disagreement_is_rejected() {
        let env = double_env();
        let checker = MicroChecker::with_env(&env);
        let lhs = MicroExpr::App(
            Arc::new(MicroExpr::Const(Arc::from("double"))),
            Arc::new(lit(21)),
        );
        // double 21 ≠ 43 — the reducer must REJECT (non-vacuous).
        assert!(matches!(
            checker.check_value_eq_result(&lhs, &lit(43)),
            MicroResult::Rejected(_)
        ));
    }

    #[test]
    fn test_unknown_const_is_unsupported_fail_closed() {
        // Empty env: an unknown const left stuck must FAIL CLOSED as Unsupported,
        // never silently Verified.
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        let lhs = MicroExpr::App(
            Arc::new(MicroExpr::Const(Arc::from("Mystery.op"))),
            Arc::new(lit(1)),
        );
        assert!(matches!(
            checker.check_value_eq_result(&lhs, &lit(1)),
            MicroResult::Unsupported(_)
        ));
    }

    #[test]
    fn test_unmodeled_recursor_head_is_unsupported() {
        // A `Nat.rec`-headed term cannot be reduced by the micro-checker; the
        // value-eq check must surface Unsupported (fail-closed), not Rejected.
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        let stuck = MicroExpr::App(
            Arc::new(MicroExpr::Const(Arc::from("Nat.rec"))),
            Arc::new(lit(3)),
        );
        assert!(matches!(
            checker.check_value_eq_result(&stuck, &lit(3)),
            MicroResult::Unsupported(_)
        ));
    }
}
