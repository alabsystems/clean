// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.dist_self : ∀ a : Int, Eq Int (Int.dist a a) (Int.ofNat 0)`.
//!
//! This is the metric-space identity `d(a, a) = 0` for the integer distance.
//! It replaces the prior `Declaration::Axiom` registration of `Int.dist_self`
//! in `algebra_dist.rs` (`init_int_dist`) with a kernel-checked
//! `Declaration::Theorem`.
//!
//! # Standalone environment
//!
//! `register_int_dist_self_proof` builds its own minimal environment: it does
//! NOT call `init_int_dist` (which registers the family of `Int.dist_*`
//! *axioms*). Instead it registers exactly the constructive ingredients it
//! needs:
//!
//! - the reducible `Int.dist` Definition (`λ a b => Int.abs (Int.sub a b)`),
//!   matching the body in `init_int_dist`;
//! - the constructive `Int.abs_zero` Theorem (`@Eq.refl Int Int.zero`);
//! - the constructive `Int.sub_self` Theorem (via
//!   `register_int_sub_self_proof`).
//!
//! Each registration is idempotency-guarded, so this fn composes cleanly with
//! the existing init pipeline (the `if get_const(..).is_some()` guards make a
//! later `init_int_dist` / `init_int_abs_props` a no-op for these names, and
//! vice-versa).
//!
//! # Proof sketch
//!
//! `Int.dist` is a reducible Definition, so the goal LHS reduces by delta:
//!
//! ```text
//! Int.dist a a ≡ Int.abs (Int.sub a a).
//! ```
//!
//! Two constructive facts close the chain:
//!
//! ```text
//! Int.sub_self a : Eq Int (Int.sub a a) Int.zero
//! Int.abs_zero   : Eq Int (Int.abs (Int.ofNat 0)) (Int.ofNat 0)
//! ```
//!
//! (`Int.zero ≡ Int.ofNat Nat.zero`, so `Int.abs Int.zero` and
//! `Int.abs (Int.ofNat 0)` are definitionally equal.)
//!
//! - `congrArg Int.abs (Int.sub_self a)`
//!   `: Eq Int (Int.abs (Int.sub a a)) (Int.abs Int.zero)`,
//! - `Eq.trans` that with `Int.abs_zero`
//!   `: Eq Int (Int.abs (Int.sub a a)) (Int.ofNat 0)`,
//!
//! whose type is definitionally equal to the goal
//! `Eq Int (Int.dist a a) (Int.ofNat 0)`. The proof term is
//!
//! ```text
//! λ a : Int =>
//!   @Eq.trans.{1} Int
//!     (Int.abs (Int.sub a a)) (Int.abs Int.zero) (Int.ofNat 0)
//!     (@congrArg.{1,1} Int Int (Int.sub a a) Int.zero Int.abs (Int.sub_self a))
//!     Int.abs_zero
//! ```
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.dist` (reducible Definition),
//! `Int.abs` (reducible Definition), `Int.sub` (reducible Definition),
//! `Int.ofNat`, `Eq`, `Eq.trans`, `congrArg`, and the constructive Theorems
//! `Int.sub_self` and `Int.abs_zero`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.dist_self")` is empty and
//! `env.proof_quality("Int.dist_self") == ProofQuality::Constructive`.
//!
//! Sibling proofs:
//! - `algebra_int_sub_self_proof.rs` (`Int.sub_self`, dependency).
//! - `algebra_int_add_neg_self_proof.rs` (transitive dependency).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntDistSelfConsts {
    int_type: Expr,
    int_dist: Expr,
    int_abs: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    int_zero: Expr,
    int_sub_self: Expr,
    int_abs_zero: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl IntDistSelfConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let int_zero = Expr::app(int_of_nat.clone(), nat_zero.clone());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_dist: Expr::const_(Name::from_string("Int.dist"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat,
            nat_zero,
            int_zero,
            int_sub_self: Expr::const_(Name::from_string("Int.sub_self"), vec![]),
            int_abs_zero: Expr::const_(Name::from_string("Int.abs_zero"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn dist(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_dist.clone(), a), b)
    }

    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), a), b)
    }

    /// `Int.ofNat 0` — the conclusion RHS, matching the original axiom signature.
    fn of_nat_zero(&self) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.nat_zero.clone())
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

/// Build `∀ a : Int, Eq Int (Int.dist a a) (Int.ofNat 0)`.
fn build_type(c: &IntDistSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.dist(a.clone(), a), c.of_nat_zero());
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Body:
/// ```text
/// λ a : Int =>
///   @Eq.trans.{1} Int
///     (Int.abs (Int.sub a a)) (Int.abs Int.zero) (Int.ofNat 0)
///     (@congrArg.{1,1} Int Int (Int.sub a a) Int.zero Int.abs (Int.sub_self a))
///     Int.abs_zero
/// ```
fn build_value(c: &IntDistSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    // sub a a, and the three points of the Eq.trans chain.
    let sub_a_a = c.sub(a.clone(), a.clone());
    let abs_sub = c.abs(sub_a_a.clone()); // Int.abs (Int.sub a a)
    let abs_zero_term = c.abs(c.int_zero.clone()); // Int.abs Int.zero  (≡ Int.abs (ofNat 0))
    let of_nat_zero = c.of_nat_zero(); // Int.ofNat 0

    // congrArg Int.abs (Int.sub_self a)
    //   : Eq Int (Int.abs (Int.sub a a)) (Int.abs Int.zero)
    let sub_self_a = Expr::app(c.int_sub_self.clone(), a.clone());
    let congr = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(), // A = Int
            c.int_type.clone(), // B = Int
            sub_a_a,            // a-side argument: Int.sub a a
            c.int_zero.clone(), // b-side argument: Int.zero
            c.int_abs.clone(),  // f = Int.abs
            sub_self_a,         // h : Eq Int (Int.sub a a) Int.zero
        ],
    );

    // Eq.trans congr Int.abs_zero
    //   : Eq Int (Int.abs (Int.sub a a)) (Int.ofNat 0)
    let trans = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),     // A = Int
            abs_sub,                // x = Int.abs (Int.sub a a)
            abs_zero_term,          // y = Int.abs Int.zero
            of_nat_zero,            // z = Int.ofNat 0
            congr,                  // h1 : Eq x y
            c.int_abs_zero.clone(), // h2 : Eq y z   (Int.abs_zero)
        ],
    );

    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), trans);
    b.finish(val_raw)
}

impl Environment {
    /// Register the reducible `Int.dist` Definition `λ a b => Int.abs (Int.sub
    /// a b)` if it is not already present. Mirrors the body registered by
    /// `init_int_dist` so the standalone `Int.dist_self` proof env is faithful.
    fn register_int_dist_def(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.dist");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_abs = Expr::const_(Name::from_string("Int.abs"), vec![]);
        let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);

        // Int.dist : Int → Int → Int
        let dist_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        // λ a b => Int.abs (Int.sub a b)
        let dist_value = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bb) = bldr.fresh_local(int_const.clone());
            let body = Expr::app(int_abs, Expr::app(Expr::app(int_sub, a), bb));
            let e = bldr.mk_lam(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: dist_type,
            value: dist_value,
            is_reducible: true,
        })
    }

    /// Register the constructive `Int.abs_zero` Theorem
    /// `Eq Int (Int.abs (Int.ofNat 0)) (Int.ofNat 0)` if not already present.
    ///
    /// Proof: `Int.abs (ofNat 0) ≡ Int.ofNat (Int.natAbs (ofNat 0)) ≡ ofNat 0`
    /// definitionally (both `Int.abs` and `Int.natAbs` are reducible), so the
    /// goal is closed by `@Eq.refl.{1} Int (Int.ofNat 0)`. Matches the
    /// constructive registration in `init_int_abs_props`.
    fn register_int_abs_zero_def(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.abs_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let type1 = Level::succ(Level::zero());
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_abs = Expr::const_(Name::from_string("Int.abs"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);
        let int_zero = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );

        // Eq Int (Int.abs (Int.ofNat 0)) (Int.ofNat 0)
        let abs_zero_type = Expr::apps(
            eq_const,
            [
                int_const.clone(),
                Expr::app(int_abs, int_zero.clone()),
                int_zero.clone(),
            ],
        );
        // @Eq.refl.{1} Int (Int.ofNat 0)
        let abs_zero_value = Expr::apps(eq_refl, [int_const, int_zero]);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: abs_zero_type,
            value: abs_zero_value,
        })
    }

    /// Register `Int.dist_self` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_sign_abs()` has registered `Int`, `Int.abs`,
    ///           `Int.natAbs`, `Int.ofNat`.
    /// REQUIRES: `self.init_int_arith()` has registered `Int.add`, `Int.neg`,
    ///           `Int.sub`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.trans`,
    ///           `congrArg`.
    /// ENSURES: On success, `Int.dist_self` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.dist_self` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_dist_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.dist_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Dependencies — provide the reducible defs and constructive Theorems
        // WITHOUT pulling in the `Int.dist_*` axiom family from `init_int_dist`.
        self.init_int_sign_abs()?; // Int.abs, Int.natAbs, Int.ofNat
        self.init_int_arith()?; // Int.add, Int.neg, Int.sub
        self.init_eq()?; // Eq, Eq.refl, Eq.trans, congrArg
        self.register_int_dist_def()?; // reducible Int.dist Definition
        self.register_int_abs_zero_def()?; // constructive Int.abs_zero Theorem
        self.register_int_sub_self_proof()?; // constructive Int.sub_self Theorem

        let c = IntDistSelfConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `Int.dist a a` reduces by
        // delta on the reducible `Int.dist` to `Int.abs (Int.sub a a)`. The
        // body `Eq.trans (congrArg Int.abs (Int.sub_self a)) Int.abs_zero` has
        // type `Eq Int (Int.abs (Int.sub a a)) (Int.ofNat 0)`, definitionally
        // equal to the goal. No `sorry`, no self-reference, no domain-axiom
        // dependency (Int.sub_self and Int.abs_zero are constructive Theorems;
        // Int.dist / Int.abs / Int.sub are reducible Definitions). Replaces the
        // prior `Declaration::Axiom` registration of `Int.dist_self` in
        // `algebra_dist.rs` (`init_int_dist`).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::axiom_audit::ProofQuality;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    /// Build a minimal env via the standalone register fn (NOT the axiom-init
    /// `init_int_dist`).
    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_int_dist_self_proof()
            .expect("register_int_dist_self_proof should succeed");
        env
    }

    /// Kernel accepts the `Eq.trans`/`congrArg` proof term: `Int.dist_self` is
    /// a Theorem (not Axiom), retains its value, and re-invocation is a no-op.
    #[test]
    fn test_int_dist_self_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_dist_self_proof()
            .expect("first registration");
        env.register_int_dist_self_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.dist_self"))
            .expect("Int.dist_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The kernel re-checks the proof term against its canonical type.
    #[test]
    fn test_int_dist_self_kernel_type_checks() {
        let env = env();
        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Int.dist_self"), vec![]))
            .expect("Int.dist_self should kernel-type-check");
    }

    /// `Int.dist_self` reaches `ProofQuality::Constructive` (empty
    /// domain-axiom closure).
    #[test]
    fn test_int_dist_self_is_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Int.dist_self"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Int.dist_self must be Constructive (no domain axiom in closure), got {q:?}"
        );
    }

    /// Axiom closure is empty and sorry-free.
    #[test]
    fn test_int_dist_self_axiom_deps_empty() {
        let env = env();
        let deps = env
            .axiom_deps(&Name::from_string("Int.dist_self"))
            .expect("Int.dist_self is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.dist_self must have empty axiom closure (constructive proof), got {domain_deps:?}"
        );
    }

    /// The proof body is a `λ`-abstraction whose root (after the binder) is an
    /// `Eq.trans` application — guards against an axiom-wrapping masquerade.
    #[test]
    fn test_int_dist_self_proof_root_is_eq_trans() {
        use crate::expr::ExprKind;
        let env = env();
        let info = env
            .get_const(&Name::from_string("Int.dist_self"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body.clone(),
            k => panic!("expected outer λ, got {k:?}"),
        };
        let mut head = outer_body;
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Eq.trans",
                "Int.dist_self proof root must be Eq.trans, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Eq.trans, ..) at proof root, got {k:?}"),
        }
    }
}
