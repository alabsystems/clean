// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the integer reverse-triangle bound
//!
//! `Int.abs_sub_le : ∀ a b : Int,
//!      Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) (Int.abs b))`.
//!
//! This is a thin transport over two already-landed constructive theorems:
//!
//! - `Int.abs_add_le : ∀ a b, Int.le (Int.abs (Int.add a b))
//!                            (Int.add (Int.abs a) (Int.abs b))`
//! - `Int.abs_neg    : ∀ a, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`
//!
//! # Reducible definitions in play
//!
//! ```text
//! Int.abs i    := Int.ofNat (Int.natAbs i)              -- reducible
//! Int.sub a b  := Int.add a (Int.neg b)                 -- reducible
//! Int.le a b   := Int.NonNeg (Int.sub b a)              -- reducible
//! ```
//!
//! # Proof strategy
//!
//! Instantiate `Int.abs_add_le` at `a` and `Int.neg b`:
//!
//! ```text
//! Int.abs_add_le a (Int.neg b)
//!   : Int.le (Int.abs (Int.add a (Int.neg b)))
//!            (Int.add (Int.abs a) (Int.abs (Int.neg b)))
//! ```
//!
//! Because `Int.sub a b` delta-reduces to `Int.add a (Int.neg b)`, the LHS
//! `Int.abs (Int.add a (Int.neg b))` is definitionally `Int.abs (Int.sub a b)`
//! — exactly the goal LHS. Only the RHS differs: it carries
//! `Int.abs (Int.neg b)` where the goal wants `Int.abs b`. Those two are
//! propositionally equal by `Int.abs_neg b`, so we rewrite with a single
//! `@Eq.subst.{1}` whose motive fixes the LHS and the left summand of the RHS
//! and abstracts the right summand:
//!
//! ```text
//! motive := fun (w : Int) =>
//!   Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) w)
//! ```
//!
//! Then
//!
//! ```text
//! @Eq.subst.{1} Int motive
//!   (Int.abs (Int.neg b))            -- `from`
//!   (Int.abs b)                      -- `to`
//!   (Int.abs_neg b)                  -- Eq Int (abs (neg b)) (abs b)
//!   (Int.abs_add_le a (Int.neg b))   -- motive `from` (defeq to abs_add_le's type)
//!   : motive (Int.abs b)
//!   ≡ Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) (Int.abs b))
//! ```
//!
//! `motive (Int.abs (Int.neg b))` is `Int.le (Int.abs (Int.sub a b))
//! (Int.add (Int.abs a) (Int.abs (Int.neg b)))`, which is definitionally the
//! type of `Int.abs_add_le a (Int.neg b)` (the `Int.sub a b` ≡ `Int.add a
//! (Int.neg b)` delta-reduction is the only conversion needed), so the base
//! term type-checks at `motive from`, and the result is exactly the stated
//! goal.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Eq.subst` (kernel machinery), the reducible
//! definitions `Int.abs` / `Int.sub` / `Int.neg`, and the two constructive
//! Theorems `Int.abs_add_le`, `Int.abs_neg` — neither of which has any
//! `Declaration::Axiom` in its closure. Therefore
//! `env.axiom_deps("Int.abs_sub_le")` is empty and
//! `env.proof_quality("Int.abs_sub_le") == ProofQuality::Constructive`.

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
#[cfg(test)]
struct AbsSubLeConsts {
    int_type: Expr,
    int_abs: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_neg: Expr,
    int_le: Expr,
    abs_add_le: Expr,
    abs_neg: Expr,
    eq_subst: Expr,
}

#[cfg(test)]
impl AbsSubLeConsts {
    #[cfg(test)]
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            abs_add_le: Expr::const_(Name::from_string("Int.abs_add_le"), vec![]),
            abs_neg: Expr::const_(Name::from_string("Int.abs_neg"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    #[cfg(test)]
    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }
    #[cfg(test)]
    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }
    #[cfg(test)]
    fn iadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [x, y])
    }
    #[cfg(test)]
    fn isub(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [x, y])
    }
    #[cfg(test)]
    fn ile(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }
}

/// `∀ a b : Int,
///    Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) (Int.abs b))`.
#[cfg(test)]
fn build_abs_sub_le_type(c: &AbsSubLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.ile(
        c.abs(c.isub(a.clone(), bv.clone())),
        c.iadd(c.abs(a.clone()), c.abs(bv.clone())),
    );
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) =>
///   @Eq.subst.{1} Int
///     (fun (w : Int) => Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) w))
///     (Int.abs (Int.neg b)) (Int.abs b)
///     (Int.abs_neg b)
///     (Int.abs_add_le a (Int.neg b))
/// ```
#[cfg(test)]
fn build_abs_sub_le_value(c: &AbsSubLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    let sub_ab = c.isub(a.clone(), bv.clone()); // a - b ≡ add a (neg b)
    let abs_a = c.abs(a.clone());
    let abs_neg_b = c.abs(c.neg(bv.clone())); // abs (neg b)
    let abs_b = c.abs(bv.clone());

    // motive: fun (w : Int) => Int.le (abs (sub a b)) (add (abs a) w)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = mb.fresh_local(c.int_type.clone());
        let body = c.ile(c.abs(sub_ab.clone()), c.iadd(abs_a.clone(), w.clone()));
        let lam = mb.mk_lam(w_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // base : Int.abs_add_le a (neg b)
    //   : Int.le (abs (add a (neg b))) (add (abs a) (abs (neg b)))
    //   ≡ motive (abs (neg b))   [abs (add a (neg b)) ≡ abs (sub a b)]
    let base = Expr::apps(c.abs_add_le.clone(), [a.clone(), c.neg(bv.clone())]);

    // bridge : Int.abs_neg b : Eq Int (abs (neg b)) (abs b)
    let bridge = Expr::app(c.abs_neg.clone(), bv.clone());

    // @Eq.subst.{1} Int motive (abs (neg b)) (abs b) bridge base : motive (abs b)
    let body = Expr::apps(
        c.eq_subst.clone(),
        [c.int_type.clone(), motive, abs_neg_b, abs_b, bridge, base],
    );

    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

#[cfg(test)]
impl Environment {
    /// Register `Int.abs_sub_le` as a kernel-checked `Declaration::Theorem`.
    ///
    /// `∀ a b : Int,
    ///    Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) (Int.abs b))`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: On success, `Int.abs_sub_le` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — guarded by `get_const`; dependencies are
    ///          themselves idempotent.
    #[cfg(test)]
    pub(crate) fn register_int_abs_sub_le(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies (each idempotent / get_const-guarded internally).
        self.init_int_sign_abs()?; // Int.abs, Int.natAbs, Int.neg, Int.ofNat, Int.negSucc, Int.rec
        self.init_int_arith()?; // Int.add, Int.sub
        self.init_int_ord()?; // Int.le, Int.NonNeg
        self.init_eq()?; // Eq, Eq.refl, Eq.subst

        // Constructive helper Theorems reused verbatim.
        self.register_int_abs_add_le()?; // Int.abs_add_le (+ its supporting lemmas)
        self.register_int_abs_neg_proof()?; // Int.abs_neg

        let name = Name::from_string("Int.abs_sub_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = AbsSubLeConsts::new();
        let type_ = build_abs_sub_le_type(&c);
        let value = build_abs_sub_le_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `Int.sub a b` delta-reduces
        // to `Int.add a (Int.neg b)`, so `Int.abs_add_le a (Int.neg b)` already
        // proves `Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a)
        // (Int.abs (Int.neg b)))`. A single `@Eq.subst.{1}` along
        // `Int.abs_neg b : Eq Int (Int.abs (Int.neg b)) (Int.abs b)` (motive
        // `fun w => Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) w)`)
        // rewrites the right summand to land on the goal. Both supporting
        // theorems (`Int.abs_add_le`, `Int.abs_neg`) are constructive with empty
        // domain-axiom closures, so this term has none either. No `sorry`, no
        // domain axiom.
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
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_abs_sub_le()
            .expect("register_int_abs_sub_le should succeed");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a kernel-checked Theorem, got {:?}",
            info.kind
        );
        assert!(info.value.is_some(), "{name} Theorem must retain its value");

        // Kernel re-checks the proof term against its canonical type.
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));

        let q = env
            .proof_quality(&Name::from_string(name))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} must be Constructive (empty domain-axiom closure), got {q:?}"
        );
    }

    #[test]
    fn test_int_abs_sub_le_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.abs_sub_le");
    }

    #[test]
    fn test_int_abs_sub_le_kernel_type_checks() {
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Int.abs_sub_le"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(value)
            .expect("proof term must type-check in the kernel");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type must match the declared Int.abs_sub_le type"
        );
    }

    #[test]
    fn test_register_int_abs_sub_le_idempotent() {
        let mut env = Environment::new();
        env.register_int_abs_sub_le().expect("first registration");
        env.register_int_abs_sub_le()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.abs_sub_le"))
            .expect("Int.abs_sub_le should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_abs_sub_le_axiom_deps_empty() {
        let env = registered_env();
        let deps = env
            .axiom_deps(&Name::from_string("Int.abs_sub_le"))
            .expect("Int.abs_sub_le registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.abs_sub_le must have empty axiom closure, got {domain_deps:?}"
        );
    }
}
