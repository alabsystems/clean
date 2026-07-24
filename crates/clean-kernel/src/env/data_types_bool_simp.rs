// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bool-level simplification equalities registered as real, kernel-checked
//! `Declaration::Theorem`s (NO axiom, NO `sorry`):
//!
//! - `Bool.true_and`  : `(true && b)  = b`     (rfl)
//! - `Bool.false_and` : `(false && b) = false` (rfl)
//! - `Bool.false_or`  : `(false || b) = b`     (rfl)
//! - `Bool.true_or`   : `(true || b)  = true`  (rfl)
//! - `Bool.and_true`  : `(b && true)  = b`      (`Bool.rec` on `b`)
//! - `Bool.and_false` : `(b && false) = false`  (`Bool.rec` on `b`)
//! - `Bool.or_false`  : `(b || false) = b`       (`Bool.rec` on `b`)
//! - `Bool.or_true`   : `(b || true)  = true`    (`Bool.rec` on `b`)
//! - `Bool.and_self`  : `(b && b) = b`           (`Bool.rec` on `b`)
//! - `Bool.or_self`   : `(b || b) = b`           (`Bool.rec` on `b`)
//! - `Bool.not_not`   : `(!!b) = b`              (`Bool.rec` on `b`)
//!
//! # Definitional facts (`data_types_nat.rs::register_bool_surface`)
//!
//! `Bool.and a b := Bool.rec false b a` and `Bool.or a b := Bool.rec b true a`
//! both recurse on their FIRST argument; `Bool.not b := Bool.rec true false b`.
//! `Bool.rec` minors are in constructor order: `false`-case, then `true`-case.
//!
//! Hence the four `(true/false ◦ b)` lemmas hold by pure `@Eq.refl Bool <rhs>`
//! (the ground first argument iota-reduces the recursor), and the seven lemmas
//! that vary `b` hold by a single `@Bool.rec.{0}` over the bound `b` whose two
//! ground-constructor leaves are each `@Eq.refl Bool <rhs>`. This is the exact
//! shape of `algebra_bool_comm_proof.rs::register_bool_comm_proof`, simplified
//! to ONE bound variable (a single `Bool.rec`, not a nested 2×2).
//!
//! # Axiom closure
//!
//! Every lemma's transitive axiom closure is empty (`Bool.rec`/`Eq.refl` are
//! recursor/constructor, not `Declaration::Axiom`), so the domain-specific
//! axiom count in `data/axiom_audit.json` is unchanged. Each is routed through
//! the normal checked `add_decl` so the kernel re-verifies the proof term.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Kernel constants reused when building the Bool-simp proof terms.
struct BoolSimpConsts {
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    and_op: Expr,
    or_op: Expr,
    not_op: Expr,
    /// `Eq.{1}` — equality at `Bool : Sort 1`.
    eq_const: Expr,
    /// `Eq.refl.{1}`.
    eq_refl: Expr,
    /// `Bool.rec.{0}` — the motive lands in `Prop = Sort 0`.
    bool_rec: Expr,
}

impl BoolSimpConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            and_op: Expr::const_(Name::from_string("Bool.and"), vec![]),
            or_op: Expr::const_(Name::from_string("Bool.or"), vec![]),
            not_op: Expr::const_(Name::from_string("Bool.not"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![one]),
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        }
    }

    fn and(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.and_op.clone(), [a, b])
    }
    fn or(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.or_op.clone(), [a, b])
    }
    fn not(&self, b: Expr) -> Expr {
        Expr::app(self.not_op.clone(), b)
    }
    /// `@Eq Bool lhs rhs`.
    fn eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.bool_ty.clone(), lhs, rhs])
    }
    /// `@Eq.refl Bool x : Eq Bool x x`.
    fn refl(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.bool_ty.clone(), x])
    }
}

impl Environment {
    /// Register the Bool-level simp equalities as real, kernel-checked
    /// `Declaration::Theorem`s.
    ///
    /// # Contract
    ///
    /// REQUIRES: nothing — seeds `Bool` (+`Bool.rec`/`Bool.and`/`Bool.or`/
    ///           `Bool.not`) and `Eq`/`Eq.refl` via the idempotent `init_*`
    ///           calls below.
    /// ENSURES: On success each lemma resolves via `env.get_const(name)`.
    /// ENSURES: Idempotent — re-invocation (and per-lemma `get_const` guards)
    ///          make this a no-op when already registered.
    /// ENSURES: Each lemma's transitive axiom closure is empty; the
    ///          domain-specific axiom count is unchanged.
    pub(crate) fn init_bool_simp_lemmas(&mut self) -> Result<(), EnvError> {
        if self.bool_simp_lemmas_init {
            return Ok(());
        }

        self.init_eq()?;
        self.init_bool()?;

        let c = BoolSimpConsts::new();

        // --- rfl lemmas: ground first-argument iota-reduces the recursor. ---
        // `Bool.true_and : (true && b) = b`.
        self.register_bool_rfl_lemma("Bool.true_and", &c, |c, b| {
            (c.and(c.btrue.clone(), b.clone()), b.clone())
        })?;
        // `Bool.false_and : (false && b) = false`.
        self.register_bool_rfl_lemma("Bool.false_and", &c, |c, b| {
            (c.and(c.bfalse.clone(), b.clone()), c.bfalse.clone())
        })?;
        // `Bool.false_or : (false || b) = b`.
        self.register_bool_rfl_lemma("Bool.false_or", &c, |c, b| {
            (c.or(c.bfalse.clone(), b.clone()), b.clone())
        })?;
        // `Bool.true_or : (true || b) = true`.
        self.register_bool_rfl_lemma("Bool.true_or", &c, |c, b| {
            (c.or(c.btrue.clone(), b.clone()), c.btrue.clone())
        })?;

        // --- recursor lemmas: single `Bool.rec` on `b`, two reflexivity leaves.
        // `Bool.and_true : (b && true) = b`.
        self.register_bool_rec_lemma(
            "Bool.and_true",
            &c,
            |c, b| (c.and(b.clone(), c.btrue.clone()), b.clone()),
            |c| c.bfalse.clone(),
            |c| c.btrue.clone(),
        )?;
        // `Bool.and_false : (b && false) = false`.
        self.register_bool_rec_lemma(
            "Bool.and_false",
            &c,
            |c, b| (c.and(b.clone(), c.bfalse.clone()), c.bfalse.clone()),
            |c| c.bfalse.clone(),
            |c| c.bfalse.clone(),
        )?;
        // `Bool.or_false : (b || false) = b`.
        self.register_bool_rec_lemma(
            "Bool.or_false",
            &c,
            |c, b| (c.or(b.clone(), c.bfalse.clone()), b.clone()),
            |c| c.bfalse.clone(),
            |c| c.btrue.clone(),
        )?;
        // `Bool.or_true : (b || true) = true`.
        self.register_bool_rec_lemma(
            "Bool.or_true",
            &c,
            |c, b| (c.or(b.clone(), c.btrue.clone()), c.btrue.clone()),
            |c| c.btrue.clone(),
            |c| c.btrue.clone(),
        )?;
        // `Bool.and_self : (b && b) = b`.
        self.register_bool_rec_lemma(
            "Bool.and_self",
            &c,
            |c, b| (c.and(b.clone(), b.clone()), b.clone()),
            |c| c.bfalse.clone(),
            |c| c.btrue.clone(),
        )?;
        // `Bool.or_self : (b || b) = b`.
        self.register_bool_rec_lemma(
            "Bool.or_self",
            &c,
            |c, b| (c.or(b.clone(), b.clone()), b.clone()),
            |c| c.bfalse.clone(),
            |c| c.btrue.clone(),
        )?;
        // `Bool.not_not : (!!b) = b`. May already be present via the
        // flip-involution path; the per-lemma `get_const` guard makes this a
        // no-op in that case.
        self.register_bool_rec_lemma(
            "Bool.not_not",
            &c,
            |c, b| (c.not(c.not(b.clone())), b.clone()),
            |c| c.bfalse.clone(),
            |c| c.btrue.clone(),
        )?;

        self.bool_simp_lemmas_init = true;
        Ok(())
    }

    /// Register `<name> : ∀ (b : Bool), @Eq Bool lhs(b) rhs(b)` whose value is
    /// `fun (b : Bool) => @Eq.refl Bool rhs(b)`.
    ///
    /// Sound only when `lhs(b)` is definitionally equal to `rhs(b)` for the
    /// generic `b` (the case for `true && b`, `false && b`, `false || b`,
    /// `true || b`, where the ground FIRST argument iota-reduces the recursor).
    fn register_bool_rfl_lemma(
        &mut self,
        name: &str,
        c: &BoolSimpConsts,
        build_lhs_rhs: impl Fn(&BoolSimpConsts, &Expr) -> (Expr, Expr),
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        // Type: ∀ (b : Bool), @Eq Bool lhs rhs
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.bool_ty.clone());
            let (lhs, rhs) = build_lhs_rhs(c, &x);
            let body = c.eq(lhs, rhs);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.bool_ty.clone(), body);
            b.finish(e)
        };

        // Value: fun (b : Bool) => @Eq.refl Bool rhs
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.bool_ty.clone());
            let (_lhs, rhs) = build_lhs_rhs(c, &x);
            let refl = c.refl(rhs);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.bool_ty.clone(), refl);
            b.finish(e)
        };

        // SOUNDNESS: pure `@Eq.refl Bool rhs` term; the kernel accepts it
        // against `lhs = rhs` because the ground first argument of the Bool
        // binop iota-reduces `lhs` to `rhs`. Routed through the checked
        // `add_decl`. Axiom closure empty; NOT an Axiom, NOT unchecked.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `<name> : ∀ (b : Bool), @Eq Bool lhs(b) rhs(b)` whose value is a
    /// single `@Bool.rec.{0}` over `b` with two ground-constructor reflexivity
    /// leaves `@Eq.refl Bool (false_leaf)` / `@Eq.refl Bool (true_leaf)`.
    ///
    /// `false_leaf`/`true_leaf` give `rhs(false)`/`rhs(true)` respectively;
    /// each leaf type-checks because at a ground `b` both `lhs(b)` and `rhs(b)`
    /// reduce to the same ground `Bool`.
    fn register_bool_rec_lemma(
        &mut self,
        name: &str,
        c: &BoolSimpConsts,
        build_lhs_rhs: impl Fn(&BoolSimpConsts, &Expr) -> (Expr, Expr),
        false_leaf: impl Fn(&BoolSimpConsts) -> Expr,
        true_leaf: impl Fn(&BoolSimpConsts) -> Expr,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        // Type: ∀ (b : Bool), @Eq Bool lhs rhs
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.bool_ty.clone());
            let (lhs, rhs) = build_lhs_rhs(c, &x);
            let body = c.eq(lhs, rhs);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.bool_ty.clone(), body);
            b.finish(e)
        };

        // Value: fun (b : Bool) => @Bool.rec.{0} motive leaf_false leaf_true b
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.bool_ty.clone());

            // motive : fun (b' : Bool) => @Eq Bool lhs(b') rhs(b')
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (bp_id, bp) = m.fresh_local(c.bool_ty.clone());
                let (lhs, rhs) = build_lhs_rhs(c, &bp);
                let body = c.eq(lhs, rhs);
                m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            let leaf_false = c.refl(false_leaf(c));
            let leaf_true = c.refl(true_leaf(c));
            let rec = Expr::apps(
                c.bool_rec.clone(),
                [motive, leaf_false, leaf_true, x.clone()],
            );
            let e = b.mk_lam(x_id, BinderInfo::Default, c.bool_ty.clone(), rec);
            b.finish(e)
        };

        // SOUNDNESS: single `@Bool.rec.{0}` casework over `b` with two
        // `@Eq.refl Bool _` leaves (each ground constructor reduces both sides
        // to the same `Bool`). Recursor + constructor only; no `Declaration::
        // Axiom`, no `sorry`, no self-reference. Routed through checked
        // `add_decl`; axiom closure empty.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
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

    const FAMILY: [&str; 11] = [
        "Bool.true_and",
        "Bool.false_and",
        "Bool.false_or",
        "Bool.true_or",
        "Bool.and_true",
        "Bool.and_false",
        "Bool.or_false",
        "Bool.or_true",
        "Bool.and_self",
        "Bool.or_self",
        "Bool.not_not",
    ];

    fn registered() -> Environment {
        let mut env = Environment::new();
        env.init_bool_simp_lemmas().expect("registration");
        env.init_bool_simp_lemmas()
            .expect("idempotent re-registration");
        env
    }

    #[test]
    fn test_bool_simp_family_registered_as_theorems() {
        let env = registered();
        for name in FAMILY {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem, not {:?}",
                info.kind
            );
            assert!(
                info.value.is_some(),
                "{name} must retain its proof value (not a body-less Axiom)"
            );
        }
    }

    #[test]
    fn test_bool_simp_family_proof_terms_typecheck() {
        let env = registered();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in FAMILY {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.as_ref().expect("Theorem has value");
            tc.check_type(value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} proof term must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_bool_simp_family_axiom_closure_empty() {
        let env = registered();
        for name in FAMILY {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered, axiom_deps should be Some"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{name} must have EMPTY domain-axiom closure, got {names:?}"
            );
            assert_eq!(
                env.proof_quality(&Name::from_string(name)),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
        }
    }

    #[test]
    fn test_bool_simp_family_present_in_prelude() {
        let env = Environment::with_prelude();
        for name in FAMILY {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} must resolve in the default prelude env"
            );
        }
    }
}
