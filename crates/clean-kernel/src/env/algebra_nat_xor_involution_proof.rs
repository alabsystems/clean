// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof that XOR by a fixed `b` is an involution:
//!
//! ```text
//! Bool.xor_xor_cancel_right : (t s : Bool) → Bool.xor (Bool.xor t s) s = t
//! Nat.xor_xor_cancel_right  : (a b : Nat)  → Nat.xor  (Nat.xor a b) b  = a
//! ```
//!
//! The `Nat` form is the key involution behind `BoolAnalysis.flipIdx n i`
//! (which toggles bit `val i` by `Nat.xor _ (2^(val i))`): toggling the same
//! bit twice is the identity. It is proved bit-by-bit through the LANDED
//! `Nat.eq_of_testBit_eq` (bit-extensionality) and `Nat.testBit_xor`
//! (`testBit (xor m n) i = Bool.xor (testBit m i) (testBit n i)`), with the
//! per-bit cancellation discharged by the pure-`Bool` `Bool.xor_xor_cancel_right`.
//!
//! `Bool.xor_xor_cancel_right` is a 4-leaf `Bool.rec` on `t` then `s`; each leaf
//! is a closed `@Eq.refl Bool t` because `Bool.xor (Bool.xor t s) s` ground-reduces
//! to `t` for each concrete `(t, s)` (the native `Bool.xor` reducer normalizes
//! both sides). No axiom is introduced; the closure routes through
//! `Bool.rec` / `Nat.rec` / `Eq.*` / `congrArg` and the constructive
//! `Nat.testBit` / bit-extensionality family — `env.axiom_deps` is empty for
//! both declarations (`ProofQuality::Constructive`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the XOR-involution lemmas.
struct XiConsts {
    nat: Expr,
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    bool_xor: Expr,
    nat_xor: Expr,
    testbit: Expr,
    eq1: Expr,       // Eq.{1}
    eq_refl1: Expr,  // Eq.refl.{1}
    eq_trans1: Expr, // Eq.trans.{1}
    congr11: Expr,   // congrArg.{1,1}
    bool_rec0: Expr, // Bool.rec.{0} (Prop motive)
}

impl XiConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            nat_xor: Expr::const_(Name::from_string("Nat.xor"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
            congr11: Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
            bool_rec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        }
    }

    fn bxor(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_xor.clone(), [a, b])
    }
    fn nxor(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_xor.clone(), [a, b])
    }
    fn testbit(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, i])
    }
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), l, r])
    }
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), a])
    }
    /// `@Eq.trans.{1} Bool a b cc h1 h2 : a = cc`.
    fn trans_bool(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.bool_ty.clone(), a, b, cc, h1, h2],
        )
    }
    /// `@congrArg.{1,1} Bool Bool a b g h : g a = g b`.
    fn congr_bool(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr11.clone(),
            [self.bool_ty.clone(), self.bool_ty.clone(), a, b, g, h],
        )
    }
}

// ===========================================================================
// Bool.xor_xor_cancel_right : (t s : Bool) → Bool.xor (Bool.xor t s) s = t
// ===========================================================================
fn build_bool_xor_cancel(c: &XiConsts) -> (Expr, Expr) {
    let goal =
        |t: &Expr, s: &Expr| c.eq_bool(c.bxor(c.bxor(t.clone(), s.clone()), s.clone()), t.clone());

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (t_id, t) = b.fresh_local(c.bool_ty.clone());
        let (s_id, s) = b.fresh_local(c.bool_ty.clone());
        let concl = goal(&t, &s);
        let e = b.mk_pi(s_id, BinderInfo::Default, c.bool_ty.clone(), concl);
        b.finish(b.mk_pi(t_id, BinderInfo::Default, c.bool_ty.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (t_id, t) = b.fresh_local(c.bool_ty.clone());
        let (s_id, s) = b.fresh_local(c.bool_ty.clone());

        // For a fixed concrete `tv`, recurse on `s`; both leaves are ground rfl.
        let inner_rec = |tv: Expr, parent: &EnvDeclBuilder| {
            let mut d = EnvDeclBuilder::child_of(parent);
            // motive_s : fun (s' : Bool) => goal tv s'
            let motive_s = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (sp_id, sp) = e.fresh_local(c.bool_ty.clone());
                let body = goal(&tv, &sp);
                e.finish_child(e.mk_lam(sp_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            // leaf at concrete sv : @Eq.refl Bool tv  (LHS ground-reduces to tv)
            let leaf = |_sv: Expr| c.refl_bool(tv.clone());
            let s_false = leaf(c.bfalse.clone());
            let s_true = leaf(c.btrue.clone());
            let e = Expr::apps(c.bool_rec0.clone(), [motive_s, s_false, s_true, s.clone()]);
            d.finish_child(e)
        };

        // motive_t : fun (t' : Bool) => goal t' s
        let motive_t = {
            let mut e = EnvDeclBuilder::child_of(&b);
            let (tp_id, tp) = e.fresh_local(c.bool_ty.clone());
            let body = goal(&tp, &s);
            e.finish_child(e.mk_lam(tp_id, BinderInfo::Default, c.bool_ty.clone(), body))
        };
        let t_false = inner_rec(c.bfalse.clone(), &b);
        let t_true = inner_rec(c.btrue.clone(), &b);
        let rec_t = Expr::apps(c.bool_rec0.clone(), [motive_t, t_false, t_true, t.clone()]);

        let lam = b.mk_lam(s_id, BinderInfo::Default, c.bool_ty.clone(), rec_t);
        b.finish(b.mk_lam(t_id, BinderInfo::Default, c.bool_ty.clone(), lam))
    };
    (type_, value)
}

// ===========================================================================
// Nat.xor_xor_cancel_right : (a b : Nat) → Nat.xor (Nat.xor a b) b = a
// ===========================================================================
fn build_nat_xor_cancel(c: &XiConsts) -> (Expr, Expr) {
    let nat_xor = c.nat_xor.clone();
    let _ = nat_xor;

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let concl = c.eq_nat(c.nxor(c.nxor(a.clone(), bb.clone()), bb.clone()), a.clone());
        let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
        b.finish(b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let lhs = c.nxor(c.nxor(a.clone(), bb.clone()), bb.clone()); // xor (xor a b) b

        // per-bit proof : fun (i : Nat) => testBit lhs i = testBit a i
        let bit_pf = {
            let mut ib = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = ib.fresh_local(c.nat.clone());

            // tb_a   : testBit a i        (atom)
            let tb_a = c.testbit(a.clone(), i.clone());
            // tb_b   : testBit b i        (atom)
            let tb_b = c.testbit(bb.clone(), i.clone());
            // tb_ab  : testBit (xor a b) i (atom)
            let tb_ab = c.testbit(c.nxor(a.clone(), bb.clone()), i.clone());

            // e1 : testBit (xor (xor a b) b) i = xor (testBit (xor a b) i) (testBit b i)
            //   := Nat.testBit_xor (xor a b) b i
            let e1 = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_xor"), vec![]),
                [c.nxor(a.clone(), bb.clone()), bb.clone(), i.clone()],
            );

            // h_inner : testBit (xor a b) i = xor (testBit a i) (testBit b i)
            //   := Nat.testBit_xor a b i
            let h_inner = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_xor"), vec![]),
                [a.clone(), bb.clone(), i.clone()],
            );
            // e2 : xor (testBit (xor a b) i) (testBit b i)
            //        = xor (xor (testBit a i) (testBit b i)) (testBit b i)
            //   := congrArg (fun w => xor w (testBit b i)) h_inner
            let g_left = {
                let mut lb = EnvDeclBuilder::child_of(&ib);
                let (w_id, w) = lb.fresh_local(c.bool_ty.clone());
                let body = c.bxor(w, tb_b.clone());
                lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            let e2 = c.congr_bool(
                tb_ab.clone(),
                c.bxor(tb_a.clone(), tb_b.clone()),
                g_left,
                h_inner,
            );

            // e3 : xor (xor (testBit a i) (testBit b i)) (testBit b i) = testBit a i
            //   := Bool.xor_xor_cancel_right (testBit a i) (testBit b i)
            let e3 = Expr::apps(
                Expr::const_(Name::from_string("Bool.xor_xor_cancel_right"), vec![]),
                [tb_a.clone(), tb_b.clone()],
            );

            // chain: testBit lhs i
            //   = xor (testBit (xor a b) i) (testBit b i)         (e1)
            //   = xor (xor (testBit a i)(testBit b i))(testBit b i) (e2)
            //   = testBit a i                                       (e3)
            let xor_ab_b = c.bxor(tb_ab.clone(), tb_b.clone());
            let xor_xab_b = c.bxor(c.bxor(tb_a.clone(), tb_b.clone()), tb_b.clone());
            let lhs_bit = c.testbit(lhs.clone(), i.clone());
            let t12 = c.trans_bool(lhs_bit.clone(), xor_ab_b.clone(), xor_xab_b.clone(), e1, e2);
            let out = c.trans_bool(lhs_bit, xor_xab_b, tb_a, t12, e3);

            ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), out))
        };

        // Nat.eq_of_testBit_eq lhs a bit_pf : lhs = a
        let body = Expr::apps(
            Expr::const_(Name::from_string("Nat.eq_of_testBit_eq"), vec![]),
            [lhs, a.clone(), bit_pf],
        );

        let lam = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), body);
        b.finish(b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam))
    };
    (type_, value)
}

impl Environment {
    /// Register `Bool.xor_xor_cancel_right` and `Nat.xor_xor_cancel_right` — the
    /// XOR-involution lemmas. Both are kernel-checked constructive theorems with
    /// empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_nat_xor_involution_proof(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_bool()?;
        // `Nat.testBit_xor` + `Nat.eq_of_testBit_eq` (and their full constructive
        // bit-foundation closure).
        self.register_nat_testbit_bitwise_proof()?;
        self.register_nat_eq_of_testbit_proof()?;

        let c = XiConsts::new();

        let bool_name = Name::from_string("Bool.xor_xor_cancel_right");
        if self.get_const(&bool_name).is_none() {
            let (type_, value) = build_bool_xor_cancel(&c);
            self.add_decl(Declaration::Theorem {
                name: bool_name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        let nat_name = Name::from_string("Nat.xor_xor_cancel_right");
        if self.get_const(&nat_name).is_none() {
            let (type_, value) = build_nat_xor_cancel(&c);
            self.add_decl(Declaration::Theorem {
                name: nat_name,
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(
            &info
                .value
                .clone()
                .unwrap_or_else(|| panic!("{name} has value")),
            &info.type_,
        )
        .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        let deps = env.axiom_deps(&nm).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "{name} closure must be empty (⊆ FOUNDATIONAL_AXIOMS), got {names:?}"
        );
        assert_eq!(
            env.proof_quality(&nm).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_bool_xor_xor_cancel_right_constructive() {
        let mut env = Environment::with_prelude();
        env.register_nat_xor_involution_proof().expect("register");
        env.register_nat_xor_involution_proof().expect("idempotent");
        check_constructive(&env, "Bool.xor_xor_cancel_right");
    }

    #[test]
    fn test_nat_xor_xor_cancel_right_constructive() {
        let mut env = Environment::with_prelude();
        env.register_nat_xor_involution_proof().expect("register");
        env.register_nat_xor_involution_proof().expect("idempotent");
        check_constructive(&env, "Nat.xor_xor_cancel_right");
    }
}
