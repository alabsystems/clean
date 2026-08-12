// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The coordinate-flip involutions, the index-domain (`flipIdx`, on `Fin (2^n)`)
//! and the point-domain (`hcFlip`, on `HCPoint n`) faces of toggling one cube
//! coordinate twice:
//!
//! ```text
//! Bool.not_not          : (b : Bool) → Bool.not (Bool.not b) = b
//! BoolAnalysis.flipIdx_involutive :
//!   (n : Nat) (i : Fin n) (jx : Fin (2^n)) → flipIdx n i (flipIdx n i jx) = jx
//! BoolAnalysis.hcFlip_involutive :
//!   (n : Nat) (x : HCPoint n) (i : Fin n) → hcFlip n (hcFlip n x i) i = x
//! ```
//!
//! `flipIdx n i jx := Fin.mk (2^n) (Nat.xor (val jx) (2^(val i))) _`, so
//! `val (flipIdx n i (flipIdx n i jx)) ≡ Nat.xor (Nat.xor (val jx) (2^(val i))) (2^(val i))`,
//! which `Nat.xor_xor_cancel_right` collapses to `val jx`; `Fin.eq_of_val_eq`
//! lifts the `val`-equality to a `Fin (2^n)` equality.
//!
//! `hcFlip n x i := fun j => Bool.rec (x j) (Bool.not (x j)) (Nat.beq (val j)(val i))`,
//! so `hcFlip n (hcFlip n x i) i` is proved coordinate-wise by `funext`: a
//! `Bool.rec` on the gate `Nat.beq (val j)(val i)` — when the gate is `true` the
//! coordinate is `Bool.not (Bool.not (x j)) = x j` (`Bool.not_not`); when `false`
//! it is `x j` unchanged.
//!
//! Both are kernel-checked `Declaration::Theorem`s with empty admitted-axiom
//! closure (`ProofQuality::Constructive`).

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FiConsts {
    nat: Expr,
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    bool_not: Expr,
    nat_beq: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    nat_xor: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    fin: Expr,
    fin_val: Expr,
    hcpoint: Expr,
    hc_flip: Expr,
    flip_idx: Expr,
    bool_rec1: Expr, // Bool.rec.{1} — Bool-valued motive
    bool_rec0: Expr, // Bool.rec.{0} — Prop motive
    eq1: Expr,
    eq_refl1: Expr,
    funext: Expr,
    fin_eq_of_val: Expr,
}

impl FiConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_not: Expr::const_(Name::from_string("Bool.not"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            #[cfg(test)]
            nat_xor: Expr::const_(Name::from_string("Nat.xor"), vec![]),
            nat_succ: succ,
            nat_zero: zero,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_flip: Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]),
            flip_idx: Expr::const_(Name::from_string("BoolAnalysis.flipIdx"), vec![]),
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]),
            bool_rec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            funext: Expr::const_(Name::from_string("funext"), vec![one.clone(), one]),
            fin_eq_of_val: Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]),
        }
    }

    fn two(&self) -> Expr {
        Expr::app(
            self.nat_succ.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }
    fn pow2(&self, e: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), e])
    }
    fn fin_of(&self, m: Expr) -> Expr {
        Expr::app(self.fin.clone(), m)
    }
    fn hcpoint_of(&self, n: Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n)
    }
    fn not_(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    fn val(&self, m: Expr, k: Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [m, k])
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn nxor(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_xor.clone(), [a, b])
    }
    fn eq_at(&self, ty: Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [ty, l, r])
    }
    fn refl_at(&self, ty: Expr, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [ty, a])
    }
}

// ===========================================================================
// Bool.not_not : (b : Bool) → Bool.not (Bool.not b) = b
// ===========================================================================
fn build_bool_not_not(c: &FiConsts) -> (Expr, Expr) {
    let goal = |b: &Expr| c.eq_at(c.bool_ty.clone(), c.not_(c.not_(b.clone())), b.clone());

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.bool_ty.clone());
        let concl = goal(&x);
        b.finish(b.mk_pi(x_id, BinderInfo::Default, c.bool_ty.clone(), concl))
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.bool_ty.clone());
        // motive : fun (b' : Bool) => goal b'
        let motive = {
            let mut e = EnvDeclBuilder::child_of(&b);
            let (bp_id, bp) = e.fresh_local(c.bool_ty.clone());
            let body = goal(&bp);
            e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, c.bool_ty.clone(), body))
        };
        // leaves: @Eq.refl Bool false / true (LHS ground-reduces to the bool)
        let leaf_false = c.refl_at(c.bool_ty.clone(), c.bfalse.clone());
        let leaf_true = c.refl_at(c.bool_ty.clone(), c.btrue.clone());
        let rec = Expr::apps(
            c.bool_rec0.clone(),
            [motive, leaf_false, leaf_true, x.clone()],
        );
        b.finish(b.mk_lam(x_id, BinderInfo::Default, c.bool_ty.clone(), rec))
    };
    (type_, value)
}

// ===========================================================================
// BoolAnalysis.flipIdx_involutive :
//   (n : Nat) (i : Fin n) (jx : Fin (2^n)) → flipIdx n i (flipIdx n i jx) = jx
// ===========================================================================
fn build_flip_idx_involutive(c: &FiConsts) -> (Expr, Expr) {
    let flip = |n: Expr, i: Expr, jx: Expr| Expr::apps(c.flip_idx.clone(), [n, i, jx]);

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(c.fin_of(c.pow2(n.clone())));
        let lhs = flip(n.clone(), i.clone(), flip(n.clone(), i.clone(), jx.clone()));
        let concl = c.eq_at(c.fin_of(c.pow2(n.clone())), lhs, jx.clone());
        let e = b.mk_pi(
            jx_id,
            BinderInfo::Default,
            c.fin_of(c.pow2(n.clone())),
            concl,
        );
        let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(n.clone()), e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(c.fin_of(c.pow2(n.clone())));

        let pow2n = c.pow2(n.clone());
        let val_i = c.val(n.clone(), i.clone()); // val i
        let two_pow_i = c.pow2(val_i.clone()); // 2^(val i)
        let val_jx = c.val(pow2n.clone(), jx.clone()); // val jx

        let fjx = flip(n.clone(), i.clone(), jx.clone()); // flipIdx n i jx
        let ffjx = flip(n.clone(), i.clone(), fjx.clone()); // flipIdx n i (flipIdx n i jx)

        // val (flipIdx n i jx) ≡ xor (val jx) (2^(val i))   (Fin.val of Fin.mk reduces)
        // val (flipIdx n i (flipIdx n i jx))
        //   ≡ xor (val (flipIdx n i jx)) (2^(val i))
        //   ≡ xor (xor (val jx) (2^(val i))) (2^(val i))   (def-eq, both reductions)
        // hval : Nat.xor (Nat.xor (val jx) (2^(val i))) (2^(val i)) = val jx
        let hval = Expr::apps(
            Expr::const_(Name::from_string("Nat.xor_xor_cancel_right"), vec![]),
            [val_jx.clone(), two_pow_i.clone()],
        );
        // This proof's TYPE LHS is `xor (xor (val jx) 2^(val i)) 2^(val i)`, which is
        // DEF-EQ to `val (flipIdx n i (flipIdx n i jx))`. We feed it to Fin.eq_of_val_eq
        // whose val-equality argument is checked up to def-eq, so we may state it with
        // the reduced spelling and let the kernel align.
        let val_ffjx = c.val(pow2n.clone(), ffjx.clone());
        // We need a proof of `val ffjx = val jx`. `hval : (xor (xor val_jx 2pi) 2pi) = val_jx`.
        // `val ffjx` is def-eq to the LHS of hval. Pass hval; the expected type
        // `Eq Nat (val ffjx) (val jx)` unifies with hval's type by def-eq.
        let _ = val_ffjx;

        // @Fin.eq_of_val_eq (2^n) ffjx jx hval : ffjx = jx
        let out = Expr::apps(
            c.fin_eq_of_val.clone(),
            [pow2n.clone(), ffjx.clone(), jx.clone(), hval],
        );

        let e = b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(pow2n.clone()), out);
        let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(n.clone()), e);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };
    (type_, value)
}

// `build_hc_flip_involutive` (the coordinate-wise funext proof of
// `hcFlip n (hcFlip n x i) i = x`) is split into a sibling file to keep each
// file under the 500-line convention; it shares this module's scope.
include!("boolean_analysis_flip_involution_build.rs");

impl Environment {
    /// Register `Bool.not_not`, `BoolAnalysis.flipIdx_involutive`, and
    /// `BoolAnalysis.hcFlip_involutive` — the coordinate-flip involutions.
    /// Kernel-checked constructive theorems, empty admitted-axiom closure.
    /// Idempotent.
    pub(crate) fn register_flip_involution_proof(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis_foundations()?; // HCPoint, hcDecode, Fin.val
                                                   // hcFlip + flipIdx + Nat.xor_xor_cancel_right (+ Fin.eq_of_val_eq via Fin init).
        self.init_boolean_analysis()?; // registers hcFlip
        self.register_hcflip_decode_roundtrip()?; // registers flipIdx (+ Fin.* + Nat.xor)
        self.register_nat_xor_involution_proof()?; // Nat.xor_xor_cancel_right
        self.init_fin()?; // Fin.eq_of_val_eq

        let c = FiConsts::new();

        let nn = Name::from_string("Bool.not_not");
        if self.get_const(&nn).is_none() {
            let (type_, value) = build_bool_not_not(&c);
            self.add_decl(Declaration::Theorem {
                name: nn,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        let fi = Name::from_string("BoolAnalysis.flipIdx_involutive");
        if self.get_const(&fi).is_none() {
            let (type_, value) = build_flip_idx_involutive(&c);
            self.add_decl(Declaration::Theorem {
                name: fi,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        let hi = Name::from_string("BoolAnalysis.hcFlip_involutive");
        if self.get_const(&hi).is_none() {
            let (type_, value) = build_hc_flip_involutive(&c);
            self.add_decl(Declaration::Theorem {
                name: hi,
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
    fn test_bool_not_not_constructive() {
        let mut env = Environment::with_prelude();
        env.register_flip_involution_proof().expect("register");
        env.register_flip_involution_proof().expect("idempotent");
        check_constructive(&env, "Bool.not_not");
    }

    #[test]
    fn test_flip_idx_involutive_constructive() {
        let mut env = Environment::with_prelude();
        env.register_flip_involution_proof().expect("register");
        check_constructive(&env, "BoolAnalysis.flipIdx_involutive");
    }

    #[test]
    fn test_hc_flip_involutive_constructive() {
        let mut env = Environment::with_prelude();
        env.register_flip_involution_proof().expect("register");
        check_constructive(&env, "BoolAnalysis.hcFlip_involutive");
    }
}
