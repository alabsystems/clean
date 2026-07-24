// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — Stage B3 (1/n): the cube dyadic-floor numerator.
//!
//! # Why this module exists
//!
//! The KKL dual `(4/3 → 4)` hypercontractive two-point base needs the
//! fractional power `x^{4/3} = x · x^{1/3}`, which requires CUBE ROOTS that the
//! landed sqrt layer (`algebra_nnreal_sqrt_*.rs`) does not provide. This module
//! is the cube-root MIRROR of `algebra_nnreal_sqrt_dyadic.rs`: it builds the
//! integer numerator sequence
//!
//! ```text
//!   k_n := largest k with (ofNat k)³ ≤ x · 8^n        (k_n ≈ ⌊cbrt x · 2^n⌋)
//! ```
//!
//! realized DIGIT-BY-DIGIT (so it is a clean primitive `Nat.rec`, NO unbounded
//! search): `k_0 = 0`, and
//!
//! ```text
//!   k_{n+1} = if (ofNat (2·k_n+1))³ ≤ x · 8^{n+1} then 2·k_n+1 else 2·k_n.
//! ```
//!
//! The cube test `(ofNat m)³ ≤ x · 8^{n+1}` is a purely RATIONAL `Rat.le`
//! (division-free: the `8^{n+1}` lives on the RHS, never a divisor), decided by
//! the constructive `Rat.ble` (the same `Bool.rec` discriminator the sqrt layer
//! uses — NOT an admitted axiom). The dyadic scaled approximation is then
//! `a_n := ofNat (k_n) · (Rat.inv (ofNat 2^n))` — identical in FORM to the sqrt
//! approximation, so the telescoping/Cauchy machinery transfers.
//!
//! # The 8^n vs 4^n difference (load-bearing)
//!
//! The sqrt layer uses `4^n = (2^n)²` as the RHS scale (squaring the digit
//! `k/2^n`). The cube layer uses `8^n = (2^n)³` (cubing the digit `k/2^n`):
//! `(k/2^n)³ = k³ / 8^n`. So everywhere the sqrt layer reads `²` / `4^n`, the
//! cube layer reads `³` / `8^n`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.cbrtDyadicPow8 : Nat → Rat` — `8^n` as a `Rat`
//!   (`Rat.powNat (ofNat 8) n`), the RHS scale. Reducible `Definition`.
//! - `Rat.cbrtDyadicNum : Rat → Nat → Nat` — the digit-by-digit numerator `k_n`
//!   above, a `Nat.rec.{1}` with the `Rat.ble` cube digit choice. Reducible
//!   `Definition`.
//!
//! These are DEFINITIONS (no proof obligation beyond well-typedness); their
//! closure bottoms out in `Rat.powNat` / `Rat.ofNat` / `Rat.ble` / `Bool.rec` /
//! `Nat.rec`, all constructive. NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cube dyadic numerator.
pub(crate) struct CbrtDyadicConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    rat: Expr,
    rat_mul: Expr,
    rat_ofnat: Expr,
    rat_pownat: Expr,
    rat_ble: Expr,
    bool_ty: Expr,
    bool_rec_nat: Expr,
    nat_rec_nat: Expr,
}

impl CbrtDyadicConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_mul: k("Nat.mul"),
            rat: k("Rat"),
            rat_mul: k("Rat.mul"),
            rat_ofnat: k("Rat.ofNat"),
            rat_pownat: k("Rat.powNat"),
            rat_ble: k("Rat.ble"),
            bool_ty: k("Bool"),
            // Bool.rec.{1} with a `fun _ : Bool => Nat` motive.
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![lvl1.clone()]),
            // Nat.rec.{1} with a `fun _ : Nat => Nat` motive.
            nat_rec_nat: Expr::const_(Name::from_string("Nat.rec"), vec![lvl1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    /// `Rat.powNat b k`.
    fn rpownat(&self, b: Expr, k: Expr) -> Expr {
        Expr::apps(self.rat_pownat.clone(), [b, k])
    }
    /// `Nat.lit n` via succ-of-zero.
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    /// `Rat.cbrtDyadicPow8 n := Rat.powNat (Rat.ofNat 8) n`.
    fn pow8(&self, n: Expr) -> Expr {
        self.rpownat(self.rofnat(self.nat_lit(8)), n)
    }
    /// `(Rat.ofNat m)³ := Rat.mul (Rat.mul (ofNat m) (ofNat m)) (ofNat m)`.
    fn cube_ofnat(&self, m: Expr) -> Expr {
        let r = self.rofnat(m);
        let sq = self.rmul(r.clone(), r.clone());
        self.rmul(sq, r)
    }
}

impl Environment {
    /// Register the cube dyadic numerator layer (`Rat.cbrtDyadicPow8`,
    /// `Rat.cbrtDyadicNum`). Idempotent; axiom-free (definitions only).
    pub fn init_algebra_nnreal_cbrt_dyadic(&mut self) -> Result<(), EnvError> {
        self.init_nat()?; // Nat, Nat.rec, Nat.add, Nat.mul, Nat.succ/zero
        self.init_bool()?; // Bool, Bool.rec
        self.register_rat_ofnat()?; // Rat.ofNat
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_minmax_proofs()?; // brings in Rat.ble (Bool comparison)

        let c = CbrtDyadicConsts::new();
        self.register_rat_cbrt_dyadic_pow8(&c)?;
        self.register_rat_cbrt_dyadic_num(&c)?;
        Ok(())
    }

    /// `Rat.cbrtDyadicPow8 : Nat → Rat := fun n => Rat.powNat (Rat.ofNat 8) n`.
    fn register_rat_cbrt_dyadic_pow8(&mut self, c: &CbrtDyadicConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicPow8");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.pow8(n);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.cbrtDyadicNum : Rat → Nat → Nat`, the cube digit-by-digit floor.
    ///
    /// ```text
    ///   cbrtDyadicNum x := @Nat.rec.{1} (fun _ => Nat) 0
    ///     (fun n k =>
    ///        @Bool.rec.{1} (fun _ => Nat)
    ///          (Nat.mul 2 k)                              -- ff: keep 2k
    ///          (Nat.add (Nat.mul 2 k) 1)                  -- tt: take 2k+1
    ///          (Rat.ble ((ofNat (2k+1))³) (x · 8^{n+1}))) -- the cube digit test
    /// ```
    ///
    /// `Bool.rec`'s minor premises in Lean order are (ff-branch, tt-branch).
    fn register_rat_cbrt_dyadic_num(&mut self, c: &CbrtDyadicConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicNum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.rat.clone(),
            Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());

            // motive : fun _ : Nat => Nat
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, _t) = m.fresh_local(c.nat.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), c.nat.clone()))
            };
            let base = c.nat_zero.clone();
            // step : fun (n k : Nat) => Bool.rec (fun _ => Nat) (2k) (2k+1) test
            let step = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = s.fresh_local(c.nat.clone());
                let (k_id, kk) = s.fresh_local(c.nat.clone());

                let two_k = c.nmul(c.nat_lit(2), kk.clone());
                let two_k_succ = c.nadd(two_k.clone(), c.nat_lit(1));

                // bool motive : fun _ : Bool => Nat
                let bmotive = {
                    let mut bm = EnvDeclBuilder::child_of(&s);
                    let (bb_id, _bb) = bm.fresh_local(c.bool_ty.clone());
                    bm.finish_child(bm.mk_lam(
                        bb_id,
                        BinderInfo::Default,
                        c.bool_ty.clone(),
                        c.nat.clone(),
                    ))
                };
                // test : Rat.ble ((ofNat (2k+1))³) (x · 8^{n+1}) : Bool
                let rhs_scale = c.pow8(c.succ(n.clone()));
                let test = Expr::apps(
                    c.rat_ble.clone(),
                    [
                        c.cube_ofnat(two_k_succ.clone()),
                        c.rmul(x.clone(), rhs_scale),
                    ],
                );
                // Bool.rec.{1} bmotive (ff→2k) (tt→2k+1) test
                let body = Expr::apps(
                    c.bool_rec_nat.clone(),
                    [bmotive, two_k.clone(), two_k_succ.clone(), test],
                );
                let e = s.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
                let e = s.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                s.finish_child(e)
            };

            // Nat.rec.{1} motive base step : Nat → Nat ; eta-expose the `n` arg so
            // cbrtDyadicNum x : Nat → Nat.
            let rec = Expr::apps(c.nat_rec_nat.clone(), [motive, base, step]);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), rec))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["Rat.cbrtDyadicPow8", "Rat.cbrtDyadicNum"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_dyadic()
            .expect("init_algebra_nnreal_cbrt_dyadic");
        env.init_algebra_nnreal_cbrt_dyadic().expect("idempotent");
        env
    }

    #[test]
    fn test_cbrt_dyadic_defs_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition"
            );
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }
}
