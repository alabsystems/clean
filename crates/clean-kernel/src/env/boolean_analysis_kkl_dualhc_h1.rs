// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — H1 STEP 1: the per-`S` spectral identity (in isolation).
//!
//! ## What this proves
//!
//! The spectral side of `dualhc_W_eq_spectral` (applied at the derivative carrier
//! `b := pm∘f`, `g := D_i b`) has the per-`S` integrand
//! `levelWt third n S · (A(D_i b, S) · A(D_i b, S))`. This module collapses that
//! integrand into the BAND-usable Fourier form, per `S`:
//!
//! ```text
//! BoolAnalysis.dualhc_per_s_spectral :
//!   ∀ (n : Nat) (f : BoolFn n) (S : HCPoint n) (i : Fin n),
//!     @Eq Rat
//!       (Rat.mul (levelWt third n S) (Rat.mul (A(D_i b,S)) (A(D_i b,S))))
//!       (Rat.mul (Rat.powNat (third·third) (setSizeNat n S))
//!                (Rat.mul (D·D)                              -- (2^n·2^n)
//!                         (Rat.mul (4·ind(S i))             -- 4·ind(S i)
//!                                  (f̂(S)·f̂(S)))))           -- f̂(S)²
//! ```
//!
//! with `third := Rat.mk (Int.ofNat 1) 3`, `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1
//! ≡ 2^n`, `b := pm∘f := fun x => pm (f x)`, `D_i b x := b x − b (hcFlip n x i)`,
//! `A(g,S) := subsetSum n (fun y => g y · χ_S y)`, and
//! `f̂(S) := FourierCoefficient n f S`.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Let `lw := levelWt third n S`, `P := (third·third)^{|S|}`, `Ad := A(D_i b,S)`,
//! `A := A(b,S)`, `c4 := 4·ind(S i)`, `D := 2^n`, `Â := f̂(S)`.
//!
//! 1. `levelWt_eq_powNat third n S` : `lw = P`. `congrArg (·(Ad·Ad))` ⇒
//!    `lw·(Ad·Ad) = P·(Ad·Ad)`.
//! 2. `deriv_coeff_sq_eq n b S i` : `Ad·Ad = c4·(A·A)`. `congrArg (P·)` ⇒
//!    `P·(Ad·Ad) = P·(c4·(A·A))`.
//! 3. inner `c4·(A·A) = (D·D)·(c4·(Â·Â))`:
//!    a. `A = D·Â`  (`acoeff_eq_pow2_fourier n f S`); square both sides ⇒
//!       `A·A = (D·Â)·(D·Â)`.
//!    b. `(D·Â)·(D·Â) = (D·D)·(Â·Â)`  (`mul_mul_mul_comm D Â D Â`).
//!    c. `A·A = (D·D)·(Â·Â)` (a·b), so `c4·(A·A) = c4·((D·D)·(Â·Â))` (`congrArg (c4·)`).
//!    d. regroup `c4·((D·D)·(Â·Â)) = (D·D)·(c4·(Â·Â))`:
//!       `c4·((D·D)·(Â·Â)) = (c4·(D·D))·(Â·Â)`  (`symm mul_assoc`)
//!       `= ((D·D)·c4)·(Â·Â)`                    (`congrArg (·(Â·Â)) (mul_comm c4 (D·D))`)
//!       `= (D·D)·(c4·(Â·Â))`                    (`mul_assoc (D·D) c4 (Â·Â)`).
//!    Then `congrArg (P·)` lifts the inner identity into the level-weight slot.
//! 4. `Eq.trans` chains (1)·(2)·(3-lifted) to land the stated RHS.
//!
//! Every leaf (`levelWt_eq_powNat`, `deriv_coeff_sq_eq`, `acoeff_eq_pow2_fourier`,
//! `Rat.mul_mul_mul_comm`, `Rat.mul_assoc`, `Rat.mul_comm`,
//! `Eq.refl/symm/trans/congrArg`) is a landed `Constructive` Theorem with empty
//! closure, so this identity is too. NO axiom is added or removed. NOT wired into
//! the always-on `init_boolean_analysis` aggregate (reachable via
//! `init_boolean_analysis_kkl_dualhc_h1`). Idempotent.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the per-`S` spectral identity. All `levelWt` / `third` / `pm`
/// / `chi` / `subsetSum` / `hcFlip` / `FourierCoefficient` / `D` spellings are
/// byte-for-byte the landed `WSpectralConsts` / `DerivCoeffConsts` / `InflConsts`
/// conventions so the brick instances stay def-eq to their endpoints.
struct H1Consts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    pm: Expr,
    ind: Expr,
    chi: Expr,
    hc_flip: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    fourier_coeff: Expr,
    rat_mmmc: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl H1Consts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            chi: k("BoolAnalysis.chi"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            level_wt: k("BoolAnalysis.levelWt"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier_coeff: k("BoolAnalysis.FourierCoefficient"),
            rat_mmmc: k("Rat.mul_mul_mul_comm"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── type / numeral helpers ───────────────────────────────────────────────
    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    fn three_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.two_nat())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ 2^n` — byte-identical to
    /// `InflConsts::cube` / `acoeff_eq_pow2_fourier`'s `P`.
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    /// `third := Rat.mk (Int.ofNat 1) 3` — byte-for-byte `WSpectralConsts::third`.
    fn third(&self) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.one_nat());
        Expr::apps(self.rat_mk.clone(), [ofnat, self.three_nat()])
    }
    /// `four := Rat.mk (Int.ofNat 4) 1` — byte-for-byte `deriv_coeff_sq`'s `4`.
    fn four(&self) -> Expr {
        let four_nat = Expr::app(
            self.nat_succ.clone(),
            Expr::app(self.nat_succ.clone(), self.two_nat()),
        );
        let ofnat = Expr::app(self.int_of_nat.clone(), four_nat);
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    // ── term builders ────────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pow(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base.clone(), k.clone()])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn level_wt(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    fn set_size_nat(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fcoeff(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.fourier_coeff.clone(),
            [n.clone(), f.clone(), s.clone()],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn congr(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mmmc.clone(), [a, b, cc, d])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `fun (z : Rat) => left·z` — congruence motive on the RIGHT mul factor.
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(left.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (z : Rat) => z·right` — congruence motive on the LEFT mul factor.
    fn mul_right_motive(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(z, right.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }

    /// `pm∘f := fun (x : HCPoint n) => pm (f x)` — byte-for-byte `InflConsts::pm_f`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.pm_(Expr::app(f.clone(), x.clone()));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `D_i b := fun x => b x − b (hcFlip n x i)` — byte-for-byte
    /// `DerivCoeffConsts::deriv`.
    fn deriv(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.sub(
            Expr::app(b.clone(), x.clone()),
            Expr::app(b.clone(), self.hc_flip_(n, &x, i)),
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `A(g,S) := subsetSum n (fun y => (g y)·(chi n S y))` — byte-for-byte
    /// `DerivCoeffConsts::acoeff` / `WSpectralConsts::a_coeff` / `InflConsts::amp`.
    fn acoeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), y.clone()), self.chi_(n, s, &y));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
}

impl Environment {
    /// Register the H1 STEP-1 per-`S` spectral identity and the STEP-2a `W_i`
    /// band-form bridge. Idempotent; kernel-checked, `Constructive`, empty
    /// domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_h1(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_per_s_spectral()?;
        self.register_dualhc_w_eq_band_form()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_per_s_spectral` — see the module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_per_s_spectral(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_per_s_spectral");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // levelWt, chi, pm, ind, FourierCoefficient, subsetSum
        self.register_subset_sum()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_levelwt_eq_pow_nat()?; // levelWt third n S = (third·third)^|S|
        self.register_deriv_coeff_sq_eq()?; // A(D_i b,S)² = (4·ind(S i))·A(b,S)²
        self.register_acoeff_eq_pow2_fourier()?; // A(pm∘f,S) = 2^n·f̂(S)
        self.register_rat_mul_mul_mul_comm_theorem()?; // (a·b)·(c·d) = (a·c)·(b·d)
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = H1Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_per_s(&c, false),
            value: build_per_s(&c, true),
        })
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_per_s_spectral`.
fn build_per_s(c: &H1Consts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let third = c.third();
    let p_base = c.mul(third.clone(), third.clone()); // third·third
    let size = c.set_size_nat(&n, &s); // |S|
    let p_pow = c.pow(&p_base, &size); // (third·third)^|S|
    let lw = c.level_wt(&third, &n, &s); // levelWt third n S

    let bf = c.pm_f(&b, &n, &f); // b := pm∘f
    let db = c.deriv(&b, &n, &bf, &i); // D_i b
    let ad = c.acoeff(&b, &n, &db, &s); // A(D_i b, S)
    let ad_sq = c.mul(ad.clone(), ad.clone()); // Ad·Ad

    let cap_a = c.acoeff(&b, &n, &bf, &s); // A(b,S)
    let a_sq = c.mul(cap_a.clone(), cap_a.clone()); // A·A

    let si = Expr::app(s.clone(), i.clone());
    let ind = c.ind_(si.clone());
    let c4 = c.mul(c.four(), ind.clone()); // 4·ind(S i)

    let dd = {
        let d = c.cube(&n);
        c.mul(d.clone(), d) // D·D  (2^n·2^n)
    };
    let dcap = c.cube(&n); // D := 2^n
    let fhat = c.fcoeff(&n, &f, &s); // f̂(S)
    let fhat_sq = c.mul(fhat.clone(), fhat.clone()); // Â·Â

    // LHS : lw·(Ad·Ad)
    let lhs = c.mul(lw.clone(), ad_sq.clone());
    // RHS : P·((D·D)·((4·ind)·(Â·Â)))
    let c4_fsq = c.mul(c4.clone(), fhat_sq.clone()); // (4·ind)·(Â·Â)
    let inner_target = c.mul(dd.clone(), c4_fsq.clone()); // (D·D)·((4·ind)·(Â·Â))
    let rhs = c.mul(p_pow.clone(), inner_target.clone());
    let concl = c.eq_rat(lhs.clone(), rhs.clone());

    let tail = if for_value {
        // ── leg 1 : lw·(Ad·Ad) = P·(Ad·Ad)  [congrArg (·(Ad·Ad)) (levelWt_eq_powNat)] ──
        let lep = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.levelWt_eq_powNat"), vec![]),
            [third.clone(), n.clone(), s.clone()],
        ); // lw = P
        let leg1 = {
            let mot = c.mul_right_motive(&b, &ad_sq); // fun z => z·(Ad·Ad)
            c.congr(lw.clone(), p_pow.clone(), mot, lep)
        };
        let p_adsq = c.mul(p_pow.clone(), ad_sq.clone()); // P·(Ad·Ad)

        // ── leg 2 : P·(Ad·Ad) = P·(c4·(A·A))  [congrArg (P·) (deriv_coeff_sq_eq)] ──
        let dcsq = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.deriv_coeff_sq_eq"), vec![]),
            [n.clone(), bf.clone(), s.clone(), i.clone()],
        ); // Ad·Ad = c4·(A·A)
        let c4_asq = c.mul(c4.clone(), a_sq.clone()); // c4·(A·A)
        let leg2 = {
            let mot = c.mul_left_motive(&b, &p_pow); // fun z => P·z
            c.congr(ad_sq.clone(), c4_asq.clone(), mot, dcsq)
        };
        let p_c4asq = c.mul(p_pow.clone(), c4_asq.clone()); // P·(c4·(A·A))

        // ── leg 3 : inner identity c4·(A·A) = (D·D)·(c4·(Â·Â)) ──
        // (3a) A = D·Â  ⇒  A·A = (D·Â)·(D·Â)
        let acf = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.acoeff_eq_pow2_fourier"),
                vec![],
            ),
            [n.clone(), f.clone(), s.clone()],
        ); // A = D·Â
        let d_fhat = c.mul(dcap.clone(), fhat.clone()); // D·Â
        let dfhat_sq = c.mul(d_fhat.clone(), d_fhat.clone()); // (D·Â)·(D·Â)
                                                              // A·A = A·(D·Â)  [congrArg (A·) acf]   then  A·(D·Â) = (D·Â)·(D·Â)  [congrArg (·(D·Â)) acf]
        let sq_a1 = {
            let mot = c.mul_left_motive(&b, &cap_a); // fun z => A·z
            c.congr(cap_a.clone(), d_fhat.clone(), mot, acf.clone())
        };
        let a_dfhat = c.mul(cap_a.clone(), d_fhat.clone()); // A·(D·Â)
        let sq_a2 = {
            let mot = c.mul_right_motive(&b, &d_fhat); // fun z => z·(D·Â)
            c.congr(cap_a.clone(), d_fhat.clone(), mot, acf.clone())
        };
        // A·A = (D·Â)·(D·Â)
        let sq_a = c.trans(
            a_sq.clone(),
            a_dfhat.clone(),
            dfhat_sq.clone(),
            sq_a1,
            sq_a2,
        );

        // (3b) (D·Â)·(D·Â) = (D·D)·(Â·Â)   [mmmc D Â D Â]
        let mmmc_b = c.mmmc(dcap.clone(), fhat.clone(), dcap.clone(), fhat.clone());
        let dd_fsq = c.mul(dd.clone(), fhat_sq.clone()); // (D·D)·(Â·Â)
                                                         // (3a·3b) A·A = (D·D)·(Â·Â)
        let a_sq_eq = c.trans(a_sq.clone(), dfhat_sq.clone(), dd_fsq.clone(), sq_a, mmmc_b);

        // (3c) c4·(A·A) = c4·((D·D)·(Â·Â))   [congrArg (c4·) a_sq_eq]
        let c4_ddfsq = c.mul(c4.clone(), dd_fsq.clone()); // c4·((D·D)·(Â·Â))
        let leg3c = {
            let mot = c.mul_left_motive(&b, &c4); // fun z => c4·z
            c.congr(a_sq.clone(), dd_fsq.clone(), mot, a_sq_eq)
        };

        // (3d) regroup c4·((D·D)·(Â·Â)) = (D·D)·(c4·(Â·Â))
        //   d1 : c4·((D·D)·(Â·Â)) = (c4·(D·D))·(Â·Â)   [symm (mul_assoc c4 (D·D) (Â·Â))]
        let c4_dd = c.mul(c4.clone(), dd.clone()); // c4·(D·D)
        let assoc_full = c.mul_assoc(c4.clone(), dd.clone(), fhat_sq.clone()); // (c4·(D·D))·(Â·Â) = c4·((D·D)·(Â·Â))
        let lhs_assoc = c.mul(c4_dd.clone(), fhat_sq.clone()); // (c4·(D·D))·(Â·Â)
        let d1 = c.symm(lhs_assoc.clone(), c4_ddfsq.clone(), assoc_full);
        //   d2 : (c4·(D·D))·(Â·Â) = ((D·D)·c4)·(Â·Â)   [congrArg (·(Â·Â)) (mul_comm c4 (D·D))]
        let dd_c4 = c.mul(dd.clone(), c4.clone()); // (D·D)·c4
        let mc = c.mul_comm(c4.clone(), dd.clone()); // c4·(D·D) = (D·D)·c4
        let d2 = {
            let mot = c.mul_right_motive(&b, &fhat_sq); // fun z => z·(Â·Â)
            c.congr(c4_dd.clone(), dd_c4.clone(), mot, mc)
        };
        let ddc4_fsq = c.mul(dd_c4.clone(), fhat_sq.clone()); // ((D·D)·c4)·(Â·Â)
                                                              //   d3 : ((D·D)·c4)·(Â·Â) = (D·D)·(c4·(Â·Â))   [mul_assoc (D·D) c4 (Â·Â)]
        let d3 = c.mul_assoc(dd.clone(), c4.clone(), fhat_sq.clone());
        //   regroup chain : c4·((D·D)·(Â·Â)) = (D·D)·(c4·(Â·Â))
        let reg12 = c.trans(
            c4_ddfsq.clone(),
            lhs_assoc.clone(),
            ddc4_fsq.clone(),
            d1,
            d2,
        );
        let regroup = c.trans(
            c4_ddfsq.clone(),
            ddc4_fsq.clone(),
            inner_target.clone(),
            reg12,
            d3,
        );

        // inner : c4·(A·A) = (D·D)·(c4·(Â·Â))   [trans leg3c regroup]
        let inner = c.trans(
            c4_asq.clone(),
            c4_ddfsq.clone(),
            inner_target.clone(),
            leg3c,
            regroup,
        );

        // leg3 : P·(c4·(A·A)) = P·((D·D)·(c4·(Â·Â)))   [congrArg (P·) inner]
        let leg3 = {
            let mot = c.mul_left_motive(&b, &p_pow); // fun z => P·z
            c.congr(c4_asq.clone(), inner_target.clone(), mot, inner)
        };

        // ── chain : lhs = P·(Ad·Ad) = P·(c4·(A·A)) = rhs ──
        let t12 = c.trans(lhs.clone(), p_adsq.clone(), p_c4asq.clone(), leg1, leg2);
        c.trans(lhs.clone(), p_c4asq.clone(), rhs.clone(), t12, leg3)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, i_id, c.fin_of(&n), tail);
    let e = bind(&b, s_id, hcp, e);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_h1()
            .expect("init_boolean_analysis_kkl_dualhc_h1");
        env.init_boolean_analysis_kkl_dualhc_h1()
            .expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_dualhc_per_s_spectral_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.dualhc_per_s_spectral");
    }
}
