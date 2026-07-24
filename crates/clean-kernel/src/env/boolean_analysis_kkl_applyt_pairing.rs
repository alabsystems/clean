// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3, the **Fubini/pairing bridge** over the
//! materialized operator `BoolAnalysis.applyT` (design §10.8, STEP 3).
//!
//! # The theorem
//!
//! ```text
//! BoolAnalysis.applyT_pairing_eq_two_norm :
//!   ∀ (n : Nat) (g : HCPoint n → Rat),
//!     subsetSum n (fun x => Rat.mul (applyT (1/9) n g x) (g x))     -- ⟨applyT(1/9)g, g⟩
//!       = subsetSum n (fun S =>                                      -- = ‖T_{1/3}g‖₂²
//!           Rat.mul (Rat.mul (powNat (1/3) |S|) (powNat (1/3) |S|))
//!                   (Rat.mul (A g S) (A g S)))
//! ```
//!
//! i.e. the single-sum pairing of the materialized operator value equals the
//! spectral 2-norm `‖T_{1/3}g‖₂²` (the LHS of the landed B3a
//! `BoolAnalysis.noise_two_norm_eq_pairing`). With `A g S := subsetSum n (fun x
//! => g x · χ_S x)` and `|S| := Fin.sumNat n (fun i => indNat (S i))`, both built
//! byte-for-byte from the B3a shapes so the spectral endpoint is def-eq.
//!
//! # Why the SPECTRAL 2-norm (not the spatial `Σ_x sq(applyT(1/3)g x)`)
//!
//! B3a expresses `‖T_{1/3}g‖₂²` in its SPECTRAL form `Σ_S ((1/3)^{|S|})²·A(S)²`.
//! The SPATIAL square `Σ_x sq(applyT(1/3)g x)` equals `2^n · (that spectral sum)`
//! by character orthogonality (`Σ_x χ_S χ_T = 2^n·δ_{S,T}`) — a separate Parseval
//! pass carrying a `2^n`. The dual-bound assembly consumes the pairing
//! `l := ⟨applyT(1/9)g, g⟩` directly (via B3a), so the spectral form is the
//! faithful, axiom-free target; the `2^n`-carrying spatial Parseval is NOT needed.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! Let `RHSpair := subsetSum n (fun x => Σ_y (g x·g y)·noiseDensityW (1/9) n x y)`
//! (the B3a RHS, the spatial double-sum `⟨T_{1/9}g, g⟩`). Two legs:
//!
//! 1. **LHS = RHSpair** — the materialization Fubini. `subsetSum_congr` over the
//!    per-`x` equality
//!    ```text
//!    applyT(1/9)g x · g x  =  Σ_y (g x·g y)·noiseDensityW (1/9) n x y
//!    ```
//!    chained as: `mul_comm` (`a·g x = g x·a`), then `applyT(1/9)g x` δ-unfolds to
//!    `Σ_y g y·W x y` so the term is `g x·Σ_y g y·W x y`; `Eq.symm subsetSum_smul`
//!    pulls the constant `g x` IN to give `Σ_y g x·(g y·W x y)`; an inner
//!    `subsetSum_congr` rewrites `g x·(g y·W) → (g x·g y)·W` per `y` by
//!    `Eq.symm (Rat.mul_assoc (g x)(g y)(W))`.
//! 2. **RHSpair = ‖T_{1/3}g‖₂²** — `Eq.symm (noise_two_norm_eq_pairing n g)` (B3a
//!    states `‖T_{1/3}g‖₂² = RHSpair`).
//!
//! `Eq.trans` chains the legs. Every leaf (`subsetSum_congr`, `subsetSum_smul`,
//! `Rat.mul_comm`, `Rat.mul_assoc`, `noise_two_norm_eq_pairing`, `Eq.symm`,
//! `Eq.trans`) is `Constructive` with empty admitted-axiom closure, so this
//! identity is too. No axiom is added or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the materialization Fubini bridge.
struct PairingConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    bool_: Expr,
    rat_mul: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    pow_nat: Expr,
    chi: Expr,
    hcpoint: Expr,
    fin: Expr,
    fin_sum_nat: Expr,
    bool_rec_nat: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    applyt: Expr,
    noise_density: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    two_norm_eq_pairing: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
}

impl PairingConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            bool_: k("Bool"),
            rat_mul: k("Rat.mul"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            pow_nat: k("Rat.powNat"),
            chi: k("BoolAnalysis.chi"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            fin_sum_nat: k("Fin.sumNat"),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            applyt: k("BoolAnalysis.applyT"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            two_norm_eq_pairing: k("BoolAnalysis.noise_two_norm_eq_pairing"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn pow(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base.clone(), k.clone()])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn applyt(&self, rho: &Expr, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            self.applyt.clone(),
            [rho.clone(), n.clone(), g.clone(), x.clone()],
        )
    }
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), l, r, h])
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `subsetSum_smul n cc f : subsetSum n (fun y => cc·f y) = cc · subsetSum n f`.
    fn ssum_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `Rat.mul_comm a b : Eq Rat (a·b) (b·a)`.
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mul_assoc a b c : Eq Rat ((a·b)·c) (a·(b·c))`.
    fn mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }

    /// `Rat.mk (Int.ofNat 1) d` — the literal `1/d`, byte-for-byte the B3a
    /// `one_over` build (so `1/9` matches `applyT (1/9)` and B3a's RHS density).
    fn one_over(&self, d: u32) -> Expr {
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut d_nat = self.nat_zero.clone();
        for _ in 0..d {
            d_nat = Expr::app(self.nat_succ.clone(), d_nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), one_nat), d_nat],
        )
    }

    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — byte-for-byte B3a.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            self.bool_rec_nat.clone(),
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — byte-for-byte B3a.
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(self.fin_sum_nat.clone(), [n.clone(), pc_fn])
    }
    /// `A g S = subsetSum n (fun x => g x · χ_S x)` — byte-for-byte B3a.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), x.clone()), self.chi_(n, s, &x));
        let f = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// LHS pairing `x`-integrand `fun x => applyT(1/9)g x · g x`.
    fn lhs_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let ninth = self.one_over(9);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.applyt(&ninth, n, g, &x),
            Expr::app(g.clone(), x.clone()),
        );
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// B3a's RHS `x`-integrand `fun x => Σ_y (g x·g y)·noiseDensityW (1/9) n x y`
    /// — byte-for-byte the B3a `rhs_x_fn` shape (`⟨T_{1/9}g, g⟩`).
    fn rhs_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let ninth = self.one_over(9);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let gx_gy = self.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(g.clone(), y.clone()),
            );
            let body = self.mul(gx_gy, self.density(&ninth, n, &x, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }

    /// B3a's LHS `S`-integrand `fun S => ((1/3)^{|S|}·(1/3)^{|S|})·(A·A)`
    /// (`‖T_{1/3}g‖₂²` spectral summand) — byte-for-byte the B3a `lhs_s_fn`.
    fn spectral_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let third = self.one_over(3);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let pc = self.popcount(&b, n, &s);
        let w_third = self.pow(&third, &pc);
        let w = self.mul(w_third.clone(), w_third);
        let aa = {
            let inner = self.a_coeff(&b, n, g, &s);
            self.mul(inner.clone(), inner)
        };
        let body = self.mul(w, aa);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

/// Build the type + proof of `BoolAnalysis.applyT_pairing_eq_two_norm`.
fn build_pairing(c: &PairingConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let g_ty = c.hcpoint_to_rat(&n);
        let (g_id, g) = b.fresh_local(g_ty.clone());
        let lhs = c.ssum(&n, c.lhs_x_fn(&b, &n, &g));
        let rhs = c.ssum(&n, c.spectral_s_fn(&b, &n, &g));
        let concl = c.eq_rat(lhs, rhs);
        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let g_ty = c.hcpoint_to_rat(&n);
        let (g_id, g) = b.fresh_local(g_ty.clone());

        let ninth = c.one_over(9);

        let lhs_fn = c.lhs_x_fn(&b, &n, &g);
        let rhs_pair_fn = c.rhs_x_fn(&b, &n, &g);
        let spectral_fn = c.spectral_s_fn(&b, &n, &g);

        let lhs = c.ssum(&n, lhs_fn.clone());
        let rhs_pair = c.ssum(&n, rhs_pair_fn.clone());
        let spectral = c.ssum(&n, spectral_fn.clone());

        // leg1 : LHS = RHSpair, via subsetSum_congr over the per-x Fubini equality
        //   applyT(1/9)g x · g x = Σ_y (g x·g y)·W(1/9) x y.
        let leg1 = {
            let hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (x_id, x) = d.fresh_local(hcp.clone());

                let gx = Expr::app(g.clone(), x.clone());
                let at = c.applyt(&ninth, &n, &g, &x); // applyT(1/9)g x

                // inner f over y : fun y => g y · W(1/9) x y  (= the applyT summand).
                let inner_f = {
                    let mut yb = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let body = c.mul(
                        Expr::app(g.clone(), y.clone()),
                        c.density(&ninth, &n, &x, &y),
                    );
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };

                // step_comm : applyT(1/9)g x · g x = g x · applyT(1/9)g x  (mul_comm at·gx)
                let step_comm = c.mul_comm(&at, &gx);
                // step_smul : Σ_y (g x · (g y·W x y)) = g x · Σ_y (g y·W x y)
                //   (subsetSum_smul n (g x) inner_f). Its RHS `g x · subsetSum n inner_f`
                //   is def-eq to `g x · applyT(1/9)g x` (applyT δ-unfolds to subsetSum inner_f).
                //   Eq.symm gives `g x · applyT(1/9)g x = Σ_y g x·(g y·W x y)`.
                let smul = c.ssum_smul(&n, &gx, &inner_f);
                // smul : subsetSum n (fun y => g x·(g y·W)) = g x · subsetSum n inner_f
                //      ≡ g x · applyT(1/9)g x
                let gx_smul_lhs = {
                    // the integrand `fun y => g x · (g y·W x y)`
                    let mut yb = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let inner = c.mul(
                        Expr::app(g.clone(), y.clone()),
                        c.density(&ninth, &n, &x, &y),
                    );
                    let body = c.mul(gx.clone(), inner);
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                let ssum_gx_inner = c.ssum(&n, gx_smul_lhs.clone()); // Σ_y g x·(g y·W)
                let gx_at = c.mul(gx.clone(), at.clone()); // g x · applyT(1/9)g x
                                                           // smul_sym : g x · applyT(1/9)g x = Σ_y g x·(g y·W)   (Eq.symm of smul,
                                                           //   whose RHS `g x · subsetSum n inner_f` is def-eq to `g x · applyT(1/9)g x`).
                let smul_sym = c.symm(ssum_gx_inner.clone(), gx_at.clone(), smul);

                // step_assoc : Σ_y g x·(g y·W) = Σ_y (g x·g y)·W
                //   (subsetSum_congr over per-y Eq.symm (mul_assoc (g x)(g y)(W))).
                let target_inner_f = {
                    let mut yb = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let gy = Expr::app(g.clone(), y.clone());
                    let w = c.density(&ninth, &n, &x, &y);
                    let body = c.mul(c.mul(gx.clone(), gy), w);
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                let per_y = {
                    let mut yb = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let gy = Expr::app(g.clone(), y.clone());
                    let w = c.density(&ninth, &n, &x, &y);
                    // mul_assoc (g x)(g y)(W) : (g x·g y)·W = g x·(g y·W)
                    let assoc = c.mul_assoc(&gx, &gy, &w);
                    // Eq.symm : g x·(g y·W) = (g x·g y)·W
                    let lhs_e = c.mul(gx.clone(), c.mul(gy.clone(), w.clone()));
                    let rhs_e = c.mul(c.mul(gx.clone(), gy.clone()), w.clone());
                    let body = c.symm(rhs_e, lhs_e, assoc);
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                let assoc_congr = c.ssum_congr(&n, &gx_smul_lhs, &target_inner_f, per_y);
                let ssum_target = c.ssum(&n, target_inner_f.clone()); // Σ_y (g x·g y)·W

                // Chain: at·gx =(comm) gx·at =(smul_sym) Σ gx·(gy·W) =(assoc) Σ (gx·gy)·W.
                let at_gx = c.mul(at.clone(), gx.clone());
                let t1 = c.trans(
                    at_gx.clone(),
                    gx_at.clone(),
                    ssum_gx_inner.clone(),
                    step_comm,
                    smul_sym,
                );
                let body = c.trans(at_gx, ssum_gx_inner, ssum_target, t1, assoc_congr);
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
            };
            c.ssum_congr(&n, &lhs_fn, &rhs_pair_fn, hyp)
        };

        // leg2 : RHSpair = ‖T_{1/3}g‖₂²  via Eq.symm (noise_two_norm_eq_pairing n g)
        //   (B3a : ‖T_{1/3}g‖₂² = RHSpair).
        let b3a = Expr::apps(c.two_norm_eq_pairing.clone(), [n.clone(), g.clone()]);
        let leg2 = c.symm(spectral.clone(), rhs_pair.clone(), b3a);

        // proof : LHS = ‖T_{1/3}g‖₂²
        let proof = c.trans(lhs, rhs_pair, spectral, leg1, leg2);

        let e = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

impl Environment {
    /// Register `BoolAnalysis.applyT_pairing_eq_two_norm` — the materialization
    /// Fubini bridge `⟨applyT(1/9)g, g⟩ = ‖T_{1/3}g‖₂²` (spectral form). Lifts the
    /// per-`x` Fubini through `subsetSum_congr`/`subsetSum_smul` and chains
    /// `Eq.symm` of the landed B3a `noise_two_norm_eq_pairing`. Kernel-checked,
    /// `ProofQuality::Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_applyt_pairing_eq_two_norm(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.applyT_pairing_eq_two_norm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_applyt()?; // applyT (+ noiseDensityW, subsetSum)
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_rat_mul_comm_proof()?;
        self.register_noise_two_norm_eq_pairing()?;
        self.init_rat_field_inst()?; // Rat.mul_assoc
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PairingConsts::new();
        let (ty, value) = build_pairing(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Init hook for the `applyT` pairing-bridge overlay module.
    pub fn init_boolean_analysis_kkl_applyt_pairing(&mut self) -> Result<(), EnvError> {
        self.register_applyt_pairing_eq_two_norm()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_applyt_pairing()
            .expect("init_boolean_analysis_kkl_applyt_pairing");
        env.init_boolean_analysis_kkl_applyt_pairing()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_applyt_pairing_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.applyT_pairing_eq_two_norm");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("applyT_pairing proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
