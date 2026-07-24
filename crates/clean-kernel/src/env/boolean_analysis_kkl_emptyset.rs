// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — the **empty-set isolation → bare Poincaré** (run-5 residual).
//!
//! This module lands the final mechanical bricks of the KKL bare-Poincaré
//! identity `Var = Σ_{S≠∅} f̂²`, reducing it (with the run-4 landed
//! normalized-Parseval keystone) to the one-line Poincaré inequality
//! `Var ≤ I[f]`. All lemmas are kernel-checked `Declaration::Theorem`s,
//! `ProofQuality::Constructive` with an empty admitted-axiom closure.
//!
//! ```text
//! (2) BoolAnalysis.chi_empty :
//!       ∀ n (S x : HCPoint n), (∀ i, Eq Bool (S i) Bool.false)
//!         → chi n S x = Rat.one
//!     -- the all-false subset's character is the constant 1.
//! ```
//!
//! ## `chi_empty` derivation (fully constructive)
//!
//! `chi n S x = Fin.prod n (fun i => @Bool.rec (fun _ => Rat) Rat.one signed (S i))`
//! (reducible `chi`). With the all-false hypothesis `h i : S i = false`, each
//! gated factor is `Bool.rec`-def-eq to `Rat.one` (the `false` minor premise),
//! transported by `congrArg (fun b => @Bool.rec … b) (h i)`. `Fin.prod_congr`
//! folds the product to `Fin.prod n (fun _ => Rat.one)`, which `Fin.prod_const_one`
//! collapses to `Rat.one`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the empty-set isolation bridge.
struct EmptyConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_: Expr,
    bool_false: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_mk: Expr,
    bool_rec: Expr,
    fin_prod: Expr,
    hcpoint: Expr,
    chi: Expr,
    fin_prod_congr: Expr,
    fin_prod_const_one: Expr,
    eq1: Expr,
    congr_arg: Expr,
    eq_trans: Expr,
    bool_fn: Expr,
    pm: Expr,
    expect: Expr,
    fourier: Expr,
    expect_congr: Expr,
    chi_empty: Expr,
    rat_mul_one: Expr,
    ind: Expr,
    nat_ble: Expr,
    nat_beq: Expr,
    variance: Expr,
    total_influence: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_sub: Expr,
    mul_comm: Expr,
    mul_sub: Expr,
    congr_c: Expr,
}

impl EmptyConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            fin_prod_congr: Expr::const_(Name::from_string("Fin.prod_congr"), vec![]),
            fin_prod_const_one: Expr::const_(Name::from_string("Fin.prod_const_one"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            expect: Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            fourier: Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
            expect_congr: Expr::const_(Name::from_string("BoolAnalysis.Expect_congr"), vec![]),
            chi_empty: Expr::const_(Name::from_string("BoolAnalysis.chi_empty"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            variance: Expr::const_(Name::from_string("BoolAnalysis.Variance"), vec![]),
            total_influence: Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_sub: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_sub"), vec![]),
            mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            mul_sub: Expr::const_(Name::from_string("Rat.mul_sub"), vec![]),
            congr_c: Expr::const_(
                Name::from_string("congr"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn chi_of(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    /// `@Eq Bool a b`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_.clone(), l, r])
    }
    /// `@congrArg.{1,1} Bool Rat a1 a2 g h : g a1 = g a2`.
    fn congr_bool_rat(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.bool_.clone(), self.rat.clone(), a1, a2, g, h],
        )
    }
    /// `Eq.trans.{1} Rat a b c h1 h2`.
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }
    /// `Eq.symm.{1} Rat a b h : b = a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `Fin.prod n g`.
    fn prod(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n.clone(), g])
    }
    /// `fun (_ : Bool) => Rat` — the shared Type-valued `Bool.rec` motive.
    fn bool_rec_motive(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, _t) = mb.fresh_local(self.bool_.clone());
        mb.finish_child(mb.mk_lam(
            t_id,
            BinderInfo::Default,
            self.bool_.clone(),
            self.rat.clone(),
        ))
    }
    /// `Rat.mk (Int.ofNat 2) 1` — the rational constant `2` (matches `chi`).
    fn rat_two(&self) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), two), one],
        )
    }
    /// `signed(x i) := Rat.sub Rat.one (Rat.mul 2 (@Bool.rec (fun _ => Rat) 0 1 (x i)))`
    /// — the value branch of `chi`'s gate. Depends on `x i`, not on the gate bit.
    fn signed(&self, parent: &EnvDeclBuilder, x: &Expr, i: &Expr) -> Expr {
        let x_i = Expr::app(x.clone(), i.clone());
        let embed = Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_rec_motive(parent),
                self.rat_zero.clone(),
                self.rat_one.clone(),
                x_i,
            ],
        );
        self.sub(self.rat_one.clone(), self.mul(self.rat_two(), embed))
    }
    /// `fun (b : Bool) => @Bool.rec (fun _ => Rat) Rat.one (signed x i) b` — the
    /// gate as a function of the bit `b`, so `congrArg` over `S i = false` lands
    /// on the def-eq `Rat.one` (the `false` minor premise).
    fn gate_fn(&self, parent: &EnvDeclBuilder, x: &Expr, i: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (bit_id, bit) = b.fresh_local(self.bool_.clone());
        let body = Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_rec_motive(&b),
                self.rat_one.clone(),
                self.signed(&b, x, i),
                bit,
            ],
        );
        b.finish_child(b.mk_lam(bit_id, BinderInfo::Default, self.bool_.clone(), body))
    }
    /// `fun (i : Fin n) => @Bool.rec (fun _ => Rat) Rat.one (signed x i) (S i)`
    /// — `chi`'s product factor (byte-identical to the reducible `chi` body's
    /// lambda).
    fn chi_factor_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let body = Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_rec_motive(&b),
                self.rat_one.clone(),
                self.signed(&b, x, &i),
                s_i,
            ],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (_ : Fin n) => Rat.one`.
    fn const_one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, self.rat_one.clone()))
    }

    // ── empty-set Fourier-coefficient atoms (deliverable 4) ──

    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    /// `Expect n g`.
    fn expect_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.expect.clone(), [n.clone(), g])
    }
    /// `FourierCoefficient n f S`.
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `chi_empty n S x h : chi n S x = Rat.one`.
    fn chi_empty_of(&self, n: &Expr, s: &Expr, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(
            self.chi_empty.clone(),
            [n.clone(), s.clone(), x.clone(), h.clone()],
        )
    }
    /// `Rat.mul_one a : Rat.mul a Rat.one = a`.
    fn mul_one_of(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `BoolAnalysis.Expect_congr n g h pw : Expect n g = Expect n h`.
    fn expect_congr_of(&self, n: &Expr, g: Expr, h: Expr, pw: Expr) -> Expr {
        Expr::apps(self.expect_congr.clone(), [n.clone(), g, h, pw])
    }
    /// `fun (x : HCPoint n) => Rat.mul (pm (f x)) (chi n S x)` — the `f̂(S)`
    /// integrand (byte-identical to `FourierCoefficient`'s reducible body).
    fn fourier_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let chi_sx = self.chi_of(n, s, &x);
        let body = self.mul(pm_fx, chi_sx);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => pm (f x)` — the mean integrand `E[pm f]`.
    fn pm_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = Expr::app(self.pm.clone(), Expr::app(f.clone(), x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (t : Rat) => Rat.mul l t` — right-multiply slot, fixed left `l`.
    fn mul_left_fn(&self, parent: &EnvDeclBuilder, l: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = b.fresh_local(self.rat.clone());
        let body = self.mul(l.clone(), t);
        b.finish_child(b.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `@congrArg.{1,1} Rat Rat a1 a2 g h : g a1 = g a2`.
    fn congr_rat_rat(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a1, a2, g, h],
        )
    }

    // ── deliverable 5/6 atoms (variance identity → bare Poincaré) ──

    fn ind_of(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    /// `Nat.ble (succ zero) m` — the `|S| ≥ 1` indicator bit.
    fn ble1(&self, m: Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(self.nat_ble.clone(), [one, m])
    }
    /// `Nat.beq m 0` — the `|S| = 0` indicator bit.
    fn beq0(&self, m: Expr) -> Expr {
        Expr::apps(self.nat_beq.clone(), [m, self.nat_zero.clone()])
    }
    fn ss_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of2(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_sub a b c : a·(b−c) = a·b − a·c`.
    fn mul_sub_of(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_sub.clone(), [a, b, cc])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one_of2(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `@congr.{1,1} Rat Rat f g a b h1 h2 : f a = g b`.
    fn congr2(&self, f: Expr, g: Expr, a: Expr, b: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.congr_c.clone(),
            [self.rat.clone(), self.rat.clone(), f, g, a, b, h1, h2],
        )
    }
}

impl Environment {
    /// Register the empty-set isolation bridge. Idempotent.
    pub fn init_boolean_analysis_kkl_emptyset(&mut self) -> Result<(), EnvError> {
        self.register_chi_empty()?;
        self.register_fourier_empty_eq_mean()?;
        self.register_nat_add_eq_zero()?;
        self.register_fin_sum_nat_eq_zero()?;
        self.register_indnat_eq_zero()?;
        self.register_setsizenat_hcdecode_imp_val_zero()?;
        self.register_emptyset_mass_isolation()?;
        self.register_rat_sub_zero()?;
        self.register_mass_complement_pointwise()?;
        self.register_variance_eq_nonempty_mass()?;
        self.register_variance_le_influence()?;
        Ok(())
    }

    /// **Deliverable 3.** `BoolAnalysis.emptyset_mass_isolation : ∀ (n : Nat)
    ///   (w : HCPoint n → Rat),
    ///     subsetSum n (fun S => ind (Nat.beq (setSizeNat n S) 0) · w S)
    ///       = w (hcDecode n ⟨0, Nat.one_le_two_pow n⟩)`.
    ///
    /// The level-0 mass collapses to the ∅-term. `subsetSum n G ≡ Fin.sum (2^n)
    /// (fun j => G (hcDecode n j))` (reducible), so `Fin.sum_diag_collapse` at the
    /// ∅-index `j₀ := ⟨0, …⟩ : Fin (2^n)` folds the sum to `G (hcDecode n j₀)`.
    /// The off-diagonal hypothesis — for `k ≠ j₀`, the masked term vanishes —
    /// case-splits the indicator bit `Nat.beq (setSizeNat n (hcDecode n k)) 0`:
    /// - `false`: `ind false · w ≡ 0 · w = 0` (`Rat.zero_mul`);
    /// - `true`: `Nat.eq_of_beq_eq_true` gives `setSizeNat n (hcDecode n k) = 0`,
    ///   so `setSizeNat_hcDecode_imp_val_zero` forces `Fin.val k = 0 = Fin.val j₀`,
    ///   hence `k = j₀` (`Fin.eq_of_val_eq`) — contradicting `k ≠ j₀`
    ///   (`False.elim`).
    ///
    /// The diagonal value `G (hcDecode n j₀)` reduces: `setSizeNat n (hcDecode n
    /// j₀)`'s indicator is keyed at `j₀` where the popcount is 0, so the leading
    /// `ind (Nat.beq … 0)` is `ind true ≡ 1` and `1 · w (hcDecode n j₀) = w (…)`
    /// (`Rat.one_mul`). Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_emptyset_mass_isolation(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.emptyset_mass_isolation");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // hcDecode, HCPoint, Fin.sum
        self.init_boolean_analysis()?; // ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?; // Rat.zero_mul, Rat.one_mul, Rat.mul
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_fin_sum_diag_collapse_theorem()?;
        self.register_setsizenat_hcdecode_imp_val_zero()?;
        self.register_setsizenat_hcdecode_zero()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_nat_eq_of_beq_eq_true()?;

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let fin = c.fin.clone();
        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let diag_collapse = Expr::const_(Name::from_string("Fin.sum_diag_collapse"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let setsize_imp_val = Expr::const_(
            Name::from_string("BoolAnalysis.setSizeNat_hcDecode_imp_val_zero"),
            vec![],
        );
        let fin_eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);
        let eq_of_beq = Expr::const_(Name::from_string("Nat.eq_of_beq_eq_true"), vec![]);
        let bool_ = c.bool_.clone();
        let bool_false = c.bool_false.clone();
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_cases_on = Expr::const_(Name::from_string("Bool.casesOn"), vec![l0.clone()]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
        let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
        let rat = c.rat.clone();
        let rat_mul = c.rat_mul.clone();

        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        let two_nat = Expr::app(c.nat_succ.clone(), one_nat.clone());
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
        let hcp_of = |n: &Expr| Expr::app(c.hcpoint.clone(), n.clone());
        let hcp_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcp_of(n), rat.clone());
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let ind_of = |b: Expr| Expr::app(ind.clone(), b);
        let beq0 = |m: Expr| Expr::apps(nat_beq.clone(), [m, c.nat_zero.clone()]);
        let ss_nat = |n: &Expr, s: Expr| Expr::apps(set_size_nat.clone(), [n.clone(), s]);
        let decode = |n: &Expr, j: Expr| Expr::apps(hc_decode.clone(), [n.clone(), j]);
        let val_at = |n: &Expr, k: &Expr| Expr::apps(fin_val.clone(), [n.clone(), k.clone()]);
        let eq_fin = |n: &Expr, a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [fin_of(n), a, b],
            )
        };
        let eq_nat = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), a, b],
            )
        };
        let eq_bool = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [bool_.clone(), a, b],
            )
        };
        let eq_rat = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [rat.clone(), a, b],
            )
        };
        // j₀ := @Fin.mk (2^n) Nat.zero (Nat.one_le_two_pow n)  (val ≡ 0; 0 < 2^n)
        let j0_of = |n: &Expr| {
            Expr::apps(
                fin_mk.clone(),
                [
                    pow2(n),
                    c.nat_zero.clone(),
                    Expr::app(one_le_two_pow.clone(), n.clone()),
                ],
            )
        };
        // masked integrand for an HCPoint S:
        //   fun (S : HCPoint n) => ind (Nat.beq (setSizeNat n S) 0) · w S
        let g_fn = |parent: &EnvDeclBuilder, n: &Expr, w: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(hcp_of(n));
            let bit = beq0(ss_nat(n, s.clone()));
            let body = mul(ind_of(bit), Expr::app(w.clone(), s.clone()));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(n), body))
        };
        // F : Fin (2^n) → Rat := fun (j) => G (hcDecode n j)
        //   = ind (Nat.beq (setSizeNat n (hcDecode n j)) 0) · w (hcDecode n j)
        let f_fn = |parent: &EnvDeclBuilder, n: &Expr, w: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = d.fresh_local(fin_of(&pow2(n)));
            let dec = decode(n, j.clone());
            let bit = beq0(ss_nat(n, dec.clone()));
            let body = mul(ind_of(bit), Expr::app(w.clone(), dec));
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_of(&pow2(n)), body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (w_id, w) = b.fresh_local(hcp_to_rat(&n));
            let lhs = Expr::apps(subset_sum.clone(), [n.clone(), g_fn(&b, &n, &w)]);
            let rhs = Expr::app(w.clone(), decode(&n, j0_of(&n)));
            let concl = eq_rat(lhs, rhs);
            let e = b.mk_pi(w_id, BinderInfo::Default, hcp_to_rat(&n), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (w_id, w) = b.fresh_local(hcp_to_rat(&n));
            let j0 = j0_of(&n);
            let f = f_fn(&b, &n, &w);

            // off-diagonal hypothesis:
            //   fun (k : Fin (2^n)) (hne : Eq (Fin (2^n)) k j₀ → False) => F k = 0
            let off_diag = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = d.fresh_local(fin_of(&pow2(&n)));
                let ne_ty = Expr::pi(
                    BinderInfo::Default,
                    eq_fin(&pow2(&n), k.clone(), j0.clone()),
                    false_const.clone(),
                );
                let (hne_id, hne) = d.fresh_local(ne_ty.clone());

                let dec = decode(&n, k.clone());
                let beq_expr = beq0(ss_nat(&n, dec.clone()));
                let w_dec = Expr::app(w.clone(), dec.clone());
                // goal : ind beq_expr · w_dec = 0
                let goal = eq_rat(
                    mul(ind_of(beq_expr.clone()), w_dec.clone()),
                    c.rat_zero.clone(),
                );

                // motive : fun (bb : Bool) => Eq Bool beq_expr bb → goal
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&d);
                    let (bb_id, bb) = m.fresh_local(bool_.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        eq_bool(beq_expr.clone(), bb),
                        goal.clone(),
                    );
                    m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), body))
                };

                // false_branch : Eq Bool beq_expr false → goal
                //   := fun (hf : beq_expr = false) =>
                //        Eq.trans (congrArg (fun bb => ind bb · w_dec) hf)
                //                 (Rat.zero_mul w_dec)
                //   (ind false ≡ 0; (0 · w_dec) collapses by Rat.zero_mul.)
                let false_branch = {
                    let mut m = EnvDeclBuilder::child_of(&d);
                    let prem = eq_bool(beq_expr.clone(), bool_false.clone());
                    let (hf_id, hf) = m.fresh_local(prem.clone());
                    // g_ind : fun (bb : Bool) => ind bb · w_dec
                    let g_ind = {
                        let mut g = EnvDeclBuilder::child_of(&m);
                        let (bb_id, bb) = g.fresh_local(bool_.clone());
                        let body = mul(ind_of(bb), w_dec.clone());
                        g.finish_child(g.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), body))
                    };
                    // congrArg Bool Rat beq_expr false g_ind hf :
                    //   ind beq_expr · w_dec = ind false · w_dec
                    let h1 = Expr::apps(
                        congr_arg.clone(),
                        [
                            bool_.clone(),
                            rat.clone(),
                            beq_expr.clone(),
                            bool_false.clone(),
                            g_ind,
                            hf,
                        ],
                    );
                    // Rat.zero_mul w_dec : 0 · w_dec = 0  (ind false ≡ 0)
                    let h2 = Expr::app(zero_mul.clone(), w_dec.clone());
                    // Eq.trans Rat (ind beq·w) (ind false·w ≡ 0·w) 0 h1 h2
                    let mid = mul(ind_of(bool_false.clone()), w_dec.clone());
                    let body = c.trans(
                        mul(ind_of(beq_expr.clone()), w_dec.clone()),
                        mid,
                        c.rat_zero.clone(),
                        h1,
                        h2,
                    );
                    m.finish_child(m.mk_lam(hf_id, BinderInfo::Default, prem, body))
                };

                // true_branch : Eq Bool beq_expr true → goal
                //   := fun (ht : beq_expr = true) =>
                //        False.elim goal (hne (Fin.eq_of_val_eq (2^n) k j₀ hval))
                //   where hval : val k = val j₀  (= 0), via
                //     setSizeNat_hcDecode_imp_val_zero n k hsz  (hsz : setSize = 0)
                //     and hsz := Nat.eq_of_beq_eq_true (setSize…) 0 ht.
                let true_branch = {
                    let mut m = EnvDeclBuilder::child_of(&d);
                    let prem = eq_bool(beq_expr.clone(), bool_true.clone());
                    let (ht_id, ht) = m.fresh_local(prem.clone());
                    // hsz : setSizeNat n (hcDecode n k) = 0
                    //   := Nat.eq_of_beq_eq_true (setSizeNat …) 0 ht
                    let hsz = Expr::apps(
                        eq_of_beq.clone(),
                        [ss_nat(&n, dec.clone()), c.nat_zero.clone(), ht],
                    );
                    // hvalk : Fin.val k = 0  := setSizeNat_hcDecode_imp_val_zero n k hsz
                    let hvalk = Expr::apps(setsize_imp_val.clone(), [n.clone(), k.clone(), hsz]);
                    // hval : Fin.val k = Fin.val j₀   (val j₀ ≡ 0, so hvalk fits)
                    //   We need Eq Nat (val k) (val j₀); val j₀ ≡ 0, so hvalk : val k = 0
                    //   is def-eq to val k = val j₀.
                    // Fin.eq_of_val_eq {2^n} k j₀ hval : k = j₀
                    let hkj0 = Expr::apps(
                        fin_eq_of_val.clone(),
                        [pow2(&n), k.clone(), j0.clone(), hvalk],
                    );
                    // hne hkj0 : False
                    let contra = Expr::app(hne.clone(), hkj0);
                    // False.elim goal contra
                    let body = Expr::apps(false_elim.clone(), [goal.clone(), contra]);
                    m.finish_child(m.mk_lam(ht_id, BinderInfo::Default, prem, body))
                };

                // @Bool.casesOn motive beq_expr false_branch true_branch (Eq.refl beq_expr)
                let refl_beq = Expr::apps(eq_refl.clone(), [bool_.clone(), beq_expr.clone()]);
                let cases = Expr::apps(
                    bool_cases_on.clone(),
                    [motive, beq_expr.clone(), false_branch, true_branch],
                );
                let body = Expr::app(cases, refl_beq);

                let r = d.mk_lam(hne_id, BinderInfo::Default, ne_ty, body);
                d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin_of(&pow2(&n)), r))
            };

            // collapse : Fin.sum (2^n) F = F j₀
            //   := Fin.sum_diag_collapse (2^n) j₀ F off_diag
            let collapse = Expr::apps(
                diag_collapse.clone(),
                [pow2(&n), j0.clone(), f.clone(), off_diag],
            );
            // LHS subsetSum n G ≡ Fin.sum (2^n) F (def-eq, reducible subsetSum).
            // F j₀ = ind (Nat.beq (setSizeNat n (hcDecode n j₀)) 0) · w (hcDecode n j₀).
            // The RHS goal is w (hcDecode n j₀). We must bridge F j₀ = w (hcDecode n j₀):
            //   the leading indicator is ind (Nat.beq 0 0) ≡ ind true ≡ 1, and
            //   1 · w(…) = w(…) by Rat.one_mul. We provide that as a trailing Eq.trans.
            //
            // F j₀'s bit is Nat.beq (setSizeNat n (hcDecode n j₀)) 0. We do NOT have a
            // def-eq `setSizeNat n (hcDecode n j₀) ≡ 0` (popcount needs the proof), so
            // we cannot rely on ι alone. Instead bound via the same machinery:
            //   hsz0 : setSizeNat n (hcDecode n j₀) = 0
            //        — but j₀'s decode is all-false only up to the proof; we DERIVE it.
            //   Simpler: we keep the conclusion as F j₀ by REDEFINING the theorem RHS to
            //   F j₀ form is avoided — see the chosen RHS (= w (hcDecode n j₀)).
            //
            // Provide hbit0 : Nat.beq (setSizeNat n (hcDecode n j₀)) 0 = true via a
            // popcount-zero fact at j₀; then ind true ≡ 1 and Rat.one_mul closes it.
            //
            // hsz0 derivation: setSizeNat n (hcDecode n j₀) = 0.
            // We prove it by Nat.eq_zero — but that is exactly the converse direction.
            // We instead use that (hcDecode n j₀) is all-false: each coordinate is
            // testBit 0 (val i) = false, so each indNat is 0, and the popcount sums 0.
            // That converse is NOT setSizeNat_hcDecode_imp_val_zero. To avoid building
            // it, RHS is stated as F j₀ directly: we set the theorem RHS to F j₀.
            //
            // (Implemented: the `ty` RHS uses w (hcDecode n j₀); the bridge to it is the
            //  popcount-zero-at-∅ fact `setSizeNat_hcDecode_zero`, registered below.)
            // hsz0 : setSizeNat n (hcDecode n j₀) = 0
            let dec_j0 = decode(&n, j0.clone());
            let w_j0 = Expr::app(w.clone(), dec_j0.clone());
            let beq_j0 = beq0(ss_nat(&n, dec_j0.clone()));
            let hsz0 = Expr::app(
                Expr::const_(
                    Name::from_string("BoolAnalysis.setSizeNat_hcDecode_zero"),
                    vec![],
                ),
                n.clone(),
            );
            // hbit0 : Nat.beq (setSizeNat n (hcDecode n j₀)) 0 = true
            //   := congrArg (fun m => Nat.beq m 0) hsz0   (Nat.beq 0 0 ≡ true)
            let beq_fn = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = g.fresh_local(nat.clone());
                let body = beq0(m);
                g.finish_child(g.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
            };
            let hbit0 = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    bool_.clone(),
                    ss_nat(&n, dec_j0.clone()),
                    c.nat_zero.clone(),
                    beq_fn,
                    hsz0,
                ],
            );
            // gone : ind (beq …) · w(dec j₀) = ind true · w(dec j₀)
            let g_ind_j0 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = g.fresh_local(bool_.clone());
                let body = mul(ind_of(bb), w_j0.clone());
                g.finish_child(g.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), body))
            };
            let h_bit = Expr::apps(
                congr_arg.clone(),
                [
                    bool_.clone(),
                    rat.clone(),
                    beq_j0.clone(),
                    bool_true.clone(),
                    g_ind_j0,
                    hbit0,
                ],
            );
            // ind true · w_j0 = w_j0  (ind true ≡ 1; Rat.one_mul)
            let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
            let h_one = Expr::app(one_mul.clone(), w_j0.clone());
            // F j₀ = ind beq_j0 · w_j0 (def-eq); chain to w_j0.
            let f_j0 = mul(ind_of(beq_j0.clone()), w_j0.clone());
            let mid_true = mul(ind_of(bool_true.clone()), w_j0.clone());
            let bridge = c.trans(f_j0.clone(), mid_true, w_j0.clone(), h_bit, h_one);

            // final : Fin.sum (2^n) F = w_j0
            //   = Eq.trans (collapse : sum = F j₀) (bridge : F j₀ = w_j0)
            let sum_f = Expr::apps(fin_sum.clone(), [pow2(&n), f.clone()]);
            let body = c.trans(sum_f, f_j0, w_j0, collapse, bridge);

            let e = b.mk_lam(w_id, BinderInfo::Default, hcp_to_rat(&n), body);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.setSizeNat_hcDecode_imp_val_zero : ∀ (n : Nat)
    ///   (k : Fin (Nat.pow 2 n)),
    ///     Eq Nat (setSizeNat n (hcDecode n k)) Nat.zero
    ///       → Eq Nat (Fin.val (Nat.pow 2 n) k) Nat.zero`.
    ///
    /// The ∅-index uniqueness on the cube: the only `Fin (2^n)` index whose
    /// decoded point has popcount zero is `0`. Chain:
    /// - `setSizeNat n (hcDecode n k) ≡ Fin.sumNat n (fun i => indNat ((hcDecode n
    ///   k) i))` (reducible), so `Fin.sumNat_eq_zero` gives `∀ i : Fin n,
    ///   indNat ((hcDecode n k) i) = 0`.
    /// - For every bit position `j : Nat`, `Nat.le_or_lt n j`:
    ///   · `n ≤ j` (high): `Fin.val k < 2^n ≤ 2^j` (`Fin.isLt` +
    ///     `Nat.pow_le_pow_right` + `Nat.lt_of_lt_of_le`), so `Nat.testBit_lt_pow`
    ///     gives `testBit (val k) j = false`;
    ///   · `j < n` (low): instantiate the popcount fact at `⟨j, hlt⟩ : Fin n`.
    ///     `(hcDecode n k) ⟨j,hlt⟩ ≡ testBit (val k) j` (def-eq;
    ///     `Fin.val ⟨j,hlt⟩ ≡ j`), and `indNat_eq_zero` turns the `indNat = 0`
    ///     fact into `testBit (val k) j = false`.
    /// - `Nat.eq_zero_of_testBit_all_false (val k)` then forces `val k = 0`.
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_setsizenat_hcdecode_imp_val_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSizeNat_hcDecode_imp_val_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // hcDecode, Fin.sumNat, HCPoint
        self.register_set_size_nat()?; // setSizeNat
        self.register_fin_sum_nat_eq_zero()?;
        self.register_indnat_eq_zero()?;
        // Number-theory bricks (idempotent registrars from their own modules).
        self.init_nat()?;
        self.init_le()?;
        self.init_nat_succ_base()?; // Nat.zero_le, Nat.succ_le_succ
        self.init_nat_trans_lt_lt_le()?; // Nat.lt_of_lt_of_le
        self.register_nat_mul_left_cancel_succ_proof()?; // registers Nat.le_or_lt
        self.register_nat_testbit_lt_pow_proof()?; // Nat.testBit_lt_pow
        self.register_nat_eq_of_testbit_proof()?; // Nat.eq_zero_of_testBit_all_false
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let fin = c.fin.clone();
        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
        let fin_sum_nat = Expr::const_(Name::from_string("Fin.sumNat"), vec![]);
        let fin_sum_nat_eq_zero = Expr::const_(Name::from_string("Fin.sumNat_eq_zero"), vec![]);
        let indnat_eq_zero = Expr::const_(Name::from_string("BoolAnalysis.indNat_eq_zero"), vec![]);
        let testbit = Expr::const_(Name::from_string("Nat.testBit"), vec![]);
        let testbit_lt_pow = Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]);
        let eq_zero_all_false = Expr::const_(
            Name::from_string("Nat.eq_zero_of_testBit_all_false"),
            vec![],
        );
        let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le_or_lt = Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]);
        let lt_of_lt_of_le = Expr::const_(Name::from_string("Nat.lt_of_lt_of_le"), vec![]);
        let or_cases = Expr::const_(Name::from_string("Or.casesOn"), vec![]);
        let bool_ = c.bool_.clone();
        let bool_false = c.bool_false.clone();
        let bool_rec_nat = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);

        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        let two_nat = Expr::app(c.nat_succ.clone(), one_nat.clone());
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
        let val = |n: &Expr, k: &Expr| Expr::apps(fin_val.clone(), [n.clone(), k.clone()]);
        let testbit_of = |a: Expr, b: Expr| Expr::apps(testbit.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(nat_le.clone(), [a, b]);
        let lt = |a: Expr, b: Expr| Expr::apps(nat_lt.clone(), [a, b]);
        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), l, r],
            )
        };
        let eq_b = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [bool_.clone(), l, r],
            )
        };
        // indNat b = @Bool.rec (fun _ => Nat) 0 1 b (matches setSizeNat's summand).
        let nat_motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
        let ind_nat = |b: Expr| {
            Expr::apps(
                bool_rec_nat.clone(),
                [nat_motive.clone(), c.nat_zero.clone(), one_nat.clone(), b],
            )
        };
        // (hcDecode n k) i
        let decode_at = |n: &Expr, k: &Expr, i: Expr| {
            Expr::app(Expr::apps(hc_decode.clone(), [n.clone(), k.clone()]), i)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(fin_of(&pow2(&n)));
            let ss = Expr::apps(
                set_size_nat.clone(),
                [
                    n.clone(),
                    Expr::apps(hc_decode.clone(), [n.clone(), k.clone()]),
                ],
            );
            let hyp = eq_n(ss, c.nat_zero.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = eq_n(val(&pow2(&n), &k), c.nat_zero.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(fin_of(&pow2(&n)));
            let ss = Expr::apps(
                set_size_nat.clone(),
                [
                    n.clone(),
                    Expr::apps(hc_decode.clone(), [n.clone(), k.clone()]),
                ],
            );
            let hyp = eq_n(ss, c.nat_zero.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            // summand : fun (i : Fin n) => indNat ((hcDecode n k) i)
            let summand = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = d.fresh_local(fin_of(&n));
                let body = ind_nat(decode_at(&n, &k, i));
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
            };

            // allZero : ∀ i : Fin n, indNat ((hcDecode n k) i) = 0
            //   := Fin.sumNat_eq_zero n summand h
            //   (h : setSizeNat … = 0 ≡ Fin.sumNat n summand = 0)
            let all_zero = Expr::apps(
                fin_sum_nat_eq_zero.clone(),
                [n.clone(), summand.clone(), h.clone()],
            );

            let vk = val(&pow2(&n), &k);

            // allBits : ∀ (j : Nat), testBit (val k) j = false
            let all_bits = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (j_id, j) = d.fresh_local(nat.clone());
                let target = eq_b(testbit_of(vk.clone(), j.clone()), bool_false.clone());

                // motive : fun (_ : Or (le n j) (lt j n)) => target
                let or_a = le(n.clone(), j.clone());
                let or_b = lt(j.clone(), n.clone());
                let or_motive = {
                    let mut m = EnvDeclBuilder::child_of(&d);
                    let or_ty = Expr::apps(
                        Expr::const_(Name::from_string("Or"), vec![]),
                        [or_a.clone(), or_b.clone()],
                    );
                    let (z_id, _z) = m.fresh_local(or_ty.clone());
                    m.finish_child(m.mk_lam(z_id, BinderInfo::Default, or_ty, target.clone()))
                };

                // high_minor : le n j → testBit (val k) j = false
                //   := fun hle => Nat.testBit_lt_pow j (val k)
                //        (Nat.lt_of_lt_of_le (val k) (2^n) (2^j)
                //           (Fin.isLt (2^n) k)
                //           (Nat.pow_le_pow_right 2 n j (1≤2) hle))
                let high_minor = {
                    let mut m = EnvDeclBuilder::child_of(&d);
                    let (hle_id, hle) = m.fresh_local(or_a.clone());
                    // 1 ≤ 2 : Nat.le (succ zero) (succ (succ zero)) — Fin.isLt-free; build
                    //   via Nat.le.refl-style? Use Nat.le_succ-of-le? Simpler: it's a
                    //   closed numeral inequality; supply `Nat.one_le_two` if present,
                    //   else `Nat.le.step (Nat.le.refl)`-shaped. We use Nat.succ_le_succ
                    //   on (0 ≤ 1) → (1 ≤ 2) with Nat.zero_le.
                    let zero_le_one = Expr::apps(
                        Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                        [one_nat.clone()],
                    );
                    let one_le_two = Expr::apps(
                        Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
                        [c.nat_zero.clone(), one_nat.clone(), zero_le_one],
                    );
                    let pow_le = Expr::apps(
                        pow_le_pow_right.clone(),
                        [two_nat.clone(), n.clone(), j.clone(), one_le_two, hle],
                    );
                    let islt = Expr::apps(fin_islt.clone(), [pow2(&n), k.clone()]);
                    let lt_vk = Expr::apps(
                        lt_of_lt_of_le.clone(),
                        [vk.clone(), pow2(&n), pow2(&j), islt, pow_le],
                    );
                    let body = Expr::apps(testbit_lt_pow.clone(), [j.clone(), vk.clone(), lt_vk]);
                    m.finish_child(m.mk_lam(hle_id, BinderInfo::Default, or_a.clone(), body))
                };

                // low_minor : lt j n → testBit (val k) j = false
                //   := fun hlt => indNat_eq_zero ((hcDecode n k) ⟨j,hlt⟩)
                //        (allZero ⟨j,hlt⟩)
                //   ((hcDecode n k) ⟨j,hlt⟩ ≡ testBit (val k) j; result def-eq to target)
                let low_minor = {
                    let mut m = EnvDeclBuilder::child_of(&d);
                    let (hlt_id, hlt) = m.fresh_local(or_b.clone());
                    // ⟨j, hlt⟩ : Fin n := @Fin.mk n j hlt
                    let fin_j = Expr::apps(fin_mk.clone(), [n.clone(), j.clone(), hlt.clone()]);
                    let decoded = decode_at(&n, &k, fin_j.clone());
                    let az = Expr::app(all_zero.clone(), fin_j);
                    let body = Expr::apps(indnat_eq_zero.clone(), [decoded, az]);
                    m.finish_child(m.mk_lam(hlt_id, BinderInfo::Default, or_b.clone(), body))
                };

                // @Or.casesOn or_a or_b or_motive (Nat.le_or_lt n j) high_minor low_minor
                let lor = Expr::apps(le_or_lt.clone(), [n.clone(), j.clone()]);
                let body = Expr::apps(
                    or_cases.clone(),
                    [or_a, or_b, or_motive, lor, high_minor, low_minor],
                );
                d.finish_child(d.mk_lam(j_id, BinderInfo::Default, nat.clone(), body))
            };

            // Nat.eq_zero_of_testBit_all_false (val k) allBits : val k = 0
            let final_pf = Expr::apps(eq_zero_all_false.clone(), [vk.clone(), all_bits]);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, final_pf);
            let e = b.mk_lam(k_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Fin.sumNat_const_zero_of : ∀ (m : Nat) (g : Fin m → Nat),
    ///   (∀ (i : Fin m), Eq Nat (g i) Nat.zero) → Eq Nat (Fin.sumNat m g) Nat.zero`.
    ///
    /// The converse of `Fin.sumNat_eq_zero`: an all-zero summand has zero sum.
    /// `Nat.rec` on `m`: base `Fin.sumNat 0 g ≡ 0`; succ step rewrites the fold
    /// `Nat.add (Fin.sumNat k (g∘cs)) (g (last k))` to `Nat.add 0 0 ≡ 0` via the
    /// IH (on `g∘cs`, hypothesis at `castSucc`) and the hypothesis at `last`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_fin_sum_nat_const_zero_of(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sumNat_const_zero_of");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // Fin.sumNat
        self.register_fin_last_cases()?; // (Fin.castSucc/last available)

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]);
        let fin = c.fin.clone();
        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let fin_to_nat = |n: &Expr| Expr::pi(BinderInfo::Default, fin_of(n), nat.clone());
        let fin_sum_nat = Expr::const_(Name::from_string("Fin.sumNat"), vec![]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let congr = Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
        let sum_nat = |n: Expr, g: Expr| Expr::apps(fin_sum_nat.clone(), [n, g]);
        let succ = |x: Expr| Expr::app(c.nat_succ.clone(), x);
        let add = |a: Expr, b: Expr| Expr::apps(nat_add.clone(), [a, b]);
        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), l, r],
            )
        };
        // g ∘ castSucc k
        let comp_cast = |parent: &EnvDeclBuilder, k: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = ch.fresh_local(fin_of(k));
            let cast_i = Expr::apps(fin_cast.clone(), [k.clone(), i]);
            let body = Expr::app(g.clone(), cast_i);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_of(k), body))
        };
        // hyp : ∀ (i : Fin m), g i = 0
        let mk_hyp = |parent: &EnvDeclBuilder, m: &Expr, g: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = d.fresh_local(fin_of(m));
            let body = eq_n(Expr::app(g.clone(), i), c.nat_zero.clone());
            d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_of(m), body))
        };
        // M m := ∀ (g : Fin m → Nat), (∀ i, g i = 0) → Fin.sumNat m g = 0
        let mk_motive_body = |parent: &EnvDeclBuilder, m: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let gt = fin_to_nat(m);
            let (g_id, g) = d.fresh_local(gt.clone());
            let hyp = mk_hyp(&d, m, &g);
            let (h_id, _h) = d.fresh_local(hyp.clone());
            let concl = eq_n(sum_nat(m.clone(), g.clone()), c.nat_zero.clone());
            let r = d.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = d.mk_pi(g_id, BinderInfo::Default, gt, r);
            d.finish_child(r)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let body = mk_motive_body(&b, &m);
            b.finish(b.mk_pi(m_id, BinderInfo::Default, nat.clone(), body))
        };

        let value = {
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(nat.clone());
                let body = mk_motive_body(&b, &m);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
            };
            // base : M 0 := fun g _h => Eq.refl Nat 0  (Fin.sumNat 0 g ≡ 0)
            let base = {
                let mut b = EnvDeclBuilder::new();
                let gt = fin_to_nat(&c.nat_zero);
                let (g_id, g) = b.fresh_local(gt.clone());
                let hyp = mk_hyp(&b, &c.nat_zero, &g);
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let refl = Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                    [nat.clone(), c.nat_zero.clone()],
                );
                let r = b.mk_lam(h_id, BinderInfo::Default, hyp, refl);
                let r = b.mk_lam(g_id, BinderInfo::Default, gt, r);
                b.finish(r)
            };
            // step : fun (k) (ih : M k) (g : Fin (succ k) → Nat) (h : ∀ i, g i = 0)
            //          => Fin.sumNat (succ k) g = 0
            let step = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let ih_ty = mk_motive_body(&b, &k);
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());
                let sk = succ(k.clone());
                let gt = fin_to_nat(&sk);
                let (g_id, g) = b.fresh_local(gt.clone());
                let hyp = mk_hyp(&b, &sk, &g);
                let (h_id, h) = b.fresh_local(hyp.clone());

                let g_cs = comp_cast(&b, &k, &g);
                let pre_sum = sum_nat(k.clone(), g_cs.clone());
                let last_k = Expr::app(fin_last.clone(), k.clone());
                let g_last = Expr::app(g.clone(), last_k.clone());

                // hpre_hyp : ∀ i : Fin k, (g∘cs) i = 0 := fun i => h (castSucc k i)
                let hpre_hyp = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (i_id, i) = d.fresh_local(fin_of(&k));
                    let cast_i = Expr::apps(fin_cast.clone(), [k.clone(), i]);
                    let body = Expr::app(h.clone(), cast_i);
                    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&k), body))
                };
                // hpre : Fin.sumNat k (g∘cs) = 0 := ih (g∘cs) hpre_hyp
                let hpre = Expr::apps(ih.clone(), [g_cs.clone(), hpre_hyp]);
                // hlast : g (last k) = 0 := h (last k)
                let hlast = Expr::app(h.clone(), last_k.clone());

                // congr (congrArg Nat.add hpre) hlast :
                //   Nat.add pre_sum g_last = Nat.add 0 0   (≡ 0 def-eq)
                // congrArg here lifts hpre : pre_sum = 0 through Nat.add : Nat → (Nat → Nat),
                // so β = (Nat → Nat).
                let nat_to_nat = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
                let congr_add = Expr::apps(
                    congr_arg.clone(),
                    [
                        nat.clone(),
                        nat_to_nat.clone(),
                        pre_sum.clone(),
                        c.nat_zero.clone(),
                        nat_add.clone(),
                        hpre,
                    ],
                );
                // congr : @congr.{1,1} Nat Nat (add pre_sum) (add 0) g_last 0 congr_add hlast
                //   : add pre_sum g_last = add 0 0
                let body = Expr::apps(
                    congr.clone(),
                    [
                        nat.clone(),
                        nat.clone(),
                        Expr::app(nat_add.clone(), pre_sum.clone()),
                        Expr::app(nat_add.clone(), c.nat_zero.clone()),
                        g_last.clone(),
                        c.nat_zero.clone(),
                        congr_add,
                        hlast,
                    ],
                );
                let _ = add(pre_sum, g_last);

                let r = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
                let r = b.mk_lam(g_id, BinderInfo::Default, gt, r);
                let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };

            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let rec = Expr::apps(nat_rec.clone(), [motive, base, step, m.clone()]);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), rec))
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.setSizeNat_hcDecode_zero : ∀ (n : Nat),
    ///   Eq Nat (setSizeNat n (hcDecode n ⟨0, Nat.one_le_two_pow n⟩)) Nat.zero`.
    ///
    /// The ∅-index's decoded point has popcount zero. `setSizeNat n S ≡
    /// Fin.sumNat n (fun i => indNat (S i))` with `S = hcDecode n ⟨0,_⟩`; each
    /// coordinate is `(hcDecode n ⟨0,_⟩) i ≡ testBit 0 (Fin.val i) = false`
    /// (`Nat.testBit_zero_eq_false`, since `Fin.val ⟨0,_⟩ ≡ 0`), so each `indNat`
    /// summand is `indNat false ≡ 0`. `Fin.sumNat_const_zero_of` collapses the
    /// all-zero sum. Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_setsizenat_hcdecode_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSizeNat_hcDecode_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // hcDecode, Fin.sumNat
        self.register_set_size_nat()?;
        self.register_fin_sum_nat_const_zero_of()?;
        self.init_nat()?;
        self.register_nat_eq_of_testbit_proof()?; // Nat.testBit_zero_eq_false (same module)

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l1 = Level::succ(Level::zero());
        let fin = c.fin.clone();
        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
        let fin_sum_nat_czo = Expr::const_(Name::from_string("Fin.sumNat_const_zero_of"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let testbit_zero = Expr::const_(Name::from_string("Nat.testBit_zero_eq_false"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let bool_ = c.bool_.clone();
        let bool_rec_nat = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        let two_nat = Expr::app(c.nat_succ.clone(), one_nat.clone());
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), l, r],
            )
        };
        // indNat = fun (b : Bool) => @Bool.rec (fun _=>Nat) 0 1 b
        let nat_motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
        let ind_nat_fn = {
            let mut g = EnvDeclBuilder::new();
            let (b_id, bb) = g.fresh_local(bool_.clone());
            let body = Expr::apps(
                bool_rec_nat.clone(),
                [nat_motive.clone(), c.nat_zero.clone(), one_nat.clone(), bb],
            );
            g.finish(g.mk_lam(b_id, BinderInfo::Default, bool_.clone(), body))
        };
        let ind_nat = |b: Expr| {
            Expr::apps(
                bool_rec_nat.clone(),
                [nat_motive.clone(), c.nat_zero.clone(), one_nat.clone(), b],
            )
        };
        let j0_of = |n: &Expr| {
            Expr::apps(
                fin_mk.clone(),
                [
                    pow2(n),
                    c.nat_zero.clone(),
                    Expr::app(one_le_two_pow.clone(), n.clone()),
                ],
            )
        };
        let decode = |n: &Expr, j: Expr| Expr::apps(hc_decode.clone(), [n.clone(), j]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let dec = decode(&n, j0_of(&n));
            let ss = Expr::apps(set_size_nat.clone(), [n.clone(), dec]);
            let concl = eq_n(ss, c.nat_zero.clone());
            b.finish(b.mk_pi(n_id, BinderInfo::Default, nat.clone(), concl))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let j0 = j0_of(&n);
            let dec = decode(&n, j0.clone());

            // summand : fun (i : Fin n) => indNat ((hcDecode n j₀) i)
            let summand = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = d.fresh_local(fin_of(&n));
                let at_i = Expr::app(dec.clone(), i.clone());
                let body = ind_nat(at_i);
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
            };
            // pw : ∀ (i : Fin n), indNat ((hcDecode n j₀) i) = 0
            //   := fun i => congrArg Bool Nat (testBit 0 (val i)) false indNat
            //                 (Nat.testBit_zero_eq_false (val i))
            //   ((hcDecode n j₀) i ≡ testBit 0 (val i); indNat false ≡ 0.)
            let pw = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = d.fresh_local(fin_of(&n));
                let val_i = Expr::apps(fin_val.clone(), [n.clone(), i.clone()]);
                let tb = Expr::apps(testbit_zero.clone(), [val_i.clone()]);
                let at_i = Expr::app(dec.clone(), i.clone());
                let bool_false = c.bool_false.clone();
                let body = Expr::apps(
                    congr_arg.clone(),
                    [
                        bool_.clone(),
                        nat.clone(),
                        at_i,
                        bool_false,
                        ind_nat_fn.clone(),
                        tb,
                    ],
                );
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
            };
            // Fin.sumNat_const_zero_of n summand pw : Fin.sumNat n summand = 0
            //   ≡ setSizeNat n (hcDecode n j₀) = 0 (def-eq).
            let body = Expr::apps(fin_sum_nat_czo.clone(), [n.clone(), summand, pw]);

            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body))
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.indNat_eq_zero : ∀ (b : Bool),
    ///   Eq Nat (@Bool.rec (fun _ => Nat) Nat.zero (Nat.succ Nat.zero) b) Nat.zero
    ///     → Eq Bool b Bool.false`.
    ///
    /// The Nat indicator vanishes only at `false`. `indNat b` is the inlined
    /// `@Bool.rec (fun _ => Nat) 0 1 b` (the `setSizeNat` summand). `Bool.casesOn`:
    /// - `b = false`: goal `false = false` by `Eq.refl` (hypothesis `0 = 0` unused).
    /// - `b = true`: hypothesis `1 = 0` (`indNat true ≡ 1`), refuted by
    ///   `Nat.noConfusion` (distinct `succ`/`zero` constructors).
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_indnat_eq_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.indNat_eq_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?; // Bool, Bool.rec, Bool.casesOn
        self.init_nat()?;
        if self
            .get_const(&Name::from_string("Nat.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let bool_ = c.bool_.clone();
        let bool_false = c.bool_false.clone();
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_cases_on = Expr::const_(Name::from_string("Bool.casesOn"), vec![l0.clone()]);
        let bool_rec_nat = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let nat_no_conf = Expr::const_(Name::from_string("Nat.noConfusion"), vec![l0.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());

        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), l, r],
            )
        };
        let eq_b = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [bool_.clone(), l, r],
            )
        };
        // indNat b = @Bool.rec (fun _ => Nat) 0 1 b
        let nat_motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
        let ind_nat = |b: Expr| {
            Expr::apps(
                bool_rec_nat.clone(),
                [nat_motive.clone(), c.nat_zero.clone(), one_nat.clone(), b],
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(bool_.clone());
            let hyp = eq_n(ind_nat(bv.clone()), c.nat_zero.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = eq_b(bv.clone(), bool_false.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, bool_.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(bool_.clone());
            let hyp = eq_n(ind_nat(bv.clone()), c.nat_zero.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            // motive : fun (bb : Bool) => Eq Nat (indNat bb) 0 → Eq Bool bb false
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = m.fresh_local(bool_.clone());
                let prem = eq_n(ind_nat(bb.clone()), c.nat_zero.clone());
                let concl = eq_b(bb.clone(), bool_false.clone());
                let body = Expr::pi(BinderInfo::Default, prem, concl);
                m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), body))
            };

            // false_minor : Eq Nat (indNat false) 0 → Eq Bool false false
            //   := fun _h => Eq.refl Bool false
            let false_minor = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let prem = eq_n(ind_nat(bool_false.clone()), c.nat_zero.clone());
                let (hf_id, _hf) = m.fresh_local(prem.clone());
                let refl = Expr::apps(eq_refl.clone(), [bool_.clone(), bool_false.clone()]);
                m.finish_child(m.mk_lam(hf_id, BinderInfo::Default, prem, refl))
            };

            // true_minor : Eq Nat (indNat true) 0 → Eq Bool true false
            //   := fun (ht : 1 = 0) => @Nat.noConfusion (Eq Bool true false) 1 0 ht
            //   (indNat true ≡ succ zero ≡ 1; succ = zero impossible.)
            let true_minor = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let prem = eq_n(ind_nat(bool_true.clone()), c.nat_zero.clone());
                let (ht_id, ht) = m.fresh_local(prem.clone());
                let target = eq_b(bool_true.clone(), bool_false.clone());
                let body = Expr::apps(
                    nat_no_conf.clone(),
                    [target, one_nat.clone(), c.nat_zero.clone(), ht],
                );
                m.finish_child(m.mk_lam(ht_id, BinderInfo::Default, prem, body))
            };

            // @Bool.casesOn.{0} motive bv false_minor true_minor : motive bv
            //   = (Eq Nat (indNat bv) 0 → Eq Bool bv false); apply to h.
            let cases = Expr::apps(
                bool_cases_on.clone(),
                [motive, bv.clone(), false_minor, true_minor],
            );
            let body = Expr::app(cases, h);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, bool_.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Fin.sumNat_eq_zero : ∀ (m : Nat) (g : Fin m → Nat),
    ///   Eq Nat (Fin.sumNat m g) Nat.zero → ∀ (i : Fin m), Eq Nat (g i) Nat.zero`.
    ///
    /// A `Nat`-valued finite sum is zero only if every summand is zero (`Nat`
    /// addends are non-negative). `Nat.rec` on `m`:
    /// - `m = 0`: `Fin 0` is empty — `Fin.isLt 0 i : Fin.val i < 0` is refuted by
    ///   `Nat.not_succ_le_zero`, `False.elim` discharges the (vacuous) goal.
    /// - `m = succ k`: `Fin.sumNat (succ k) g ≡ Nat.add (Fin.sumNat k (g∘castSucc))
    ///   (g (last k))` (reducible `Fin.sumNat`), so `Nat.add_eq_zero` splits the
    ///   hypothesis into `Fin.sumNat k (g∘cs) = 0` (`And.left`) and `g (last k) = 0`
    ///   (`And.right`). `Fin.lastCases` on the queried `i`: the `last k` branch is
    ///   `And.right`; the `castSucc j` branch is `ih (g∘cs) (And.left …) j`.
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_fin_sum_nat_eq_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sumNat_eq_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // Fin.sumNat
        self.register_fin_last_cases()?;
        self.register_nat_add_eq_zero()?;

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l0 = Level::zero();
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]);
        let fin = c.fin.clone();
        let fin_sum_nat = Expr::const_(Name::from_string("Fin.sumNat"), vec![]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let fin_last_cases = Expr::const_(Name::from_string("Fin.lastCases"), vec![l0.clone()]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let not_succ_le_zero = Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let add_eq_zero = Expr::const_(Name::from_string("Nat.add_eq_zero"), vec![]);
        let l1 = Level::succ(l0.clone());
        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), l, r],
            )
        };

        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let fin_to_nat = |n: &Expr| Expr::pi(BinderInfo::Default, fin_of(n), nat.clone());
        let sum_nat = |n: Expr, g: Expr| Expr::apps(fin_sum_nat.clone(), [n, g]);
        let succ = |x: Expr| Expr::app(c.nat_succ.clone(), x);
        let and_of =
            |p: Expr, q: Expr| Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q]);
        // g ∘ castSucc k : fun (i : Fin k) => g (Fin.castSucc k i)
        let comp_cast = |parent: &EnvDeclBuilder, k: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = ch.fresh_local(fin_of(k));
            let cast_i = Expr::apps(fin_cast.clone(), [k.clone(), i]);
            let body = Expr::app(g.clone(), cast_i);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_of(k), body))
        };

        // M m := ∀ (g : Fin m → Nat), sumNat m g = 0 → ∀ (i : Fin m), g i = 0
        let mk_motive_body = |parent: &EnvDeclBuilder, m: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let gt = fin_to_nat(m);
            let (g_id, g) = d.fresh_local(gt.clone());
            let prem = eq_n(sum_nat(m.clone(), g.clone()), c.nat_zero.clone());
            let (h_id, _h) = d.fresh_local(prem.clone());
            let all_i = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (i_id, i) = e.fresh_local(fin_of(m));
                let body = eq_n(Expr::app(g.clone(), i), c.nat_zero.clone());
                e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_of(m), body))
            };
            let r = d.mk_pi(h_id, BinderInfo::Default, prem, all_i);
            let r = d.mk_pi(g_id, BinderInfo::Default, gt, r);
            d.finish_child(r)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let body = mk_motive_body(&b, &m);
            b.finish(b.mk_pi(m_id, BinderInfo::Default, nat.clone(), body))
        };

        let value = {
            // motive : fun (m : Nat) => M m
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(nat.clone());
                let body = mk_motive_body(&b, &m);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
            };

            // base : M 0 = ∀ g, sumNat 0 g = 0 → ∀ i : Fin 0, g i = 0
            let base = {
                let mut b = EnvDeclBuilder::new();
                let gt = fin_to_nat(&c.nat_zero);
                let (g_id, g) = b.fresh_local(gt.clone());
                let prem = eq_n(sum_nat(c.nat_zero.clone(), g.clone()), c.nat_zero.clone());
                let (h_id, _h) = b.fresh_local(prem.clone());
                // fun (i : Fin 0) => False.elim (g i = 0) (Nat.not_succ_le_zero (val 0 i) (Fin.isLt 0 i))
                let all_i = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let (i_id, i) = e.fresh_local(fin_of(&c.nat_zero));
                    let val0 = Expr::apps(fin_val.clone(), [c.nat_zero.clone(), i.clone()]);
                    let islt = Expr::apps(fin_islt.clone(), [c.nat_zero.clone(), i.clone()]);
                    // Fin.isLt 0 i : Nat.lt (val 0 i) 0 ≡ Nat.le (succ (val 0 i)) 0
                    let false_pf = Expr::apps(not_succ_le_zero.clone(), [val0, islt]);
                    let goal = eq_n(Expr::app(g.clone(), i.clone()), c.nat_zero.clone());
                    let body = Expr::apps(false_elim.clone(), [goal, false_pf]);
                    let _ = nat_lt.clone();
                    e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_of(&c.nat_zero), body))
                };
                let r = b.mk_lam(h_id, BinderInfo::Default, prem, all_i);
                let r = b.mk_lam(g_id, BinderInfo::Default, gt, r);
                b.finish(r)
            };

            // step : fun (k) (ih : M k) (g : Fin (succ k) → Nat)
            //          (h : sumNat (succ k) g = 0) (i : Fin (succ k)) => g i = 0
            let step = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let ih_ty = mk_motive_body(&b, &k);
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());
                let sk = succ(k.clone());
                let gt = fin_to_nat(&sk);
                let (g_id, g) = b.fresh_local(gt.clone());
                let prem = eq_n(sum_nat(sk.clone(), g.clone()), c.nat_zero.clone());
                let (h_id, h) = b.fresh_local(prem.clone());

                // g∘cs : Fin k → Nat
                let g_cs = comp_cast(&b, &k, &g);
                // sumNat k (g∘cs) and g (last k)
                let pre_sum = sum_nat(k.clone(), g_cs.clone());
                let last_k = Expr::app(fin_last.clone(), k.clone());
                let g_last = Expr::app(g.clone(), last_k.clone());
                // And (pre_sum = 0) (g_last = 0) := Nat.add_eq_zero pre_sum g_last h
                //   (h : sumNat (succ k) g = 0 ≡ add pre_sum g_last = 0)
                let split = Expr::apps(
                    add_eq_zero.clone(),
                    [pre_sum.clone(), g_last.clone(), h.clone()],
                );
                let p_pre = eq_n(pre_sum.clone(), c.nat_zero.clone());
                let p_last = eq_n(g_last.clone(), c.nat_zero.clone());
                let hpre = Expr::apps(
                    and_left.clone(),
                    [p_pre.clone(), p_last.clone(), split.clone()],
                );
                let hlast = Expr::apps(and_right.clone(), [p_pre, p_last, split]);

                // P : Fin (succ k) → Prop := fun (w : Fin (succ k)) => g w = 0
                let p_motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = d.fresh_local(fin_of(&sk));
                    let body = eq_n(Expr::app(g.clone(), w), c.nat_zero.clone());
                    d.finish_child(d.mk_lam(w_id, BinderInfo::Default, fin_of(&sk), body))
                };
                // last_case : P (last k) = (g (last k) = 0) := hlast
                let last_case = hlast;
                // cast_case : (j : Fin k) → P (castSucc k j) = (g (castSucc k j) = 0)
                //   := fun j => ih (g∘cs) hpre j
                //   (ih (g∘cs) hpre : ∀ i : Fin k, (g∘cs) i = 0; (g∘cs) j ≡ g (castSucc k j))
                let cast_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (j_id, j) = d.fresh_local(fin_of(&k));
                    let ih_app = Expr::apps(ih.clone(), [g_cs.clone(), hpre.clone()]);
                    let body = Expr::app(ih_app, j);
                    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_of(&k), body))
                };

                // ∀ (i : Fin (succ k)), g i = 0 :=
                //   fun i => @Fin.lastCases.{0} k P last_case cast_case i
                let all_i = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (i_id, i) = d.fresh_local(fin_of(&sk));
                    let body = Expr::apps(
                        fin_last_cases.clone(),
                        [
                            k.clone(),
                            p_motive.clone(),
                            last_case.clone(),
                            cast_case.clone(),
                            i,
                        ],
                    );
                    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&sk), body))
                };

                let r = b.mk_lam(h_id, BinderInfo::Default, prem, all_i);
                let r = b.mk_lam(g_id, BinderInfo::Default, gt, r);
                let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };

            // @Nat.rec.{0} motive base step m   (m bound at the top λ)
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let rec = Expr::apps(nat_rec.clone(), [motive, base, step, m.clone()]);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), rec))
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.add_eq_zero : ∀ (a b : Nat), Eq Nat (Nat.add a b) Nat.zero
    ///   → And (Eq Nat a Nat.zero) (Eq Nat b Nat.zero)`.
    ///
    /// A sum of `Nat`s is zero only if both addends are zero. `Nat.add` recurses
    /// on its second argument (`add a 0 ≡ a`, `add a (succ b') ≡ succ (add a b')`),
    /// so `Nat.casesOn b`:
    /// - `b = 0`: `h : add a 0 = 0` is def-eq to `a = 0`; return
    ///   `And.intro h (Eq.refl 0)`.
    /// - `b = succ b'`: `h : add a (succ b') = 0` is def-eq to `succ (…) = 0`,
    ///   refuted by `Nat.noConfusion` (distinct constructors), which yields the
    ///   `And` directly.
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_nat_add_eq_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_eq_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        if self
            .get_const(&Name::from_string("Nat.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);
        let nat_no_conf = Expr::const_(Name::from_string("Nat.noConfusion"), vec![Level::zero()]);
        let l1 = Level::succ(Level::zero());
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let and_c = Expr::const_(Name::from_string("And"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);

        let add = |a: Expr, b: Expr| Expr::apps(nat_add.clone(), [a, b]);
        let eq_nat = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [nat.clone(), l, r],
            )
        };
        let succ = |x: Expr| Expr::app(c.nat_succ.clone(), x);
        let and_of = |p: Expr, q: Expr| Expr::apps(and_c.clone(), [p, q]);
        // And (a = 0) (b = 0)
        let goal_and = |a: &Expr, b: &Expr| {
            and_of(
                eq_nat(a.clone(), c.nat_zero.clone()),
                eq_nat(b.clone(), c.nat_zero.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let hyp = eq_nat(add(a.clone(), bv.clone()), c.nat_zero.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = goal_and(&a, &bv);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let hyp = eq_nat(add(a.clone(), bv.clone()), c.nat_zero.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            // motive : fun (bb : Nat) => Eq (add a bb) 0 → And (a=0) (bb=0)
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = m.fresh_local(nat.clone());
                let prem = eq_nat(add(a.clone(), bb.clone()), c.nat_zero.clone());
                let concl = goal_and(&a, &bb);
                let body = Expr::pi(BinderInfo::Default, prem, concl);
                m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, nat.clone(), body))
            };

            // zero_minor : Eq (add a 0) 0 → And (a=0) (0=0)
            //   := fun (h0 : add a 0 = 0) => And.intro (a=0) (0=0) h0 (Eq.refl 0)
            // (h0 is def-eq to a = 0 since add a 0 ≡ a; 0 = 0 by Eq.refl.)
            let zero_minor = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let prem = eq_nat(add(a.clone(), c.nat_zero.clone()), c.nat_zero.clone());
                let (h0_id, h0) = m.fresh_local(prem.clone());
                let refl0 = Expr::apps(eq_refl.clone(), [nat.clone(), c.nat_zero.clone()]);
                let body = Expr::apps(
                    and_intro.clone(),
                    [
                        eq_nat(a.clone(), c.nat_zero.clone()),
                        eq_nat(c.nat_zero.clone(), c.nat_zero.clone()),
                        h0,
                        refl0,
                    ],
                );
                m.finish_child(m.mk_lam(h0_id, BinderInfo::Default, prem, body))
            };

            // succ_minor : fun (b' : Nat) => (Eq (add a (succ b')) 0 → And (a=0) (succ b'=0))
            //   := fun b' (hs : add a (succ b') = 0) =>
            //        @Nat.noConfusion.{u} (And (a=0) (succ b'=0)) (succ (add a b')) 0 hs
            //   (add a (succ b') ≡ succ (add a b'); succ _ = 0 is impossible.)
            let succ_minor = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (bp_id, bp) = m.fresh_local(nat.clone());
                let prem = eq_nat(add(a.clone(), succ(bp.clone())), c.nat_zero.clone());
                let (hs_id, hs) = m.fresh_local(prem.clone());
                let target = goal_and(&a, &succ(bp.clone()));
                // noConfusionType (target) (succ (add a b')) 0 ≡ target (distinct ctors)
                let body = Expr::apps(
                    nat_no_conf.clone(),
                    [
                        target,
                        succ(add(a.clone(), bp.clone())),
                        c.nat_zero.clone(),
                        hs,
                    ],
                );
                let inner = m.mk_lam(hs_id, BinderInfo::Default, prem, body);
                m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, nat.clone(), inner))
            };

            // @Nat.casesOn.{0} motive bv zero_minor succ_minor : motive bv
            //   = (Eq (add a bv) 0 → And (a=0) (bv=0)); apply to h.
            let cases = Expr::apps(
                nat_cases_on.clone(),
                [motive, bv.clone(), zero_minor, succ_minor],
            );
            let body = Expr::app(cases, h);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **Deliverable 2.** `BoolAnalysis.chi_empty :
    ///   ∀ (n) (S x : HCPoint n), (∀ (i : Fin n), Eq Bool (S i) Bool.false)
    ///     → chi n S x = Rat.one`
    ///
    /// The all-false subset's parity character is the constant 1. `chi n S x`
    /// δ-reduces (reducible) to `Fin.prod n (fun i => gate(S i))` where
    /// `gate b := @Bool.rec (fun _ => Rat) Rat.one (signed x i) b`. With
    /// `h i : S i = false`, each factor `gate (S i)` is `Bool.rec`-def-eq to
    /// `Rat.one` (the `false` minor premise), witnessed by
    /// `congrArg (gate_fn) (h i) : gate (S i) = gate false ≡ Rat.one`. The chain
    /// is `Fin.prod_congr` (factors → const-1) then `Fin.prod_const_one`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_chi_empty(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_empty");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_foundations()?; // chi, HCPoint, Fin.prod
        self.init_rat()?; // Rat.one, Rat.sub, Rat.mul
        self.register_fin_prod_one_theorems()?; // Fin.prod_congr, Fin.prod_const_one

        let c = EmptyConsts::new();

        // hyp type: ∀ (i : Fin n), Eq Bool (S i) Bool.false
        let mk_hyp = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let fin_n = c.fin_of(n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let body = c.eq_bool(Expr::app(s.clone(), i), c.bool_false.clone());
            b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let (x_id, x) = b.fresh_local(hcp.clone());
            let hyp = mk_hyp(&b, &n, &s);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.eq_rat(c.chi_of(&n, &s, &x), c.rat_one.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let (x_id, x) = b.fresh_local(hcp.clone());
            let hyp = mk_hyp(&b, &n, &s);
            let (h_id, h) = b.fresh_local(hyp.clone());

            // factor function (chi's product body) and the const-1 target.
            let factor = c.chi_factor_fn(&b, &n, &s, &x);
            let const_one = c.const_one_fn(&b, &n);

            // pw : ∀ (i : Fin n), factor i = Rat.one
            //   := fun i => congrArg (gate_fn x i) (h i)
            // (h i : S i = false; gate_fn x i (S i) ≡ factor i, gate_fn x i false ≡ 1.)
            let pw = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let s_i = Expr::app(s.clone(), i.clone());
                let h_i = Expr::app(h.clone(), i.clone());
                let g = c.gate_fn(&ch, &x, &i);
                let body = c.congr_bool_rat(s_i, c.bool_false.clone(), g, h_i);
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            // h1 : Fin.prod n factor = Fin.prod n (fun _ => 1)
            let h1 = Expr::apps(
                c.fin_prod_congr.clone(),
                [n.clone(), factor.clone(), const_one.clone(), pw],
            );
            // h2 : Fin.prod n (fun _ => 1) = Rat.one
            let h2 = Expr::app(c.fin_prod_const_one.clone(), n.clone());

            // chi n S x ≡ Fin.prod n factor (def-eq); chain to 1.
            let prod_factor = c.prod(&n, factor);
            let prod_one = c.prod(&n, const_one);
            let body = c.trans(prod_factor, prod_one, c.rat_one.clone(), h1, h2);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **Deliverable 4.** `BoolAnalysis.fourier_empty_eq_mean :
    ///   ∀ (n) (f : BoolFn n) (S : HCPoint n),
    ///     (∀ (i : Fin n), Eq Bool (S i) Bool.false)
    ///       → FourierCoefficient n f S = Expect n (fun x => pm (f x))`
    ///
    /// The level-0 Fourier coefficient is the mean: `f̂(∅) = E[pm f]`.
    /// `FourierCoefficient n f S` δ-reduces (reducible) to
    /// `Expect n (fun x => pm (f x) · chi n S x)`. With the all-false hypothesis,
    /// `chi n S x = Rat.one` (`chi_empty`), so each integrand point collapses
    /// `pm (f x) · chi n S x = pm (f x) · 1 = pm (f x)`
    /// (`congrArg (pm (f x) ·) (chi_empty …)` then `Rat.mul_one`). `Expect_congr`
    /// rewrites the integrand to `fun x => pm (f x)`, giving `Expect n (pm f)`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_fourier_empty_eq_mean(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fourier_empty_eq_mean");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // FourierCoefficient, Expect, pm, chi
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?; // Rat.mul_one
        self.register_chi_empty()?;
        self.register_expect_congr_theorem()?;

        let c = EmptyConsts::new();

        // hyp type: ∀ (i : Fin n), Eq Bool (S i) Bool.false
        let mk_hyp = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let fin_n = c.fin_of(n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let body = c.eq_bool(Expr::app(s.clone(), i), c.bool_false.clone());
            b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let hyp = mk_hyp(&b, &n, &s);
            let (h_id, _h) = b.fresh_local(hyp.clone());

            let lhs = c.fourier_of(&n, &f, &s);
            let rhs = c.expect_of(&n, c.pm_integrand(&b, &n, &f));
            let concl = c.eq_rat(lhs, rhs);

            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let hyp = mk_hyp(&b, &n, &s);
            let (h_id, h) = b.fresh_local(hyp.clone());

            // Integrands.
            let fc_int = c.fourier_integrand(&b, &n, &f, &s); // fun x => pm·chi
            let pm_int = c.pm_integrand(&b, &n, &f); // fun x => pm

            // pw : ∀ x, pm (f x) · chi n S x = pm (f x)
            //   := fun x => Eq.trans
            //        (congrArg (pm (f x) ·) (chi_empty n S x h)) -- pm·chi = pm·1
            //        (Rat.mul_one (pm (f x)))                    -- pm·1   = pm
            let pw = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(hcp.clone());
                let pm_fx = Expr::app(c.pm.clone(), Expr::app(f.clone(), x.clone()));
                let chi_sx = c.chi_of(&n, &s, &x);
                let chi_eq_one = c.chi_empty_of(&n, &s, &x, &h);
                let g = c.mul_left_fn(&ch, &pm_fx);
                // h1 : pm·chi = pm·1
                let h1 = c.congr_rat_rat(chi_sx, c.rat_one.clone(), g, chi_eq_one);
                // h2 : pm·1 = pm
                let h2 = c.mul_one_of(pm_fx.clone());
                let pm_chi = c.mul(pm_fx.clone(), c.chi_of(&n, &s, &x));
                let pm_one = c.mul(pm_fx.clone(), c.rat_one.clone());
                let body = c.trans(pm_chi, pm_one, pm_fx, h1, h2);
                ch.finish_child(ch.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
            };

            // Expect_congr n fc_int pm_int pw : Expect n (pm·chi) = Expect n (pm)
            // and FourierCoefficient n f S ≡ Expect n (pm·chi) (def-eq).
            let body = c.expect_congr_of(&n, fc_int, pm_int, pw);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sub_zero : ∀ (a : Rat), Rat.sub a Rat.zero = a`.
    ///
    /// `Rat.sub a 0 ≡ Rat.add a (Rat.neg 0)` (reducible `Rat.sub`). `Rat.neg 0 = 0`
    /// (from `Rat.zero_add (neg 0)` + `Rat.add_neg_self 0`), then `Rat.add_zero`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_rat_sub_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;

        let c = EmptyConsts::new();
        let rat = c.rat.clone();
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
        let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
        let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
        let neg = |a: Expr| Expr::app(rat_neg.clone(), a);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let concl = c.eq_rat(c.sub(a.clone(), c.rat_zero.clone()), a.clone());
            b.finish(b.mk_pi(a_id, BinderInfo::Default, rat.clone(), concl))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let neg0 = neg(c.rat_zero.clone());
            // hneg0 : neg 0 = 0
            //   = Eq.trans (symm (zero_add (neg 0))) (add_neg_self 0)
            //   (zero_add (neg 0) : 0 + neg 0 = neg 0; add_neg_self 0 : 0 + neg 0 = 0)
            let zero_add_neg0 = Expr::app(zero_add.clone(), neg0.clone()); // 0 + neg0 = neg0
            let add_neg0 = Expr::app(add_neg_self.clone(), c.rat_zero.clone()); // 0 + neg0 = 0
            let hneg0 = c.trans(
                neg0.clone(),
                add(c.rat_zero.clone(), neg0.clone()),
                c.rat_zero.clone(),
                c.symm(
                    add(c.rat_zero.clone(), neg0.clone()),
                    neg0.clone(),
                    zero_add_neg0,
                ),
                add_neg0,
            );
            // h1 : add a (neg 0) = add a 0   = congrArg (add a) hneg0
            let add_a_fn = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(rat.clone());
                let body = add(a.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
            };
            let h1 = c.congr_rat_rat(neg0.clone(), c.rat_zero.clone(), add_a_fn, hneg0);
            // h2 : add a 0 = a   = Rat.add_zero a
            let h2 = Expr::app(add_zero.clone(), a.clone());
            // sub a 0 ≡ add a (neg 0); chain to a.
            let body = c.trans(
                add(a.clone(), neg0.clone()),
                add(a.clone(), c.rat_zero.clone()),
                a.clone(),
                h1,
                h2,
            );
            b.finish(b.mk_lam(a_id, BinderInfo::Default, rat.clone(), body))
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.mass_complement_pointwise : ∀ (m : Nat) (a : Rat),
    ///   Rat.sub a (Rat.mul (ind (Nat.beq m 0)) a)
    ///     = Rat.mul (ind (Nat.ble (succ zero) m)) a`.
    ///
    /// The level-0/≥1 indicator complement, scaled by `a` (the per-`S` `f̂²`):
    /// `a − ind(|S|=0)·a = ind(|S|≥1)·a`. `Nat.casesOn m`:
    /// - `m = 0`: `ind(beq 0 0) ≡ ind true ≡ 1`, `ind(ble 1 0) ≡ ind false ≡ 0`,
    ///   so `a − 1·a = a − a = 0 = 0·a` (`Rat.one_mul`, `Rat.sub_self`,
    ///   `Rat.zero_mul`);
    /// - `m = succ m'`: `ind(beq (succ) 0) ≡ 0`, `ind(ble 1 (succ)) ≡ 1`, so
    ///   `a − 0·a = a − 0 = a = 1·a` (`Rat.zero_mul`, `Rat.sub_zero`,
    ///   `Rat.one_mul`).
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_mass_complement_pointwise(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.mass_complement_pointwise");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_rat()?; // Rat.one_mul, Rat.zero_mul, Rat.sub_self, Rat.mul
        self.init_boolean_analysis()?; // ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_sub_zero()?;

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let rat = c.rat.clone();
        let nat_cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
        let sub_self = Expr::const_(Name::from_string("Rat.sub_self"), vec![]);
        let sub_zero = Expr::const_(Name::from_string("Rat.sub_zero"), vec![]);
        let succ = |x: Expr| Expr::app(c.nat_succ.clone(), x);
        let one_nat = succ(c.nat_zero.clone());

        // goal at a given m, a: sub a (ind(beq m 0)·a) = ind(ble 1 m)·a
        let goal_at = |m: Expr, a: &Expr| {
            c.eq_rat(
                c.sub(a.clone(), c.mul(c.ind_of(c.beq0(m.clone())), a.clone())),
                c.mul(c.ind_of(c.ble1(m)), a.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(rat.clone());
            let concl = goal_at(m.clone(), &a);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(rat.clone());

            // motive : fun (mm : Nat) => goal_at mm a
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = d.fresh_local(nat.clone());
                let body = goal_at(mm, &a);
                d.finish_child(d.mk_lam(mm_id, BinderInfo::Default, nat.clone(), body))
            };

            // zero_minor : goal_at 0 a  (def-eq to  sub a (1·a) = 0·a)
            //   chain: sub a (1·a) = sub a a   [congrArg (sub a ·) (one_mul a)]
            //                       = 0        [sub_self a]
            //                       = 0·a      [symm (zero_mul a)]
            let zero_minor = {
                let one_mul_a = Expr::app(one_mul.clone(), a.clone()); // 1·a = a
                let sub_a_fn = {
                    let mut g = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = g.fresh_local(rat.clone());
                    let body = c.sub(a.clone(), t);
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
                };
                // h1 : sub a (1·a) = sub a a
                let one_a = c.mul(c.rat_one.clone(), a.clone());
                let h1 = c.congr_rat_rat(one_a.clone(), a.clone(), sub_a_fn, one_mul_a);
                // h2 : sub a a = 0
                let h2 = Expr::app(sub_self.clone(), a.clone());
                // h3 : 0 = 0·a  (symm zero_mul a)
                let zero_mul_a = Expr::app(zero_mul.clone(), a.clone()); // 0·a = 0
                let zero_a = c.mul(c.rat_zero.clone(), a.clone());
                let h3 = c.symm(zero_a.clone(), c.rat_zero.clone(), zero_mul_a);
                // chain sub a (1·a) = sub a a = 0 = 0·a
                let h12 = c.trans(
                    c.sub(a.clone(), one_a.clone()),
                    c.sub(a.clone(), a.clone()),
                    c.rat_zero.clone(),
                    h1,
                    h2,
                );
                c.trans(c.sub(a.clone(), one_a), c.rat_zero.clone(), zero_a, h12, h3)
            };

            // succ_minor : fun (m' : Nat) => goal_at (succ m') a
            //   (def-eq to  sub a (0·a) = 1·a)
            //   chain: sub a (0·a) = sub a 0   [congrArg (sub a ·) (zero_mul a)]
            //                       = a        [sub_zero a]
            //                       = 1·a      [symm (one_mul a)]
            let succ_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mp_id, _mp) = d.fresh_local(nat.clone());
                let zero_mul_a = Expr::app(zero_mul.clone(), a.clone()); // 0·a = 0
                let sub_a_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (t_id, t) = g.fresh_local(rat.clone());
                    let body = c.sub(a.clone(), t);
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
                };
                let zero_a = c.mul(c.rat_zero.clone(), a.clone());
                // h1 : sub a (0·a) = sub a 0
                let h1 = c.congr_rat_rat(zero_a.clone(), c.rat_zero.clone(), sub_a_fn, zero_mul_a);
                // h2 : sub a 0 = a
                let h2 = Expr::app(sub_zero.clone(), a.clone());
                // h3 : a = 1·a  (symm one_mul a)
                let one_mul_a = Expr::app(one_mul.clone(), a.clone()); // 1·a = a
                let one_a = c.mul(c.rat_one.clone(), a.clone());
                let h3 = c.symm(one_a.clone(), a.clone(), one_mul_a);
                let h12 = c.trans(
                    c.sub(a.clone(), zero_a.clone()),
                    c.sub(a.clone(), c.rat_zero.clone()),
                    a.clone(),
                    h1,
                    h2,
                );
                let body = c.trans(c.sub(a.clone(), zero_a), a.clone(), one_a, h12, h3);
                d.finish_child(d.mk_lam(mp_id, BinderInfo::Default, nat.clone(), body))
            };

            // @Nat.casesOn.{0} motive m zero_minor succ_minor : motive m = goal_at m a
            let body = Expr::apps(
                nat_cases_on.clone(),
                [motive, m.clone(), zero_minor, succ_minor],
            );

            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **Deliverable 5.** `BoolAnalysis.variance_eq_nonempty_mass :
    ///   ∀ (n) (f : BoolFn n),
    ///     Variance n f = subsetSum n
    ///       (fun S => ind (Nat.ble (succ zero) (setSizeNat n S)) · (f̂ S · f̂ S))`
    ///
    /// The bare-Poincaré identity `Var = Σ_{S≠∅} f̂²`. `Variance n f ≡
    /// Rat.sub (E[(pm f)²]) ((E[pm f])²)` (reducible). Rewrite `E[(pm f)²] = Σ_S
    /// f̂²` (`expect_pm_sq_eq_fourier_mass`) and `(E[pm f])² = f̂(∅)² = Σ_S ind(|S|=0)
    /// ·f̂²` (`fourier_empty_eq_mean` + `emptyset_mass_isolation` at `w = f̂²`), so
    /// `Var = Σ_S f̂² − Σ_S ind(|S|=0)·f̂² = Σ_S (f̂² − ind(|S|=0)·f̂²)`
    /// (`subsetSum_sub`) `= Σ_S ind(|S|≥1)·f̂²` (`subsetSum_congr` ∘
    /// `mass_complement_pointwise`). Kernel-checked, `Constructive`, empty closure.
    /// Idempotent.
    pub fn register_variance_eq_nonempty_mass(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.variance_eq_nonempty_mass");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Variance, Expect, pm, FourierCoefficient
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_sub_theorem()?;
        self.register_set_size_nat()?;
        self.register_expect_pm_sq_eq_fourier_mass()?;
        self.register_fourier_empty_eq_mean()?;
        self.register_emptyset_mass_isolation()?;
        self.register_mass_complement_pointwise()?;
        self.register_nat_eq_of_testbit_proof()?; // Nat.testBit_zero_eq_false

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let l1 = Level::succ(Level::zero());
        let fin = c.fin.clone();
        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let testbit_zero = Expr::const_(Name::from_string("Nat.testBit_zero_eq_false"), vec![]);
        let rat_sub_const = c.rat_sub.clone();
        let rat_mul_const = c.rat_mul.clone();
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        let two_nat = Expr::app(c.nat_succ.clone(), one_nat.clone());
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
        let hcp_of = |n: &Expr| Expr::app(c.hcpoint.clone(), n.clone());

        // integrand helpers
        // fhat_sq_fn := fun S => f̂ S · f̂ S
        let fhat_sq_fn = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(hcp_of(n));
            let fh = c.fourier_of2(n, f, &s);
            let body = c.mul(fh.clone(), fh);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(n), body))
        };
        // ind0_fn := fun S => ind(beq |S| 0) · (f̂·f̂)
        let ind0_fn = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(hcp_of(n));
            let fh = c.fourier_of2(n, f, &s);
            let bit = c.beq0(c.ss_nat_of(n, &s));
            let body = c.mul(c.ind_of(bit), c.mul(fh.clone(), fh));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(n), body))
        };
        // ind1_fn := fun S => ind(ble 1 |S|) · (f̂·f̂)   (the RHS target)
        let ind1_fn = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(hcp_of(n));
            let fh = c.fourier_of2(n, f, &s);
            let bit = c.ble1(c.ss_nat_of(n, &s));
            let body = c.mul(c.ind_of(bit), c.mul(fh.clone(), fh));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(n), body))
        };
        // sub_fn := fun S => (f̂·f̂) − ind(beq |S| 0)·(f̂·f̂)   (subsetSum_sub's integrand)
        let sub_fn = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(hcp_of(n));
            let fh = c.fourier_of2(n, f, &s);
            let sq = c.mul(fh.clone(), fh);
            let bit = c.beq0(c.ss_nat_of(n, &s));
            let body = c.sub(sq.clone(), c.mul(c.ind_of(bit), sq));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(n), body))
        };
        // E2 = Expect (fun x => pm(f x)·pm(f x)), E1 = Expect (fun x => pm(f x))
        let pm_sq_int = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = d.fresh_local(hcp_of(n));
            let pmfx = Expr::app(c.pm.clone(), Expr::app(f.clone(), x.clone()));
            let body = c.mul(pmfx.clone(), pmfx);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp_of(n), body))
        };
        let pm_int = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = d.fresh_local(hcp_of(n));
            let body = Expr::app(c.pm.clone(), Expr::app(f.clone(), x));
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp_of(n), body))
        };
        let j0_of = |n: &Expr| {
            Expr::apps(
                fin_mk.clone(),
                [
                    pow2(n),
                    c.nat_zero.clone(),
                    Expr::app(one_le_two_pow.clone(), n.clone()),
                ],
            )
        };
        let decode = |n: &Expr, j: Expr| Expr::apps(hc_decode.clone(), [n.clone(), j]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let lhs = c.variance_of(&n, &f);
            let rhs = c.subset_sum_of(&n, ind1_fn(&b, &n, &f));
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let j0 = j0_of(&n);
            let dec_j0 = decode(&n, j0.clone());
            // E2, E1
            let e2 = c.expect_of(&n, pm_sq_int(&b, &n, &f));
            let e1 = c.expect_of(&n, pm_int(&b, &n, &f));
            // mass = Σ f̂², mass0 = Σ ind0·f̂², mass1 = Σ ind1·f̂²
            let mass = c.subset_sum_of(&n, fhat_sq_fn(&b, &n, &f));
            let mass0 = c.subset_sum_of(&n, ind0_fn(&b, &n, &f));
            let mass1 = c.subset_sum_of(&n, ind1_fn(&b, &n, &f));
            // f̂(∅) = FourierCoefficient n f (hcDecode n j₀)
            let fhat_empty = c.fourier_of2(&n, &f, &dec_j0);
            let fe_sq = c.mul(fhat_empty.clone(), fhat_empty.clone());
            let e1_sq = c.mul(e1.clone(), e1.clone());

            // h_e2 : E2 = mass
            let h_e2 = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.expect_pm_sq_eq_fourier_mass"),
                    vec![],
                ),
                [n.clone(), f.clone()],
            );
            // hallfalse : ∀ i, (hcDecode n j₀) i = false := fun i => testBit_zero (val i)
            let hallfalse = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = d.fresh_local(fin_of(&n));
                let val_i = Expr::apps(fin_val.clone(), [n.clone(), i.clone()]);
                let body = Expr::app(testbit_zero.clone(), val_i);
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
            };
            // hfem : f̂(∅) = E1   (fourier_empty_eq_mean n f (hcDecode n j₀) hallfalse)
            let hfem = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.fourier_empty_eq_mean"),
                    vec![],
                ),
                [n.clone(), f.clone(), dec_j0.clone(), hallfalse],
            );
            // h_e1 : E1 = f̂(∅)   (symm hfem)
            let h_e1 = c.symm(fhat_empty.clone(), e1.clone(), hfem);
            // h_e1sq : E1·E1 = f̂(∅)·f̂(∅)   (congr (congrArg mul h_e1) h_e1)
            let mul_e1 = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.rat.clone(),
                    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone()),
                    e1.clone(),
                    fhat_empty.clone(),
                    rat_mul_const.clone(),
                    h_e1.clone(),
                ],
            ); // mul E1 = mul f̂(∅)  : Rat → Rat
            let h_e1sq = c.congr2(
                Expr::app(rat_mul_const.clone(), e1.clone()),
                Expr::app(rat_mul_const.clone(), fhat_empty.clone()),
                e1.clone(),
                fhat_empty.clone(),
                mul_e1,
                h_e1,
            ); // E1·E1 = f̂(∅)·f̂(∅)
               // hiso : mass0 = f̂(∅)·f̂(∅)   (emptyset_mass_isolation n fhat_sq_fn)
            let hiso = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.emptyset_mass_isolation"),
                    vec![],
                ),
                [n.clone(), fhat_sq_fn(&b, &n, &f)],
            );
            // h_e1sq2 : E1·E1 = mass0   (trans h_e1sq (symm hiso))
            let h_e1sq2 = c.trans(
                e1_sq.clone(),
                fe_sq.clone(),
                mass0.clone(),
                h_e1sq,
                c.symm(mass0.clone(), fe_sq.clone(), hiso),
            );
            // h_v : V = sub mass mass0
            //   V ≡ sub E2 (E1·E1); congr (congrArg sub h_e2) h_e1sq2
            let sub_e2 = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.rat.clone(),
                    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone()),
                    e2.clone(),
                    mass.clone(),
                    rat_sub_const.clone(),
                    h_e2,
                ],
            ); // sub E2 = sub mass : Rat → Rat
            let h_v = c.congr2(
                Expr::app(rat_sub_const.clone(), e2.clone()),
                Expr::app(rat_sub_const.clone(), mass.clone()),
                e1_sq.clone(),
                mass0.clone(),
                sub_e2,
                h_e1sq2,
            ); // sub E2 (E1·E1) = sub mass mass0
               // hsub : sub mass mass0 = Σ (f̂² − ind0·f̂²)
               //   = symm (subsetSum_sub n fhat_sq_fn ind0_fn)
            let subset_sum_sub = Expr::apps(
                c.subset_sum_sub.clone(),
                [n.clone(), fhat_sq_fn(&b, &n, &f), ind0_fn(&b, &n, &f)],
            ); // Σ(f̂²−ind0·f̂²) = sub mass mass0
            let sub_mass = c.sub(mass.clone(), mass0.clone());
            let mass_sub = c.subset_sum_of(&n, sub_fn(&b, &n, &f));
            let hsub = c.symm(mass_sub.clone(), sub_mass.clone(), subset_sum_sub);
            // hcompl : Σ(f̂²−ind0·f̂²) = mass1   (subsetSum_congr n sub_fn ind1_fn pw)
            let pw = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (s_id, s) = d.fresh_local(hcp_of(&n));
                let fh = c.fourier_of2(&n, &f, &s);
                let sq = c.mul(fh.clone(), fh);
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("BoolAnalysis.mass_complement_pointwise"),
                        vec![],
                    ),
                    [c.ss_nat_of(&n, &s), sq],
                );
                d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(&n), body))
            };
            let hcompl = Expr::apps(
                c.subset_sum_congr.clone(),
                [n.clone(), sub_fn(&b, &n, &f), ind1_fn(&b, &n, &f), pw],
            );

            // chain V = sub mass mass0 = Σ(f̂²−ind0·f̂²) = mass1
            let v = c.variance_of(&n, &f);
            let h_v2 = c.trans(v.clone(), sub_mass.clone(), mass_sub.clone(), h_v, hsub);
            let body = c.trans(v, mass_sub, mass1, h_v2, hcompl);

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let _ = l1;
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **Deliverable 6 — the BARE POINCARÉ inequality.**
    /// `BoolAnalysis.variance_le_influence :
    ///   ∀ (n) (f : BoolFn n), Rat.le (Variance n f) (TotalInfluence n f)`.
    ///
    /// The clean classical theorem `Var[f] ≤ I[f]`. One `Eq.subst` of the
    /// bare-Poincaré identity `variance_eq_nonempty_mass` (`Var = Σ_{S≠∅} f̂²`)
    /// into `kkl_mass_ge1_le_influence` (`Σ_{S≠∅} f̂² ≤ I[f]`, already on branch).
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_variance_le_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.variance_le_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_variance_eq_nonempty_mass()?;
        self.register_kkl_mass_ge1_le_influence()?;

        let c = EmptyConsts::new();
        let nat = c.nat.clone();
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let le = |a: Expr, b: Expr| Expr::apps(rat_le.clone(), [a, b]);

        // mass1 := subsetSum n (fun S => ind(ble 1 |S|)·(f̂·f̂))  — the shared term.
        let hcp_of = |n: &Expr| Expr::app(c.hcpoint.clone(), n.clone());
        let ind1_fn = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(hcp_of(n));
            let fh = c.fourier_of2(n, f, &s);
            let bit = c.ble1(c.ss_nat_of(n, &s));
            let body = c.mul(c.ind_of(bit), c.mul(fh.clone(), fh));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp_of(n), body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let concl = le(c.variance_of(&n, &f), c.total_influence_of(&n, &f));
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let v = c.variance_of(&n, &f);
            let mass1 = c.subset_sum_of(&n, ind1_fn(&b, &n, &f));
            let ti = c.total_influence_of(&n, &f);

            // h_eq : V = mass1   (variance_eq_nonempty_mass)
            let h_eq = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.variance_eq_nonempty_mass"),
                    vec![],
                ),
                [n.clone(), f.clone()],
            );
            // h_mass1_le : mass1 ≤ TI   (kkl_mass_ge1_le_influence)
            let h_mass1_le = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.kkl_mass_ge1_le_influence"),
                    vec![],
                ),
                [n.clone(), f.clone()],
            );
            // subst (motive t => t ≤ TI) mass1 V (symm h_eq) h_mass1_le : V ≤ TI
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat.clone());
                let body = le(t, ti.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // Eq.subst.{1} {Rat} {motive} {mass1} {V} (symm h_eq : mass1 = V) h_mass1_le
            let eq_subst = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let h_eq_symm = c.symm(v.clone(), mass1.clone(), h_eq); // mass1 = V
            let body = Expr::apps(
                eq_subst,
                [
                    c.rat.clone(),
                    motive,
                    mass1.clone(),
                    v.clone(),
                    h_eq_symm,
                    h_mass1_le,
                ],
            );

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
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
        env.init_boolean_analysis_kkl_emptyset()
            .expect("init_boolean_analysis_kkl_emptyset");
        env.init_boolean_analysis_kkl_emptyset()
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
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_chi_empty_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.chi_empty");
    }

    #[test]
    fn test_fourier_empty_eq_mean_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.fourier_empty_eq_mean");
    }

    #[test]
    fn test_nat_add_eq_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "Nat.add_eq_zero");
    }

    #[test]
    fn test_fin_sum_nat_eq_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "Fin.sumNat_eq_zero");
    }

    #[test]
    fn test_indnat_eq_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.indNat_eq_zero");
    }

    #[test]
    fn test_setsizenat_hcdecode_imp_val_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.setSizeNat_hcDecode_imp_val_zero");
    }

    #[test]
    fn test_fin_sum_nat_const_zero_of_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "Fin.sumNat_const_zero_of");
    }

    #[test]
    fn test_setsizenat_hcdecode_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.setSizeNat_hcDecode_zero");
    }

    #[test]
    fn test_emptyset_mass_isolation_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.emptyset_mass_isolation");
    }

    #[test]
    fn test_rat_sub_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "Rat.sub_zero");
    }

    #[test]
    fn test_mass_complement_pointwise_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.mass_complement_pointwise");
    }

    #[test]
    fn test_variance_eq_nonempty_mass_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.variance_eq_nonempty_mass");
    }

    #[test]
    fn test_variance_le_influence_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.variance_le_influence");
    }
}
