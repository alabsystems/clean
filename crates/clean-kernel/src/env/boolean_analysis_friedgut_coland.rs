// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut TCB→3 CO-LAND bricks — the empty-junta (`J := ∅`) branch connectors
//! the final `friedgut_boolean` assembly consumes for the `eps ≥ 1` and `eps = 0`
//! cases of the `n > B` outer branch.
//!
//! Each is a genuine `Declaration::Theorem`, `Constructive`, with an EMPTY
//! admitted-axiom closure. Hand-constructed `Expr` (no tactics). Idempotent.
//! Gated behind `cfg(any(test, feature = "math-overlays"))`.
//!
//! # BRICK — `BoolAnalysis.friedgut_empty_junta_mass_eq_variance`
//!
//! ```text
//! ∀ (n : Nat) (f : BoolFn n),
//!   subsetSum n (fun S => ind(notSubsetMask n S ∅) · (f̂ S · f̂ S))  =  Variance n f
//! ```
//!
//! where `∅ := fun (_ : Fin n) => Bool.false`. This is the keystone identity that
//! turns the v3-body masked Fourier mass at the empty junta into the `Variance`,
//! so the banked `variance_le_one` / `variance_le_influence` bounds discharge the
//! two cheap cases of the `friedgut_boolean` proof.
//!
//! ## Proof
//!
//! `notSubsetMask n S ∅` δ-unfolds (reducible) to
//! `Nat.ble 1 (setSizeNat n (fun i => Bool.and (S i) (Bool.not Bool.false)))`.
//! Since `Bool.not Bool.false ≡ Bool.true` and (via `Bool.and_comm` then the
//! `Bool.and Bool.true x ≡ x` ι-reduction) `Bool.and (S i) Bool.true = S i`, the
//! inner indicator function is `funext`-equal to `S`, so
//! `setSizeNat n (and-true-fn) = setSizeNat n S` (`congrArg (setSizeNat n)`),
//! hence `notSubsetMask n S ∅ = Nat.ble 1 (setSizeNat n S)`
//! (`congrArg (Nat.ble 1 ·)`). Lifting through `congrArg (fun b => ind b·(f̂·f̂))`
//! gives the per-`S` integrand equality, and `subsetSum_congr` lifts it to the
//! sum. Chaining with `Eq.symm (variance_eq_nonempty_mass n f)` (which states
//! `Variance n f = subsetSum n (fun S => ind(Nat.ble 1 |S|)·(f̂·f̂))`) lands the
//! identity. The integrand RHS is BYTE-IDENTICAL to `variance_eq_nonempty_mass`'s
//! `ind1_fn` (`Nat.ble (succ zero) (setSizeNat n S)`), so the `symm` slots in
//! directly.
//!
//! `funext` reaches `Quot.sound` (a FOUNDATIONAL axiom), so the admitted-axiom
//! closure stays empty (`Constructive`).
//!
//! NO `sorry` / `sorryAx` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Real` / `Rat.dist` / new `Axiom`. No axiom added
//! or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared carrier atoms for the co-land bricks. Spellings byte-match the banked
/// `variance_eq_nonempty_mass` (`EmptyConsts`) and
/// `friedgut_empty_junta_mass_le_total` (`TcbConsts`).
struct ColandConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    bool_and: Expr,
    bool_not: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_ble: Expr,
    rat_mul: Expr,
    fin: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fourier: Expr,
    subset_sum: Expr,
    ind: Expr,
    not_subset_mask: Expr,
    set_size_nat: Expr,
    variance: Expr,
    bool_rec: Expr,
    nat_one: Expr,
    l0: Level,
    l1: Level,
}

impl ColandConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_ble: k("Nat.ble"),
            rat_mul: k("Rat.mul"),
            fin: k("Fin"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            ind: k("BoolAnalysis.ind"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            variance: k("BoolAnalysis.Variance"),
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            nat_one: Expr::app(k("Nat.succ"), k("Nat.zero")),
            l0,
            l1,
        }
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
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn band(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [a, b])
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    /// `Nat.ble (succ zero) m` — byte-matches `EmptyConsts::ble1`.
    fn ble1(&self, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [self.one_nat(), m])
    }
    fn set_size_nat_of(&self, n: &Expr, s: Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s])
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    /// `@congrArg.{1,1} A B a1 a2 g h : g a1 = g a2`.
    fn congr_arg(&self, dom: Expr, cod: Expr, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [dom, cod, a1, a2, g, h],
        )
    }
    /// `@Eq.symm.{1} A a b h : b = a`.
    fn symm(&self, ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [ty, a, b, h],
        )
    }
    /// `@Eq.trans.{1} A a b c h1 h2 : a = c`.
    fn trans(&self, ty: Expr, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [ty, a, b, c, h1, h2],
        )
    }
    /// `∅ : HCPoint n := fun (_ : Fin n) => Bool.false`.
    fn empty_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, self.bool_false.clone()))
    }
    /// `Nat.le a b`.
    fn le_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
    }
    /// `LE.le.{0} Rat instLERat a b` — the v3-body `Rat`-order spelling.
    fn le_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![self.l0.clone()]),
            [
                self.rat.clone(),
                Expr::const_(Name::from_string("instLERat"), vec![]),
                a,
                b,
            ],
        )
    }
    /// `And P Q`.
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
    }
    /// `And.intro P Q hp hq : And P Q`.
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [p, q, hp, hq],
        )
    }
    /// `indNat b = @Bool.rec.{1} (fun _=>Nat) 0 1 b` (byte-matches `setSizeNat`'s
    /// per-coordinate summand).
    fn ind_nat_of(&self, bit: Expr) -> Expr {
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            self.bool_rec.clone(),
            [nat_motive, self.nat_zero.clone(), self.nat_one.clone(), bit],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
}

impl Environment {
    /// `BoolAnalysis.friedgut_empty_junta_mass_eq_variance :
    ///   ∀ (n : Nat) (f : BoolFn n),
    ///     subsetSum n (fun S => ind(notSubsetMask n S ∅)·(f̂·f̂)) = Variance n f`.
    ///
    /// The empty-junta masked Fourier mass EQUALS the variance — the keystone for
    /// the cheap (`eps ≥ 1`, `eps = 0`) cases of the `friedgut_boolean` retirement.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    /// No axiom added or removed.
    pub fn register_friedgut_empty_junta_mass_eq_variance(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_empty_junta_mass_eq_variance");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // BoolFn, FourierCoefficient, ind, Variance
        self.init_bool()?; // Bool.and / Bool.not carriers
        self.init_funext()?; // funext (derived from Quot.sound)
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_set_size_nat()?;
        self.register_not_subset_mask()?;
        self.register_bool_comm_proofs()?; // Bool.and_comm
        self.register_variance_eq_nonempty_mass()?; // Variance = Σ ind(ble 1 |S|)·f̂²
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ColandConsts::new();
        let and_comm = Expr::const_(Name::from_string("Bool.and_comm"), vec![]);
        let var_eq = Expr::const_(
            Name::from_string("BoolAnalysis.variance_eq_nonempty_mass"),
            vec![],
        );
        let subset_sum_congr =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
        // funext.{1,1} — α = Fin n : Sort 1, β x = Bool : Sort 1.
        let funext = Expr::const_(
            Name::from_string("funext"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );

        // `fun S => ind(notSubsetMask n S ∅)·(f̂·f̂)` — the empty-junta integrand
        // (byte-matches `friedgut_empty_junta_mass_le_total`'s `empty_masked_fn`).
        let empty_fn_g = |c: &ColandConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let empty = c.empty_fn(&b, n);
            let bit = c.not_subset_mask_of(n, &s, &empty);
            let coeff = c.fourier_of(n, f, &s);
            let body = c.mul(c.ind_of(bit), c.mul(coeff.clone(), coeff));
            b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        // `fun S => ind(Nat.ble 1 |S|)·(f̂·f̂)` — the variance-RHS integrand
        // (byte-matches `variance_eq_nonempty_mass`'s `ind1_fn`).
        let var_fn_h = |c: &ColandConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let bit = c.ble1(c.set_size_nat_of(n, s.clone()));
            let coeff = c.fourier_of(n, f, &s);
            let body = c.mul(c.ind_of(bit), c.mul(coeff.clone(), coeff));
            b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());

            let g = empty_fn_g(&c, &b, &n, &f);
            let ss_g = c.ssum(&n, g.clone());
            let variance = c.variance_of(&n, &f);

            if !for_value {
                let concl = c.eq_rat(ss_g, variance);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            let h = var_fn_h(&c, &b, &n, &f);
            let ss_h = c.ssum(&n, h.clone());

            // per_S : ∀ (S : HCPoint n), g S = h S.
            //   g S ≡ ind(notSubsetMask n S ∅)·(f̂·f̂),  h S ≡ ind(ble1 |S|)·(f̂·f̂).
            //   We rewrite the mask: notSubsetMask n S ∅ = ble1 (setSizeNat n S).
            let per_s = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = e.fresh_local(hcp.clone());
                let empty = c.empty_fn(&e, &n);
                let coeff = c.fourier_of(&n, &f, &s);
                let sq = c.mul(coeff.clone(), coeff); // f̂·f̂ = X

                // and_true_fn := fun (i : Fin n) => Bool.and (S i) (Bool.not Bool.false).
                //   This is the inner setSizeNat-argument function inside
                //   notSubsetMask n S ∅ (∅ i ≡ Bool.false).
                let and_true_fn = {
                    let mut g0 = EnvDeclBuilder::child_of(&e);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = g0.fresh_local(fin_n.clone());
                    let s_i = Expr::app(s.clone(), i.clone());
                    let body = c.band(s_i, c.bnot(c.bool_false.clone()));
                    g0.finish_child(g0.mk_lam(i_id, BinderInfo::Default, fin_n, body))
                };

                // fn_pw : ∀ (i : Fin n), Eq Bool (and_true_fn i) (S i).
                //   and_true_fn i ≡ Bool.and (S i) (Bool.not false) ≡ Bool.and (S i) true.
                //   Bool.and_comm (S i) true : and (S i) true = and true (S i).
                //   RHS `and true (S i)` ≡ S i (ι-reduce first true). So the eq's
                //   RHS is def-eq to `S i`, closing `and_true_fn i = S i`.
                let fn_pw = {
                    let mut g0 = EnvDeclBuilder::child_of(&e);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = g0.fresh_local(fin_n.clone());
                    let s_i = Expr::app(s.clone(), i.clone());
                    // comm : and (S i) true = and true (S i).
                    let comm = Expr::apps(and_comm.clone(), [s_i.clone(), c.bool_true.clone()]);
                    g0.finish_child(g0.mk_lam(i_id, BinderInfo::Default, fin_n, comm))
                };

                // fn_eq : and_true_fn = S  := funext fn_pw.
                //   funext.{1,1} (Fin n) (fun _ => Bool) and_true_fn S fn_pw.
                let fin_n = c.fin_of(&n);
                let bool_const_fam = {
                    let mut g0 = EnvDeclBuilder::child_of(&e);
                    let (i_id, _i) = g0.fresh_local(fin_n.clone());
                    g0.finish_child(g0.mk_lam(
                        i_id,
                        BinderInfo::Default,
                        fin_n.clone(),
                        c.bool_.clone(),
                    ))
                };
                let fn_eq = Expr::apps(
                    funext.clone(),
                    [
                        fin_n.clone(),
                        bool_const_fam,
                        and_true_fn.clone(),
                        s.clone(),
                        fn_pw,
                    ],
                );

                // size_eq : setSizeNat n and_true_fn = setSizeNat n S
                //   := congrArg (HCPoint n) Nat and_true_fn S (setSizeNat n) fn_eq.
                let set_size_partial = Expr::apps(c.set_size_nat.clone(), [n.clone()]);
                let size_eq = c.congr_arg(
                    hcp.clone(),
                    c.nat.clone(),
                    and_true_fn.clone(),
                    s.clone(),
                    set_size_partial,
                    fn_eq,
                );

                // mask_eq : (ble 1 (setSizeNat n and_true_fn)) = (ble 1 (setSizeNat n S))
                //   := congrArg Nat Bool (setSizeNat n and_true_fn) (setSizeNat n S)
                //               (fun m => Nat.ble 1 m) size_eq.
                //   LHS is DEF-EQ to notSubsetMask n S ∅ (notSubsetMask unfolds to
                //   ble 1 (setSizeNat n and_true_fn) at ∅ i ≡ false).
                let ble1_fn = {
                    let mut g0 = EnvDeclBuilder::child_of(&e);
                    let (m_id, m) = g0.fresh_local(c.nat.clone());
                    let body = c.ble1(m);
                    g0.finish_child(g0.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let size_and = c.set_size_nat_of(&n, and_true_fn.clone());
                let size_s = c.set_size_nat_of(&n, s.clone());
                let mask_eq = c.congr_arg(
                    c.nat.clone(),
                    c.bool_.clone(),
                    size_and,
                    size_s.clone(),
                    ble1_fn,
                    size_eq,
                );

                // integrand_eq : ind(notSubsetMask n S ∅)·(f̂·f̂) = ind(ble1 |S|)·(f̂·f̂)
                //   := congrArg Bool Rat (notSubsetMask n S ∅) (ble1 |S|)
                //               (fun bit => ind(bit)·X) mask_eq.
                //   `mask_eq`'s LHS `ble 1 (setSizeNat n and_true_fn)` is def-eq to
                //   `notSubsetMask n S ∅`, and its RHS is `ble1 (setSizeNat n S)`,
                //   so `congrArg` lands exactly the integrand equality.
                let mask_lhs = c.not_subset_mask_of(&n, &s, &empty); // notSubsetMask n S ∅
                let mask_rhs = c.ble1(size_s.clone()); // ble1 (setSizeNat n S)
                let ind_x_fn = {
                    let mut g0 = EnvDeclBuilder::child_of(&e);
                    let (bit_id, bit) = g0.fresh_local(c.bool_.clone());
                    let body = c.mul(c.ind_of(bit), sq.clone());
                    g0.finish_child(g0.mk_lam(bit_id, BinderInfo::Default, c.bool_.clone(), body))
                };
                let integrand_eq = c.congr_arg(
                    c.bool_.clone(),
                    c.rat.clone(),
                    mask_lhs,
                    mask_rhs,
                    ind_x_fn,
                    mask_eq,
                );
                e.finish_child(e.mk_lam(s_id, BinderInfo::Default, hcp, integrand_eq))
            };

            // congr_sum : subsetSum n g = subsetSum n h  := subsetSum_congr n g h per_s.
            let congr_sum = Expr::apps(
                subset_sum_congr.clone(),
                [n.clone(), g.clone(), h.clone(), per_s],
            );

            // var_eq_nf : Variance n f = subsetSum n h.
            let var_eq_nf = Expr::apps(var_eq.clone(), [n.clone(), f.clone()]);
            // var_eq_symm : subsetSum n h = Variance n f.
            let var_eq_symm = c.symm(c.rat.clone(), variance.clone(), ss_h.clone(), var_eq_nf);

            // proof : subsetSum n g = Variance n f.
            let proof = c.trans(
                c.rat.clone(),
                ss_g.clone(),
                ss_h.clone(),
                variance.clone(),
                congr_sum,
                var_eq_symm,
            );

            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, proof);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
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

    /// `BoolAnalysis.friedgut_boolean_case_empty :
    ///   ∀ (n : Nat) (f : BoolFn n) (eps : Rat) (B : Nat),
    ///     Rat.le (Variance n f) eps →
    ///       Exists (J : HCPoint n)
    ///         (And (Nat.le (setSizeNat n J) B)
    ///              (Rat.le (subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂·f̂))) eps))`
    ///
    /// The empty-junta (`J := ∅`) existential branch of `friedgut_boolean`,
    /// abstracted over the `Variance ≤ eps` bound — the SHARED skeleton both cheap
    /// cases of the `n > B` outer branch reuse:
    ///
    /// * `eps ≥ 1`: instantiate the hyp with `Var ≤ 1 ≤ eps` (`variance_le_one`).
    /// * `eps = 0` : instantiate with `Var ≤ I ≤ K ≤ 0 = eps` (`variance_le_influence`).
    ///
    /// SIZE: `setSizeNat n ∅ ≡ Fin.sumNat n (fun i => indNat false) = 0`
    /// (`Fin.sumNat_const_zero_of`, each summand def-eq `0`), then `Nat.zero_le B`
    /// transported along `0 = setSizeNat n ∅`. MASS:
    /// `friedgut_empty_junta_mass_eq_variance n f` rewrites the masked mass to
    /// `Variance n f`, then the hyp gives `≤ eps`. The Exists predicate is
    /// BYTE-IDENTICAL to the v3-body branch (`ind(notSubsetMask n S J)·(f̂·f̂)`),
    /// so it slots into the `friedgut_boolean` assembly verbatim. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent. No axiom added or
    /// removed.
    pub fn register_friedgut_boolean_case_empty(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_boolean_case_empty");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?; // LE.le/instLERat surface
        self.init_bool()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_not_subset_mask()?;
        self.register_fin_sum_nat_const_zero_of()?; // Fin.sumNat_const_zero_of
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.register_friedgut_empty_junta_mass_eq_variance()?; // mass(∅) = Variance
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ColandConsts::new();
        let u1 = c.l1.clone();
        let exists_c = Expr::const_(Name::from_string("Exists"), vec![u1.clone()]);
        let exists_intro = Expr::const_(Name::from_string("Exists.intro"), vec![u1.clone()]);
        let const_zero_of = Expr::const_(Name::from_string("Fin.sumNat_const_zero_of"), vec![]);
        let nat_zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        let mass_eq_var = Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_empty_junta_mass_eq_variance"),
            vec![],
        );
        let eq_refl_nat = Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]);
        let eq_symm_nat = Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]);

        // `fun S => ind(notSubsetMask n S J)·(f̂·f̂)` — the masked-mass integrand
        // at an arbitrary junta `J` (byte-matches the v3 body's `mass_fn`).
        let mass_fn =
            |c: &ColandConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr| -> Expr {
                let mut b = EnvDeclBuilder::child_of(parent);
                let hcp = c.hcpoint_of(n);
                let (s_id, s) = b.fresh_local(hcp.clone());
                let bit = c.not_subset_mask_of(n, &s, j);
                let coeff = c.fourier_of(n, f, &s);
                let body = c.mul(c.ind_of(bit), c.mul(coeff.clone(), coeff));
                b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

        // Shared existential predicate (byte-matches the v3 body / case_le):
        //   fun (J : HCPoint n) => And (Nat.le (setSizeNat n J) B)
        //                              (Rat.le (subsetSum n (mass J)) eps).
        let pred_of = |c: &ColandConsts,
                       parent: &EnvDeclBuilder,
                       n: &Expr,
                       f: &Expr,
                       eps: &Expr,
                       big_b: &Expr|
         -> Expr {
            let mut g = EnvDeclBuilder::child_of(parent);
            let hcp = c.hcpoint_of(n);
            let (j_id, j) = g.fresh_local(hcp.clone());
            let size_concl = c.le_nat(c.set_size_nat_of(n, j.clone()), big_b.clone());
            let mass = mass_fn(c, &g, n, f, &j);
            let mass_concl = c.le_rat(c.ssum(n, mass), eps.clone());
            let and = c.and(size_concl, mass_concl);
            g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcp, and))
        };

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (bb_id, big_b) = b.fresh_local(c.nat.clone());

            // hvar : Variance n f ≤ eps.
            let hvar_ty = c.le_rat(c.variance_of(&n, &f), eps.clone());

            let hcp = c.hcpoint_of(&n);
            let pred = pred_of(&c, &b, &n, &f, &eps, &big_b);
            let exists_goal = Expr::apps(exists_c.clone(), [hcp.clone(), pred.clone()]);

            let (hvar_id, hvar) = b.fresh_local(hvar_ty.clone());

            if !for_value {
                let e = b.mk_pi(hvar_id, BinderInfo::Default, hvar_ty.clone(), exists_goal);
                let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
                let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // ── witness J := ∅ ──
            let empty = c.empty_fn(&b, &n);

            // SIZE : Nat.le (setSizeNat n ∅) B.
            //   ind_nat_empty := fun (i : Fin n) => indNat (∅ i).
            //     setSizeNat n ∅ ≡ Fin.sumNat n ind_nat_empty.
            let ind_nat_empty = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let body = c.ind_nat_of(Expr::app(empty.clone(), i));
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // pw : ∀ (i : Fin n), Eq Nat (ind_nat_empty i) 0.
            //   ind_nat_empty i ≡ indNat false ≡ 0, so Eq.refl Nat 0 (def-eq).
            let pw = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, _i) = e.fresh_local(fin_n.clone());
                let refl0 = Expr::apps(eq_refl_nat.clone(), [c.nat.clone(), c.nat_zero.clone()]);
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, refl0))
            };
            // ssz : Fin.sumNat n ind_nat_empty = 0  (≡ setSizeNat n ∅ = 0).
            let ssz = Expr::apps(
                const_zero_of.clone(),
                [n.clone(), ind_nat_empty.clone(), pw],
            );
            let size_empty = c.set_size_nat_of(&n, empty.clone()); // ≡ Fin.sumNat n ind_nat_empty
                                                                   // ssz_symm : 0 = setSizeNat n ∅.
            let ssz_symm = Expr::apps(
                eq_symm_nat.clone(),
                [c.nat.clone(), size_empty.clone(), c.nat_zero.clone(), ssz],
            );
            // size_proof : Nat.le (setSizeNat n ∅) B.
            //   motive : fun (t : Nat) => Nat.le t B.
            //   Nat.zero_le B : Nat.le 0 B.
            //   subst motive (a := 0) (b := setSizeNat n ∅) ssz_symm (zero_le B).
            let size_motive = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = e.fresh_local(c.nat.clone());
                let body = c.le_nat(t, big_b.clone());
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let zero_le_b = Expr::app(nat_zero_le.clone(), big_b.clone());
            let size_proof = Expr::apps(
                Expr::const_(Name::from_string("Eq.subst"), vec![u1.clone()]),
                [
                    c.nat.clone(),
                    size_motive,
                    c.nat_zero.clone(),
                    size_empty.clone(),
                    ssz_symm,
                    zero_le_b,
                ],
            );

            // MASS : Rat.le (subsetSum n (mass ∅)) eps.
            //   meq : subsetSum n (mass ∅) = Variance n f.
            //   motive : fun (t : Rat) => Rat.le t eps.
            //   symm meq : Variance = subsetSum n (mass ∅).
            //   subst motive (a := Variance) (b := subsetSum n (mass ∅)) (symm meq) hvar.
            let mass = mass_fn(&c, &b, &n, &f, &empty);
            let ss_mass = c.ssum(&n, mass.clone());
            let variance = c.variance_of(&n, &f);
            let meq = Expr::apps(mass_eq_var.clone(), [n.clone(), f.clone()]);
            // symm meq : Variance n f = subsetSum n (mass ∅).
            let meq_symm = c.symm(c.rat.clone(), ss_mass.clone(), variance.clone(), meq);
            let mass_motive = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = e.fresh_local(c.rat.clone());
                let body = c.le_rat(t, eps.clone());
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let mass_proof = c.subst_rat(
                mass_motive,
                variance.clone(),
                ss_mass.clone(),
                meq_symm,
                hvar,
            );

            // And.intro size_concl mass_concl size_proof mass_proof.
            let size_concl = c.le_nat(size_empty, big_b.clone());
            let mass_concl = c.le_rat(ss_mass, eps.clone());
            let and_proof = c.and_intro(size_concl, mass_concl, size_proof, mass_proof);

            // Exists.intro (HCPoint n) pred ∅ and_proof.
            let intro = Expr::apps(
                exists_intro.clone(),
                [hcp.clone(), pred.clone(), empty, and_proof],
            );

            let e = b.mk_lam(hvar_id, BinderInfo::Default, hvar_ty, intro);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
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

/// Shared atoms for the final 4-case `friedgut_boolean` assembly proof. Spellings
/// byte-match the v3 helper body (`friedgut_l2_faithful_body_v3`) and the three
/// landed case bricks (`case_le`, `case_empty`, `case_threshold`) so the assembled
/// term's `Exists` slots into the (reducible-unfolded) helper conclusion verbatim.
#[cfg(test)]
struct AssemblyConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_false: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    nat_ble: Expr,
    nat_le: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    variance: Expr,
    total_influence: Expr,
    l0: Level,
    l1: Level,
}

#[cfg(test)]
impl AssemblyConsts {
    #[cfg(test)]
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_false: k("Bool.false"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_mul: k("Nat.mul"),
            nat_pow: k("Nat.pow"),
            nat_ble: k("Nat.ble"),
            nat_le: k("Nat.le"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            variance: k("BoolAnalysis.Variance"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            l0: Level::zero(),
            l1: Level::succ(Level::zero()),
        }
    }

    #[cfg(test)]
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    #[cfg(test)]
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    #[cfg(test)]
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    #[cfg(test)]
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    #[cfg(test)]
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    #[cfg(test)]
    fn two(&self) -> Expr {
        self.nat_lit(2)
    }
    /// `Nat.pow 2 n`.
    #[cfg(test)]
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), n.clone()])
    }
    #[cfg(test)]
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    /// `friedgut_budget_v3 e := Nat.mul 48 (Nat.pow 2 e)` — byte-matches the body.
    #[cfg(test)]
    fn budget_v3(&self, e: &Expr) -> Expr {
        self.nmul(self.nat_lit(48), self.pow2(e))
    }
    /// `B := Nat.pow 2 (48·2^e)` — byte-matches the body's `pow2b`.
    #[cfg(test)]
    fn big_b(&self, e: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), self.budget_v3(e)])
    }
    #[cfg(test)]
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Nat.ble n m : Bool`.
    #[cfg(test)]
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    /// `Nat.le a b`.
    #[cfg(test)]
    fn le_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Nat.lt a b`.
    #[cfg(test)]
    fn lt_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
    }
    /// `LE.le.{0} Rat instLERat a b`.
    #[cfg(test)]
    fn le_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![self.l0.clone()]),
            [
                self.rat.clone(),
                Expr::const_(Name::from_string("instLERat"), vec![]),
                a,
                b,
            ],
        )
    }
    /// `Rat.lt a b`.
    #[cfg(test)]
    fn lt_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    /// `And P Q`.
    #[cfg(test)]
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
    }
    /// `Or P Q`.
    #[cfg(test)]
    fn or(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [p, q])
    }
    /// `@Eq Rat a b`.
    #[cfg(test)]
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    /// `@Eq Bool a b`.
    #[cfg(test)]
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.bool_.clone(), a, b],
        )
    }
    /// `@Eq.refl Bool v`.
    #[cfg(test)]
    fn refl_bool(&self, v: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.bool_.clone(), v],
        )
    }
    /// `@Eq.symm Rat a b h : b = a`.
    #[cfg(test)]
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    #[cfg(test)]
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `Rat.le_trans a b c (a≤b) (b≤c) : a ≤ c` (over the `Rat.le` carrier, def-eq
    /// to the `LE.le instLERat` spelling).
    #[cfg(test)]
    fn le_trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` — byte-matches the v3 body / guard.
    #[cfg(test)]
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    m.clone(),
                ),
                self.nat_lit(1),
            ],
        )
    }
}

/// The final 4-case `friedgut_boolean` proof term — `fun n f K eps hI heps e hg =>`
/// the `Exists` of the (reducible-unfolded) helper body. Outer split on
/// `Nat.ble n B` (`B := 2^(48·2^e)`); on the `n > B` branch a `Rat`-order
/// trichotomy of `eps` routes to the three landed case bricks.
#[cfg(test)]
fn build_friedgut_boolean_assembly(for_value: bool) -> Expr {
    let c = AssemblyConsts::new();
    let u1 = c.l1.clone();

    let case_le = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_boolean_case_le"),
        vec![],
    );
    let case_empty = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_boolean_case_empty"),
        vec![],
    );
    let case_threshold = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_boolean_case_threshold"),
        vec![],
    );
    let variance_le_one = Expr::const_(Name::from_string("BoolAnalysis.variance_le_one"), vec![]);
    let variance_le_influence = Expr::const_(
        Name::from_string("BoolAnalysis.variance_le_influence"),
        vec![],
    );
    let lt_or_eq = Expr::const_(Name::from_string("Rat.lt_or_eq_of_le"), vec![]);
    let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let not_le_of_ble_false = Expr::const_(Name::from_string("Nat.not_le_of_ble_eq_false"), vec![]);
    let nat_not_le = Expr::const_(Name::from_string("Nat.not_le"), vec![]);
    let iff_mp = Expr::const_(Name::from_string("Iff.mp"), vec![]);
    let mul_zero = Expr::const_(Name::from_string("Rat.mul_zero"), vec![]);
    let exists_c = Expr::const_(Name::from_string("Exists"), vec![u1.clone()]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (k_id, kk) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    // hI : I[f] ≤ K   (LE.le instLERat).
    let hi_ty = c.le_rat(c.total_influence_of(&n, &f), kk.clone());
    let (hi_id, hi) = b.fresh_local(hi_ty.clone());
    // heps : 0 ≤ eps   (LE.le instLERat).
    let heps_ty = c.le_rat(c.rat_zero.clone(), eps.clone());
    let (heps_id, heps) = b.fresh_local(heps_ty.clone());
    let (e_id, e) = b.fresh_local(c.nat.clone());

    // guard(e) := And (natCast(2^e)·eps ≤ K) (K ≤ natCast(2^(e+1))·eps).
    let pow_e = c.pow2(&e);
    let e1 = Expr::app(c.nat_succ.clone(), e.clone());
    let pow_e1 = c.pow2(&e1);
    let guard_lo = c.le_rat(c.mul(c.natcast(&pow_e), eps.clone()), kk.clone());
    let guard_hi = c.le_rat(kk.clone(), c.mul(c.natcast(&pow_e1), eps.clone()));
    let guard_ty = c.and(guard_lo.clone(), guard_hi.clone());
    let (hg_id, hg) = b.fresh_local(guard_ty.clone());

    let big_b = c.big_b(&e);
    let hcp_n = c.hcpoint_of(&n);

    // The shared `Exists` goal predicate (byte-identical to the v3 body's), built
    // for `B := 2^(48·2^e)`.
    let pred = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = g.fresh_local(hcp_n.clone());
        let size_concl = c.le_nat(
            Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
                [n.clone(), j.clone()],
            ),
            big_b.clone(),
        );
        let mass_fn = {
            let mut h = EnvDeclBuilder::child_of(&g);
            let (s_id, s) = h.fresh_local(hcp_n.clone());
            let coeff = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
                [n.clone(), f.clone(), s.clone()],
            );
            let mask = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.notSubsetMask"), vec![]),
                [n.clone(), s.clone(), j.clone()],
            );
            let ind = Expr::app(
                Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
                mask,
            );
            let body = c.mul(ind, c.mul(coeff.clone(), coeff));
            h.finish_child(h.mk_lam(s_id, BinderInfo::Default, hcp_n.clone(), body))
        };
        let mass = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            [n.clone(), mass_fn],
        );
        let mass_concl = c.le_rat(mass, eps.clone());
        let and = c.and(size_concl, mass_concl);
        g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcp_n.clone(), and))
    };
    let exists_goal = Expr::apps(exists_c.clone(), [hcp_n.clone(), pred.clone()]);

    if !for_value {
        // The proof's type is the v3 helper body; we re-declare it structurally so
        // the registrar can `check_type` it directly. The kernel sees this as
        // def-eq to `helper n f K eps` (reducible).
        let r = b.mk_pi(hg_id, BinderInfo::Default, guard_ty, exists_goal);
        let r = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), r);
        let r = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, r);
        let r = b.mk_pi(hi_id, BinderInfo::Default, hi_ty, r);
        let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
        let r = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), r);
        let r = b.mk_pi(f_id, BinderInfo::Default, bf_ty, r);
        return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r));
    }

    // ── value: the 4-case proof of `exists_goal` ──

    // The `eps ≥ 1` empty-junta branch, as a function of a proof `h1 : 1 ≤ eps`.
    //   var_le_eps : Variance n f ≤ eps := le_trans (variance_le_one) h1.
    //   case_empty n f eps B var_le_eps.
    let empty_via_one = |c: &AssemblyConsts, h1: Expr| -> Expr {
        let var = c.variance_of(&n, &f);
        let vlo = Expr::apps(variance_le_one.clone(), [n.clone(), f.clone()]); // Var ≤ 1
        let var_le_eps = c.le_trans_rat(var, c.rat_one.clone(), eps.clone(), vlo, h1);
        Expr::apps(
            case_empty.clone(),
            [n.clone(), f.clone(), eps.clone(), big_b.clone(), var_le_eps],
        )
    };

    // ── outer split on `Nat.ble n B` (B := 2^(48·2^e)) ──
    let ble_nb = c.ble(n.clone(), big_b.clone());

    // motive : fun (v : Bool) => Eq Bool (Nat.ble n B) v → exists_goal.
    let outer_motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (v_id, v) = m.fresh_local(c.bool_.clone());
        let disc = c.eq_bool(ble_nb.clone(), v.clone());
        let body = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (hd_id, _hd) = mm.fresh_local(disc.clone());
            mm.finish_child(mm.mk_pi(
                hd_id,
                BinderInfo::Default,
                disc.clone(),
                exists_goal.clone(),
            ))
        };
        m.finish_child(m.mk_lam(v_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // minor (v = true): n ≤ B → case_le.
    //   from heq_t : Nat.ble n B = true, hn_le : n ≤ B := Nat.le_of_ble_eq_true n B heq_t.
    //   case_le n f eps B hn_le heps : Exists.
    let minor_true = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let disc_t = c.eq_bool(
            ble_nb.clone(),
            Expr::const_(Name::from_string("Bool.true"), vec![]),
        );
        let (heq_id, heq) = m.fresh_local(disc_t.clone());
        let hn_le = Expr::apps(
            Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]),
            [n.clone(), big_b.clone(), heq],
        );
        let body = Expr::apps(
            case_le.clone(),
            [
                n.clone(),
                f.clone(),
                eps.clone(),
                big_b.clone(),
                hn_le,
                heps.clone(),
            ],
        );
        m.finish_child(m.mk_lam(heq_id, BinderInfo::Default, disc_t, body))
    };

    // minor (v = false): n > B → eps-trichotomy → {case_empty | case_threshold}.
    let minor_false = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let disc_f = c.eq_bool(ble_nb.clone(), c.bool_false.clone());
        let (heqf_id, heqf) = m.fresh_local(disc_f.clone());

        // hn : Nat.lt B n  := Iff.mp (Nat.not_le n B) (not_le_of_ble_eq_false n B heqf).
        let not_le = Expr::apps(
            not_le_of_ble_false.clone(),
            [n.clone(), big_b.clone(), heqf],
        ); // (n ≤ B) → False
        let nb_iff = Expr::apps(nat_not_le.clone(), [n.clone(), big_b.clone()]); // Iff ((n≤B)→False) (B<n)
        let lt_concl = c.lt_nat(big_b.clone(), n.clone());
        let hn = Expr::apps(
            iff_mp.clone(),
            [
                Expr::pi(
                    BinderInfo::Default,
                    c.le_nat(n.clone(), big_b.clone()),
                    Expr::const_(Name::from_string("False"), vec![]),
                ),
                lt_concl.clone(),
                nb_iff,
                not_le,
            ],
        );

        // OUTER eps trichotomy via `Rat.le_total eps 1`:
        //   left  : eps ≤ 1 → split (eps<1 | eps=1).
        //   right : 1 ≤ eps → empty_via_one.
        let eps_le_1 = c.le_rat(eps.clone(), c.rat_one.clone()); // wait: le_total uses Rat.le const spelling
                                                                 // NOTE: Rat.le_total yields `Or (Rat.le a b) (Rat.le b a)` over the bare
                                                                 // `Rat.le` carrier (def-eq to the LE.le instLERat spelling).
        let le_total_eps1 = Expr::apps(le_total.clone(), [eps.clone(), c.rat_one.clone()]);
        let p_le = c.le_rat(eps.clone(), c.rat_one.clone()); // eps ≤ 1
        let q_le = c.le_rat(c.rat_one.clone(), eps.clone()); // 1 ≤ eps
        let _ = eps_le_1;

        // motive for the OUTER Or.rec: const exists_goal.
        let outer_or_motive = {
            let mut om = EnvDeclBuilder::child_of(&m);
            let or_ty = c.or(p_le.clone(), q_le.clone());
            let (hh_id, _hh) = om.fresh_local(or_ty.clone());
            om.finish_child(om.mk_lam(hh_id, BinderInfo::Default, or_ty, exists_goal.clone()))
        };

        // RIGHT branch: 1 ≤ eps → empty_via_one.
        let outer_right = {
            let mut rc = EnvDeclBuilder::child_of(&m);
            let (h1_id, h1) = rc.fresh_local(q_le.clone());
            let body = empty_via_one(&c, h1);
            rc.finish_child(rc.mk_lam(h1_id, BinderInfo::Default, q_le.clone(), body))
        };

        // LEFT branch: eps ≤ 1 → INNER split via `Rat.lt_or_eq_of_le eps 1`.
        let outer_left = {
            let mut lc = EnvDeclBuilder::child_of(&m);
            let (hle_id, hle) = lc.fresh_local(p_le.clone()); // eps ≤ 1

            // inner : Or (eps < 1) (eps = 1) := lt_or_eq_of_le eps 1 hle.
            let inner = Expr::apps(lt_or_eq.clone(), [eps.clone(), c.rat_one.clone(), hle]);
            let lt_e1 = c.lt_rat(eps.clone(), c.rat_one.clone()); // eps < 1
            let eq_e1 = c.eq_rat(eps.clone(), c.rat_one.clone()); // eps = 1

            // inner Or.rec motive: const exists_goal.
            let inner_or_motive = {
                let mut om = EnvDeclBuilder::child_of(&lc);
                let or_ty = c.or(lt_e1.clone(), eq_e1.clone());
                let (hh_id, _hh) = om.fresh_local(or_ty.clone());
                om.finish_child(om.mk_lam(hh_id, BinderInfo::Default, or_ty, exists_goal.clone()))
            };

            // inner LEFT (eps < 1): 0 < eps (from heps + eps≠0… use heps : 0≤eps
            //   together with eps<1? No — threshold needs 0<eps STRICT). We obtain
            //   0<eps by ANOTHER trichotomy on heps below; package it as a function.
            // We compute `heps_pos : 0 < eps` lazily inside, via `lt_or_eq 0 eps heps`.
            // But in the (eps<1) inner-left we still need 0<eps. Re-derive:
            //   lt_or_eq 0 eps heps : Or (0<eps) (0=eps).
            //     0<eps → threshold.
            //     0=eps → eps=0 → case_empty (K ≤ 0 chain).
            let pos_or = {
                Expr::apps(
                    lt_or_eq.clone(),
                    [c.rat_zero.clone(), eps.clone(), heps.clone()],
                )
            };
            let lt_0e = c.lt_rat(c.rat_zero.clone(), eps.clone()); // 0 < eps
            let eq_0e = c.eq_rat(c.rat_zero.clone(), eps.clone()); // 0 = eps

            // case_empty for eps = 0 path, as a function of `heq0 : 0 = eps`.
            //   guard_hi : K ≤ natCast(2^(e+1))·eps.
            //   subst (eps→0 via symm heq0 : eps = 0) → K ≤ natCast(2^(e+1))·0.
            //   subst (mul_zero) → K ≤ 0.
            //   Var ≤ I ≤ K ≤ 0   →  Var ≤ 0  →  subst (heq0 : 0=eps) →  Var ≤ eps.
            let empty_via_zero = |c: &AssemblyConsts, heq0: Expr| -> Expr {
                // hg components.
                let hg_hi = Expr::apps(
                    Expr::const_(Name::from_string("And.right"), vec![]),
                    [guard_lo.clone(), guard_hi.clone(), hg.clone()],
                ); // K ≤ natCast(2^(e+1))·eps
                let cast_pe1 = c.natcast(&pow_e1);
                // eps = 0 := symm heq0.
                let eps_eq_0 = c.symm_rat(c.rat_zero.clone(), eps.clone(), heq0.clone());
                // motive_a : fun t => K ≤ natCast(2^(e+1))·t.
                let motive_a = {
                    let mut d = EnvDeclBuilder::child_of(&lc);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le_rat(kk.clone(), c.mul(cast_pe1.clone(), t));
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // hk_mul0 : K ≤ natCast(2^(e+1))·0.
                let hk_mul0 =
                    c.subst_rat(motive_a, eps.clone(), c.rat_zero.clone(), eps_eq_0, hg_hi);
                // mz : natCast(2^(e+1))·0 = 0  (Rat.mul_zero (natCast(2^(e+1)))).
                let mz = Expr::app(mul_zero.clone(), cast_pe1.clone());
                let cast_pe1_mul0 = c.mul(cast_pe1.clone(), c.rat_zero.clone());
                // motive_b : fun t => K ≤ t.
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&lc);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le_rat(kk.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // hk_le_0 : K ≤ 0.
                let hk_le_0 = c.subst_rat(motive_b, cast_pe1_mul0, c.rat_zero.clone(), mz, hk_mul0);
                // Var ≤ I ≤ K ≤ 0.
                let var = c.variance_of(&n, &f);
                let ti = c.total_influence_of(&n, &f);
                let vli = Expr::apps(variance_le_influence.clone(), [n.clone(), f.clone()]); // Var ≤ I
                let var_le_k = c.le_trans_rat(var.clone(), ti, kk.clone(), vli, hi.clone()); // Var ≤ K
                let var_le_0 = c.le_trans_rat(
                    var.clone(),
                    kk.clone(),
                    c.rat_zero.clone(),
                    var_le_k,
                    hk_le_0,
                ); // Var ≤ 0
                   // motive_c : fun t => Var ≤ t. subst (heq0 : 0 = eps) into Var ≤ 0.
                let motive_c = {
                    let mut d = EnvDeclBuilder::child_of(&lc);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le_rat(var.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let var_le_eps =
                    c.subst_rat(motive_c, c.rat_zero.clone(), eps.clone(), heq0, var_le_0);
                Expr::apps(
                    case_empty.clone(),
                    [n.clone(), f.clone(), eps.clone(), big_b.clone(), var_le_eps],
                )
            };

            // pos Or.rec motive: const exists_goal.
            let pos_or_motive = {
                let mut om = EnvDeclBuilder::child_of(&lc);
                let or_ty = c.or(lt_0e.clone(), eq_0e.clone());
                let (hh_id, _hh) = om.fresh_local(or_ty.clone());
                om.finish_child(om.mk_lam(hh_id, BinderInfo::Default, or_ty, exists_goal.clone()))
            };
            // pos LEFT (0 < eps): threshold (we are in eps<1 too via `hlt1`).
            // We need `hlt1 : eps < 1` here; captured below.
            // pos RIGHT (0 = eps): empty_via_zero.
            // These are built inside the (eps<1) inner-left, where `hlt1` is bound.

            // INNER LEFT minor (eps < 1):
            let inner_left = {
                let mut il = EnvDeclBuilder::child_of(&lc);
                let (hlt1_id, hlt1) = il.fresh_local(lt_e1.clone()); // eps < 1

                // pos LEFT (0 < eps) → threshold.
                let pos_left = {
                    let mut pl = EnvDeclBuilder::child_of(&il);
                    let (hpos_id, hpos) = pl.fresh_local(lt_0e.clone()); // 0 < eps
                    let body = Expr::apps(
                        case_threshold.clone(),
                        [
                            n.clone(),
                            f.clone(),
                            kk.clone(),
                            eps.clone(),
                            e.clone(),
                            hi.clone(),
                            hpos,
                            hlt1.clone(),
                            hg.clone(),
                            hn.clone(),
                        ],
                    );
                    pl.finish_child(pl.mk_lam(hpos_id, BinderInfo::Default, lt_0e.clone(), body))
                };
                // pos RIGHT (0 = eps) → empty_via_zero.
                let pos_right = {
                    let mut pr = EnvDeclBuilder::child_of(&il);
                    let (hz_id, hz) = pr.fresh_local(eq_0e.clone());
                    let body = empty_via_zero(&c, hz);
                    pr.finish_child(pr.mk_lam(hz_id, BinderInfo::Default, eq_0e.clone(), body))
                };
                let body = Expr::apps(
                    or_rec.clone(),
                    [
                        lt_0e.clone(),
                        eq_0e.clone(),
                        pos_or_motive.clone(),
                        pos_left,
                        pos_right,
                        pos_or.clone(),
                    ],
                );
                il.finish_child(il.mk_lam(hlt1_id, BinderInfo::Default, lt_e1.clone(), body))
            };

            // INNER RIGHT minor (eps = 1): 1 ≤ eps via subst, then empty_via_one.
            let inner_right = {
                let mut ir = EnvDeclBuilder::child_of(&lc);
                let (heq1_id, heq1) = ir.fresh_local(eq_e1.clone()); // eps = 1
                                                                     // h1 : 1 ≤ eps  := subst (motive t => 1 ≤ t) (a:=1) (b:=eps)
                                                                     //   needs `eps = 1` flipped to `1 = eps`? motive over the var slot:
                                                                     //   Rat.le_refl 1 : 1 ≤ 1; subst (symm heq1 : 1 = eps) into (t => 1 ≤ t).
                let refl1 = Expr::apps(
                    Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
                    [c.rat_one.clone()],
                ); // 1 ≤ 1
                let one_eq_eps = c.symm_rat(eps.clone(), c.rat_one.clone(), heq1); // 1 = eps
                let motive_1le = {
                    let mut d = EnvDeclBuilder::child_of(&ir);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le_rat(c.rat_one.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h1 = c.subst_rat(
                    motive_1le,
                    c.rat_one.clone(),
                    eps.clone(),
                    one_eq_eps,
                    refl1,
                );
                let body = empty_via_one(&c, h1);
                ir.finish_child(ir.mk_lam(heq1_id, BinderInfo::Default, eq_e1.clone(), body))
            };

            let body = Expr::apps(
                or_rec.clone(),
                [
                    lt_e1.clone(),
                    eq_e1.clone(),
                    inner_or_motive,
                    inner_left,
                    inner_right,
                    inner,
                ],
            );
            lc.finish_child(lc.mk_lam(hle_id, BinderInfo::Default, p_le.clone(), body))
        };

        let body = Expr::apps(
            or_rec.clone(),
            [
                p_le.clone(),
                q_le.clone(),
                outer_or_motive,
                outer_left,
                outer_right,
                le_total_eps1,
            ],
        );
        m.finish_child(m.mk_lam(heqf_id, BinderInfo::Default, disc_f, body))
    };

    // Bool.rec.{0} motive minor_false minor_true (Nat.ble n B) applied to refl.
    //   Bool.rec order: motive, (false case), (true case), major.
    let outer_rec = Expr::apps(
        bool_rec.clone(),
        [outer_motive, minor_false, minor_true, ble_nb.clone()],
    );
    // Seed the discriminant equation with `Eq.refl Bool (Nat.ble n B)`.
    let seeded = Expr::app(outer_rec, c.refl_bool(ble_nb.clone()));

    let e = b.mk_lam(hg_id, BinderInfo::Default, guard_ty, seeded);
    let e = b.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, e);
    let e = b.mk_lam(hi_id, BinderInfo::Default, hi_ty, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register every dependency the final `friedgut_boolean` proof consumes: the
    /// three case bricks (`case_le` / `case_empty` / `case_threshold`), the two
    /// variance bounds, and the `Rat`/`Nat` order glue. Used by the co-land
    /// (`register_friedgut_boolean_helper` → Definition, `register_friedgut_boolean`
    /// → Theorem). Idempotent; no axiom added or removed.
    #[cfg(test)]
    pub(crate) fn register_friedgut_boolean_assembly_deps(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?; // LE.le / instLERat
        self.init_bool()?;
        self.init_nat_totality_proofs()?; // constructive Nat.not_le Theorem
        self.init_nat_not_lt_le()?; // Nat.not_le (Theorem form preferred)
        self.register_nat_ble_le_lemmas()?; // Nat.le_of_ble_eq_true, Nat.not_le_of_ble_eq_false
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_lt_or_eq_of_le()?; // Rat.lt_or_eq_of_le
        self.register_rat_order_proofs()?; // Rat.le_total, Rat.le_refl
        self.init_rat_field_inst()?; // Rat.mul_zero (via the field instance carriers)
                                     // The three landed case bricks.
        self.register_friedgut_boolean_case_le()?;
        self.register_friedgut_boolean_case_empty()?;
        self.register_friedgut_boolean_case_threshold()?;
        // The two variance bounds.
        self.register_variance_le_one()?;
        self.register_variance_le_influence()?;
        Ok(())
    }

    /// Build the assembled `friedgut_boolean` proof term (4-case). The returned
    /// `Expr` has the v3 helper body type (def-eq to `helper n f K eps`).
    #[cfg(test)]
    pub(crate) fn friedgut_boolean_assembled_proof(&self) -> Expr {
        build_friedgut_boolean_assembly(true)
    }

    /// The structural type of the assembled proof (the v3 helper body, re-spelled).
    #[cfg(test)]
    pub(crate) fn friedgut_boolean_assembled_type(&self) -> Expr {
        build_friedgut_boolean_assembly(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|err| panic!("{name} must kernel-check: {err:?}"));
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
                .map(|dp| dp.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_friedgut_empty_junta_mass_eq_variance_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_empty_junta_mass_eq_variance()
            .expect("register_friedgut_empty_junta_mass_eq_variance");
        env.register_friedgut_empty_junta_mass_eq_variance()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_empty_junta_mass_eq_variance");
    }

    #[test]
    fn test_friedgut_boolean_case_empty_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_boolean_case_empty()
            .expect("register_friedgut_boolean_case_empty");
        env.register_friedgut_boolean_case_empty()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_boolean_case_empty");
    }

    /// The assembled 4-case `friedgut_boolean` proof term kernel-CHECKS against its
    /// structural (v3-helper-body) type, with an empty admitted-axiom closure. This
    /// is the standalone gate for the co-land: if this fails the proof is wrong and
    /// the body must NOT be installed.
    #[test]
    fn test_friedgut_boolean_assembly_kernel_checks() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_boolean_assembly_deps()
            .expect("assembly deps");
        let value = env.friedgut_boolean_assembled_proof();
        let type_ = env.friedgut_boolean_assembled_type();
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &type_)
            .unwrap_or_else(|err| panic!("friedgut_boolean assembly must kernel-check: {err:?}"));
    }
}
