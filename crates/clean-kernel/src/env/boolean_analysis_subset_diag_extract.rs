// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Subset-cube delta-extraction — "sum against a Kronecker δ picks the term".
//!
//! The noise-semigroup collapse needs the general-pivot point-mass extraction:
//! summing `f(T)` weighted by the empty-symm-diff indicator `[S = T]` over all
//! `2^n` subsets `T` recovers `f(S)`. With the pivot carried as a `Fin (2^n)`
//! index `jS` (so `S = hcDecode n jS`, mirroring `subsetSum_inversion_core` and
//! sidestepping a `hcEncode` surjectivity):
//!
//! ```text
//! BoolAnalysis.subsetSum_subset_diag_extract :
//!   ∀ (n : Nat) (jS : Fin (Nat.pow 2 n)) (f : HCPoint n → Rat),
//!     subsetSum n (fun T =>
//!       Rat.mul (f T)
//!               (ind (Nat.beq (setSizeNat n
//!                       (fun i => Bool.xor (hcDecode n jS i) (T i))) 0)))
//!       = f (hcDecode n jS)
//! ```
//!
//! ## Proof (mirrors `emptyset_mass_isolation`, at a general pivot)
//!
//! `subsetSum n G ≡ Fin.sum (2^n) (fun j => G (hcDecode n j))` (reducible), so
//! `Fin.sum_diag_collapse` at the pivot index `jS` folds the sum to `F jS`. The
//! off-diagonal hypothesis — for `jT ≠ jS`, the masked term vanishes —
//! case-splits the indicator bit `Nat.beq (setSizeNat n (S Δ hcDecode jT)) 0`:
//! - `false`: `f · ind false ≡ f · 0 = 0` (`Rat.mul_zero`);
//! - `true`: `Nat.eq_of_beq_eq_true` gives `setSizeNat n (S Δ hcDecode jT) = 0`,
//!   so `setSizeNat_symmDiff_hcDecode_imp_val_eq` forces `val jS = val jT`, hence
//!   `jS = jT` (`Fin.eq_of_val_eq`); `Eq.symm` to `jT = jS` contradicts `jT ≠ jS`
//!   (`False.elim`).
//!
//! The diagonal value `F jS = f S · ind (Nat.beq (setSizeNat n (S Δ S)) 0)`. The
//! self-symm-diff is empty: `xor (S i)(S i) ≡ false`, so each `indNat` is `0` and
//! `setSizeNat n (S Δ S) = 0` (`Fin.sumNat_const_zero_of`); hence the indicator
//! is `ind (Nat.beq 0 0) ≡ ind true ≡ 1`, and `f S · 1 = f S` (`Rat.mul_one`).
//!
//! Every cited brick is constructive with an empty admitted-axiom closure, so
//! this is `ProofQuality::Constructive`, empty closure. No axiom added/removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `BoolAnalysis.subsetSum_subset_diag_extract` — see module docs.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub(crate) fn register_subset_sum_subset_diag_extract(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_subset_diag_extract");
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
        self.init_bool()?; // Bool.xor
        self.init_rat()?; // Rat.mul, Rat.zero, Rat.mul_zero, Rat.one, Rat.mul_one
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_fin_sum_diag_collapse_theorem()?;
        self.register_setsizenat_symmdiff_hcdecode_imp_val_eq()?;
        self.register_fin_sum_nat_const_zero_of()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_nat_eq_of_beq_eq_true()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let (ty, value) = build_diag_extract();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `BoolAnalysis.subsetSum_subset_diag_extract_scaled` — the
    /// `2^n`-scaled delta-extraction the noise semigroup consumes:
    ///
    /// ```text
    /// ∀ (n : Nat) (jS : Fin (Nat.pow 2 n)) (f : HCPoint n → Rat),
    ///   subsetSum n (fun T =>
    ///     Rat.mul (f T)
    ///             (Rat.mul (cube n)
    ///                      (ind (Nat.beq (setSizeNat n
    ///                              (fun i => Bool.xor (hcDecode n jS i) (T i))) 0))))
    ///     = Rat.mul (cube n) (f (hcDecode n jS))
    /// ```
    ///
    /// with `cube n := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1` (the keystone's `2^n`).
    /// I.e. `Σ_T f(T)·(2^n·[S = T]) = 2^n·f(S)`. Derived from the unscaled
    /// extraction by (i) regrouping the integrand `f(T)·(2^n·ind) = 2^n·(f(T)·ind)`
    /// per `T` (`subsetSum_congr` over a `Rat.mul_assoc`/`Rat.mul_comm` leaf),
    /// (ii) `subsetSum_smul` to pull `2^n` out, then (iii) `subsetSum_subset_diag_extract`
    /// lifted by `congrArg (2^n · ·)`. Kernel-checked, `Constructive`, empty
    /// closure. Idempotent.
    pub(crate) fn register_subset_sum_subset_diag_extract_scaled(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_subset_diag_extract_scaled");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_set_size_nat()?;
        self.register_subset_sum_subset_diag_extract()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_comm, Rat.mul_assoc
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let (ty, value) = build_diag_extract_scaled();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

fn build_diag_extract_scaled() -> (Expr, Expr) {
    let l1 = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let _bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
    let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
    let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
    let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
    let subset_sum_congr = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
    let subset_sum_smul = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]);
    let diag_extract = Expr::const_(
        Name::from_string("BoolAnalysis.subsetSum_subset_diag_extract"),
        vec![],
    );
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
    let mul_assoc = Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]);
    let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
    let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
    let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
    let hcp_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
    let hcp_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcp_of(n), rat.clone());
    let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
    let ind_of = |b: Expr| Expr::app(ind.clone(), b);
    let beq0 = |m: Expr| Expr::apps(nat_beq.clone(), [m, nat_zero.clone()]);
    let ss_nat = |n: &Expr, s: Expr| Expr::apps(set_size_nat.clone(), [n.clone(), s]);
    let decode = |n: &Expr, j: Expr| Expr::apps(hc_decode.clone(), [n.clone(), j]);
    let xor = |a: Expr, b: Expr| Expr::apps(bool_xor.clone(), [a, b]);
    // cube n := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1  (the keystone's 2^n)
    let cube = |n: &Expr| {
        let ofnat = Expr::app(int_of_nat.clone(), pow2(n));
        Expr::apps(rat_mk.clone(), [ofnat, one_nat.clone()])
    };
    let eq_rat = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [rat.clone(), a, b],
        )
    };
    // S Δ T integrand at pivot point s and subset t: fun i => xor (s i)(t i)
    let sd_point = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = d.fresh_local(fin_of(n));
        let body = xor(Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(n), body))
    };
    let bit_of = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr| -> Expr {
        ind_of(beq0(ss_nat(n, sd_point(parent, n, s, t))))
    };
    // scaled integrand: fun T => f T · (cube · ind(bit S T))
    let scaled_fn = |parent: &EnvDeclBuilder, n: &Expr, js: &Expr, f: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let s = decode(n, js.clone());
        let (t_id, t) = d.fresh_local(hcp_of(n));
        let indbit = bit_of(&d, n, &s, &t);
        let body = mul(Expr::app(f.clone(), t.clone()), mul(cube(n), indbit));
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, hcp_of(n), body))
    };
    // pulled integrand: fun T => cube · (f T · ind(bit S T))   (subsetSum_smul's scaled form)
    let pulled_fn = |parent: &EnvDeclBuilder, n: &Expr, js: &Expr, f: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let s = decode(n, js.clone());
        let (t_id, t) = d.fresh_local(hcp_of(n));
        let indbit = bit_of(&d, n, &s, &t);
        let body = mul(cube(n), mul(Expr::app(f.clone(), t.clone()), indbit));
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, hcp_of(n), body))
    };
    // unscaled integrand (the extraction's): fun T => f T · ind(bit S T)
    let unscaled_fn = |parent: &EnvDeclBuilder, n: &Expr, js: &Expr, f: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let s = decode(n, js.clone());
        let (t_id, t) = d.fresh_local(hcp_of(n));
        let indbit = bit_of(&d, n, &s, &t);
        let body = mul(Expr::app(f.clone(), t.clone()), indbit);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, hcp_of(n), body))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (js_id, js) = b.fresh_local(fin_of(&pow2(&n)));
        let (f_id, f) = b.fresh_local(hcp_to_rat(&n));
        let lhs = Expr::apps(subset_sum.clone(), [n.clone(), scaled_fn(&b, &n, &js, &f)]);
        let rhs = mul(cube(&n), Expr::app(f.clone(), decode(&n, js.clone())));
        let concl = eq_rat(lhs, rhs);
        let e = b.mk_pi(f_id, BinderInfo::Default, hcp_to_rat(&n), concl);
        let e = b.mk_pi(js_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (js_id, js) = b.fresh_local(fin_of(&pow2(&n)));
        let (f_id, f) = b.fresh_local(hcp_to_rat(&n));
        let s = decode(&n, js.clone());

        // ── leg1 : Σ_T f(T)·(cube·ind) = Σ_T cube·(f(T)·ind)   (subsetSum_congr) ──
        // per-T leaf: f(T)·(cube·ind) = cube·(f(T)·ind)
        //   = symm(assoc f(T) cube ind) : f(T)·(cube·ind) = (f(T)·cube)·ind  [reversed]
        //     actually assoc a b c : (a·b)·c = a·(b·c); we want the reverse for step.
        //   chain: f·(cube·ind)
        //     →[symm (assoc f cube ind)]    (f·cube)·ind
        //     →[congr (·ind) (comm f cube)] (cube·f)·ind
        //     →[assoc cube f ind]           cube·(f·ind)
        let leaf_hyp = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(hcp_of(&n));
            let ft = Expr::app(f.clone(), t.clone());
            let cu = cube(&n);
            let indbit = bit_of(&d, &n, &s, &t);

            let l0 = mul(ft.clone(), mul(cu.clone(), indbit.clone())); // f·(cube·ind)
            let m1 = mul(mul(ft.clone(), cu.clone()), indbit.clone()); // (f·cube)·ind
            let m2 = mul(mul(cu.clone(), ft.clone()), indbit.clone()); // (cube·f)·ind
            let r0 = mul(cu.clone(), mul(ft.clone(), indbit.clone())); // cube·(f·ind)

            // s1 : l0 = m1  via Eq.symm (assoc f cube ind)   (assoc : (f·cube)·ind = f·(cube·ind))
            let assoc1 = Expr::apps(mul_assoc.clone(), [ft.clone(), cu.clone(), indbit.clone()]);
            let s1 = Expr::apps(
                eq_symm.clone(),
                [rat.clone(), m1.clone(), l0.clone(), assoc1],
            );
            // s2 : m1 = m2  via congr (fun z => z·ind) (comm f cube)
            let g_ind = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (z_id, z) = g.fresh_local(rat.clone());
                let body = mul(z, indbit.clone());
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, rat.clone(), body))
            };
            let comm_fc = Expr::apps(mul_comm.clone(), [ft.clone(), cu.clone()]);
            let s2 = Expr::apps(
                congr_arg.clone(),
                [
                    rat.clone(),
                    rat.clone(),
                    mul(ft.clone(), cu.clone()),
                    mul(cu.clone(), ft.clone()),
                    g_ind,
                    comm_fc,
                ],
            );
            // s3 : m2 = r0  via assoc cube f ind : (cube·f)·ind = cube·(f·ind)
            let s3 = Expr::apps(mul_assoc.clone(), [cu.clone(), ft.clone(), indbit.clone()]);
            // chain l0 = m1 = m2 = r0
            let t12 = Expr::apps(
                eq_trans.clone(),
                [rat.clone(), l0.clone(), m1.clone(), m2.clone(), s1, s2],
            );
            let body = Expr::apps(
                eq_trans.clone(),
                [rat.clone(), l0.clone(), m2.clone(), r0.clone(), t12, s3],
            );
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, hcp_of(&n), body))
        };
        let leg1 = Expr::apps(
            subset_sum_congr.clone(),
            [
                n.clone(),
                scaled_fn(&b, &n, &js, &f),
                pulled_fn(&b, &n, &js, &f),
                leaf_hyp,
            ],
        );

        // ── leg2 : Σ_T cube·(f(T)·ind) = cube·Σ_T (f(T)·ind)   (subsetSum_smul) ──
        let leg2 = Expr::apps(
            subset_sum_smul.clone(),
            [n.clone(), cube(&n), unscaled_fn(&b, &n, &js, &f)],
        );

        // ── leg3 : cube·Σ_T (f(T)·ind) = cube·(f S)  via congrArg (cube·) (extract) ──
        // extract : Σ_T (f(T)·ind) = f S  (subsetSum_subset_diag_extract n jS f)
        let extract = Expr::apps(diag_extract.clone(), [n.clone(), js.clone(), f.clone()]);
        let f_s = Expr::app(f.clone(), s.clone());
        let g_cube = {
            let mut g = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = g.fresh_local(rat.clone());
            let body = mul(cube(&n), z);
            g.finish_child(g.mk_lam(z_id, BinderInfo::Default, rat.clone(), body))
        };
        let inner_sum = Expr::apps(
            subset_sum.clone(),
            [n.clone(), unscaled_fn(&b, &n, &js, &f)],
        );
        let leg3 = Expr::apps(
            congr_arg.clone(),
            [
                rat.clone(),
                rat.clone(),
                inner_sum.clone(),
                f_s.clone(),
                g_cube,
                extract,
            ],
        );

        // chain: lhs(scaled) = pulled-sum = cube·inner_sum = cube·(f S)
        let lhs = Expr::apps(subset_sum.clone(), [n.clone(), scaled_fn(&b, &n, &js, &f)]);
        let pulled_sum = Expr::apps(subset_sum.clone(), [n.clone(), pulled_fn(&b, &n, &js, &f)]);
        let cube_inner = mul(cube(&n), inner_sum);
        let target = mul(cube(&n), f_s);
        let t12 = Expr::apps(
            eq_trans.clone(),
            [
                rat.clone(),
                lhs.clone(),
                pulled_sum.clone(),
                cube_inner.clone(),
                leg1,
                leg2,
            ],
        );
        let body = Expr::apps(
            eq_trans.clone(),
            [rat.clone(), lhs, cube_inner, target, t12, leg3],
        );

        let e = b.mk_lam(f_id, BinderInfo::Default, hcp_to_rat(&n), body);
        let e = b.mk_lam(js_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

fn build_diag_extract() -> (Expr, Expr) {
    let l0 = Level::zero();
    let l1 = Level::succ(l0.clone());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
    let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
    let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
    let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
    let fin_sum_nat = Expr::const_(Name::from_string("Fin.sumNat"), vec![]);
    let diag_collapse = Expr::const_(Name::from_string("Fin.sum_diag_collapse"), vec![]);
    let const_zero_of = Expr::const_(Name::from_string("Fin.sumNat_const_zero_of"), vec![]);
    let symm_imp_val_eq = Expr::const_(
        Name::from_string("BoolAnalysis.setSizeNat_symmDiff_hcDecode_imp_val_eq"),
        vec![],
    );
    let fin_eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);
    let eq_of_beq = Expr::const_(Name::from_string("Nat.eq_of_beq_eq_true"), vec![]);
    let bool_cases_on = Expr::const_(Name::from_string("Bool.casesOn"), vec![l0.clone()]);
    let bool_rec_nat = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
    let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
    let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
    let mul_zero = Expr::const_(Name::from_string("Rat.mul_zero"), vec![]);
    let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
    let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
    let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
    let hcp_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
    let hcp_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcp_of(n), rat.clone());
    let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
    let ind_of = |b: Expr| Expr::app(ind.clone(), b);
    let beq0 = |m: Expr| Expr::apps(nat_beq.clone(), [m, nat_zero.clone()]);
    let ss_nat = |n: &Expr, s: Expr| Expr::apps(set_size_nat.clone(), [n.clone(), s]);
    let decode = |n: &Expr, j: Expr| Expr::apps(hc_decode.clone(), [n.clone(), j]);
    let _decode_at = |n: &Expr, k: &Expr, i: Expr| Expr::app(decode(n, k.clone()), i);
    let val_at = |n: &Expr, k: &Expr| Expr::apps(fin_val.clone(), [n.clone(), k.clone()]);
    let xor = |a: Expr, b: Expr| Expr::apps(bool_xor.clone(), [a, b]);
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
    // indNat b = @Bool.rec (fun _ => Nat) 0 1 b
    let nat_motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
    let ind_nat = |b: Expr| {
        Expr::apps(
            bool_rec_nat.clone(),
            [nat_motive.clone(), nat_zero.clone(), one_nat.clone(), b],
        )
    };
    // S Δ T integrand for a fixed pivot point `s` (an HCPoint) and a subset `t`:
    //   fun i => Bool.xor (s i) (t i)
    let sd_point = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = d.fresh_local(fin_of(n));
        let body = xor(Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(n), body))
    };
    // bit at (S, T): Nat.beq (setSizeNat n (S Δ T)) 0
    let bit_of = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr| -> Expr {
        beq0(ss_nat(n, sd_point(parent, n, s, t)))
    };
    // masked integrand G : fun (T : HCPoint n) => f T · ind (bit (S, T))
    //   with S = hcDecode n jS.
    let g_fn = |parent: &EnvDeclBuilder, n: &Expr, js: &Expr, f: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let s = decode(n, js.clone());
        let (t_id, t) = d.fresh_local(hcp_of(n));
        let bit = bit_of(&d, n, &s, &t);
        let body = mul(Expr::app(f.clone(), t.clone()), ind_of(bit));
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, hcp_of(n), body))
    };
    // F : Fin (2^n) → Rat := fun jT => G (hcDecode n jT)
    let f_fn = |parent: &EnvDeclBuilder, n: &Expr, js: &Expr, f: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let s = decode(n, js.clone());
        let (jt_id, jt) = d.fresh_local(fin_of(&pow2(n)));
        let t = decode(n, jt.clone());
        let bit = bit_of(&d, n, &s, &t);
        let body = mul(Expr::app(f.clone(), t.clone()), ind_of(bit));
        d.finish_child(d.mk_lam(jt_id, BinderInfo::Default, fin_of(&pow2(n)), body))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (js_id, js) = b.fresh_local(fin_of(&pow2(&n)));
        let (f_id, f) = b.fresh_local(hcp_to_rat(&n));
        let lhs = Expr::apps(subset_sum.clone(), [n.clone(), g_fn(&b, &n, &js, &f)]);
        let rhs = Expr::app(f.clone(), decode(&n, js.clone()));
        let concl = eq_rat(lhs, rhs);
        let e = b.mk_pi(f_id, BinderInfo::Default, hcp_to_rat(&n), concl);
        let e = b.mk_pi(js_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (js_id, js) = b.fresh_local(fin_of(&pow2(&n)));
        let (f_id, f) = b.fresh_local(hcp_to_rat(&n));
        let s = decode(&n, js.clone()); // pivot point S = hcDecode n jS
        let f_lam = f_fn(&b, &n, &js, &f);

        // ── off-diagonal hypothesis ──
        //   fun (jT : Fin (2^n)) (hne : Eq (Fin (2^n)) jT jS → False) => F jT = 0
        let off_diag = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jt_id, jt) = d.fresh_local(fin_of(&pow2(&n)));
            let ne_ty = Expr::pi(
                BinderInfo::Default,
                eq_fin(&pow2(&n), jt.clone(), js.clone()),
                false_const.clone(),
            );
            let (hne_id, hne) = d.fresh_local(ne_ty.clone());

            let t = decode(&n, jt.clone());
            let beq_expr = bit_of(&d, &n, &s, &t);
            let f_t = Expr::app(f.clone(), t.clone());
            // goal : f T · ind beq_expr = 0
            let goal = eq_rat(mul(f_t.clone(), ind_of(beq_expr.clone())), rat_zero.clone());

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

            // false_branch : beq_expr = false → goal
            //   := fun hf => Eq.trans (congrArg (fun bb => f T · ind bb) hf)
            //                         (Rat.mul_zero (f T))
            //   (ind false ≡ 0; f T · 0 = 0 by Rat.mul_zero.)
            let false_branch = {
                let mut m = EnvDeclBuilder::child_of(&d);
                let prem = eq_bool(beq_expr.clone(), bool_false.clone());
                let (hf_id, hf) = m.fresh_local(prem.clone());
                // g_ind : fun (bb : Bool) => f T · ind bb
                let g_ind = {
                    let mut g = EnvDeclBuilder::child_of(&m);
                    let (bb_id, bb) = g.fresh_local(bool_.clone());
                    let body = mul(f_t.clone(), ind_of(bb));
                    g.finish_child(g.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), body))
                };
                // h1 : f T · ind beq_expr = f T · ind false
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
                // h2 : f T · 0 = 0   (ind false ≡ 0; Rat.mul_zero)
                let h2 = Expr::app(mul_zero.clone(), f_t.clone());
                let mid = mul(f_t.clone(), ind_of(bool_false.clone()));
                let body = Expr::apps(
                    eq_trans.clone(),
                    [
                        rat.clone(),
                        mul(f_t.clone(), ind_of(beq_expr.clone())),
                        mid,
                        rat_zero.clone(),
                        h1,
                        h2,
                    ],
                );
                let _ = zero_mul; // unused here (mul_zero variant)
                m.finish_child(m.mk_lam(hf_id, BinderInfo::Default, prem, body))
            };

            // true_branch : beq_expr = true → goal
            //   hsz : setSizeNat n (S Δ T) = 0 := Nat.eq_of_beq_eq_true (…) 0 ht
            //   hval : val jS = val jT := setSizeNat_symmDiff_hcDecode_imp_val_eq n jS jT hsz
            //   hjs_jt : jS = jT := Fin.eq_of_val_eq (2^n) jS jT hval
            //   hjt_js : jT = jS := Eq.symm hjs_jt
            //   False.elim goal (hne hjt_js)
            let true_branch = {
                let mut m = EnvDeclBuilder::child_of(&d);
                let prem = eq_bool(beq_expr.clone(), bool_true.clone());
                let (ht_id, ht) = m.fresh_local(prem.clone());
                let sd = sd_point(&m, &n, &s, &t);
                let hsz = Expr::apps(eq_of_beq.clone(), [ss_nat(&n, sd), nat_zero.clone(), ht]);
                // hval : Eq Nat (val jS) (val jT)
                let hval = Expr::apps(
                    symm_imp_val_eq.clone(),
                    [n.clone(), js.clone(), jt.clone(), hsz],
                );
                // hjs_jt : jS = jT  (Fin.eq_of_val_eq (2^n) jS jT hval; val jS, val jT match)
                let hjs_jt = Expr::apps(
                    fin_eq_of_val.clone(),
                    [pow2(&n), js.clone(), jt.clone(), hval],
                );
                // hjt_js : jT = jS := Eq.symm (Fin (2^n)) jS jT hjs_jt
                let hjt_js = Expr::apps(
                    eq_symm.clone(),
                    [fin_of(&pow2(&n)), js.clone(), jt.clone(), hjs_jt],
                );
                let contra = Expr::app(hne.clone(), hjt_js);
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
            d.finish_child(d.mk_lam(jt_id, BinderInfo::Default, fin_of(&pow2(&n)), r))
        };

        // collapse : Fin.sum (2^n) F = F jS  := Fin.sum_diag_collapse (2^n) jS F off_diag
        let collapse = Expr::apps(
            diag_collapse.clone(),
            [pow2(&n), js.clone(), f_lam.clone(), off_diag],
        );

        // ── diagonal bridge: F jS = f S ──
        // F jS = f S · ind (Nat.beq (setSizeNat n (S Δ S)) 0).
        // hsz0 : setSizeNat n (S Δ S) = 0 via Fin.sumNat_const_zero_of:
        //   summand i = indNat (xor (S i)(S i)); pw i : indNat (xor (S i)(S i)) = 0
        //   (Bool.casesOn (S i): xor false false ≡ false, xor true true ≡ not true ≡
        //    false, so indNat ≡ 0 either way — Eq.refl).
        let sd_self = sd_point(&b, &n, &s, &s); // fun i => xor (S i)(S i)
                                                // summand : fun (i : Fin n) => indNat ((S Δ S) i)
        let summand = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(fin_of(&n));
            let body = ind_nat(xor(
                Expr::app(s.clone(), i.clone()),
                Expr::app(s.clone(), i.clone()),
            ));
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
        };
        // pw : ∀ i, indNat (xor (S i)(S i)) = 0
        let pw = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(fin_of(&n));
            let s_i = Expr::app(s.clone(), i.clone());
            // target : indNat (xor (S i)(S i)) = 0
            let target = eq_nat(ind_nat(xor(s_i.clone(), s_i.clone())), nat_zero.clone());
            // motive : fun (bv : Bool) => indNat (xor bv bv) = 0
            let cmotive = {
                let mut m = EnvDeclBuilder::child_of(&d);
                let (bv_id, bv) = m.fresh_local(bool_.clone());
                let body = eq_nat(ind_nat(xor(bv.clone(), bv.clone())), nat_zero.clone());
                m.finish_child(m.mk_lam(bv_id, BinderInfo::Default, bool_.clone(), body))
            };
            // false_minor : indNat (xor false false) = 0  := Eq.refl Nat 0
            let false_minor = Expr::apps(eq_refl.clone(), [nat.clone(), nat_zero.clone()]);
            // true_minor : indNat (xor true true) = 0  := Eq.refl Nat 0
            let true_minor = Expr::apps(eq_refl.clone(), [nat.clone(), nat_zero.clone()]);
            // @Bool.casesOn cmotive (S i) false_minor true_minor : motive (S i)
            //   = (indNat (xor (S i)(S i)) = 0) = target (def-eq).
            let body = Expr::apps(
                bool_cases_on.clone(),
                [cmotive, s_i, false_minor, true_minor],
            );
            let _ = target;
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
        };
        // hsz0 : Fin.sumNat n summand = 0  := Fin.sumNat_const_zero_of n summand pw
        //   (setSizeNat n (S Δ S) ≡ Fin.sumNat n summand, reducible)
        let hsz0 = Expr::apps(const_zero_of.clone(), [n.clone(), summand.clone(), pw]);
        let _ = (fin_sum_nat, val_at, &js_id); // keep names for clarity / silence

        // hbit0 : Nat.beq (setSizeNat n (S Δ S)) 0 = true
        //   := congrArg (fun m => Nat.beq m 0) hsz0   (Nat.beq 0 0 ≡ true)
        let beq_self = beq0(ss_nat(&n, sd_self.clone()));
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
                ss_nat(&n, sd_self.clone()),
                nat_zero.clone(),
                beq_fn,
                hsz0,
            ],
        );
        // f S · ind beq_self = f S · ind true  via congrArg (fun bb => f S · ind bb) hbit0
        let f_s = Expr::app(f.clone(), s.clone());
        let g_ind_self = {
            let mut g = EnvDeclBuilder::child_of(&b);
            let (bb_id, bb) = g.fresh_local(bool_.clone());
            let body = mul(f_s.clone(), ind_of(bb));
            g.finish_child(g.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), body))
        };
        let h_bit = Expr::apps(
            congr_arg.clone(),
            [
                bool_.clone(),
                rat.clone(),
                beq_self.clone(),
                bool_true.clone(),
                g_ind_self,
                hbit0,
            ],
        );
        // f S · ind true = f S  (ind true ≡ 1; Rat.mul_one)
        let h_one = Expr::app(mul_one.clone(), f_s.clone());
        // F jS = f S · ind beq_self (def-eq); chain to f S.
        let f_js = mul(f_s.clone(), ind_of(beq_self.clone()));
        let mid_true = mul(f_s.clone(), ind_of(bool_true.clone()));
        let bridge = Expr::apps(
            eq_trans.clone(),
            [
                rat.clone(),
                f_js.clone(),
                mid_true,
                f_s.clone(),
                h_bit,
                h_one,
            ],
        );

        // final : Fin.sum (2^n) F = f S
        //   = Eq.trans (collapse : sum = F jS) (bridge : F jS = f S)
        let sum_f = Expr::apps(fin_sum.clone(), [pow2(&n), f_lam.clone()]);
        let body = Expr::apps(
            eq_trans.clone(),
            [rat.clone(), sum_f, f_js, f_s, collapse, bridge],
        );

        let e = b.mk_lam(f_id, BinderInfo::Default, hcp_to_rat(&n), body);
        let e = b.mk_lam(js_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_subset_diag_extract_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_subset_diag_extract()
            .expect("register_subset_sum_subset_diag_extract");
        env.register_subset_sum_subset_diag_extract()
            .expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.subsetSum_subset_diag_extract");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_subset_diag_extract proof must check against its type");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_subset_sum_subset_diag_extract_scaled_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_subset_diag_extract_scaled()
            .expect("register_subset_sum_subset_diag_extract_scaled");
        env.register_subset_sum_subset_diag_extract_scaled()
            .expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.subsetSum_subset_diag_extract_scaled");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("scaled extraction proof must check against its type");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
