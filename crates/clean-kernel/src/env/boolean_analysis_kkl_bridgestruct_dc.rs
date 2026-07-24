// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL STRUCTURAL bridge — the spectral DOUBLE-COUNT bound (axiom-free).
//!
//! # The double-count half of the §9.6 bridge
//!
//! The genuine O'Donnell §9.6 per-coordinate bridge upper-bounds the low-degree
//! Fourier mass `M_{1..k}` by the influence-`^{3/2}` sum. Its first, PURELY
//! COMBINATORIAL half — entirely independent of the (separately in-flight)
//! per-coordinate dual hypercontractive bound `‖T_{1/3}D_i f‖₂² ≤ 4·Inf^{3/2}` —
//! is the spectral DOUBLE-COUNT:
//!
//! ```text
//!   M_{1..k}  =  Σ_{1≤|S|≤k}            f̂(S)²
//!             ≤  Σ_{1≤|S|≤k}  |S| ·     f̂(S)²   =  Σ_i W^{≤k}[D_i f].
//! ```
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.lowband_double_count_le :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.le
//!       (subsetSum n (fun S =>
//!           ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                         (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!               · (f̂ S · f̂ S)))                                              -- M_{1..k}
//!       (subsetSum n (fun S =>
//!           ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                         (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!               · (setSize n S · (f̂ S · f̂ S))))                              -- Σ_i W^{≤k}[D_i f]
//! ```
//!
//! i.e. `M_{1..k} ≤ Σ_{1≤|S|≤k} |S|·f̂(S)²`. The LHS band integrand
//! `ind(band)·(f̂·f̂)` is BYTE-IDENTICAL to the landed `variance_high_mass_complement`
//! / `variance_low_band_influence` `M_{1..k}` integrand (`m_lo_fn`). The RHS is the
//! SAME band, degree-weighted by `setSize n S` — the band-restricted analog of the
//! landed unbanded `total_influence_spectral` RHS `Σ_S |S|·f̂(S)²`; by the
//! double-count `subsetSum_double_count`, summing the per-coordinate derivative
//! low-bands `W^{≤k}[D_i f] = Σ_{|S|≤k,i∈S} f̂(S)²` over `i` lands exactly the
//! degree-weight `Σ_{|S|≤k}|S|·f̂(S)²`, so the RHS IS `Σ_i W^{≤k}[D_i f]` on the band.
//!
//! ## Why it is TRUE and refute-safe
//!
//! On the non-empty band (`band = true`), the `Nat.ble 1 |S|` conjunct fires, so
//! `1 ≤ |S|` (Nat), hence `1 ≤ setSize n S` (`Rat`, via `setSize_eq_natCast` +
//! `Nat.cast_le_of_ble`), and since `f̂(S)² ≥ 0`, `f̂(S)² ≤ |S|·f̂(S)²` TERMWISE.
//! Off the band (`band = false`), both integrands are `0·… = 0`. The per-`S` step
//! is the landed `lowband_dc_term`; `subsetSum_le_of_pointwise` lifts it to the
//! cube sum. It asserts NO hypercontractive inequality — a sound, unconditional
//! `≤ 1` ⟹ degree-weight domination. Refute-checked against the dictator / parity /
//! constant battery (on the dictator `χ_i`, `M_{1..k} = Σ_i W^{≤k} = 1` for `k ≥ 1`;
//! on parity at `|S| > k` both sides vanish; neither refutes).
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! `subsetSum_le_of_pointwise n m_lo_fn m_lo_weighted_fn per_s`, where
//! `per_s S := lowband_dc_term (band S) (setSize n S) (f̂ S · f̂ S) h_w h_sz` with
//! - `h_w := Rat.sq_nonneg (f̂ S) : 0 ≤ f̂ S · f̂ S`;
//! - `h_sz : band S = true → 1 ≤ setSize n S` :=
//!   `fun h => Eq.subst (motive t => natCast 1 ≤ t)
//!                      (symm (setSize_eq_natCast n S))
//!                      (Nat.cast_le_of_ble 1 (setSizeNat n S)
//!                         (Bool.and_left_eq_true (ble 1 |S|) (not (ble (k+1) |S|)) h))`
//!   (`natCast 1 ≡ Rat.one`, so the result is the atom's expected `Rat.one ≤ …`).
//!
//! Every leaf (`subsetSum_le_of_pointwise`, `lowband_dc_term`, `Rat.sq_nonneg`,
//! `Nat.cast_le_of_ble`, `setSize_eq_natCast`, `Bool.and_left_eq_true`, Eq
//! built-ins) is `Constructive` with empty closure, so this rung is too. No axiom
//! is added or removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the structural double-count bound. Spellings are
/// byte-identical to the on-branch `MassSplitConsts` / `LowBandConsts` /
/// `DyadicConsts` carriers so all terms stay def-eq to the bands and casts.
struct DcConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    ind: Expr,
    fourier: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    u1: Level,
}

impl DcConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            rat_mul: k("Rat.mul"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            u1: l1,
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S) · f̂(S)`.
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn ss_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `Nat.ble (succ zero) m` — the `|S| ≥ 1` bit.
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.one_nat(), m)
    }
    /// `Nat.ble (succ k) m` — the `|S| ≥ k+1` (= `|S| > k`) bit.
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    fn band_of(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// The band mask `Bool.and (ble 1 |S|) (not (ble (k+1) |S|))`.
    fn band_bit(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        let ss = self.ss_nat_of(n, s);
        self.band_of(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)))
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.one_nat(),
            ],
        )
    }
    /// `LE.le Rat instLERat a b`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), l, r],
        )
    }
    /// `Eq.symm.{1} Rat a b h : b = a`.
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }

    /// `fun S => ind (band) · (f̂·f̂)` — the `M_{1..k}` band integrand
    /// (byte-identical to the landed keystone `m_lo_fn`).
    fn m_lo_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let band = self.band_bit(n, k, &s);
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => ind (band) · (setSize n S · (f̂·f̂))` — the degree-weighted band
    /// integrand `Σ_i W^{≤k}[D_i f]` (the double-count RHS, masked).
    fn m_lo_weighted_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let band = self.band_bit(n, k, &s);
        let weighted = self.mul(self.set_size_of(n, &s), self.fsq(n, f, &s));
        let body = self.mul(self.ind_of(band), weighted);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the structural double-count bound. Idempotent.
    pub fn init_boolean_analysis_kkl_bridgestruct_dc(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_kkl_bridgestruct_pointwise()?;
        self.register_lowband_double_count_le()?;
        Ok(())
    }

    /// `BoolAnalysis.lowband_double_count_le :
    ///   ∀ (n k : Nat) (f : BoolFn n),
    ///     Rat.le (subsetSum n (fun S => ind(band)·(f̂·f̂)))
    ///            (subsetSum n (fun S => ind(band)·(setSize n S·(f̂·f̂))))`.
    ///
    /// The spectral DOUBLE-COUNT `M_{1..k} ≤ Σ_i W^{≤k}[D_i f]`. See module docs.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_lowband_double_count_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_double_count_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // FourierCoefficient, ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_set_size_eq_natcast()?;
        self.register_nat_cast_le_of_ble()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg
        self.init_boolean_analysis_kkl_bridgestruct_pointwise()?; // lowband_dc_term, Bool.and_left_eq_true

        let c = DcConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_dc_type(&c),
            value: build_dc_value(&c),
        })
    }
}

fn build_dc_type(c: &DcConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f));
    let m_lo_w = c.subset_sum_of(&n, c.m_lo_weighted_fn(&b, &n, &k, &f));
    let concl = c.le(m_lo, m_lo_w);

    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn build_dc_value(c: &DcConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let m_lo_fn = c.m_lo_fn(&b, &n, &k, &f);
    let m_lo_w_fn = c.m_lo_weighted_fn(&b, &n, &k, &f);

    let subset_sum_le = Expr::const_(
        Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
        vec![],
    );
    let dc_term = Expr::const_(Name::from_string("BoolAnalysis.lowband_dc_term"), vec![]);
    let and_left = Expr::const_(Name::from_string("Bool.and_left_eq_true"), vec![]);
    let cast_le_of_ble = Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]);
    let set_size_eq_natcast =
        Expr::const_(Name::from_string("BoolAnalysis.setSize_eq_natCast"), vec![]);
    let sq_nonneg = Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]);

    // per_s : ∀ (S : HCPoint n), m_lo_fn S ≤ m_lo_weighted_fn S
    let per_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());

        let band = c.band_bit(&n, &k, &s);
        let size = c.set_size_of(&n, &s); // setSize n S (Rat)
        let size_nat = c.ss_nat_of(&n, &s); // setSizeNat n S (Nat)
        let coeff = c.fourier_of(&n, &f, &s);
        let w = c.mul(coeff.clone(), coeff.clone()); // f̂·f̂

        // h_w : 0 ≤ f̂·f̂   (Rat.sq_nonneg (f̂ S))
        let h_w = Expr::app(sq_nonneg.clone(), coeff.clone());

        // h_sz : band = true → 1 ≤ setSize n S
        let h_sz = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let ante = c.eq_bool(band.clone(), c.bool_true.clone());
            let (h_id, h) = e.fresh_local(ante.clone());

            let ble1 = c.ble1(size_nat.clone());
            let bnot_k = c.bnot(c.ble_succ_k(&k, size_nat.clone()));
            // h_ble1 : ble 1 |S| = true
            let h_ble1 = Expr::apps(and_left.clone(), [ble1.clone(), bnot_k, h]);
            // h_cast : natCast 1 ≤ natCast |S|   (Nat.cast_le_of_ble 1 |S| h_ble1)
            let h_cast = Expr::apps(
                cast_le_of_ble.clone(),
                [c.one_nat(), size_nat.clone(), h_ble1],
            );
            // h_size_eq : setSize n S = natCast |S|   (setSize_eq_natCast n S)
            let h_size_eq = Expr::apps(set_size_eq_natcast.clone(), [n.clone(), s.clone()]);
            // symm : natCast |S| = setSize n S
            let cast_size = c.natcast(&size_nat);
            let h_size_eq_symm = c.symm_rat(size.clone(), cast_size.clone(), h_size_eq);
            // motive t := natCast 1 ≤ t ; subst (natCast |S|) → (setSize n S)
            let motive = {
                let mut g = EnvDeclBuilder::child_of(&e);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.le(c.natcast(&c.one_nat()), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // 1 ≤ setSize n S  (natCast 1 ≡ Rat.one defeq, so type matches the atom)
            let body = c.subst_rat(motive, cast_size, size.clone(), h_size_eq_symm, h_cast);
            e.finish_child(e.mk_lam(h_id, BinderInfo::Default, ante, body))
        };

        // lowband_dc_term band (setSize n S) (f̂·f̂) h_w h_sz
        //   : ind(band)·(f̂·f̂) ≤ ind(band)·((setSize n S)·(f̂·f̂))
        let body = Expr::apps(dc_term.clone(), [band, size, w, h_w, h_sz]);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };

    // subsetSum_le_of_pointwise n m_lo_fn m_lo_weighted_fn per_s
    let body = Expr::apps(subset_sum_le, [n.clone(), m_lo_fn, m_lo_w_fn, per_s]);

    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_bridgestruct_dc()
            .expect("init_boolean_analysis_kkl_bridgestruct_dc");
        env.init_boolean_analysis_kkl_bridgestruct_dc()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_lowband_double_count_le_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.lowband_double_count_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("lowband_double_count_le must kernel-check");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "lowband_double_count_le must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "lowband_double_count_le closure must be empty (foundational-only)"
        );
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute the structural double-count — it is a sound, unconditional termwise
    /// `≤ 1` ⟹ degree-weight domination — when probed over the dictator / parity /
    /// constant battery. A refutation would mean the statement is FALSE.
    #[test]
    fn test_lowband_double_count_le_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.lowband_double_count_le"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the structural double-count is a true inequality; it must NOT refute \
             on the dictator/parity/constant battery"
        );
    }
}
