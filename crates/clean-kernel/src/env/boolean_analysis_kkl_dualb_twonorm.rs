// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bridge — Component B3a: the noise 2-norm = pairing
//! IDENTITY `‖T_{1/3} g‖₂² = ⟨T_{1/9} g, g⟩`, in spectral / `subsetSum` form.
//!
//! This is the first equality of the §9.6 dual chain
//! `‖T_{1/3} g‖₂² = ⟨T_{1/9} g, g⟩ ≤ ‖T_{1/9} g‖₄·‖g‖_{4/3}`. The 2-norm of the
//! noise operator at parameter `1/3`, expanded spectrally, has per-level weight
//! `((1/3)^{|S|})²` (the square of the `T_{1/3}` Fourier multiplier `(1/3)^{|S|}`),
//! while the inner-product pairing `⟨T_{1/9} g, g⟩` has per-level weight
//! `(1/9)^{|S|}`. The two coincide because the noise operator is a SEMIGROUP:
//! `T_{1/3} ∘ T_{1/3} = T_{1/9}`, whose per-level spectral signature is exactly
//! `(1/3)^{|S|}·(1/3)^{|S|} = (1/9)^{|S|}` — the landed
//! `BoolAnalysis.noise_semigroup_third` (component B1).
//!
//! ```text
//! BoolAnalysis.noise_two_norm_eq_pairing :
//!   ∀ (n : Nat) (g : HCPoint n → Rat),
//!     subsetSum n (fun S =>                                     -- ‖T_{1/3}g‖₂²
//!       Rat.mul (Rat.mul (powNat (1/3) |S|) (powNat (1/3) |S|))
//!               (Rat.mul (A g S) (A g S)))
//!       = subsetSum n (fun x => subsetSum n (fun y =>           -- ⟨T_{1/9}g, g⟩
//!           Rat.mul (Rat.mul (g x) (g y)) (noiseDensityW (1/9) n x y)))
//! ```
//!
//! with `A g S := subsetSum n (fun x => g x · χ_S x)` the un-normalized Fourier
//! coefficient and `|S| := Fin.sumNat n (fun i => indNat (S i))` the popcount —
//! both built byte-for-byte from the `noise_spectral_core` shapes so the middle
//! endpoint stays def-eq.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! Let `MID := subsetSum n (fun S => (1/9)^{|S|} · (A g S · A g S))` — the
//! `noise_spectral_core (1/9) n g` RHS (the weight `powNat (1/9) (pc n S)` with
//! `pc n S ≡ |S|` byte-for-byte). Two legs:
//!
//! 1. **LHS = MID** — the semigroup rewrite. `subsetSum_congr` over the pointwise
//!    `((1/3)^{|S|}·(1/3)^{|S|}) · (A·A) = (1/9)^{|S|} · (A·A)`, which is
//!    `congrArg (fun w => w·(A·A)) (noise_semigroup_third |S|)` — `noise_semigroup_third`
//!    instantiated at the exponent `k := |S|`.
//! 2. **MID = RHS** — the spectral Fubini, reversed. `Eq.symm` of
//!    `noise_spectral_core (1/9) n g : ⟨T_{1/9}g,g⟩ = Σ_S (1/9)^{|S|}·A(S)²`
//!    (the LHS of `noise_spectral_core` is `⟨T_{1/9}g, g⟩`, its RHS is `MID`).
//!
//! `Eq.trans` chains the two legs. Every leaf (`subsetSum_congr`, `congrArg`,
//! `noise_semigroup_third`, `noise_spectral_core`, `Eq.symm`, `Eq.trans`) is
//! `Constructive` with empty admitted-axiom closure, so this identity is too.
//! No axiom is added or removed. Idempotent.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Atoms for the 2-norm = pairing identity. The popcount / `indNat` / `A(S)`
/// builds are byte-for-byte the `SpectralConsts` shapes so the middle endpoint
/// `subsetSum n (fun S => (1/9)^{|S|}·(A·A))` is def-eq to the
/// `noise_spectral_core (1/9)` RHS, and the RHS pairing is def-eq to its LHS.
struct DualBTwoNormConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    chi: Expr,
    hcpoint: Expr,
    fin: Expr,
    fin_sum_nat: Expr,
    bool_rec_nat: Expr,
    noise_density: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    noise_semigroup_third: Expr,
    noise_spectral_core: Expr,
    congr_arg: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
}

impl DualBTwoNormConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum_nat: Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            noise_semigroup_third: Expr::const_(
                Name::from_string("BoolAnalysis.noise_semigroup_third"),
                vec![],
            ),
            noise_spectral_core: Expr::const_(
                Name::from_string("BoolAnalysis.noise_spectral_core"),
                vec![],
            ),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
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
    /// `@congrArg.{1,1} Rat Rat from to motive h : motive from = motive to`.
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }

    /// `Rat.mk (Int.ofNat 1) d` — the literal `1/d`. Byte-for-byte the
    /// `DualSemigroupConsts::one_over` build, so the `1/3` / `1/9` literals match
    /// `noise_semigroup_third`'s `(1/3)^k·(1/3)^k = (1/9)^k` endpoints exactly.
    fn one_over(&self, d: u32) -> Expr {
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut d_nat = self.nat_zero.clone();
        for _ in 0..d {
            d_nat = Expr::app(self.nat_succ.clone(), d_nat);
        }
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(int_of_nat, one_nat), d_nat],
        )
    }

    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — byte-for-byte the
    /// `SpectralConsts::ind_nat` per-bit popcount summand.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            self.bool_rec_nat.clone(),
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — the popcount `|S|`,
    /// byte-for-byte the `SpectralConsts::popcount` build (so the rewritten weight
    /// `(1/9)^{pc n S}` is def-eq to `noise_spectral_core (1/9)`'s RHS weight).
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(self.fin_sum_nat.clone(), [n.clone(), pc_fn])
    }
    /// `A g S = subsetSum n (fun x => g x · χ_S x)` — byte-for-byte the
    /// `SpectralConsts::g_fn` over `ssum` (the `noise_spectral_core` Fourier sum).
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), x.clone()), self.chi_(n, s, &x));
        let f = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// The LHS `S`-integrand `fun S => ((1/3)^{|S|}·(1/3)^{|S|})·(A·A)` — the
    /// `‖T_{1/3}g‖₂²` spectral summand with the SQUARED per-level `T_{1/3}` weight.
    fn lhs_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let third = self.one_over(3);
        let pc = self.popcount(&b, n, &s);
        let w_third = self.pow(&third, &pc);
        let w = self.mul(w_third.clone(), w_third); // (1/3)^{|S|}·(1/3)^{|S|}
        let aa = {
            let inner = self.a_coeff(&b, n, g, &s);
            self.mul(inner.clone(), inner)
        };
        let body = self.mul(w, aa);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The MID `S`-integrand `fun S => (1/9)^{|S|}·(A·A)` — byte-for-byte the
    /// `noise_spectral_core (1/9)` RHS summand (`SpectralConsts::rhs_s_fn` at
    /// `ρ := 1/9`: weight `powNat (1/9) (pc n S)`, body `(A·A)`).
    fn mid_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let ninth = self.one_over(9);
        let pc = self.popcount(&b, n, &s);
        let w = self.pow(&ninth, &pc); // (1/9)^{|S|}
        let aa = {
            let inner = self.a_coeff(&b, n, g, &s);
            self.mul(inner.clone(), inner)
        };
        let body = self.mul(w, aa);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The RHS pairing `x`-integrand `fun x => Σ_y (g x·g y)·noiseDensityW (1/9) n x y`
    /// — byte-for-byte the `noise_spectral_core (1/9)` LHS shape
    /// (`SpectralConsts::lhs_x_fn` at `ρ := 1/9, a := g`); this is `⟨T_{1/9}g, g⟩`.
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
}

/// `∀ (n : Nat) (g : HCPoint n → Rat), ‖T_{1/3}g‖₂² = ⟨T_{1/9}g, g⟩`.
fn build_type(c: &DualBTwoNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let lhs = c.ssum(&n, c.lhs_s_fn(&b, &n, &g));
    let rhs = c.ssum(&n, c.rhs_x_fn(&b, &n, &g));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Body: `λ n g => Eq.trans LHS MID RHS leg1 leg2`.
fn build_value(c: &DualBTwoNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let ninth = c.one_over(9);

    let lhs_fn = c.lhs_s_fn(&b, &n, &g);
    let mid_fn = c.mid_s_fn(&b, &n, &g);
    let lhs = c.ssum(&n, lhs_fn.clone());
    let mid = c.ssum(&n, mid_fn.clone());
    let rhs = c.ssum(&n, c.rhs_x_fn(&b, &n, &g));

    // leg1 (semigroup) : LHS = MID, via subsetSum_congr over the pointwise
    //   ((1/3)^{|S|}·(1/3)^{|S|})·(A·A) = (1/9)^{|S|}·(A·A)
    //   = congrArg (fun w => w·(A·A)) (noise_semigroup_third |S|).
    let leg1 = {
        let hyp = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let third = c.one_over(3);
            let pc = c.popcount(&d, &n, &s);
            let w_third = c.pow(&third, &pc);
            let from = c.mul(w_third.clone(), w_third); // (1/3)^{|S|}·(1/3)^{|S|}
            let to = c.pow(&ninth, &pc); // (1/9)^{|S|}
            let aa = {
                let inner = c.a_coeff(&d, &n, &g, &s);
                c.mul(inner.clone(), inner)
            };
            // semigroup |S| : (1/3)^{|S|}·(1/3)^{|S|} = (1/9)^{|S|}
            let sg = Expr::app(c.noise_semigroup_third.clone(), pc);
            // motive : fun (w : Rat) => w·(A·A)
            let motive = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (w_id, w) = e.fresh_local(c.rat.clone());
                e.finish_child(e.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    c.rat.clone(),
                    c.mul(w, aa.clone()),
                ))
            };
            let body = c.congr_rat(from, to, motive, sg);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        c.ssum_congr(&n, &lhs_fn, &mid_fn, hyp)
    };

    // leg2 (spectral Fubini, reversed) : MID = RHS.
    //   nsc : RHS = MID  (noise_spectral_core (1/9) n g; its LHS is ⟨T_{1/9}g,g⟩
    //   = RHS, its RHS is the (1/9)-weighted spectral sum = MID).
    //   leg2 = Eq.symm nsc : MID = RHS.
    let leg2 = {
        let nsc = Expr::apps(
            c.noise_spectral_core.clone(),
            [ninth.clone(), n.clone(), g.clone()],
        );
        c.symm(rhs.clone(), mid.clone(), nsc)
    };

    let proof = c.trans(lhs, mid, rhs, leg1, leg2);

    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.noise_two_norm_eq_pairing` — the dual-bound B3a
    /// identity `‖T_{1/3}g‖₂² = ⟨T_{1/9}g, g⟩` in spectral / `subsetSum` form: the
    /// 2-norm with the SQUARED per-level `T_{1/3}` weight `(1/3)^{|S|}·(1/3)^{|S|}`
    /// equals the `(1/9)`-pairing through `noiseDensityW`. `subsetSum_congr` over
    /// the semigroup `noise_semigroup_third` (B1) chained with `Eq.symm` of
    /// `noise_spectral_core (1/9)` (the spectral Fubini). Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_noise_two_norm_eq_pairing(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_two_norm_eq_pairing");
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
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_rat_pow_nat()?;
        self.register_noise_density_w()?;
        self.register_noise_semigroup_third()?; // B1 (+ Rat.powNat, third_mul_third)
        self.register_noise_spectral_core_theorem()?; // spectral Fubini
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DualBTwoNormConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_noise_two_norm_eq_pairing()
            .expect("register_noise_two_norm_eq_pairing");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check against its type: {e:?}"));
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
    fn test_noise_two_norm_eq_pairing_is_constructive_theorem() {
        check_constructive(&env(), "BoolAnalysis.noise_two_norm_eq_pairing");
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_two_norm_eq_pairing().expect("first");
        env.register_noise_two_norm_eq_pairing()
            .expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute the 2-norm = pairing identity — it is a TRUE algebraic identity (an
    /// equality of two `subsetSum`s, no influence parameter), so the
    /// constant/dictator/parity carrier battery cannot manufacture a false
    /// instance. By-hand: both sides equal `Σ_S (1/9)^{|S|}·A(S)²` — the LHS by the
    /// semigroup `(1/3)^k·(1/3)^k = (1/9)^k`, the RHS by the spectral Fubini
    /// `noise_spectral_core (1/9)` — so the identity holds for every `g`, `n`.
    #[test]
    fn test_two_norm_eq_pairing_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.noise_two_norm_eq_pairing"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "noise_two_norm_eq_pairing is a TRUE algebraic identity; it must NOT refute"
        );
    }
}
