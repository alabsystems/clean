// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner / noise campaign — the un-normalized noise operator on decoded
//! cube points.
//!
//! `BoolAnalysis.noiseFn` packages the action of the ρ-noise operator `T_ρ` on a
//! function `F : HCPoint n → Rat`, indexed over the `2^n` cube points enumerated
//! by `hcDecode` (the same indexing convention `BoolAnalysis.Expect` and
//! `noise_spectral_core` use), in the **un-normalized** form `2^n · (T_ρ F)`:
//!
//! ```text
//! BoolAnalysis.noiseFn (ρ : Rat) (n : Nat) (F : HCPoint n → Rat)
//!     : Fin (Nat.pow 2 n) → Rat :=
//!   fun (jx : Fin (2^n)) =>
//!     Fin.sum (2^n) (fun (jy : Fin (2^n)) =>
//!       Rat.mul (F (hcDecode n jy))
//!               (noiseDensityW ρ n (hcDecode n jx) (hcDecode n jy)))
//! ```
//!
//! With `x := hcDecode n jx`, `y := hcDecode n jy`, the value at `jx` is
//! `Σ_y F(y) · noiseDensityW ρ n x y`. Since `noiseDensityW ρ n x y =
//! Σ_S ρ^{|S|} χ_S(x) χ_S(y)`, this is `2^n · (T_ρ F)(x)` — the carrier the
//! spectral identity `noise_spectral_core` decomposes (the inner `Fin.sum (2^n)
//! (F ∘ hcDecode · noiseDensityW)` matches the `Expect`-grade cube sum, so the
//! spectral Fubini applies after summing `noiseFn jx · (F ∘ hcDecode) jx` over
//! `jx`).
//!
//! Reducible `Declaration::Definition`. No axiom is added or removed; built from
//! `Fin.sum`, `BoolAnalysis.hcDecode`, `BoolAnalysis.noiseDensityW`, `Rat.mul`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the `noiseFn` carrier.
struct NoiseFnConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nat_pow: Expr,
    two: Expr,
    rat_mul: Expr,
    fin_sum: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    noise_density: Expr,
}

impl NoiseFnConsts {
    fn new() -> Self {
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two: Expr::app(nat_succ, nat_one),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    /// `Fin (Nat.pow 2 n)`.
    fn fin_pow(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), self.pow2(n))
    }
    /// `HCPoint n → Rat` — the type of the input function `F`.
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `BoolAnalysis.hcDecode n k`.
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `noiseDensityW ρ n x y`.
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `Fin.sum (2^n) f`.
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [self.pow2(n), f])
    }
}

impl Environment {
    /// Register `BoolAnalysis.noiseFn`: the un-normalized noise operator
    /// `2^n · T_ρ F` on decoded cube points, as a reducible `Declaration::Definition`.
    /// Idempotent. No axiom added/removed.
    pub(crate) fn register_noise_fn(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseFn");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis()?; // hcDecode
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_noise_density_w()?;
        // Re-check: the `init_boolean_analysis` pass above registers the full
        // hc24 chain (bonami retirement), which includes `noiseFn` itself.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseFnConsts::new();
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_noise_fn_type(&c),
            value: build_noise_fn_value(&c),
            is_reducible: true,
        })
    }
}

/// `(ρ : Rat) → (n : Nat) → (F : HCPoint n → Rat) → Fin (2^n) → Rat`.
fn build_noise_fn_type(c: &NoiseFnConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, _rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, _f) = b.fresh_local(c.f_type(&n));
    let result = Expr::pi(BinderInfo::Default, c.fin_pow(&n), c.rat.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), result);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `fun ρ n F jx => Fin.sum (2^n) (fun jy => F(hcDecode n jy)·noiseDensityW ρ n
///  (hcDecode n jx) (hcDecode n jy))`.
fn build_noise_fn_value(c: &NoiseFnConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    // fun (jx : Fin (2^n)) => Fin.sum (2^n) (inner jx)
    let outer = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = d.fresh_local(c.fin_pow(&n));
        let x = c.decode(&n, &jx);
        // fun (jy : Fin (2^n)) => F(hcDecode n jy)·noiseDensityW ρ n x (hcDecode n jy)
        let inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (jy_id, jy) = e.fresh_local(c.fin_pow(&n));
            let y = c.decode(&n, &jy);
            let f_y = Expr::app(f.clone(), y.clone());
            let dens = c.density(&rho, &n, &x, &y);
            let body = c.mul(f_y, dens);
            e.finish_child(e.mk_lam(jy_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        let body = c.sum(&n, inner);
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(&n), body))
    };

    let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), outer);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `BoolAnalysis.noiseFn_zero_dim`: a smoke lemma anchoring the
    /// `noiseFn` carrier at `n = 0`, where the cube has a single point and the
    /// density collapses.
    ///
    /// `∀ (ρ : Rat) (F : HCPoint 0 → Rat) (jx : Fin (2^0)),
    ///     noiseFn ρ 0 F jx = Rat.mul (F (hcDecode 0 (Fin.last 0)))
    ///         (noiseDensityW ρ 0 (hcDecode 0 jx) (hcDecode 0 (Fin.last 0)))`
    ///
    /// At `n = 0`, `2^0 = 1`, so `Fin.sum 1 g` ι-reduces (one `Fin.sum_succ` step
    /// onto `Fin.sum 0 (… ∘ castSucc) + g (Fin.last 0)` ≡ `0 + g (Fin.last 0)`),
    /// leaving the single summand at the lone cube index `Fin.last 0`. Proved via
    /// `Fin.sum_succ` + `Fin.sum_zero` + `Rat.zero_add`, so the carrier is
    /// exercised, not merely restated. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_noise_fn_zero_dim(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseFn_zero_dim");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_fn()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.zero_add
        }
        // Re-check: `register_noise_fn`'s `init_boolean_analysis` pass registers
        // the hc24 chain (bonami retirement), which includes `noiseFn_zero_dim`.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseFnConsts::new();
        let (ty, value) = build_zero_dim(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `noiseFn_zero_dim`.
fn build_zero_dim(c: &NoiseFnConsts) -> (Expr, Expr) {
    let l1 = Level::succ(Level::zero());
    let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let noise_fn = Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]);

    let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
    let last0 = Expr::app(fin_last, nat_zero.clone());

    let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [c.rat.clone(), l, r]);
    // `noiseFn ρ 0 F jx`.
    let noise_at = |rho: &Expr, f: &Expr, jx: &Expr| {
        Expr::apps(
            noise_fn.clone(),
            [rho.clone(), nat_zero.clone(), f.clone(), jx.clone()],
        )
    };
    // The single surviving summand at the unique cube point `Fin.last 0`:
    //   `F(hcDecode 0 (last 0)) · noiseDensityW ρ 0 (hcDecode 0 jx) (hcDecode 0 (last 0))`
    // (the `jy`-slot is `Fin.last 0`, the lone element of `Fin (2^0) = Fin 1`).
    let single = |rho: &Expr, f: &Expr, jx: &Expr| {
        let x = c.decode(&nat_zero, jx);
        let y = c.decode(&nat_zero, &last0);
        c.mul(
            Expr::app(f.clone(), y.clone()),
            c.density(rho, &nat_zero, &x, &y),
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&nat_zero));
        let (jx_id, jx) = b.fresh_local(c.fin_pow(&nat_zero));
        let concl = eq_rat(noise_at(&rho, &f, &jx), single(&rho, &f, &jx));
        let e = b.mk_pi(jx_id, BinderInfo::Default, c.fin_pow(&nat_zero), concl);
        let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&nat_zero), e);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    let value = build_zero_dim_proof(c, &eq_rat, &noise_at, &single, &nat_zero);
    (ty, value)
}

/// Proof of `noiseFn_zero_dim`.
///
/// `noiseFn ρ 0 F jx` δ-unfolds to `Fin.sum (2^0) (fun jy => F(decode jy)·dens jy)`,
/// and `2^0 ≡ 1 ≡ Nat.succ 0`. `Fin.sum_succ 0 g : Fin.sum 1 g =
/// Rat.add (Fin.sum 0 (g ∘ castSucc 0)) (g (Fin.last 0))`. `Fin.sum_zero` collapses
/// the prefix to `0`, so `noiseFn = Rat.add 0 (g (Fin.last 0))`, and `Rat.zero_add`
/// gives `g (Fin.last 0)`. `g (Fin.last 0)` is the `single` term because
/// `hcDecode 0 (Fin.last 0)` and `hcDecode 0 jx` agree (`Fin (2^0) = Fin 1` is a
/// singleton — both decode to the empty cube point) — definitionally, so the
/// final `g (Fin.last 0)` is `single` up to `Fin`-eta, closed by `Eq.refl`.
fn build_zero_dim_proof<EqF, NF, SF>(
    c: &NoiseFnConsts,
    eq_rat: &EqF,
    noise_at: &NF,
    single: &SF,
    nat_zero: &Expr,
) -> Expr
where
    EqF: Fn(Expr, Expr) -> Expr,
    NF: Fn(&Expr, &Expr, &Expr) -> Expr,
    SF: Fn(&Expr, &Expr, &Expr) -> Expr,
{
    let l1 = Level::succ(Level::zero());
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
    let fin_sum_succ = Expr::const_(Name::from_string("Fin.sum_succ"), vec![]);
    let fin_sum_zero = Expr::const_(Name::from_string("Fin.sum_zero"), vec![]);
    let fin_cast_succ = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
    let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
    let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);

    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(nat_zero));
    let (jx_id, jx) = b.fresh_local(c.fin_pow(nat_zero));

    // The inner summand `g := fun jy => F(decode jy)·noiseDensityW ρ 0 (decode jx)(decode jy)`.
    let x = c.decode(nat_zero, &jx);
    let g = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (jy_id, jy) = d.fresh_local(c.fin_pow(nat_zero));
        let y = c.decode(nat_zero, &jy);
        let body = c.mul(
            Expr::app(f.clone(), y.clone()),
            c.density(&rho, nat_zero, &x, &y),
        );
        d.finish_child(d.mk_lam(jy_id, BinderInfo::Default, c.fin_pow(nat_zero), body))
    };

    // LHS `noiseFn ρ 0 F jx` ≡ `Fin.sum 1 g` (defeq via δ + 2^0 ≡ 1).
    let lhs = noise_at(&rho, &f, &jx);

    // Fin.sum_succ 0 g : Fin.sum 1 g = Rat.add (Fin.sum 0 (g ∘ castSucc 0)) (g (last 0))
    let step_succ = Expr::apps(fin_sum_succ.clone(), [nat_zero.clone(), g.clone()]);
    // g ∘ castSucc 0 : fun i : Fin 0 => g (castSucc 0 i)
    let g_cast = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin0 = Expr::app(c.fin.clone(), nat_zero.clone());
        let (i_id, i) = d.fresh_local(fin0.clone());
        let cast = Expr::apps(fin_cast_succ.clone(), [nat_zero.clone(), i]);
        let body = Expr::app(g.clone(), cast);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin0, body))
    };
    let sum_prefix = Expr::apps(c.fin_sum.clone(), [nat_zero.clone(), g_cast.clone()]);
    let g_last = Expr::app(g.clone(), Expr::app(fin_last.clone(), nat_zero.clone()));
    let succ_rhs = Expr::apps(rat_add.clone(), [sum_prefix.clone(), g_last.clone()]);

    // Fin.sum_zero (g ∘ castSucc 0) : Fin.sum 0 (g∘cast) = Rat.zero
    let step_zero = Expr::app(fin_sum_zero.clone(), g_cast);
    // congrArg (fun z => Rat.add z (g last)) step_zero : (prefix + g last) = (0 + g last)
    let add_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = Expr::apps(rat_add.clone(), [z, g_last.clone()]);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let zero_plus = Expr::apps(rat_add.clone(), [rat_zero.clone(), g_last.clone()]);
    let cong_zero = Expr::apps(
        congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            sum_prefix.clone(),
            rat_zero.clone(),
            add_fn,
            step_zero,
        ],
    );
    // Rat.zero_add (g last) : Rat.add 0 (g last) = g last
    let zero_add = Expr::app(rat_zero_add.clone(), g_last.clone());

    // `g (last 0)` is defeq to `single` (both decode the singleton Fin 1 to the
    // same empty cube point), so Eq.refl on `single` closes the last leg.
    let single_t = single(&rho, &f, &jx);
    let refl_single = Expr::apps(eq_refl.clone(), [c.rat.clone(), single_t.clone()]);

    // chain: lhs = succ_rhs = zero_plus = g_last = single
    let trans = |a: Expr, bb: Expr, cc: Expr, h1: Expr, h2: Expr| {
        Expr::apps(eq_trans.clone(), [c.rat.clone(), a, bb, cc, h1, h2])
    };
    let t1 = trans(
        lhs.clone(),
        succ_rhs.clone(),
        zero_plus.clone(),
        step_succ,
        cong_zero,
    );
    let t2 = trans(lhs.clone(), zero_plus.clone(), g_last.clone(), t1, zero_add);
    let proof = trans(lhs, g_last, single_t, t2, refl_single);

    let _ = eq_rat;
    let e = b.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(nat_zero), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(nat_zero), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_fn_registered_as_reducible_definition() {
        let mut env = Environment::with_prelude();
        env.register_noise_fn().expect("register_noise_fn");
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.noiseFn"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc
            .infer_type(&Expr::const_(
                Name::from_string("BoolAnalysis.noiseFn"),
                vec![],
            ))
            .expect("noiseFn should type-check");
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "noiseFn type is a Pi"
        );
    }

    #[test]
    fn test_noise_fn_zero_dim_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_fn_zero_dim()
            .expect("register_noise_fn_zero_dim");
        let name = Name::from_string("BoolAnalysis.noiseFn_zero_dim");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noiseFn_zero_dim proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
