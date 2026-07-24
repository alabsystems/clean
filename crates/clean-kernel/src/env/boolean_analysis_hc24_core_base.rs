// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **base case** `hc24_core_base` (n = 0) of the
//! (2,4)-hypercontractivity operator induction, plus the shared `hc24_core`
//! statement builder.
//!
//! The full induction target (built by [`hc24_core_concl`], reused by base and
//! step):
//!
//! ```text
//! BoolAnalysis.hc24_core :
//!   ∀ (ρ : Rat) (n : Nat) (F : HCPoint n → Rat),
//!     Rat.le (3·(ρ·ρ)) 1 →
//!       Rat.le
//!         (Fin.sum (2^n) (fun jx => pow4 (noiseFn ρ n F jx)))
//!         ((Rat.powNat 8 n) · sq (Fin.sum (2^n) (fun jx => sq (F (hcDecode n jx)))))
//! ```
//!
//! with `pow4 x := (x·x)·(x·x)`, `sq x := x·x`, scalar `8^n = Rat.powNat 8 n`
//! (the `powNat` recurrence is defeq, which the step needs).
//!
//! ## Base case (`n = 0`) — pure carrier collapse
//!
//! `2^0 = 1`, `powNat 8 0 ≡ 1`. Both the outer `Fin.sum 1` (LHS) and the inner
//! `Fin.sum 1` (RHS) collapse to their single cube point `Fin.last 0`
//! (`Fin.sum_succ` + `Fin.sum_zero` + `Rat.zero_add`). `noiseFn ρ 0 F (last 0)`
//! collapses (`noiseFn_zero_dim` + `noiseDensityW ρ 0 ≡ 1` defeq + `Rat.mul_one`)
//! to `F (hcDecode 0 (last 0))`. So LHS `= pow4 (F dec)` and RHS `= 1 · sq (sq (F
//! dec)) = pow4 (F dec)` (`powNat_zero` + `mul_one`), and the goal closes by
//! `Rat.le_refl (pow4 (F dec))`. No domain content.
//!
//! Constructive, empty domain-axiom closure (leaves: `Fin.sum_succ`/`_zero`,
//! `Rat.zero_add`/`mul_one`, `noiseFn_zero_dim`, `Rat.powNat_zero`, `Rat.le_refl`,
//! `Eq`/`subst`/`congrArg` built-ins).

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants + smart-constructors for the `hc24_core` statement and the
/// base-case proof.
pub(super) struct Hc24Consts {
    pub(super) o: HcBoundsConsts,
    pub(super) l1: Level,
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) nat_pow: Expr,
    pub(super) nat_zero: Expr,
    pub(super) two: Expr,
    pub(super) eight: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_one: Expr,
    pub(super) fin_sum: Expr,
    pub(super) fin_last: Expr,
    pub(super) pow_nat: Expr,
    pub(super) hcpoint: Expr,
    pub(super) hc_decode: Expr,
    pub(super) noise_fn: Expr,
    pub(super) noise_density: Expr,
}

impl Hc24Consts {
    pub(super) fn new() -> Self {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let n1 = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), n1.clone());
        // 8 = succ^8 0
        let mut eight = nat_zero.clone();
        for _ in 0..8 {
            eight = Expr::app(nat_succ.clone(), eight);
        }
        Self {
            o: HcBoundsConsts::new(),
            l1: Level::succ(Level::zero()),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_zero,
            two,
            eight,
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            noise_fn: Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
        }
    }

    pub(super) fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    pub(super) fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    pub(super) fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    pub(super) fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.le(a, b)
    }
    /// `pow4 x := (x·x)·(x·x)`.
    pub(super) fn pow4(&self, x: &Expr) -> Expr {
        let sq = self.mul(x.clone(), x.clone());
        self.mul(sq.clone(), sq)
    }
    /// `sq x := x·x`.
    pub(super) fn sq(&self, x: &Expr) -> Expr {
        self.mul(x.clone(), x.clone())
    }
    /// `hcDecode n k`.
    pub(super) fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    /// `noiseFn ρ n F jx`.
    pub(super) fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), n.clone(), f.clone(), jx.clone()],
        )
    }
    /// `noiseDensityW ρ n x y`.
    pub(super) fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `Rat.powNat 8 n`.
    pub(super) fn pow8(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.eight_rat(), n.clone()])
    }
    /// The rational constant `8` (`Rat.ofNat`-free: `Rat.mk (Int.ofNat 8) 1`).
    pub(super) fn eight_rat(&self) -> Expr {
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            self.nat_zero.clone(),
        );
        Expr::apps(rat_mk, [Expr::app(int_of_nat, self.eight.clone()), nat_one])
    }
    /// `Fin.sum n f`.
    pub(super) fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f])
    }
    /// `Fin.last n`.
    pub(super) fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `@Eq Rat l r`.
    pub(super) fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    /// `@Eq.trans Rat a b c h1 h2`.
    pub(super) fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, c, h1, h2],
        )
    }
    /// `@Eq.symm Rat a b h`.
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@congrArg Rat Rat from to f h`.
    pub(super) fn congr_arg(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), from, to, f, h],
        )
    }
    /// `Rat.mul_one a : a·1 = a`.
    pub(super) fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), a)
    }
    /// `Rat.one_mul a : 1·a = a`.
    pub(super) fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), a)
    }
    /// `Rat.le_refl a : a ≤ a`.
    pub(super) fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.le_refl"), vec![]), a)
    }
}

/// The `hc24_core` conclusion (the LE goal) at a concrete `n`, for FREE `ρ`, `F`.
/// Reused by the base case and the induction step so the targets agree
/// byte-for-byte. `parent` is the enclosing builder that owns the free `ρ`/`n`/`F`.
pub(super) fn hc24_core_concl(
    c: &Hc24Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
) -> Expr {
    let p2n = c.pow2(n);
    // LHS: Fin.sum (2^n) (fun jx => pow4 (noiseFn ρ n F jx)).
    let lhs_fn = {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = b.fresh_local(c.fin_of(&p2n));
        let body = c.pow4(&c.noise_fn(rho, n, f, &jx));
        b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    let lhs = c.sum(&p2n, lhs_fn);
    // inner: Fin.sum (2^n) (fun jx => sq (F (hcDecode n jx))).
    let inner_fn = {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = b.fresh_local(c.fin_of(&p2n));
        let body = c.sq(&Expr::app(f.clone(), c.decode(n, &jx)));
        b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    let inner = c.sum(&p2n, inner_fn);
    let rhs = c.mul(c.pow8(n), c.sq(&inner));
    c.le(lhs, rhs)
}

impl Environment {
    /// Initialize the `hc24_core` base case (`n = 0`).
    ///
    /// Registers `BoolAnalysis.hc24_core_base` as a kernel-checked
    /// `Declaration::Theorem`. Idempotent. No axiom is added or removed.
    pub fn init_boolean_analysis_hc24_core_base(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_noise_fn_zero_dim()?;
        self.register_rat_pow_nat_zero_theorem()?;
        self.init_boolean_analysis_hc_bounds()?; // Rat order surface + le
        self.init_fin_sum()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.zero_add / mul_one / one_mul / le_refl
        }

        let name = Name::from_string("BoolAnalysis.hc24_core_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Hc24Consts::new();
        let (ty, value) = build_base(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `hc24_core_base`:
/// `∀ ρ (F : HCPoint 0 → Rat), 3·(ρ·ρ) ≤ 1 → <hc24_core conclusion at n=0>`.
fn build_base(c: &Hc24Consts) -> (Expr, Expr) {
    let zero = c.nat_zero.clone();

    let hyp_ty = |rho: &Expr| {
        // 3·(ρ·ρ) ≤ 1.  (Matches the hc-bounds hypothesis shape.)
        let three = c.o.three();
        let rho_sq = c.mul(rho.clone(), rho.clone());
        c.le(c.mul(three, rho_sq), c.rat_one.clone())
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&zero));
        let h_ty = hyp_ty(&rho);
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = hc24_core_concl(c, &b, &rho, &zero, &f);
        let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&zero), e);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&zero));
        let h_ty = hyp_ty(&rho);
        let (h_id, _h) = b.fresh_local(h_ty.clone());

        let proof = build_base_proof(c, &b, &rho, &f);

        let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
        let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&zero), e);
        let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

include!("boolean_analysis_hc24_core_base_proof.rs");

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc24_core_base_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc24_core_base()
            .expect("init_boolean_analysis_hc24_core_base");
        let name = Name::from_string("BoolAnalysis.hc24_core_base");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc24_core_base proof must check against its type");
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
