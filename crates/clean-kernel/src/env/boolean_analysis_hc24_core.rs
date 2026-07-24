// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — `hc24_core`, the (2,4)-hypercontractivity operator
//! bound, assembled by `Nat.rec` from the base case (`hc24_core_base`) and the
//! induction step (`hc24_core_step`).
//!
//! ```text
//! BoolAnalysis.hc24_core :
//!   ∀ (ρ : Rat) (n : Nat) (F : HCPoint n → Rat),
//!     3·(ρ·ρ) ≤ 1 →
//!       Σ_{2^n} pow4(noiseFn ρ n F jx)
//!         ≤ (Rat.powNat 8 n) · sq(Σ_{2^n} sq(F (hcDecode n jx)))
//! ```
//!
//! ## Assembly
//!
//! `ρ`, `n`, `F`, `h : 3·(ρ·ρ) ≤ 1` are bound; then `Nat.rec` with motive
//! `fun m => ∀ (F' : HCPoint m → Rat), <concl m F'>` (F universally quantified
//! INSIDE the recursion, so the step can instantiate it at both `gPart n F` and
//! `liftH n F`):
//!
//! - base `fun F' => hc24_core_base ρ F' h : ∀ F', concl 0 F'`,
//! - step `fun m ih => hc24_core_step ρ m h ih : ∀ m, (∀F', concl m F') →
//!   ∀ F', concl (m+1) F'`.
//!
//! `(Nat.rec motive base step n) F : concl n F` is the body. The captured `h`
//! (type `3·(ρ·ρ)≤1`, independent of `n`/`F`) feeds both minor premises.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! the only leaves are `hc24_core_base`, `hc24_core_step` (both Constructive)
//! and `Nat.rec`.

use super::boolean_analysis_hc24_core_base::{hc24_core_concl, Hc24Consts};
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `BoolAnalysis.hc24_core` — the full (2,4)-hypercontractivity
    /// operator induction. Idempotent; axiom-free.
    pub fn init_boolean_analysis_hc24_core(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_hc24_core_base()?; // hc24_core_base (+ statement builder deps)
        self.register_hc24_core_step()?; // hc24_core_step

        let name = Name::from_string("BoolAnalysis.hc24_core");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Hc24Consts::new();
        let (type_, value) = build_hc24_core(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// `3·(ρ·ρ) ≤ 1` (matches base / step / concl hypothesis).
fn hyp_ty(c: &Hc24Consts, rho: &Expr) -> Expr {
    let three = c.o.three();
    let rho_sq = c.mul(rho.clone(), rho.clone());
    c.le(c.mul(three, rho_sq), c.rat_one.clone())
}

/// `f_type m := HCPoint m → Rat`.
fn build_hc24_core(c: &Hc24Consts) -> (Expr, Expr) {
    let nat = c.nat.clone();

    // motive(parent, rho) := fun (m : Nat) => ∀ (F' : HCPoint m → Rat), concl m F'.
    let motive = |parent: &EnvDeclBuilder, rho: &Expr| -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = mb.fresh_local(nat.clone());
        let body = {
            let mut fb = EnvDeclBuilder::child_of(&mb);
            let (fp_id, fp) = fb.fresh_local(c.f_type(&m));
            let concl = hc24_core_concl(c, &fb, rho, &m, &fp);
            fb.finish_child(fb.mk_pi(fp_id, BinderInfo::Default, c.f_type(&m), concl))
        };
        mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
    };

    // ── Type: ∀ ρ n (F : HCPoint n → Rat), hyp → concl n F.
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (n_id, n) = b.fresh_local(nat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&n));
        let h_ty = hyp_ty(c, &rho);
        let (h_id, _) = b.fresh_local(h_ty.clone());
        let concl = hc24_core_concl(c, &b, &rho, &n, &f);
        let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    // ── Proof: fun ρ n F h => (Nat.rec motive base step n) F.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (n_id, n) = b.fresh_local(nat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&n));
        let h_ty = hyp_ty(c, &rho);
        let (h_id, h) = b.fresh_local(h_ty.clone());

        let base_const = Expr::const_(Name::from_string("BoolAnalysis.hc24_core_base"), vec![]);
        let step_const = Expr::const_(Name::from_string("BoolAnalysis.hc24_core_step"), vec![]);
        let zero = c.nat_zero.clone();

        // base : ∀ (F' : HCPoint 0 → Rat), concl 0 F'  := fun F' => hc24_core_base ρ F' h
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&b);
            let (fp_id, fp) = bb.fresh_local(c.f_type(&zero));
            let body = Expr::apps(base_const, [rho.clone(), fp.clone(), h.clone()]);
            bb.finish_child(bb.mk_lam(fp_id, BinderInfo::Default, c.f_type(&zero), body))
        };

        // step : ∀ (m : Nat), (∀F', concl m F') → ∀F', concl (m+1) F'
        //   := fun m ih => hc24_core_step ρ m h ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (m_id, m) = sb.fresh_local(nat.clone());
            // ih type = motive m = ∀ F', concl m F'
            let ih_ty = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (fp_id, fp) = ib.fresh_local(c.f_type(&m));
                let concl = hc24_core_concl(c, &ib, &rho, &m, &fp);
                ib.finish_child(ib.mk_pi(fp_id, BinderInfo::Default, c.f_type(&m), concl))
            };
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            let body = Expr::apps(step_const, [rho.clone(), m.clone(), h.clone(), ih]);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            sb.finish_child(sb.mk_lam(m_id, BinderInfo::Default, nat.clone(), lam))
        };

        // @Nat.rec.{1} motive base step n : motive n = ∀ F', concl n F'
        let mtv = motive(&b, &rho);
        let rec = Expr::apps(
            Expr::const_(
                Name::from_string("Nat.rec"),
                vec![crate::level::Level::zero()],
            ),
            [mtv, base, step, n.clone()],
        );
        // apply to F : concl n F
        let body = Expr::app(rec, f.clone());

        let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
        let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc24_core_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc24_core()
            .expect("init_boolean_analysis_hc24_core");
        env.init_boolean_analysis_hc24_core().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc24_core");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc24_core proof must check against its type");
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
