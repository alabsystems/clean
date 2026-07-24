// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC normalization — `Rat.powNat_pos`, the STRICT positivity of the
//! `Rat.powNat` recurrence.
//!
//! ```text
//! Rat.powNat_pos : ∀ (b : Rat) (k : Nat), Rat.lt 0 b → Rat.lt 0 (Rat.powNat b k)
//! ```
//!
//! # Why this lemma exists
//!
//! The make-or-break of the dual-HC connect is the cancellation of the common
//! measure factor `8^n = Rat.powNat 8 n` across a `≤`: from
//! `8^n · W^{≤k}[D_i f] ≤ 8^n · ((4·9^k)·r_i)` the connect concludes
//! `W^{≤k}[D_i f] ≤ (4·9^k)·r_i` (the n-FREE per-coordinate bound) via
//! `Rat.le_of_mul_le_mul_left_pos`, which needs the STRICT hypothesis
//! `0 < 8^n`. The `Rat.powNat` ladder already has `Rat.powNat_nonneg`
//! (`0 ≤ b → 0 ≤ b^k`) but NOT the strict `0 < b → 0 < b^k`; this module lands
//! it as a clean, reusable, general-purpose `Rat` lemma.
//!
//! # Proof shape (constructive, empty admitted-axiom closure)
//!
//! `Nat.rec` over `k` with motive `fun k => 0 < powNat b k`:
//! - base `powNat b 0 ≡ 1`, `0 < 1` (`Rat.zero_lt_one`; defeq through the single
//!   ι-step of the `Nat.rec` carrier — no `powNat_zero` rewrite needed);
//! - step `powNat b (k+1) ≡ b·powNat b k`, `Rat.mul_pos b (powNat b k) hb ih`
//!   (again the reduction equation is defeq, so no `powNat_succ` rewrite).
//!
//! Every leaf (`Rat.zero_lt_one`, `Rat.mul_pos`, the `Nat.rec` / `Rat.lt`
//! built-ins) is `Constructive` with empty closure, so this is too. NO axiom is
//! added or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.powNat_pos : ∀ b k, 0 < b → 0 < powNat b k`.
    /// Idempotent; kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub(crate) fn register_rat_pow_nat_pos(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_order_proofs()?; // Rat.mul_pos, Rat.zero_lt_one
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        let name = Name::from_string("Rat.powNat_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (type_, value) = build_pow_nat_pos();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

fn build_pow_nat_pos() -> (Expr, Expr) {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
    let pow_nat = Expr::const_(Name::from_string("Rat.powNat"), vec![]);
    let pow = |b: &Expr, k: &Expr| Expr::apps(pow_nat.clone(), [b.clone(), k.clone()]);
    // `0 < x`.
    let lt0 = |x: Expr| Expr::apps(rat_lt.clone(), [zero.clone(), x]);

    // ── Type: ∀ b k, 0 < b → 0 < powNat b k.
    let ty = {
        let mut bld = EnvDeclBuilder::new();
        let (b_id, bv) = bld.fresh_local(rat.clone());
        let (k_id, k) = bld.fresh_local(nat.clone());
        let hb_ty = lt0(bv.clone());
        let (hb_id, _) = bld.fresh_local(hb_ty.clone());
        let concl = lt0(pow(&bv, &k));
        let e = bld.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
        let e = bld.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
        let e = bld.mk_pi(b_id, BinderInfo::Default, rat.clone(), e);
        bld.finish(e)
    };

    // ── Proof: fun b k hb => Nat.rec base step k.
    let value = {
        let mut bld = EnvDeclBuilder::new();
        let (b_id, bv) = bld.fresh_local(rat.clone());
        let (k_id, k) = bld.fresh_local(nat.clone());
        let hb_ty = lt0(bv.clone());
        let (hb_id, hb) = bld.fresh_local(hb_ty.clone());

        // motive : fun (m : Nat) => 0 < powNat b m   (Sort 0)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bld);
            let (m_id, m) = mb.fresh_local(nat.clone());
            let body = lt0(pow(&bv, &m));
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
        };

        // base : 0 < powNat b 0   (defeq to 0 < 1)
        let base = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);

        // step : fun (m : Nat) (ih : 0 < powNat b m) => mul_pos b (powNat b m) hb ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&bld);
            let (m_id, m) = sb.fresh_local(nat.clone());
            let ih_ty = lt0(pow(&bv, &m));
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            // mul_pos b (powNat b m) hb ih : 0 < b·powNat b m  (defeq 0 < powNat b (m+1))
            let body = Expr::apps(
                Expr::const_(Name::from_string("Rat.mul_pos"), vec![]),
                [bv.clone(), pow(&bv, &m), hb.clone(), ih],
            );
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            sb.finish_child(sb.mk_lam(m_id, BinderInfo::Default, nat.clone(), lam))
        };

        // @Nat.rec.{0} motive base step k
        let rec = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, base, step, k.clone()],
        );

        let e = bld.mk_lam(hb_id, BinderInfo::Default, hb_ty, rec);
        let e = bld.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
        let e = bld.mk_lam(b_id, BinderInfo::Default, rat.clone(), e);
        bld.finish(e)
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
    fn test_pow_nat_pos_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_pos().expect("register");
        env.register_rat_pow_nat_pos().expect("idempotent");
        let name = Name::from_string("Rat.powNat_pos");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("powNat_pos proof must check against its type");
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
