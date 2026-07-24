// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_influence_chain.rs — STEP 1 of the dual-HC
// connect: the `A ↔ FourierCoefficient` representation bridge. Shares
// `InflConsts` + its imports.
//
//   BoolAnalysis.acoeff_eq_pow2_fourier :
//     ∀ (n : Nat) (f : BoolFn n) (S : HCPoint n),
//       @Eq Rat
//         (subsetSum n (fun y => pm (f y) · χ_S y))           -- A(pm∘f, S)
//         (Rat.mul (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)       -- P · f̂(S)
//                  (BoolAnalysis.FourierCoefficient n f S))
//
// i.e. `A(pm∘f, S) = 2^n · f̂(S)`. Both `Expect` and `FourierCoefficient` are
// reducible, so `f̂(S) ≡ A(pm∘f, S)·P⁻¹` DEFINITIONALLY (P := 2^n). The proof is
// the `mul_inv_cancel` un-normalization
//   A = 1·A = (P·P⁻¹)·A = P·(P⁻¹·A) = P·(A·P⁻¹) ≡ P·f̂.
// Constructive, EMPTY admitted-axiom closure. No axiom added or removed.

impl InflConsts {
    /// `Rat.one`.
    fn rat_one_atom(&self) -> Expr {
        self.rat_one.clone()
    }
    /// `Nat` atom.
    fn nat_atom(&self) -> Expr {
        self.nat.clone()
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `acoeff_eq_pow2_fourier`.
fn acoeff_fourier_build(c: &InflConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_atom());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let p = c.cube(&n); // P := 2^n  (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)
    let pinv = c.inv(p.clone()); // P⁻¹
    let pmf = c.pm_f(&b, &n, &f); // pm∘f
    let a = c.amp(&b, &n, &pmf, &s); // A := A(pm∘f, S)
    let fc = c.fcoeff(&n, &f, &s); // f̂(S) ≡ A·P⁻¹ def-eq

    let p_fc = c.mul(p.clone(), fc.clone()); // P · f̂(S)
    let concl = c.eq_rat(a.clone(), p_fc.clone());

    let tail = if for_value {
        let one = c.rat_one_atom();
        // e0 : A = 1·A         [symm (one_mul A)]
        let one_a = c.mul(one.clone(), a.clone());
        let e0 = c.symm(one_a.clone(), a.clone(), c.one_mul(a.clone()));

        // e1 : 1·A = (P·P⁻¹)·A [congrArg (·A) (symm (mul_inv_cancel P))]
        let p_pinv = c.mul(p.clone(), pinv.clone()); // P·P⁻¹
        let mic = c.mul_inv_cancel(p.clone(), c.p_ne_zero(&n)); // P·P⁻¹ = 1
        let mic_sym = c.symm(p_pinv.clone(), one.clone(), mic); // 1 = P·P⁻¹
        let ppinv_a = c.mul(p_pinv.clone(), a.clone()); // (P·P⁻¹)·A
        let e1 = c.mul_right_congr(&b, &a, one.clone(), p_pinv.clone(), mic_sym);

        // e2 : (P·P⁻¹)·A = P·(P⁻¹·A)   [mul_assoc P P⁻¹ A]
        let pinv_a = c.mul(pinv.clone(), a.clone()); // P⁻¹·A
        let p_pinv_a = c.mul(p.clone(), pinv_a.clone()); // P·(P⁻¹·A)
        let e2 = c.assoc(p.clone(), pinv.clone(), a.clone());

        // e3 : P·(P⁻¹·A) = P·(A·P⁻¹)   [congrArg (P·) (mul_comm P⁻¹ A)]
        let a_pinv = c.mul(a.clone(), pinv.clone()); // A·P⁻¹  (≡ f̂ def-eq)
        let cm = c.mul_comm_e(pinv.clone(), a.clone()); // P⁻¹·A = A·P⁻¹
        let e3 = c.mul_left_congr(&b, &p, pinv_a.clone(), a_pinv.clone(), cm);

        // chain: A = 1·A = (P·P⁻¹)·A = P·(P⁻¹·A) = P·(A·P⁻¹) ≡ P·f̂.
        // The endpoint `P·(A·P⁻¹)` is def-eq to `p_fc = P·f̂`, so we state the
        // chain RHS as `p_fc` and the kernel reduces them.
        let t1 = c.trans(a.clone(), one_a.clone(), ppinv_a.clone(), e0, e1);
        let t2 = c.trans(a.clone(), ppinv_a.clone(), p_pinv_a.clone(), t1, e2);
        c.trans(a.clone(), p_pinv_a.clone(), p_fc.clone(), t2, e3)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, s_id, hcp, tail);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, n_id, c.nat_atom(), e);
    b.finish(e)
}

impl Environment {
    /// Register `BoolAnalysis.acoeff_eq_pow2_fourier` — STEP 1 of the dual-HC
    /// connect: `A(pm∘f, S) = 2^n · FourierCoefficient n f S`. Kernel-checked,
    /// `Constructive`, EMPTY admitted-axiom closure. Idempotent.
    pub(crate) fn register_acoeff_eq_pow2_fourier(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.acoeff_eq_pow2_fourier");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // FourierCoefficient, Expect, chi, pm, subsetSum
        self.register_subset_sum()?;
        self.register_expect_one_theorems()?; // natCast_ne_zero_of_pos, one_le_two_pow
        self.init_rat()?; // Rat.inv, Rat.mul_inv_cancel, Rat.one_mul
        self.init_rat_field_inst()?; // Rat.mul_assoc, Rat.mul_comm
        self.init_le()?; // Nat.le.refl/step (for the ≠0 witness leaves)
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: acoeff_fourier_build(&c, false),
            value: acoeff_fourier_build(&c, true),
        })
    }
}

#[cfg(test)]
mod acoeff_fourier_tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_acoeff_eq_pow2_fourier_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_acoeff_eq_pow2_fourier()
            .expect("register_acoeff_eq_pow2_fourier");
        env.register_acoeff_eq_pow2_fourier().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.acoeff_eq_pow2_fourier");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
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
