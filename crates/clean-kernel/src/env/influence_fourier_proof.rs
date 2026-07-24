// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive support lemmas toward the `influence_fourier` discharge
//! (`Inf_i[f] = Σ_{S∋i} f̂(S)²`, O'Donnell Thm. 2.20).
//!
//! `Influence n f i = Expect n (fun x => ind (Bool.not (Bool.beq (f x) (f (hcFlip n x i)))))`.
//! The spectral route rewrites the pointwise disagreement indicator as a
//! squared discrete derivative and expands both points in the Fourier basis.
//!
//! This module lands the self-contained, axiom-free pieces of that route:
//!
//! - `BoolAnalysis.disagree_sq_bridge : ∀ (a b : Bool),
//!     Rat.mul 4 (ind (Bool.not (Bool.beq a b)))
//!       = Rat.mul (Rat.sub (pm a) (pm b)) (Rat.sub (pm a) (pm b))`
//!   — the 2×2 Bool identity `4·[a≠b] = (pm a − pm b)²`. Division-free (the
//!     downstream square-and-Expect step multiplies by 4 anyway), so each of the
//!     four `Bool.rec` leaves is a CLOSED Rat-numeral identity. `pm` and `ind`
//!     reduce on concrete bools, `Bool.beq`/`Bool.not` reduce natively.
//!
//! x-SIDE PARSEVAL pieces (see `boolean_analysis_chi_xside_proof`): the influence
//! discharge applies the x-side core `Σ_x (Σ_S a(S)·χ_S(x))² = 2^n·Σ_S a(S)²`,
//! whose inner collapse `Σ_x χ_S(x)·χ_T(x)` is character orthonormality. The
//! GENERAL (coordinate-agnostic) orthonormality is now LANDED in numerator form:
//!   • `chi_diag_subsetSum_cube` — DIAGONAL `Σ_x χ_S(x)² = 2^n`;
//!   • `chi_offdiag_subsetSum_zero` — OFF-DIAGONAL `Σ_x χ_{hcDecode jS}·χ_{hcDecode jT} = 0`
//!     for ANY distinct decoded gates `jS ≠ jT` (no top-coordinate restriction).
//!
//! Both are read off the SIGN-side bilinear `subsetSum_chi_sign_bilinear`
//! (`Σ_x χ_S(x)·χ_T(x) = Π_i (1 + pm(S i)·pm(T i))`, the coordinate-agnostic dual
//! of `subsetSum_chi_bilinear`) composed with the EXISTING Kronecker product
//! collapse `prod_diag_eq_cube` / `prod_offdiag_eq_zero`. This removes the former
//! residual (the top-coordinate-only `chi_expect_zero` / `chi_offdiag_numerator_zero`
//! could not reach arbitrary present coordinates).
//!
//! The x-side Parseval CORE is now LANDED and kernel-checked:
//!   `BoolAnalysis.subsetSum_xside_core :`
//!   `  Σ_x (Σ_S a(S)·χ_S(x))² = 2^n · Σ_S a(S)²`
//! (`boolean_analysis_xside_core`, the dual of `subsetSum_parseval_core`).
//!
//! HISTORICAL (the discharge is now COMPLETE — see "RETIRED" below). The
//! assembly is: (1) flip-difference per decoded point
//! `Σ_S (2·ind(S i)·A_S)·χ_S(x) = 2^n·(pm(f x) − pm(f(hcFlip n x i)))`
//! (`A_S := subsetSum n (fun y => pm(f y)·χ_S(y)) = 2^n·f̂(S)`), via
//! `flip_coeff_absorb` + `chi_flip_spectral` + the two inversions; (2) square +
//! sum over `x` via `subsetSum_xside_core` at `a(S) = 2·ind(S i)·A_S`
//! (`ind²=ind`); (3) `disagree_sq_bridge` + the `Expect = subsetSum/2^n`
//! normalization, landing `Influence n f i = Σ_{S∋i} f̂(S)²`.
//!
//! The step-1 SECOND term (`subsetSum_inversion_core` at the FLIPPED point) was
//! the former blocker, RESOLVED via the `hcEncode`/XOR roundtrip route (a).
//! `Σ_S A_S·χ_S(hcFlip n x i)` is `subsetSum_inversion_core` evaluated AT THE
//! FLIPPED POINT `hcFlip n x i`, which only holds at DECODED points. Route (a)
//! (the `hcEncode`/XOR roundtrip) is now LANDED in
//! `boolean_analysis_flip_roundtrip_proof.rs` (all `ProofQuality::Constructive`,
//! empty admitted-axiom closure):
//!
//!   • `Nat.testBit_two_pow : testBit (2^i) j = Nat.beq j i` (constructive
//!     trichotomy, NOT the admitted `Nat.lt_trichotomy`);
//!   • `Nat.lt_two_pow_of_testBit_ge` (bits-determine-bound) +
//!     `Nat.lt_two_pow_xor_two_pow : a<2^n → i<n → xor a (2^i) < 2^n`;
//!   • `BoolAnalysis.flipIdx n i jx := Fin.mk (2^n) (xor (val jx) (2^(val i))) …`
//!     — names the Fin index of the flipped point;
//!   • `BoolAnalysis.hcFlip_decode_roundtrip :
//!       hcDecode n (flipIdx n i jx) = hcFlip n (hcDecode n jx) i`
//!     (funext; per-coordinate `testBit_xor ; testBit_two_pow ; xor_eq_cond`);
//!   • `BoolAnalysis.subsetSum_inversion_core_flip` — inversion AT THE FLIPPED
//!     POINT, i.e. `subsetSum_inversion_core n b (flipIdx n i jx)` transported
//!     along the roundtrip. THIS is exactly the second term, now reducible to
//!     `2^n·pm(f(hcFlip n x i))`.
//!
//! RETIRED. The assembly above is now LANDED — `influence_fourier` is a
//! kernel-CHECKED constructive `Declaration::Theorem` (census 39→38, see
//! `register_influence_fourier`). The full chain lives in
//! `boolean_analysis_influence_chain.rs` (leg/chain style mirroring
//! `boolean_analysis_xside_core_chain.rs`):
//!   1. `subsetSum_flip_spectral_split` — gate-sum flip difference at a sign
//!      point (`flip_coeff_absorb` + `chi_flip_spectral` + `subsetSum_sub`);
//!   2. `subsetSum_flip_diff_decoded` — inversion-glued (`subsetSum_inversion_core`
//!      at jx + `subsetSum_inversion_core_flip` at the flipped point);
//!   3. `subsetSum_influence_master` — `subsetSum_xside_core` at `a(S) =
//!      2·ind(S i)·A_S`, squared via `Fin.sum_congr` over the decoded cube;
//!   4. `subsetSum_disagree_side` / `subsetSum_coeff_side` — `disagree_sq_bridge`
//!      + `ind_mul_self` (`ind²=ind`) un-normalized bridges;
//!   5. `subsetSum_influence_unnorm` — `2^n·Σ_x ind(disagree) = Σ_S ind(S i)·A_S²`
//!      by cancelling `2^n·4` (multiplicative, no division);
//!   6. the `Expect=Σ/2^n` + `f̂=A_S/2^n` normalization lands the registered
//!      `influence_fourier_helper` form `Influence n f i = Σ_{S∋i} f̂(S)²`.
//!
//! Empty admitted-axiom closure (`ProofQuality::Constructive`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `BoolAnalysis.disagree_sq_bridge :
    ///   ∀ (a b : Bool), Rat.mul 4 (ind (Bool.not (Bool.beq a b)))
    ///     = Rat.mul (Rat.sub (pm a) (pm b)) (Rat.sub (pm a) (pm b))`
    /// as a kernel-checked, constructive theorem. Idempotent.
    ///
    /// `Bool.rec` on `a` then `b` (four leaves). Each leaf is a closed Rat
    /// identity that ground-reduces:
    ///   * `(true,true)/(false,false)`: `4·0 = 0` and `(pm a − pm a)² = 0`.
    ///   * `(true,false)`: `4·1 = 4` and `((−1) − 1)² = (−2)² = 4`.
    ///   * `(false,true)`: `4·1 = 4` and `(1 − (−1))² = 2² = 4`.
    ///
    /// Closed by `@Eq.refl Rat <LHS>` per leaf (native Rat reducers normalize
    /// both sides to the same `Rat.mk` numeral).
    pub(crate) fn register_disagree_sq_bridge(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.disagree_sq_bridge");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_beq()?; // Bool.beq
        self.init_boolean_analysis()?; // ind, pm, Rat foundations

        // `init_boolean_analysis` now re-enters the full influence_fourier
        // assembly (which registers this lemma); re-check before re-declaring.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let one = Level::succ(Level::zero());
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let bool_beq = Expr::const_(Name::from_string("Bool.beq"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![one]);
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        // `4/1 : Rat`.
        let four = {
            let mut n = nat_zero.clone();
            for _ in 0..4 {
                n = Expr::app(nat_succ.clone(), n);
            }
            let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
            Expr::apps(rat_mk.clone(), [Expr::app(int_of_nat.clone(), n), one_nat])
        };

        // lhs(a,b) = Rat.mul 4 (ind (Bool.not (Bool.beq a b)))
        let lhs = |a: Expr, b: Expr| {
            let beq = Expr::apps(bool_beq.clone(), [a, b]);
            let not_beq = Expr::app(bool_not.clone(), beq);
            let ind_term = Expr::app(ind.clone(), not_beq);
            Expr::apps(rat_mul.clone(), [four.clone(), ind_term])
        };
        // rhs(a,b) = Rat.mul (Rat.sub (pm a)(pm b)) (Rat.sub (pm a)(pm b))
        let rhs = |a: Expr, b: Expr| {
            let diff = Expr::apps(
                rat_sub.clone(),
                [Expr::app(pm.clone(), a), Expr::app(pm.clone(), b)],
            );
            Expr::apps(rat_mul.clone(), [diff.clone(), diff])
        };
        let eqn = |l: Expr, r: Expr| Expr::apps(eq_rat.clone(), [rat.clone(), l, r]);

        // Type: ∀ (a b : Bool), lhs a b = rhs a b
        let type_ = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, a) = bld.fresh_local(bool_c.clone());
            let (b_id, b) = bld.fresh_local(bool_c.clone());
            let concl = eqn(lhs(a.clone(), b.clone()), rhs(a.clone(), b.clone()));
            let e = bld.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl);
            let e = bld.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            bld.finish(e)
        };

        // value: fun (a b : Bool) => Bool.rec (motive_a) <a=false> <a=true> a
        // each inner case splits on b and emits @Eq.refl Rat (lhs a b)
        // (lhs a b ≡ rhs a b by ground Rat reduction).
        let value = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, a) = bld.fresh_local(bool_c.clone());
            let (b_id, b) = bld.fresh_local(bool_c.clone());

            // motive_a : fun (a' : Bool) => lhs a' b = rhs a' b
            let motive_a = {
                let mut d = EnvDeclBuilder::child_of(&bld);
                let (ap_id, ap) = d.fresh_local(bool_c.clone());
                let body = eqn(lhs(ap.clone(), b.clone()), rhs(ap.clone(), b.clone()));
                d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), body))
            };

            // For a fixed concrete `av`, split on `b` and emit Eq.refl leaves.
            let inner_rec = |av: Expr, parent: &EnvDeclBuilder| {
                let mut d = EnvDeclBuilder::child_of(parent);
                // motive_b : fun (b' : Bool) => lhs av b' = rhs av b'
                let motive_b = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (bp_id, bp) = e.fresh_local(bool_c.clone());
                    let body = eqn(lhs(av.clone(), bp.clone()), rhs(av.clone(), bp.clone()));
                    e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let leaf =
                    |bv: Expr| Expr::apps(eq_refl.clone(), [rat.clone(), lhs(av.clone(), bv)]);
                let b_false = leaf(bfalse.clone());
                let b_true = leaf(btrue.clone());
                let e = Expr::apps(bool_rec0.clone(), [motive_b, b_false, b_true, b.clone()]);
                d.finish_child(e)
            };

            let a_false_case = inner_rec(bfalse.clone(), &bld);
            let a_true_case = inner_rec(btrue.clone(), &bld);

            let rec_a = Expr::apps(
                bool_rec0.clone(),
                [motive_a, a_false_case, a_true_case, a.clone()],
            );
            let e = bld.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_a);
            let e = bld.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
            bld.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_disagree_sq_bridge_is_constructive() {
        let mut env = Environment::new();
        env.register_disagree_sq_bridge()
            .expect("first registration");
        env.register_disagree_sq_bridge().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.disagree_sq_bridge");
        let info = env.get_const(&name).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("disagree_sq_bridge must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "disagree_sq_bridge must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }
}
