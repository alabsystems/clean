// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — rung 4: THE CUBE KEYSTONE IDENTITY
//! `NNReal.mul (NNReal.mul (cbrt x)(cbrt x))(cbrt x) = NNReal.ofRat x` on `[0,1)`.
//!
//! Mirrors the sqrt keystone `NNReal.sqrtRat_mul_self` (binary `Quot.sound`),
//! one factor up — the TRIPLE pointwise CauSeq product.
//!
//! # The two rungs
//!
//! - **4a** `NNReal.cbrtDyadicApprox_cube_equiv_const :
//!     ∀ x (h0:0≤x)(h1:x<1),
//!       NNReal.CauSeq.Equiv
//!         (NNReal.CauSeq.mul (NNReal.CauSeq.mul (cbrtSeq x)(cbrtSeq x))(cbrtSeq x))
//!         (NNReal.CauSeq.const (NNRat.ofRat x h0))`
//!   where `cbrtSeq x := NNReal.CauSeq.mk (Rat.cbrtDyadicApproxNN x)
//!   (NNReal.cbrtDyadicApprox_isCauchy x)`. By the `NNRat.val`/`Subtype`/
//!   `NNReal.CauSeq.mul`/`NNReal.CauSeq.const` defeqs, the `Equiv` conjuncts at
//!   index `m` reduce to `a_m³ < x+ε` and `x < a_m³+ε` for
//!   `a_m := Rat.cbrtDyadicApprox x m` (and `a_m³ = (a_m·a_m)·a_m`), built
//!   directly from the cube squeeze bounds.
//!
//!   LOWER conjunct (`a_m³ < x+ε`, all m): `a_m³ ≤ x` (`cbrtDyadicApprox_cube_le`)
//!   `< x+ε`.
//!   UPPER conjunct (`x < a_m³+ε`, for `m ≥ N := M+3` from
//!   `exists_inv_two_pow_lt ε ↦ M`): `x < a_m³ + (3iv+(3iv+iv))`
//!   (`x_lt_cbrtDyadicApprox_cube_add_seven_inv`) and `(3iv+(3iv+iv)) < ε`
//!   (telescoped: `7·inv(2^m) ≤ 8·inv(2^{M+3}) = inv(2^M) < ε`).
//!
//! - **4b** `NNReal.cbrt_cubed :
//!     ∀ x (h0:0≤x)(h1:x<1),
//!       NNReal.mul (NNReal.mul (cbrt x)(cbrt x))(cbrt x) = NNReal.ofRat x h0`.
//!   `NNReal.mul (NNReal.mk s)(NNReal.mk s)` ι-reduces (binary `Quot.lift`) to
//!   `NNReal.mk (CauSeq.mul s s)`, and once more to
//!   `NNReal.mk (CauSeq.mul (CauSeq.mul s s) s)`; the RHS
//!   `NNReal.ofRat x h0 = NNReal.mk (CauSeq.const (NNRat.ofRat x h0))`, so the
//!   goal is `Quot.sound` applied to rung 4a.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, closure ⊆
//! `{Quot.sound, propext, Classical.choice}` ∪ Eq builtins (all foundational →
//! `axiom_deps` filters them out, so the reported closure is empty). NO `sorry`
//! / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

mod equiv;

/// Pre-resolved handles for the cube identity rung.
pub(crate) struct CbrtIdentityConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_cbrt_approx: Expr,
    // Rat order bricks.
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_lt_of_lt_of_le: Expr,
    rat_lt_trans: Expr,
    rat_le_trans: Expr,
    rat_add_le_add: Expr,
    rat_add_le_add_left: Expr,
    rat_add_assoc: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_le_refl: Expr,
    rat_eq_subst1: Expr,
    rat_eq_symm1: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    // squeeze lemmas.
    cube_le: Expr,
    x_lt_cube_add: Expr,
    // modulus + telescoping.
    exists_inv_two_pow_lt: Expr,
    inv_two_pow_le_of_le: Expr,
    inv_two_pow_succ_add_self: Expr,
    // carrier.
    nnrat: Expr,
    nnrat_of_rat: Expr,
    nnreal: Expr,
    causeq: Expr,
    causeq_mk: Expr,
    causeq_mul: Expr,
    causeq_const: Expr,
    causeq_equiv: Expr,
    cbrt_approxnn: Expr,
    cbrt_iscauchy: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_cbrt: Expr,
    quot_sound: Expr,
    // logic.
    and_c: Expr,
    and_intro: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
}

impl CbrtIdentityConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_le: k("Nat.le"),
            nat_le_refl: k("Nat.le.refl"),
            nat_le_step: k("Nat.le.step"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_cbrt_approx: k("Rat.cbrtDyadicApprox"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_lt_trans: k("Rat.lt_trans"),
            rat_le_trans: k("Rat.le_trans"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_add_le_add_left: k("Rat.add_le_add_left"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_le_refl: k("Rat.le_refl"),
            rat_eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            rat_eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            cube_le: k("Rat.cbrtDyadicApprox_cube_le"),
            x_lt_cube_add: k("Rat.x_lt_cbrtDyadicApprox_cube_add_seven_inv"),
            exists_inv_two_pow_lt: k("Rat.exists_inv_two_pow_lt"),
            inv_two_pow_le_of_le: k("Rat.inv_two_pow_le_of_le"),
            inv_two_pow_succ_add_self: k("Rat.inv_two_pow_succ_add_self"),
            nnrat: k("NNRat"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnreal: k("NNReal"),
            causeq: k("NNReal.CauSeq"),
            causeq_mk: k("NNReal.CauSeq.mk"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_const: k("NNReal.CauSeq.const"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            cbrt_approxnn: k("Rat.cbrtDyadicApproxNN"),
            cbrt_iscauchy: k("NNReal.cbrtDyadicApprox_isCauchy"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_cbrt: k("NNReal.cbrt"),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1]),
        }
    }

    // ── small constructors ──
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(
            self.nat_pow.clone(),
            [self.succ(self.succ(self.nat_zero.clone())), n],
        )
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn inv_two_pow(&self, n: Expr) -> Expr {
        self.inv(self.ofnat(self.npow2(n)))
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_approx.clone(), [x.clone(), n])
    }
    /// `(a·a)·a` (the left-nested cube form).
    fn cube(&self, a: Expr) -> Expr {
        let sq = self.mul(a.clone(), a.clone());
        self.mul(sq, a)
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, c, h1, h2])
    }
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, c, h1, h2])
    }
    fn lt_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_trans.clone(), [a, b, c, h1, h2])
    }
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, c, h1, h2])
    }
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn inv_le_of_le(&self, big_n: Expr, n: Expr, h: Expr) -> Expr {
        Expr::apps(self.inv_two_pow_le_of_le.clone(), [big_n, n, h])
    }
    /// `inv_two_pow_succ_add_self k : inv(2^{k+1})+inv(2^{k+1}) = inv(2^k)`.
    fn succ_add_self(&self, k: Expr) -> Expr {
        Expr::app(self.inv_two_pow_succ_add_self.clone(), k)
    }
    /// `Rat.add_le_add_left : ∀ a b, a≤b → ∀ c, (c+a) ≤ (c+b)` — binder order
    /// `a b (h:a≤b) c`.
    fn add_le_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add_left.clone(), [a, b, h, cc])
    }
    /// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, c])
    }
    /// `0 ≤ inv(2^n)` from `0 < inv(2^n)` (lt_iff_le_not_le + And.left).
    fn zero_le_inv_two_pow(&self, n: Expr) -> Expr {
        let iv = self.inv_two_pow(n.clone());
        let hpos = Expr::app(self.rat_zero_lt_inv_two_pow.clone(), n);
        let le0a = self.le(self.rat_zero.clone(), iv.clone());
        let not_le = Expr::app(
            self.not_c.clone(),
            self.le(iv.clone(), self.rat_zero.clone()),
        );
        let and_ty = self.and_ty(le0a.clone(), not_le.clone());
        let lt0a = self.lt(self.rat_zero.clone(), iv.clone());
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), iv],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt0a, and_ty, iff, hpos]);
        Expr::apps(self.and_left.clone(), [le0a, not_le, mp])
    }

    /// The Cauchy sequence carrier underneath `NNReal.cbrt x`:
    /// `NNReal.CauSeq.mk (cbrtDyadicApproxNN x)(cbrtDyadicApprox_isCauchy x)`.
    fn cbrt_seq(&self, x: &Expr) -> Expr {
        let seq = Expr::app(self.cbrt_approxnn.clone(), x.clone());
        let hcau = Expr::app(self.cbrt_iscauchy.clone(), x.clone());
        Expr::apps(self.causeq_mk.clone(), [seq, hcau])
    }
    /// `NNReal.CauSeq.mul (NNReal.CauSeq.mul (cbrtSeq x)(cbrtSeq x))(cbrtSeq x)`.
    fn cmul3(&self, x: &Expr) -> Expr {
        let s = self.cbrt_seq(x);
        let s2 = Expr::apps(self.causeq_mul.clone(), [s.clone(), s.clone()]);
        Expr::apps(self.causeq_mul.clone(), [s2, s])
    }
    /// `NNReal.CauSeq.const (NNRat.ofRat x h0)`.
    fn cconst(&self, x: &Expr, h0: &Expr) -> Expr {
        let q = Expr::apps(self.nnrat_of_rat.clone(), [x.clone(), h0.clone()]);
        Expr::app(self.causeq_const.clone(), q)
    }
    /// `NNReal.CauSeq.Equiv f g`.
    fn equiv(&self, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [f, g])
    }
}

impl Environment {
    /// Register rung 4a (`NNReal.cbrtDyadicApprox_cube_equiv_const`) and rung 4b
    /// (`NNReal.cbrt_cubed`). Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_cbrt_identity(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_exists()?;
        self.init_nat()?;
        self.init_nat_succ_base()?; // Nat.le.refl, Nat.le.step
        self.init_quot(); // Quot.sound
                          // carrier + cbrt + mul + ofRat.
        self.init_algebra_nnreal_cbrt_def()?; // NNReal.cbrt, cbrtSeq pieces
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, NNReal.CauSeq.mul
                                              // squeeze bounds (cube_le, x_lt_cube_add).
        self.init_algebra_nnreal_cbrt_squeeze()?;
        // modulus + telescoping.
        self.init_algebra_rat_inv_dyadic_modulus()?; // exists_inv_two_pow_lt
        self.init_algebra_nnreal_sqrt_cauchy()?; // inv_two_pow_le_of_le
        self.init_algebra_nnreal_sqrt_cauchy_double()?; // inv_two_pow_succ_add_self
                                                        // Rat order toolkit used in the assembly.
        self.register_rat_add_lt_add_left()?; // add_lt_add_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.init_rat_linear_order()?; // le_trans, le_refl, lt_trans
        self.register_rat_add_le_add()?; // add_le_add

        let c = CbrtIdentityConsts::new();
        self.register_cbrt_cube_equiv_const(&c)?;
        self.register_cbrt_cubed(&c)?;
        Ok(())
    }

    /// Rung 4b — `NNReal.cbrt_cubed`.
    fn register_cbrt_cubed(&mut self, c: &CbrtIdentityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cbrt_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let equiv_thm = Expr::const_(
            Name::from_string("NNReal.cbrtDyadicApprox_cube_equiv_const"),
            vec![],
        );
        let eq_nn = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [c.nnreal.clone(), a, b],
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let cx = Expr::app(c.nnreal_cbrt.clone(), x.clone());
            let cx2 = Expr::apps(c.nnreal_mul.clone(), [cx.clone(), cx.clone()]);
            let lhs = Expr::apps(c.nnreal_mul.clone(), [cx2, cx]);
            let rhs = Expr::apps(c.nnreal_of_rat.clone(), [x.clone(), h0.clone()]);
            let concl = eq_nn(lhs, rhs);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());

            // h_equiv : Equiv (cmul3 x)(cconst x h0).
            let h_equiv = Expr::apps(equiv_thm.clone(), [x.clone(), h0.clone(), h1.clone()]);
            // Quot.sound (cmul3 x)(cconst x h0) h_equiv :
            //   Quot.mk Equiv (cmul3 x) = Quot.mk Equiv (cconst x h0).
            //   LHS defeq NNReal.mul (NNReal.mul (cbrt x)(cbrt x))(cbrt x);
            //   RHS defeq NNReal.ofRat x h0.
            let body = Expr::apps(
                c.quot_sound.clone(),
                [
                    c.causeq.clone(),
                    c.causeq_equiv.clone(),
                    c.cmul3(&x),
                    c.cconst(&x, &h0),
                    h_equiv,
                ],
            );
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, body);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.cbrtDyadicApprox_cube_equiv_const",
        "NNReal.cbrt_cubed",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_identity()
            .expect("init_algebra_nnreal_cbrt_identity");
        env.init_algebra_nnreal_cbrt_identity().expect("idempotent");
        env
    }

    #[test]
    fn test_cbrt_identity_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_cbrt_identity_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
