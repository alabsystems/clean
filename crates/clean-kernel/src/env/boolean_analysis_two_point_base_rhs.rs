// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami dual `(4/3, 4)` two-point base — STEP 3, the RHS-cube scalar pull
//! `NNReal.cube_mul`, and the STEP-4 PIN (`BoolAnalysis.two_point_base_43`,
//! stated + the exact analytic residual isolated).
//!
//! # The RHS of the two-point base
//!
//! With `P := |a+b|`, `Q := |a−b|`, `α := P^{4/3} = pow43Gen(P …)`,
//! `β := Q^{4/3} = pow43Gen(Q …)`, the RHS is
//!
//! ```text
//!   (½·(α + β))³.
//! ```
//!
//! # STEP 3 — the part that CLOSES axiom-free: `NNReal.cube_mul`
//!
//! ```text
//!   NNReal.cube_mul : ∀ c x : NNReal,
//!     ((c·x)·(c·x))·(c·x) = ((c·c)·c)·((x·x)·x).
//! ```
//!
//! i.e. `(c·x)³ = c³·x³` — the SCALAR PULL that turns the RHS into
//! `(½)³·(α+β)³ = ⅛·(α+β)³`. It is the SAME `mul_mul_mul_comm` regroup the
//! landed `NNReal.pow43_cubed` / `cbrtGen_cubed` use for the `(A·C)³` step, so it
//! closes with the EXISTING carrier multiplicative algebra (no `add_comm`/
//! `add_assoc` needed). `Declaration::Theorem`, `ProofQuality::Constructive`,
//! empty admitted-axiom closure.
//!
//! Combined with the LANDED `NNReal.pow43Gen_cubed` (`(x^{4/3})³ = x⁴`), the two
//! RATIONAL CORNERS of the expanded cube are pinned: `α³ = P⁴ = (a+b)⁴` and
//! `β³ = Q⁴ = (a−b)⁴` are PURE RATIONALS.
//!
//! # STEP 4 — the PIN: `BoolAnalysis.two_point_base_43` (stated, NOT faked)
//!
//! The two-point base is the NNReal inequality
//!
//! ```text
//!   NNReal.le
//!     (ofRat (a⁴ + (2/3)·a²b² + (1/81)·b⁴) hm)        -- = ½·[(a+b/3)⁴+(a−b/3)⁴]
//!     ((½·(α + β))³).
//! ```
//!
//! Its well-formed TYPE is constructed and kernel-typechecked by the test
//! `pin_two_point_base_43_typechecks` (it is a genuine `Prop`). It is NOT
//! registered with a proof: the proof reduces to the genuine ANALYTIC CRUX
//! (documented in the module test + the agent report), which AM-GM does NOT
//! close. No Axiom, no refl-over-circular-def is registered.
//!
//! ## The exact residual (after pulling out the rationals)
//!
//! Expanding `(½(α+β))³ = ⅛·(α+β)³ = ⅛·(α³ + 3α²β + 3αβ² + β³)` (the `cube_of_sum`
//! collection — the A1 sub-build still pending `NNReal.add_comm`/`add_assoc`),
//! and using `α³ = (a+b)⁴`, `β³ = (a−b)⁴`, `α²β = (P²Q)^{4/3} = pow43Gen(P²·Q …)`,
//! `αβ² = (P Q²)^{4/3} = pow43Gen(P·Q² …)`, the rational corners contribute
//! `⅛·[(a+b)⁴ + (a−b)⁴] = ¼·[a⁴ + 6a²b² + b⁴]`. Subtracting the rational LHS
//! `a⁴ + (2/3)a²b² + (1/81)b⁴` leaves the RESIDUAL inequality
//!
//! ```text
//!   ⅜·[ (P²Q)^{4/3} + (P Q²)^{4/3} ]  ≥  (3/4)·a⁴ − (5/6)·a²b² − (77/324)·b⁴.
//! ```
//!
//! This is the genuine hard analytic content: the cross terms `(P²Q)^{4/3}`,
//! `(P Q²)^{4/3}` are SINGLE `4/3`-powers of nonneg-Rat products (`pow43Gen`
//! handles their VALUES and their cubes), but the INEQUALITY needs their true
//! magnitudes — AM-GM (`cross ≥ 2P²Q²`) is provably TOO WEAK for large `a`. See
//! the agent report for the recommended next attack (1-variable reduction
//! `t = b/a`, tangent-line/convexity bound on `cbrt`).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached carrier atoms + smart-constructors for `cube_mul`.
struct CubeMulConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_mmm_comm: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl CubeMulConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn refl(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    fn trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                h1,
                h2,
            ],
        )
    }
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmm(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mmm_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `a·p = a·q` from `h : p = q`.
    #[cfg(test)]
    fn cong_mul_right(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        p: &Expr,
        q: &Expr,
        h: Expr,
    ) -> Expr {
        let ap = self.mul(a, p);
        let motive = {
            let mut mm = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = mm.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&ap, &self.mul(a, &t));
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst(motive, p, q, h, self.refl(&ap))
    }
    /// `p·a = q·a` from `h : p = q`.
    fn cong_mul_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        a: &Expr,
        h: Expr,
    ) -> Expr {
        let pa = self.mul(p, a);
        let motive = {
            let mut mm = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = mm.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&pa, &self.mul(&t, a));
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst(motive, p, q, h, self.refl(&pa))
    }
}

impl Environment {
    /// Register `NNReal.cube_mul` (the RHS scalar-pull). Reuses the landed
    /// `NNReal.mul_mul_mul_comm`. Idempotent; foundational-only closure.
    pub fn init_boolean_analysis_two_point_base_rhs(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_pow43_cubed()?; // NNReal.mul_mul_mul_comm
        self.init_algebra_nnreal_add_mul()?; // NNReal.add_mul (A1 partial) + carrier mul algebra
        self.init_eq()?;

        let c = CubeMulConsts::new();
        self.register_nnreal_cube_mul(&c)?;
        Ok(())
    }

    /// `NNReal.cube_mul : ∀ c x : NNReal,
    ///   ((c·x)·(c·x))·(c·x) = ((c·c)·c)·((x·x)·x)`   — i.e. `(c·x)³ = c³·x³`.
    fn register_nnreal_cube_mul(&mut self, c: &CubeMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cv_id, cv) = b.fresh_local(c.nnreal.clone());
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let cx = c.mul(&cv, &x);
            let lhs = c.mul(&c.mul(&cx, &cx), &cx);
            let ccc = c.mul(&c.mul(&cv, &cv), &cv);
            let xxx = c.mul(&c.mul(&x, &x), &x);
            let rhs = c.mul(&ccc, &xxx);
            let concl = c.eq_nn(&lhs, &rhs);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_cube_mul_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `(c·x)³ = c³·x³` via the SAME regroup as `pow43_cubed`'s `(A·C)³` step:
///   `((c·x)·(c·x))·(c·x)`
///     =[cong_left  (mmm c x c x)]  `((c·c)·(x·x))·(c·x)`
///     =[mmm (c·c) (x·x) c x]       `((c·c)·c)·((x·x)·x)`.
fn build_cube_mul_value(c: &CubeMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(c.nnreal.clone());
    let (x_id, x) = b.fresh_local(c.nnreal.clone());

    let cx = c.mul(&cv, &x); // c·x
    let lhs = c.mul(&c.mul(&cx, &cx), &cx); // ((c·x)·(c·x))·(c·x)

    let cc = c.mul(&cv, &cv); // c·c
    let xx = c.mul(&x, &x); // x·x
    let cxcx = c.mul(&cx, &cx); // (c·x)·(c·x)
    let ccxx = c.mul(&cc, &xx); // (c·c)·(x·x)
    let i1 = c.mmm(&cv, &x, &cv, &x); // (c·x)·(c·x) = (c·c)·(x·x)
    let ccxx_cx = c.mul(&ccxx, &cx); // ((c·c)·(x·x))·(c·x)
                                     // left rewrite: ((c·x)·(c·x))·(c·x) = ((c·c)·(x·x))·(c·x).
    let left_rw = c.cong_mul_left(&b, &cxcx, &ccxx, &cx, i1);

    let ccc = c.mul(&cc, &cv); // (c·c)·c
    let xxx = c.mul(&xx, &x); // (x·x)·x
    let ccc_xxx = c.mul(&ccc, &xxx); // ((c·c)·c)·((x·x)·x)
    let i2 = c.mmm(&cc, &xx, &cv, &x); // ((c·c)·(x·x))·(c·x) = ((c·c)·c)·((x·x)·x)

    let body = c.trans(&lhs, &ccxx_cx, &ccc_xxx, left_rw, i2);

    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), body);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_base_rhs()
            .expect("init_boolean_analysis_two_point_base_rhs");
        env.init_boolean_analysis_two_point_base_rhs()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_cube_mul_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.cube_mul");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.cube_mul must kernel-check: {e:?}"));
    }

    #[test]
    fn test_cube_mul_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.cube_mul");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }

    /// STEP-4 PIN: construct the well-formed TYPE of the two-point base
    /// inequality `BoolAnalysis.two_point_base_43` and verify it is a genuine
    /// `Prop` (kernel-typechecks). This PINS the statement WITHOUT registering a
    /// proof — the proof is the genuine analytic residual (see module docs).
    ///
    /// Statement (with abstract nonneg `α, β : NNReal` standing for the cross
    /// `4/3`-powers `P^{4/3}, Q^{4/3}` realized by `pow43Gen`, `half := ofRat ½`,
    /// `m := ofRat (a⁴+(2/3)a²b²+(1/81)b⁴)`):
    ///
    ///   `∀ (a b : Rat)(α β : NNReal)
    ///       (hm : 0 ≤ a⁴ + (2/3)·a²b² + (1/81)·b⁴),
    ///     NNReal.le (NNReal.ofRat (…) hm)
    ///               (NNReal.mul (NNReal.mul H H) H)`   where `H := ½·(α+β)`.
    #[test]
    fn pin_two_point_base_43_typechecks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nnreal = k("NNReal");
        let rat = k("Rat");
        let nnmul = |a: Expr, b: Expr| Expr::apps(k("NNReal.mul"), [a, b]);
        let nnadd = |a: Expr, b: Expr| Expr::apps(k("NNReal.add"), [a, b]);
        let nnle = |a: Expr, b: Expr| Expr::apps(k("NNReal.le"), [a, b]);
        let ofrat = |x: Expr, h: Expr| Expr::apps(k("NNReal.ofRat"), [x, h]);
        let rmul = |a: Expr, b: Expr| Expr::apps(k("Rat.mul"), [a, b]);
        let radd = |a: Expr, b: Expr| Expr::apps(k("Rat.add"), [a, b]);
        let rle = |a: Expr, b: Expr| Expr::apps(k("Rat.le"), [a, b]);
        let rat_zero = k("Rat.zero");
        let nat_lit = |n: u64| {
            let mut e = k("Nat.zero");
            for _ in 0..n {
                e = Expr::app(k("Nat.succ"), e);
            }
            e
        };
        let frac = |num: u64, den: u64| {
            Expr::apps(
                k("Rat.mk"),
                [Expr::app(k("Int.ofNat"), nat_lit(num)), nat_lit(den)],
            )
        };

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(rat.clone());
        let (bv_id, bv) = b.fresh_local(rat.clone());
        let (alpha_id, alpha) = b.fresh_local(nnreal.clone());
        let (beta_id, beta) = b.fresh_local(nnreal.clone());

        // moment rational : (a⁴ + (2/3)·a²b²) + (1/81)·b⁴   (matches two_point_fourth_moment RHS).
        let aa = rmul(a.clone(), a.clone());
        let bb = rmul(bv.clone(), bv.clone());
        let a4 = rmul(aa.clone(), aa.clone());
        let b4 = rmul(bb.clone(), bb.clone());
        let a2b2 = rmul(aa.clone(), bb.clone());
        let moment = radd(
            radd(a4.clone(), rmul(frac(2, 3), a2b2.clone())),
            rmul(frac(1, 81), b4.clone()),
        );
        let hm_ty = rle(rat_zero.clone(), moment.clone());
        let (hm_id, hm) = b.fresh_local(hm_ty.clone());

        // half := ofRat ½ (nonneg via boolean reflection — but for the TYPE we just need
        // a nonneg proof term of the right type; use `Rat.le_of_ble_eq_true` form via a
        // hole-free constant: here we take half as a bound NNReal parameter is overkill,
        // so we inline ofRat ½ with its nonneg proof.).
        let half_pos = Expr::apps(
            k("Rat.le_of_ble_eq_true"),
            [
                rat_zero.clone(),
                frac(1, 2),
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [k("Bool"), k("Bool.true")],
                ),
            ],
        );
        let half = ofrat(frac(1, 2), half_pos);

        // H := ½·(α+β) ; RHS := (H·H)·H.
        let h_nn = nnmul(half, nnadd(alpha.clone(), beta.clone()));
        let rhs_cube = nnmul(nnmul(h_nn.clone(), h_nn.clone()), h_nn);

        // LHS := ofRat moment hm.
        let lhs = ofrat(moment.clone(), hm);

        let concl = nnle(lhs, rhs_cube);
        let e = b.mk_pi(hm_id, BinderInfo::Default, hm_ty, concl);
        let e = b.mk_pi(beta_id, BinderInfo::Default, nnreal.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Default, nnreal.clone(), e);
        let e = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), e);
        let pin_ty = b.finish(b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e));

        // The statement is well-formed iff its type is a Sort (Prop).
        let sort = tc.infer_type(&pin_ty).unwrap_or_else(|err| {
            panic!("pinned two_point_base_43 TYPE must be well-formed: {err:?}")
        });
        assert!(
            matches!(sort.kind(), crate::expr::ExprKind::Sort(_)),
            "pinned statement must inhabit a Sort (a genuine Prop), got {:?}",
            sort.kind()
        );
        // NOTE: NO proof is registered — the inhabitant is the analytic residual
        // (module docs). This test pins WELL-FORMEDNESS only.
    }
}
