// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.finSum_cube_le_cube_sum`: the finSum-level CUBE
//! collapse `Σ_i (W i)³ ≤ (Σ_i W i)³`, the root-free `ℓ³`-collapse the `(4/3,4)`
//! dual-HC tensorization's `H_CLOSE` discharge needs.
//!
//! # Why this module exists (the `H_CLOSE` collapse rung)
//!
//! After the per-coordinate two-point base is summed (`finSum_le`), the residual
//! `H_CLOSE` of the `(4/3,4)` dual tensorization (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md` §11) needs the SUM of
//! per-coordinate cubes `Σ_k (W k)³` bounded by the CUBE of the single sum
//! `(Σ_k W k)³` (the cube of `norm43_{m+1}` after the norm-split). This is the
//! finSum lift of the scalar cube super-additivity `NNReal.cube_superadd`
//! (`u³ + v³ ≤ (u+v)³`):
//!
//! ```text
//!   NNReal.finSum_cube_le_cube_sum : ∀ (n : Nat)(W : Fin n → NNReal),
//!     NNReal.le (NNReal.finSum n (fun i => ((W i · W i)· W i)))      -- Σ W³
//!               (let s := NNReal.finSum n W in ((s · s)· s))         -- (Σ W)³
//! ```
//!
//! (cubes left-nested as `(a·a)·a`, matching `NNReal.cube_superadd`).
//!
//! # Proof shape (axiom-free, root-free — `Nat.rec` over the cardinality)
//!
//! `Nat.rec.{0}` over `n` (Prop motive `fun k => ∀ W, le (finSum k W³)((finSum k W)³)`),
//! mirroring `NNReal.finSum_le`:
//! - **BASE `n=0`**: `finSum 0 W³ ≡ NNReal.zero` and `(finSum 0 W)³ ≡ zero³`. By
//!   `NNReal.mul_zero` (twice) `zero³ = ((zero·zero)·zero) = zero`, so the goal
//!   `le zero zero³` transports along that equality to `le zero zero` = `le.refl`.
//! - **STEP `n=k+1`**: `finSum (k+1) W³ ≡ add (finSum k (W³∘castSucc))((W(last k))³)`
//!   and `finSum (k+1) W ≡ add (finSum k (W∘castSucc))(W(last k))` (the `finSum`
//!   step ι). Write `p := finSum k (W∘castSucc)`, `w := W(last k)`. Then:
//!     1. IH at `W∘castSucc`: `finSum k ((W∘cast)³) ≤ p³`. Note `(W³∘cast) ≡
//!        ((W∘cast)³)` definitionally (both `(W(cast i)·W(cast i))·W(cast i)`).
//!     2. `add_le_add` with `le.refl (w³)`: `finSum k (W³∘cast) + w³ ≤ p³ + w³`.
//!     3. `cube_superadd p w`: `p³ + w³ ≤ (p+w)³`.
//!     4. `le.trans` of (2),(3): `finSum (k+1) W³ ≤ (p+w)³ ≡ (finSum (k+1) W)³`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only — `cube_superadd`/`add_le_add`/`mul_zero`/`finSum`
//! recursion are all constructive). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::algebra_nnreal_finsum::NNFinSumConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.finSum_cube_le_cube_sum`.
pub(crate) struct FinSumCubeConsts {
    base: NNFinSumConsts,
    l1: Level,
    nat_rec0: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_le_refl: Expr,
    nnreal_le_trans: Expr,
    nnreal_add_le_add: Expr,
    nnreal_cube_superadd: Expr,
    nnreal_mul_zero: Expr,
}

impl FinSumCubeConsts {
    pub(crate) fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            base: NNFinSumConsts::new(),
            l1: Level::succ(Level::zero()),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_le_refl: k("NNReal.le.refl"),
            nnreal_le_trans: k("NNReal.le.trans"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
            nnreal_cube_superadd: k("NNReal.cube_superadd"),
            nnreal_mul_zero: k("NNReal.mul_zero"),
        }
    }

    fn nat(&self) -> Expr {
        self.base.nat.clone()
    }
    fn nnreal(&self) -> Expr {
        self.base.nnreal.clone()
    }
    fn fin_to_nnreal(&self, n: Expr) -> Expr {
        self.base.fin_to_nnreal(n)
    }
    fn fin(&self, n: Expr) -> Expr {
        Expr::app(self.base.fin.clone(), n)
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        self.base.sum(n, f)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.base.add(a, b)
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    /// `(a·a)·a` — the left-nested cube.
    fn cube(&self, a: &Expr) -> Expr {
        self.mul(&self.mul(a, a), a)
    }
    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn le_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.nnreal_le_refl.clone(), a.clone())
    }
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.cube_superadd u v : u³ + v³ ≤ (u+v)³`.
    fn cube_superadd(&self, u: &Expr, v: &Expr) -> Expr {
        Expr::apps(self.nnreal_cube_superadd.clone(), [u.clone(), v.clone()])
    }
    /// `NNReal.mul_zero c : c·zero = zero`.
    fn mul_zero(&self, cc: &Expr) -> Expr {
        Expr::app(self.nnreal_mul_zero.clone(), cc.clone())
    }
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.nnreal(), a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nnreal(), a.clone(), b.clone(), h],
        )
    }
    /// `@congrArg NNReal NNReal from to f h`.
    fn congr_arg_nn(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.nnreal(), self.nnreal(), from.clone(), to.clone(), f, h],
        )
    }
    /// `@Eq.subst NNReal motive a b h_eq h : motive b` (motive lands in Prop).
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.nnreal(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    /// `fun (i : Fin n) => ((W i · W i)· W i)` — the `W³` summand.
    fn cube_summand(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let fin_n = self.fin(n.clone());
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let wi = Expr::app(w.clone(), i.clone());
        let body = self.cube(&wi);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

impl Environment {
    /// Register `NNReal.finSum_cube_le_cube_sum`. Idempotent; foundational-only.
    pub fn init_algebra_nnreal_finsum_cube(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.zero, NNReal.finSum
        self.init_algebra_nnreal_le()?; // NNReal.le.refl / le.trans
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_algebra_nnreal_cube_superadd()?; // NNReal.cube_superadd
        self.init_algebra_nnreal_finsum_smul()?; // NNReal.mul_zero
        self.init_eq()?;

        let name = Name::from_string("NNReal.finSum_cube_le_cube_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = FinSumCubeConsts::new();
        let ty = build_finsum_cube_type(&c);
        let value = build_finsum_cube_value(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ (n : Nat)(W : Fin n → NNReal), le (finSum n (cube∘W)) ((finSum n W)³)`.
fn build_finsum_cube_type(c: &FinSumCubeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let w_type = c.fin_to_nnreal(n.clone());
    let (w_id, w) = b.fresh_local(w_type.clone());
    let lhs = c.sum(n.clone(), c.cube_summand(&b, &n, &w));
    let sum_w = c.sum(n.clone(), w.clone());
    let rhs = c.cube(&sum_w);
    let concl = c.le(&lhs, &rhs);
    let e = b.mk_pi(w_id, BinderInfo::Default, w_type, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
    b.finish(e)
}

/// The `Nat.rec.{0}` motive `fun k => ∀ W, le (finSum k (cube∘W)) ((finSum k W)³)`.
fn build_motive(c: &FinSumCubeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());
    let w_type = c.fin_to_nnreal(k.clone());
    let (w_id, w) = b.fresh_local(w_type.clone());
    let lhs = c.sum(k.clone(), c.cube_summand(&b, &k, &w));
    let sum_w = c.sum(k.clone(), w.clone());
    let rhs = c.cube(&sum_w);
    let concl = c.le(&lhs, &rhs);
    let pi_w = b.mk_pi(w_id, BinderInfo::Default, w_type, concl);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.nat(), pi_w);
    b.finish(lam)
}

/// Base case (n=0): `fun W => <le zero zero³ transported to le zero zero>`.
/// `finSum 0 (cube∘W) ≡ zero`, `finSum 0 W ≡ zero`, so the goal is `le zero zero³`.
/// `cube zero = ((zero·zero)·zero)`; by `mul_zero` (`zero·zero = zero`, then
/// `(zero)·zero = zero`) `cube zero = zero`, so transport `le.refl zero` backward
/// along that equality (subst the RHS `zero → cube zero`).
fn build_base(c: &FinSumCubeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = c.base.nat_zero.clone();
    let w_type = c.fin_to_nnreal(zero.clone());
    let (w_id, _w) = b.fresh_local(w_type.clone());

    let nnzero = c.base.nnreal_zero.clone();
    // h1 : zero·zero = zero   (mul_zero zero).
    let zz = c.mul(&nnzero, &nnzero);
    let h1 = c.mul_zero(&nnzero); // zero·zero = zero
                                  // cube zero = (zz)·zero.
                                  //   step A: (zz)·zero = zero·zero      via congrArg (fun t => t·zero) h1
                                  //   step B: zero·zero = zero           via h1
    let cube_zero = c.mul(&zz, &nnzero); // (zero·zero)·zero
    let mul_right_zero = {
        // fun t => t·zero
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal());
        let body = c.mul(&t, &nnzero);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal(), body))
    };
    let step_a = c.congr_arg_nn(&zz, &nnzero, mul_right_zero, h1.clone()); // (zz)·zero = zero·zero
    let hc = c.trans_nn(&cube_zero, &zz, &nnzero, step_a, h1); // cube zero = zero

    // Goal : le zero (cube zero). subst RHS along (symm hc : zero = cube zero)
    // from `le.refl zero : le zero zero`.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal());
        let body = c.le(&nnzero, &t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal(), body))
    };
    let refl = c.le_refl(&nnzero); // le zero zero
    let proof = c.subst_nn(
        motive,
        &nnzero,
        &cube_zero,
        c.symm_nn(&cube_zero, &nnzero, hc),
        refl,
    );

    let val = b.mk_lam(w_id, BinderInfo::Default, w_type, proof);
    b.finish(val)
}

/// Step case (n=k+1).
fn build_step(c: &FinSumCubeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());

    // ih : ∀ W, le (finSum k (cube∘W)) ((finSum k W)³).
    let w_type_k = c.fin_to_nnreal(k.clone());
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let (ihw_id, ihw) = ib.fresh_local(w_type_k.clone());
        let lhs = c.sum(k.clone(), c.cube_summand(&ib, &k, &ihw));
        let sum_w = c.sum(k.clone(), ihw.clone());
        let rhs = c.cube(&sum_w);
        let concl = c.le(&lhs, &rhs);
        ib.finish_child(ib.mk_pi(ihw_id, BinderInfo::Default, w_type_k.clone(), concl))
    };
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(c.base.nat_succ.clone(), k.clone());
    let w_type_succ = c.fin_to_nnreal(succ_k.clone());
    let (w_id, w) = b.fresh_local(w_type_succ.clone());

    // W∘castSucc and (W(last k)).
    let w_cast = c.base.cast_prefix(&b, k.clone(), w.clone());
    let last_k = Expr::app(c.base.fin_last.clone(), k.clone());
    let w_last = Expr::app(w.clone(), last_k.clone());

    // p := finSum k (W∘cast).
    let p = c.sum(k.clone(), w_cast.clone());

    // IH at (W∘cast) : le (finSum k (cube∘(W∘cast))) (p³).
    //   note `cube∘(W∘cast) ≡ (cube∘W)∘cast` definitionally (both
    //   `(W(cast i)·W(cast i))·W(cast i)`), so `finSum k (cube∘(W∘cast))` is
    //   defeq to `finSum k ((cube∘W)∘cast)`, the prefix of `finSum (k+1) (cube∘W)`.
    let ih_at = Expr::app(ih, w_cast.clone());
    let sum_cube_cast = c.sum(k.clone(), c.cube_summand(&b, &k, &w_cast)); // finSum k (cube∘(W∘cast))
    let p_cube = c.cube(&p);
    let w_last_cube = c.cube(&w_last);

    // (2) add_le_add : finSum k (cube∘cast) + w_last³ ≤ p³ + w_last³.
    let mid_lhs = c.add(sum_cube_cast.clone(), w_last_cube.clone()); // ≡ finSum (k+1) (cube∘W)
    let p3_plus_w3 = c.add(p_cube.clone(), w_last_cube.clone());
    let step2 = c.add_le_add(
        &sum_cube_cast,
        &p_cube,
        &w_last_cube,
        &w_last_cube,
        ih_at,
        c.le_refl(&w_last_cube),
    );

    // (3) cube_superadd p w_last : p³ + w_last³ ≤ (p+w_last)³.
    let p_plus_w = c.add(p.clone(), w_last.clone()); // ≡ finSum (k+1) W
    let target = c.cube(&p_plus_w);
    let step3 = c.cube_superadd(&p, &w_last);

    // le.trans (2),(3) : finSum (k+1) (cube∘W) ≤ (finSum (k+1) W)³.
    let proof = c.le_trans(&mid_lhs, &p3_plus_w3, &target, step2, step3);

    let val = b.mk_lam(w_id, BinderInfo::Default, w_type_succ, proof);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat(), val);
    b.finish(val)
}

/// `fun n => Nat.rec.{0} motive base step n` (W binder from the motive body).
fn build_finsum_cube_value(c: &FinSumCubeConsts) -> Expr {
    let motive = build_motive(c);
    let base = build_base(c);
    let step = build_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let body = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat(), body);
    b.finish(val)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum_cube()
            .expect("init_algebra_nnreal_finsum_cube");
        env.init_algebra_nnreal_finsum_cube().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_finsum_cube_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.finSum_cube_le_cube_sum");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.finSum_cube_le_cube_sum must kernel-check: {e:?}"));
    }

    #[test]
    fn test_nnreal_finsum_cube_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.finSum_cube_le_cube_sum");
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
}
