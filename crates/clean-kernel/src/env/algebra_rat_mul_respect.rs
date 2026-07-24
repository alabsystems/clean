// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component A, Step (4a): the symmetric pure-`Rat`
//! product-respect core for `NNReal.mul`'s `Quot.lift` respect proof.
//!
//! # Why this module exists
//!
//! The multiplicative `Quot.lift` respect `Equiv (mul s x)(mul s x2)` from
//! `Equiv x x2` (shared factor `s`, varying factor `x`/`x2`) reduces, at each
//! index, to the TWO-SIDED product-closeness with a FIXED first factor:
//!
//! - `Rat.mul_respect_close : ∀ (s x x2 Bs Bx Bx2 ε δ : Rat),
//!       Rat.le 0 s → Rat.le 0 x → Rat.le 0 x2 → Rat.le 0 δ →
//!       Rat.le s Bs → Rat.le x Bx → Rat.le x2 Bx2 →
//!       Rat.le x (x2+δ) → Rat.le x2 (x+δ) →
//!       Rat.le (Rat.mul δ (Bs+Bx2)) (Rat.div ε Rat.two) →
//!       Rat.le (Rat.mul δ (Bs+Bx)) (Rat.div ε Rat.two) →
//!       Rat.lt 0 ε →
//!       And (Rat.lt (Rat.mul s x) (Rat.add (Rat.mul s x2) ε))
//!           (Rat.lt (Rat.mul s x2) (Rat.add (Rat.mul s x) ε))`
//!
//! Each conjunct is `Rat.mul_close_of_close` with the fixed first factor
//! (`a = a' = s`, trivial self-closeness `s ≤ s+δ`); the two δ-budgets cover the
//! two directions (the relevant other-factor bound differs: `Bx2` forward,
//! `Bx` reverse).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.mul_respect_close`.
pub(crate) struct MulRespectConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    add_le_add: Expr,
    le_refl: Expr,
    add_zero: Expr,
    mul_close: Expr,
    and_c: Expr,
    and_intro: Expr,
    eq_rat: Expr,
    eq_subst: Expr,
}

impl MulRespectConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            add_le_add: k("Rat.add_le_add"),
            le_refl: k("Rat.le_refl"),
            add_zero: k("Rat.add_zero"),
            mul_close: k("Rat.mul_close_of_close"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }
    fn half(&self, eps: Expr) -> Expr {
        self.div(eps, self.rat_two.clone())
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a)
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.add_zero.clone(), a)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `s ≤ s+δ` from `0≤δ`: `s+0 ≤ s+δ` (add_le_add refl h0d), transport add_zero.
    fn self_close(&self, parent: &EnvDeclBuilder, s: &Expr, delta: &Expr, h0d: &Expr) -> Expr {
        let raw = self.add_le_add(
            s.clone(),
            s.clone(),
            self.rat_zero.clone(),
            delta.clone(),
            self.le_refl(s.clone()),
            h0d.clone(),
        ); // s+0 ≤ s+δ
        let s_plus_zero = self.add(s.clone(), self.rat_zero.clone());
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = mb.fresh_local(self.rat.clone());
            let body = self.le(t, self.add(s.clone(), delta.clone()));
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(
            motive,
            s_plus_zero,
            s.clone(),
            self.add_zero(s.clone()),
            raw,
        )
    }
    /// `mul_close_of_close a a' b b' Ba Bb ε δ + the 10 hyps`.
    #[allow(clippy::too_many_arguments)]
    fn mul_close(&self, args: [Expr; 18]) -> Expr {
        Expr::apps(self.mul_close.clone(), args)
    }
}

impl Environment {
    /// Register `Rat.mul_respect_close`. Idempotent.
    pub fn init_algebra_rat_mul_respect(&mut self) -> Result<(), EnvError> {
        self.init_algebra_rat_mul_close()?; // mul_close_of_close + Rat surface
        self.register_rat_add_le_add()?; // add_le_add
        self.register_rat_order_proofs()?; // le_refl
        self.init_rat_field_inst()?; // add_zero

        let c = MulRespectConsts::new();
        self.register_rat_mul_respect_close(&c)
    }

    fn register_rat_mul_respect_close(&mut self, c: &MulRespectConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_respect_close");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_respect_type(c);
        let value = build_respect_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type of `Rat.mul_respect_close`.
fn build_respect_type(c: &MulRespectConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (x2_id, x2) = b.fresh_local(c.rat.clone());
    let (bs_id, bs) = b.fresh_local(c.rat.clone());
    let (bx_id, bx) = b.fresh_local(c.rat.clone());
    let (bx2_id, bx2) = b.fresh_local(c.rat.clone());
    let (e_id, eps) = b.fresh_local(c.rat.clone());
    let (d_id, delta) = b.fresh_local(c.rat.clone());

    let half = c.half(eps.clone());
    let hyps = [
        c.nonneg(s.clone()),
        c.nonneg(x.clone()),
        c.nonneg(x2.clone()),
        c.nonneg(delta.clone()),
        c.le(s.clone(), bs.clone()),
        c.le(x.clone(), bx.clone()),
        c.le(x2.clone(), bx2.clone()),
        c.le(x.clone(), c.add(x2.clone(), delta.clone())),
        c.le(x2.clone(), c.add(x.clone(), delta.clone())),
        c.le(
            c.mul(delta.clone(), c.add(bs.clone(), bx2.clone())),
            half.clone(),
        ),
        c.le(
            c.mul(delta.clone(), c.add(bs.clone(), bx.clone())),
            half.clone(),
        ),
        c.lt(c.rat_zero.clone(), eps.clone()),
    ];
    let concl = c.and_ty(
        c.lt(
            c.mul(s.clone(), x.clone()),
            c.add(c.mul(s.clone(), x2.clone()), eps.clone()),
        ),
        c.lt(
            c.mul(s.clone(), x2.clone()),
            c.add(c.mul(s.clone(), x.clone()), eps.clone()),
        ),
    );

    // Build Π over hyps (reverse fold), then over the 8 Rat binders.
    let mut e = concl;
    for hyp in hyps.iter().rev() {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (h_id, _) = bn.fresh_local(hyp.clone());
        e = bn.finish_child(bn.mk_pi(h_id, BinderInfo::Default, hyp.clone(), e));
    }
    let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bx2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bx_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bs_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term of `Rat.mul_respect_close`.
fn build_respect_proof(c: &MulRespectConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (x2_id, x2) = b.fresh_local(c.rat.clone());
    let (bs_id, bs) = b.fresh_local(c.rat.clone());
    let (bx_id, bx) = b.fresh_local(c.rat.clone());
    let (bx2_id, bx2) = b.fresh_local(c.rat.clone());
    let (e_id, eps) = b.fresh_local(c.rat.clone());
    let (d_id, delta) = b.fresh_local(c.rat.clone());

    let half = c.half(eps.clone());
    let hyp_tys = [
        c.nonneg(s.clone()),                               // 0: 0≤s
        c.nonneg(x.clone()),                               // 1: 0≤x
        c.nonneg(x2.clone()),                              // 2: 0≤x2
        c.nonneg(delta.clone()),                           // 3: 0≤δ
        c.le(s.clone(), bs.clone()),                       // 4: s≤Bs
        c.le(x.clone(), bx.clone()),                       // 5: x≤Bx
        c.le(x2.clone(), bx2.clone()),                     // 6: x2≤Bx2
        c.le(x.clone(), c.add(x2.clone(), delta.clone())), // 7: x≤x2+δ
        c.le(x2.clone(), c.add(x.clone(), delta.clone())), // 8: x2≤x+δ
        c.le(
            c.mul(delta.clone(), c.add(bs.clone(), bx2.clone())),
            half.clone(),
        ), // 9
        c.le(
            c.mul(delta.clone(), c.add(bs.clone(), bx.clone())),
            half.clone(),
        ), // 10
        c.lt(c.rat_zero.clone(), eps.clone()),             // 11: 0<ε
    ];
    let mut hyp_ids = Vec::with_capacity(12);
    let mut hyp_vars = Vec::with_capacity(12);
    for ty in &hyp_tys {
        let (id, v) = b.fresh_local(ty.clone());
        hyp_ids.push(id);
        hyp_vars.push(v);
    }
    let h = |i: usize| hyp_vars[i].clone();

    // self-closeness s ≤ s+δ (uses 0≤δ = h(3)).
    let self_close = c.self_close(&b, &s, &delta, &h(3));

    // FORWARD: s·x < s·x2 + ε.
    //   a=s, a'=s, b=x, b'=x2, Ba=Bs, Bb=Bx2.
    let fwd = c.mul_close([
        s.clone(),
        s.clone(),
        x.clone(),
        x2.clone(),
        bs.clone(),
        bx2.clone(),
        eps.clone(),
        delta.clone(),
        h(0),               // 0≤s = 0≤a
        h(1),               // 0≤x = 0≤b
        h(2),               // 0≤x2 = 0≤b'
        h(3),               // 0≤δ
        h(4),               // s≤Bs = a≤Ba
        h(6),               // x2≤Bx2 = b'≤Bb
        self_close.clone(), // s≤s+δ = a≤a'+δ
        h(7),               // x≤x2+δ = b≤b'+δ
        h(9),               // δ·(Bs+Bx2)≤ε/2
        h(11),              // 0<ε
    ]);

    // REVERSE: s·x2 < s·x + ε.
    //   a=s, a'=s, b=x2, b'=x, Ba=Bs, Bb=Bx.
    let rev = c.mul_close([
        s.clone(),
        s.clone(),
        x2.clone(),
        x.clone(),
        bs.clone(),
        bx.clone(),
        eps.clone(),
        delta.clone(),
        h(0),       // 0≤s
        h(2),       // 0≤x2 = 0≤b
        h(1),       // 0≤x = 0≤b'
        h(3),       // 0≤δ
        h(4),       // s≤Bs
        h(5),       // x≤Bx = b'≤Bb
        self_close, // s≤s+δ
        h(8),       // x2≤x+δ = b≤b'+δ
        h(10),      // δ·(Bs+Bx)≤ε/2
        h(11),      // 0<ε
    ]);

    let l_concl = c.lt(
        c.mul(s.clone(), x.clone()),
        c.add(c.mul(s.clone(), x2.clone()), eps.clone()),
    );
    let r_concl = c.lt(
        c.mul(s.clone(), x2.clone()),
        c.add(c.mul(s.clone(), x.clone()), eps.clone()),
    );
    let mut proof = Expr::apps(c.and_intro.clone(), [l_concl, r_concl, fwd, rev]);

    // Wrap the 12 hypothesis lambdas (reverse order).
    for (id, ty) in hyp_ids.into_iter().zip(hyp_tys).rev() {
        proof = b.mk_lam(id, BinderInfo::Default, ty, proof);
    }
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), proof);
    let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bx2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bx_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bs_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
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
        env.init_algebra_rat_mul_respect()
            .expect("init_algebra_rat_mul_respect");
        env.init_algebra_rat_mul_respect().expect("idempotent");
        env
    }

    #[test]
    fn test_mul_respect_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("Rat.mul_respect_close");
        let info = env
            .get_const(&nm)
            .expect("Rat.mul_respect_close registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.mul_respect_close must kernel-check");
    }

    #[test]
    fn test_mul_respect_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.mul_respect_close");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
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
