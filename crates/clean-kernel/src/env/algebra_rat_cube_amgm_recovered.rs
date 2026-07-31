// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the cubed 3-term AM-GM `Rat.cube_amgm_two_one`.
//!
//! The honest `Rat`-level SOS content that the `NNReal` cube-Hölder cross-term
//! (CH3 rung 3, design `2026-06-20-hc43-dual-tensorization-cross-term.md`)
//! cannot derive on its subtraction-free carrier:
//!
//! ```text
//! Rat.cube_amgm_two_one : ∀ (p q : Rat),
//!   Rat.le Rat.zero p → Rat.le Rat.zero q →
//!     Rat.le (Rat.mul N27 ((p·p)·q)) (((s·s)·s))
//!   where s := (p+p)+q   (= 2p+q),  N27 := 27 (additive, from Rat.one).
//! ```
//!
//! i.e. `27·p²·q ≤ (2p+q)³` for `p,q ≥ 0`.
//!
//! ## Numerals
//!
//! Closed `Rat.ofNat n` numerals do NOT reduce through the kernel here
//! (`Rat.ble 0 (Rat.ofNat 8)` is not def-eq `true`), whereas additive numerals
//! built from `Rat.one` DO (`Rat.ble 0 (1+1) ≡ true`). So — exactly as
//! `Rat.add_cube` spells `3 = (1+1)+1` — every numeral here (`2`, `8`, `27`) is
//! built additively from `Rat.one`. This keeps the `0 ≤ 8p+q` reflection and
//! the ring identity provable without leaning on `Rat.ofNat` reduction.
//!
//! ## Route (pure root-free `Rat` SOS — no new HC)
//!
//! The certificate is the perfect square `(p−q)²·(8p+q)`:
//!
//! 1. **Ring identity** `RID : (2p+q)³ = 27·((p·p)·q) + (((p−q)·(p−q))·(8p+q))`,
//!    proven by a small *verified* polynomial normalizer (`identity.rs`): both
//!    sides are reduced — through `left/right_distrib`, `mul_assoc/comm`,
//!    `add_assoc/comm`, `one_mul`, `mul_neg`, `neg_neg`, `add_neg_self` applied
//!    via `congrArg` — to the shared canonical monomial form
//!    `8p³ + (12·p²q + (6·pq² + q³))`, then chained by `Eq.trans`.
//! 2. **Nonneg remainder** `0 ≤ (p−q)²·(8p+q)` from `Rat.sq_nonneg (p−q)` and
//!    `0 ≤ 8p+q` (`Rat.mul_nonneg` on `8≥0`/`p≥0`, then `Rat.add_le_add` with
//!    `q≥0`).
//! 3. **Close** via `Rat.le_add_of_nonneg_right (27p²q) R hR : 27p²q ≤ 27p²q+R`,
//!    then `Eq.subst` the identity to `27p²q ≤ (2p+q)³`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

#[path = "algebra_rat_cube_amgm_recovered_identity.rs"]
mod identity;

/// Constants + smart-constructors. Bundles `RingConsts` (ring rewriting) and
/// `HcBoundsConsts` (order surface); both wrap an `OrderConsts`, so atoms agree
/// byte-for-byte with `boolean_analysis_amgm`.
pub(crate) struct CubeAmGmConstsRecovered {
    r: RingConsts,
    o: HcBoundsConsts,
    mul_neg: Expr,
    mul_nonneg: Expr,
    add_le_add: Expr,
    le_add_of_nonneg_right: Expr,
    le_of_ble_eq_true: Expr,
    sq_nonneg: Expr,
    // Eq.{1} + subst toolkit (Rat is Sort 1)
    eq_subst1: Expr,
    eq_refl1: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    eq_refl_bool: Expr,
    rat_zero: Expr,
    rat_le: Expr,
}

impl CubeAmGmConstsRecovered {
    pub(crate) fn new() -> Self {
        use crate::level::Level;
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            r: RingConsts::new(),
            o: HcBoundsConsts::new(),
            mul_neg: k("Rat.mul_neg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            add_le_add: k("Rat.add_le_add"),
            le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            sq_nonneg: k("Rat.sq_nonneg"),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            // Bool : Sort 1, so the reflexivity proof over Bool is `Eq.refl.{1}`.
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
        }
    }

    /// Bare `Rat.le a b` — the prompt-mandated statement spelling (def-eq to the
    /// `LE.le Rat instLERat a b` the order bricks produce; the kernel bridges
    /// the two at every binder/`subst` boundary).
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }

    // ── basic constructors (delegate to the ring/order surface) ──
    fn rat(&self) -> Expr {
        self.r.rat()
    }
    fn one(&self) -> Expr {
        self.r.one()
    }
    #[cfg(test)]
    fn two(&self) -> Expr {
        self.r.two()
    }
    fn zero(&self) -> Expr {
        self.o.zero()
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.r.add(a, b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.r.mul(a, b)
    }
    fn neg(&self, a: Expr) -> Expr {
        self.r.neg(a)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.r.sub(a, b)
    }
    #[cfg(test)]
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.le(a, b)
    }
    #[cfg(test)]
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.r.eq(a, b)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.r.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.r.trans(a, b, cc, h1, h2)
    }
    /// `Eq.refl.{1} @Rat a : a = a`.
    fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat(), a])
    }
    fn add_op(&self) -> Expr {
        self.r.add_const()
    }
    fn mul_op(&self) -> Expr {
        self.r.mul_const()
    }
    /// `(x `op` fixed) = (y `op` fixed)` from `h : x = y`.
    fn cong_l(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        self.r.cong_left(parent, op, x, y, fixed, h)
    }
    /// `(fixed `op` x) = (fixed `op` y)` from `h : x = y`.
    fn cong_r(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        self.r.cong_right(parent, op, x, y, fixed, h)
    }
    fn ldist(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.r.ldist(a, b, cc)
    }
    fn rdist(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.r.rdist(a, b, cc)
    }
    fn mcomm(&self, a: Expr, b: Expr) -> Expr {
        self.r.mcomm(a, b)
    }
    fn massoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.r.massoc(a, b, cc)
    }
    fn aassoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.r.aassoc(a, b, cc)
    }
    fn acomm(&self, a: Expr, b: Expr) -> Expr {
        self.r.acomm(a, b)
    }
    fn one_mul(&self, a: Expr) -> Expr {
        self.r.one_mul(a)
    }
    #[cfg(test)]
    fn mneg(&self, a: Expr, b: Expr) -> Expr {
        self.r.mneg(a, b)
    }

    /// `(a·a)·a` — left-nested cube (matches `Rat.add_cube`).
    fn cube(&self, a: &Expr) -> Expr {
        let sq = self.mul(a.clone(), a.clone());
        self.mul(sq, a.clone())
    }

    /// Additive numeral `n` built left-nested from `Rat.one`:
    /// `1`, `1+1`, `(1+1)+1`, … (matches `Rat.add_cube`'s `3 = (1+1)+1`).
    fn nat_lit(&self, n: usize) -> Expr {
        debug_assert!(n >= 1, "nat_lit only for n>=1");
        let one = self.one();
        let mut acc = one.clone();
        for _ in 1..n {
            acc = self.add(acc, one.clone());
        }
        acc
    }

    // ── leaf applications ──
    /// `Rat.mul_neg a b : a·(-b) = -(a·b)`.
    pub(crate) fn mul_neg(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.mul_neg.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    pub(super) fn mmmc(&self, a: &Expr, b: &Expr, cc: &Expr, dd: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a.clone(), b.clone(), cc.clone(), dd.clone()],
        )
    }
    /// `Rat.neg_mul_neg a b : (-a)·(-b) = a·b`.
    pub(super) fn neg_mul_neg(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.neg_mul_neg"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nn(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.add_le_add a b c d h1 h2 : (a+c) ≤ (b+d)`.
    fn add_le(&self, a: Expr, b: Expr, cc: Expr, dd: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, cc, dd, h1, h2])
    }
    /// `Rat.le_add_of_nonneg_right a b h : a ≤ a+b`.
    fn le_add_nn(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_add_of_nonneg_right.clone(), [a, b, h])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nn(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `0 ≤ x` via the boolean-reflection idiom `le_of_ble_eq_true 0 x rfl`,
    /// valid whenever `Rat.ble 0 x` reduces to `true` (closed additive numeral).
    fn ble_nonneg(&self, x: &Expr) -> Expr {
        // `le_of_ble_eq_true 0 x (h : Eq Bool (Rat.ble 0 x) true)`. The reflection
        // proof `Eq.refl true` checks because `Rat.ble 0 x` def-reduces to `true`
        // for a closed additive numeral `x`.
        let refl = Expr::apps(
            self.eq_refl_bool.clone(),
            [self.bool_ty.clone(), self.bool_true.clone()],
        );
        Expr::apps(
            self.le_of_ble_eq_true.clone(),
            [self.rat_zero.clone(), x.clone(), refl],
        )
    }
    /// `Eq.subst.{1} @Rat motive @a @b h_eq h` : `motive b` from `motive a`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_subst1.clone(), [self.rat(), motive, a, b, h_eq, h])
    }
}

impl Environment {
    /// Register `Rat.cube_amgm_two_one`. Idempotent; foundational-only closure.
    pub fn init_algebra_rat_cube_amgm_recovered(&mut self) -> Result<(), EnvError> {
        // `add_cube` + `add_sq` + the full ring/order surface
        // (`mul_comm/assoc`, `left/right_distrib`, `add_assoc/comm`, `one_mul`,
        // `mul_nonneg`, `sq_nonneg`, `le_total`, `lt_*`).
        self.init_algebra_rat_cube_identity()?;
        // `sub_sq_regroup`, `mul_neg`, `neg_mul_neg`, `add_le_add`,
        // `le_of_sub_nonneg`, `le_add_of_nonneg_right`, `le_of_ble_eq_true`.
        self.init_boolean_analysis_amgm()?;
        self.init_rat_quotient_poc()?; // Rat.le_add_of_nonneg_right
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true

        let name = Name::from_string("Rat.cube_amgm_two_one_recovered");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = CubeAmGmConstsRecovered::new();
        let ty = build_type(&c);
        let value = build_proof(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `27·((p·p)·q)`.
fn lhs_term(c: &CubeAmGmConstsRecovered, p: &Expr, q: &Expr) -> Expr {
    let p2q = c.mul(c.mul(p.clone(), p.clone()), q.clone());
    c.mul(c.nat_lit(27), p2q)
}

/// `s := (p+p)+q`.
fn s_of(c: &CubeAmGmConstsRecovered, p: &Expr, q: &Expr) -> Expr {
    c.add(c.add(p.clone(), p.clone()), q.clone())
}

/// `R := ((p−q)·(p−q))·((8·p)+q)` — the SOS certificate.
fn remainder(c: &CubeAmGmConstsRecovered, p: &Expr, q: &Expr) -> Expr {
    let d = c.sub(p.clone(), q.clone());
    let dd = c.mul(d.clone(), d);
    let eight_p = c.mul(c.nat_lit(8), p.clone());
    let eight_p_plus_q = c.add(eight_p, q.clone());
    c.mul(dd, eight_p_plus_q)
}

/// Type: `∀ p q, 0 ≤ p → 0 ≤ q → 27·((p·p)·q) ≤ (2p+q)³`.
fn build_type(c: &CubeAmGmConstsRecovered) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let hp_ty = c.rle(c.zero(), p.clone());
    let hq_ty = c.rle(c.zero(), q.clone());
    let concl = c.rle(lhs_term(c, &p, &q), c.cube(&s_of(c, &p, &q)));
    let (hp_id, _) = b.fresh_local(hp_ty.clone());
    let (hq_id, _) = b.fresh_local(hq_ty.clone());
    let e = b.mk_pi(hq_id, BinderInfo::Default, hq_ty, concl);
    let e = b.mk_pi(hp_id, BinderInfo::Default, hp_ty, e);
    let e = b.mk_pi(q_id, BinderInfo::Default, c.rat(), e);
    b.finish(b.mk_pi(p_id, BinderInfo::Default, c.rat(), e))
}

/// `0 ≤ R` where `R = ((p−q)·(p−q))·((8·p)+q)`.
fn remainder_nonneg(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    hp: &Expr,
    hq: &Expr,
) -> Expr {
    let d = c.sub(p.clone(), q.clone());
    let dd = c.mul(d.clone(), d.clone());
    let eight = c.nat_lit(8);
    let eight_p = c.mul(eight.clone(), p.clone());
    let eight_p_plus_q = c.add(eight_p.clone(), q.clone());

    // 0 ≤ (p−q)·(p−q)
    let h_dd = c.sq_nn(d);
    // 0 ≤ 8·p  := mul_nonneg 8 p (0≤8) hp
    let h_eight = c.ble_nonneg(&eight);
    let h_eight_p = c.mul_nn(eight.clone(), p.clone(), h_eight, hp.clone());
    // 0 ≤ 8p+q : add_le_add 0 (8p) 0 q h_eight_p hq : (0+0) ≤ (8p+q); rewrite (0+0)→0
    let h_sum_raw = c.add_le(
        c.zero(),
        eight_p.clone(),
        c.zero(),
        q.clone(),
        h_eight_p,
        hq.clone(),
    );
    // (0+0) = 0  via Rat.zero_add 0
    let zero_add_zero = c.add(c.zero(), c.zero());
    let h_zero_add = {
        // Rat.zero_add 0 : 0+0 = 0
        let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
        Expr::app(zero_add, c.zero())
    };
    // subst_le_left along (0+0 = 0): from (0+0 ≤ 8p+q) get (0 ≤ 8p+q)
    let h_eight_p_plus_q = c.o.subst_le_left(
        parent,
        eight_p_plus_q.clone(),
        zero_add_zero,
        c.zero(),
        h_zero_add,
        h_sum_raw,
    );
    // 0 ≤ (p−q)²·(8p+q)
    c.mul_nn(dd, eight_p_plus_q, h_dd, h_eight_p_plus_q)
}

/// Build the full proof term.
fn build_proof(c: &CubeAmGmConstsRecovered) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let hp_ty = c.rle(c.zero(), p.clone());
    let hq_ty = c.rle(c.zero(), q.clone());
    let (hp_id, hp) = b.fresh_local(hp_ty.clone());
    let (hq_id, hq) = b.fresh_local(hq_ty.clone());

    let lhs = lhs_term(c, &p, &q); // 27·p²q
    let r = remainder(c, &p, &q); // (p−q)²(8p+q)
    let cube_s = c.cube(&s_of(c, &p, &q)); // (2p+q)³
    let lhs_plus_r = c.add(lhs.clone(), r.clone());

    // RID : cube_s = lhs + r
    let rid = identity::build_rid(c, &b, &p, &q);

    // hR : 0 ≤ r
    let h_r = remainder_nonneg(c, &b, &p, &q, &hp, &hq);

    // hle : lhs ≤ lhs + r
    let h_le = c.le_add_nn(lhs.clone(), r.clone(), h_r);

    // goal : lhs ≤ cube_s
    //   Eq.subst (motive λx. lhs ≤ x) (a := lhs+r) (b := cube_s)
    //     (h_eq : lhs+r = cube_s) (h := hle).
    //   h_eq = symm rid : (lhs+r) = cube_s.
    let h_eq = c.symm(cube_s.clone(), lhs_plus_r.clone(), rid);
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(c.rat());
        let body = c.rle(lhs.clone(), x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat(), body))
    };
    let proof = c.subst(motive, lhs_plus_r, cube_s, h_eq, h_le);

    let e = b.mk_lam(hq_id, BinderInfo::Default, hq_ty, proof);
    let e = b.mk_lam(hp_id, BinderInfo::Default, hp_ty, e);
    let e = b.mk_lam(q_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.rat(), e);
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
        env.init_algebra_rat_cube_amgm_recovered()
            .expect("init_algebra_rat_cube_amgm_recovered");
        env.init_algebra_rat_cube_amgm_recovered()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_rat_cube_amgm_two_one_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("Rat.cube_amgm_two_one_recovered");
        let info = env.get_const(&nm).expect("registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.cube_amgm_two_one must kernel-check");
    }

    #[test]
    fn test_rat_cube_amgm_two_one_statement_is_target() {
        // Pin the exact statement: bare `Rat.le`, `Rat.zero`, additive numerals,
        // `s := (p+p)+q`, `(p·p)·q`, left-nested `cube`. Byte-identical to the
        // freshly-built target type.
        let env = env();
        let nm = Name::from_string("Rat.cube_amgm_two_one_recovered");
        let info = env.get_const(&nm).expect("registered");
        let c = CubeAmGmConstsRecovered::new();
        let want = build_type(&c);
        assert_eq!(
            info.type_, want,
            "registered statement must equal the target type"
        );
    }

    #[test]
    fn test_rat_cube_amgm_two_one_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.cube_amgm_two_one_recovered");
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
