// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 ASSEMBLY, the §9.6 sharp reduction at
//! the rational level.
//!
//! # What this lands and why
//!
//! The keystone of the §9.6 content is the dual `(4/3→2)` hypercontractive bound
//! `‖T_{1/3}(D_i f)‖₂² ≤ 4·Inf_i^{3/2}`, whose rational (root-free) shadow is the
//! SQUARED form `(‖T_{1/3}g‖₂²)² ≤ 16·count_i³` (`count_i := subsetSum n
//! (ind∘disagree_i)`, the un-normalized influence). The campaign's analysis
//! (design `2026-06-18-kkl-real-sqrt-layer-plan.md` §10.6) established — and this
//! module's `refute`-checked tests guard — that the SHARP bound factors through
//! the SINGLE `(4,4/3)` Hölder step
//!
//! ```text
//!   (‖T_{1/3}g‖₂²)⁴  =  ⟨T_{1/9}g, g⟩⁴  ≤  ‖T_{1/9}g‖₄⁴ · ‖g‖_{4/3}⁴
//!                    ≤  ‖g‖_{4/3}⁴ · ‖g‖_{4/3}⁴   (dual (4/3→4) HC: ‖T_{1/9}g‖₄ ≤ ‖g‖_{4/3})
//!                    =  (16·count³)²,
//! ```
//!
//! taking ONE rational square root (`Rat.le_of_sq_le_sq`) to land
//! `(‖T_{1/3}g‖₂²)² ≤ 16·count³`. The three ingredients of the chain
//! (`h_holder4` the single Hölder, `h_m2` the dual hypercontractivity,
//! `h_m1` the `4/3`-norm identity) are the GENUINELY-MISSING analytic lemmas
//! (`§10.6` M-Hölder / M2 / M1); none is currently provable axiom-free in the
//! overlay. The B3c double-CS shadow `subsetSum_holder_fourth` is NOT the
//! operative inequality — it interpolates the WRONG side and yields only
//! `Inf^{5/4}`, never the sharp `Inf^{3/2}` (`§10.6` point 4).
//!
//! THIS module therefore registers the **conditional reduction** as a
//! kernel-checked, axiom-free `Theorem`: given the three named missing facts as
//! hypotheses, the squared dual bound follows by pure rational order reasoning.
//! It turns the §9.6 reduction "(dual bound) ⟸ {M-Hölder, M2, M1}" into a
//! checked object (NOT prose), so the residual is pinned to EXACTLY those three
//! hypotheses and the only remaining work is discharging them.
//!
//! ```text
//! BoolAnalysis.two_norm_sq_le_of_holder_chain :
//!   ∀ (l f4 b43 cnt : Rat),
//!     Rat.le Rat.zero l →                                  -- 0 ≤ ‖T_{1/3}g‖₂²
//!     Rat.le Rat.zero f4 →                                 -- 0 ≤ ‖T_{1/9}g‖₄⁴
//!     Rat.le Rat.zero cnt →                                -- 0 ≤ count
//!     Rat.le (Rat.mul (Rat.mul l l) (Rat.mul l l))         -- (h_holder4) ⟨T_{1/9}g,g⟩⁴
//!            (Rat.mul f4 b43)                               --   ≤ ‖T_{1/9}g‖₄⁴·‖g‖_{4/3}⁴
//!     → Rat.le f4 b43                                       -- (h_m2) ‖T_{1/9}g‖₄⁴ ≤ ‖g‖_{4/3}⁴
//!     → Eq Rat b43 (Rat.mul (Rat.mul (ofNat 16) cnt)       -- (h_m1) ‖g‖_{4/3}⁴ = 16·count³
//!                            (Rat.mul cnt cnt))
//!     → Rat.le (Rat.mul l l)                               -- ⟹ (‖T_{1/3}g‖₂²)²
//!              (Rat.mul (Rat.mul (ofNat 16) cnt) (Rat.mul cnt cnt))  --   ≤ 16·count³
//! ```
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! With `LL := l·l`, `B43 := b43`, the chain over the live `Rat`:
//! 1. `h_holder4 : (LL)·(LL) ≤ f4·B43`.
//! 2. `f4·B43 ≤ B43·B43` from `h_m2 : f4 ≤ B43` by
//!    `Rat.mul_le_mul_of_nonneg_right B43 f4 B43 h_m2 h_b43nn` (right-mono, with
//!    `0 ≤ B43` derived from `h_m1` + nonneg of `16·count·count²`).
//! 3. `le_trans` (1)(2) ⟹ `(LL)·(LL) ≤ B43·B43`.
//! 4. `Rat.le_of_sq_le_sq LL B43 (0≤LL) (0≤B43) step3 : LL ≤ B43` — ONE rational
//!    square root.
//! 5. transport `B43 → 16·count³` by `Eq.subst` along `h_m1` ⟹ `LL ≤ 16·count³`.
//!
//! Every leaf (`Rat.le_trans`, `Rat.mul_le_mul_of_nonneg_right`, `Rat.sq_nonneg`,
//! `Rat.mul_nonneg`, `Rat.le_of_sq_le_sq`, `Eq.subst`, `Rat.ofNat`) is
//! `Constructive` with empty admitted-axiom closure (the `Classical.em` reached
//! by `Rat.le_of_sq_le_sq` is FOUNDATIONAL — `Classical.choice`), so this
//! conditional reduction is too.
//!
//! # The residual (the three hypotheses — design §10.6 M-Hölder / M2 / M1)
//!
//! - **M-Hölder** `h_holder4`: the genuine single `(4,4/3)` Hölder
//!   `⟨a,b⟩⁴ ≤ ‖a‖₄⁴·‖b‖_{4/3}⁴`. UNBUILT (the landed B3c is the double-CS shadow
//!   with the WRONG b-side norm `‖b‖₂⁴`).
//! - **M2** `h_m2`: the dual `(4/3→4)` hypercontractivity `‖T_{1/9}g‖₄ ≤ ‖g‖_{4/3}`
//!   (4th-power `f4 ≤ b43`). UNBUILT (the forward `hc24_at_third` has a fatal
//!   `8^n`; this is a separate theorem).
//! - **M1** `h_m1`: the `4/3`-norm identity `‖g‖_{4/3}⁴ = 16·count³` for
//!   `g ∈ {0,±2}`. UNBUILT (B3b lands the `4`-norm `‖g‖₄⁴ = 16·count`, a SIBLING
//!   with the wrong `count¹` exponent).

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached atoms for the conditional dual-bound reduction.
struct AssembleConsts {
    o: OrderConsts,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    mul_le_right: Expr,
    le_trans: Expr,
    le_of_sq_le_sq: Expr,
}

impl AssembleConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: OrderConsts::new(),
            #[cfg(test)]
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            le_trans: k("Rat.le_trans"),
            le_of_sq_le_sq: k("Rat.le_of_sq_le_sq"),
        }
    }

    fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_eq(a, b)
    }
    /// The literal `16 : Rat` as `Rat.mk (Int.ofNat 16) 1`. Built byte-for-byte
    /// from `Nat` successors so it is a concrete ground rational.
    fn lit16(&self) -> Expr {
        let mut nat16 = self.nat_zero.clone();
        for _ in 0..16 {
            nat16 = Expr::app(self.nat_succ.clone(), nat16);
        }
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nat16), one_nat],
        )
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h:b≤c)(h0:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.le_trans a b c (h1:a≤b)(h2:b≤c) : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.le_of_sq_le_sq a b (ha:0≤a)(hb:0≤b)(h:a·a ≤ b·b) : a ≤ b`.
    fn le_of_sq_le_sq(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_of_sq_le_sq.clone(), [a, b, ha, hb, h])
    }
}

impl Environment {
    /// Register `BoolAnalysis.two_norm_sq_le_of_holder_chain` — the conditional
    /// rational reduction of the §9.6 dual `(4/3→2)` bound to its three genuine
    /// missing ingredients (the single `(4,4/3)` Hölder, the dual `(4/3→4)`
    /// hypercontractivity, the `4/3`-norm identity). Kernel-checked,
    /// `ProofQuality::Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_two_norm_sq_le_of_holder_chain(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_norm_sq_le_of_holder_chain");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?; // sq_nonneg, rat_le, subst plumbing
        self.init_boolean_analysis_order_toolkit_b1d()?; // le_of_sq_le_sq
        self.register_rat_order_proofs()?; // le_trans, mul_nonneg, mul_le_mul_of_nonneg_right
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true (0 ≤ 16)

        let c = AssembleConsts::new();
        let (ty, value) = build_assemble(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `BoolAnalysis.two_norm_sq_le_of_holder_chain`.
fn build_assemble(c: &AssembleConsts) -> (Expr, Expr) {
    // RHS target `16·cnt³ := (16·cnt)·(cnt·cnt)` as a function of `cnt`.
    let cube16 = |cnt: &Expr| -> Expr {
        let c16 = c.lit16();
        c.mul(c.mul(c16, cnt.clone()), c.mul(cnt.clone(), cnt.clone()))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (l_id, l) = b.fresh_local(c.rat());
        let (f4_id, f4) = b.fresh_local(c.rat());
        let (b43_id, b43) = b.fresh_local(c.rat());
        let (cnt_id, cnt) = b.fresh_local(c.rat());

        let hl_ty = c.le(c.zero(), l.clone());
        let hf4_ty = c.le(c.zero(), f4.clone());
        let hcnt_ty = c.le(c.zero(), cnt.clone());
        let ll = c.mul(l.clone(), l.clone());
        let holder_ty = c.le(
            c.mul(ll.clone(), ll.clone()),
            c.mul(f4.clone(), b43.clone()),
        );
        let m2_ty = c.le(f4.clone(), b43.clone());
        let m1_ty = c.eq(b43.clone(), cube16(&cnt));
        let concl = c.le(ll, cube16(&cnt));

        let (hm1_id, _) = b.fresh_local(m1_ty.clone());
        let e = b.mk_pi(hm1_id, BinderInfo::Default, m1_ty, concl);
        let (hm2_id, _) = b.fresh_local(m2_ty.clone());
        let e = b.mk_pi(hm2_id, BinderInfo::Default, m2_ty, e);
        let (hh_id, _) = b.fresh_local(holder_ty.clone());
        let e = b.mk_pi(hh_id, BinderInfo::Default, holder_ty, e);
        let (hcnt_id, _) = b.fresh_local(hcnt_ty.clone());
        let e = b.mk_pi(hcnt_id, BinderInfo::Default, hcnt_ty, e);
        let (hf4_id, _) = b.fresh_local(hf4_ty.clone());
        let e = b.mk_pi(hf4_id, BinderInfo::Default, hf4_ty, e);
        let (hl_id, _) = b.fresh_local(hl_ty.clone());
        let e = b.mk_pi(hl_id, BinderInfo::Default, hl_ty, e);
        let e = b.mk_pi(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(b43_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(f4_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(l_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (l_id, l) = b.fresh_local(c.rat());
        let (f4_id, f4) = b.fresh_local(c.rat());
        let (b43_id, b43) = b.fresh_local(c.rat());
        let (cnt_id, cnt) = b.fresh_local(c.rat());

        let hl_ty = c.le(c.zero(), l.clone());
        let hf4_ty = c.le(c.zero(), f4.clone());
        let hcnt_ty = c.le(c.zero(), cnt.clone());
        let ll = c.mul(l.clone(), l.clone());
        let holder_ty = c.le(
            c.mul(ll.clone(), ll.clone()),
            c.mul(f4.clone(), b43.clone()),
        );
        let m2_ty = c.le(f4.clone(), b43.clone());
        let m1_ty = c.eq(b43.clone(), cube16(&cnt));

        let (hl_id, h_l) = b.fresh_local(hl_ty.clone());
        let (hf4_id, _h_f4) = b.fresh_local(hf4_ty.clone());
        let (hcnt_id, h_cnt) = b.fresh_local(hcnt_ty.clone());
        let (hh_id, h_holder) = b.fresh_local(holder_ty.clone());
        let (hm2_id, h_m2) = b.fresh_local(m2_ty.clone());
        let (hm1_id, h_m1) = b.fresh_local(m1_ty.clone());

        // 0 ≤ l·l (sq_nonneg l), 0 ≤ b43, 0 ≤ 16·count³.
        let h_ll_nn = c.sq_nonneg(l.clone());
        // 0 ≤ cnt·cnt (sq_nonneg cnt); 0 ≤ 16 (lit, via sq? no — use mul_nonneg chain).
        // 0 ≤ 16·count : need 0 ≤ 16 and 0 ≤ cnt. 0 ≤ 16 = 0 ≤ (4)·(4) via sq_nonneg 4.
        // Cleaner: 16 = lit; 0 ≤ 16 from sq_nonneg of (lit 4) is not defeq.
        // Use: 0 ≤ 16·cnt³ derived as mul_nonneg of (16·cnt) and (cnt·cnt).
        //   0 ≤ 16·cnt := mul_nonneg 16 cnt h16 h_cnt ; 0 ≤ cnt·cnt := sq_nonneg cnt.
        // 0 ≤ 16 : the literal 16 = (lit4)·(lit4)? Not defeq. Instead 0 ≤ 16 via
        //   sq_nonneg is unavailable; use the order-toolkit-free route:
        //   16·cnt³ = b43 (h_m1), and 0 ≤ b43 is NOT a hypothesis. So derive
        //   0 ≤ b43 from h_m2 chain? No. Derive 0 ≤ 16·cnt³ directly.
        let h16 = h16_nonneg(c);
        let h_16cnt_nn = c.mul_nonneg(c.lit16(), cnt.clone(), h16, h_cnt.clone());
        let h_cntsq_nn = c.sq_nonneg(cnt.clone());
        let cube = cube16(&cnt);
        let h_cube_nn = c.mul_nonneg(
            c.mul(c.lit16(), cnt.clone()),
            c.mul(cnt.clone(), cnt.clone()),
            h_16cnt_nn,
            h_cntsq_nn,
        );
        // 0 ≤ b43 : Eq.subst (motive z => 0 ≤ z) (h_m1.symm : 16cnt³ = b43) h_cube_nn.
        let h_b43_nn = {
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = d.fresh_local(c.rat());
                let body = c.le(c.zero(), z);
                d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
            };
            // h_m1 : b43 = 16cnt³ ; symm : 16cnt³ = b43.
            let h_m1_symm = c.o.symm(b43.clone(), cube.clone(), h_m1.clone());
            c.o.subst(motive, cube.clone(), b43.clone(), h_m1_symm, h_cube_nn)
        };

        // step2 : f4·b43 ≤ b43·b43  (right-mono at a:=b43, b:=f4, c:=b43)
        let step2 = c.mul_le_right(b43.clone(), f4.clone(), b43.clone(), h_m2, h_b43_nn.clone());
        // step3 : (l·l)·(l·l) ≤ b43·b43  (le_trans of h_holder, step2)
        let ll_ll = c.mul(ll.clone(), ll.clone());
        let f4_b43 = c.mul(f4.clone(), b43.clone());
        let b43_b43 = c.mul(b43.clone(), b43.clone());
        let step3 = c.le_trans(ll_ll, f4_b43, b43_b43, h_holder, step2);
        // step4 : l·l ≤ b43  (le_of_sq_le_sq at a:=l·l, b:=b43)
        let step4 = c.le_of_sq_le_sq(ll.clone(), b43.clone(), h_ll_nn, h_b43_nn, step3);
        // step5 : l·l ≤ 16·cnt³  (Eq.subst along h_m1 : b43 = 16cnt³)
        let proof = {
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = d.fresh_local(c.rat());
                let body = c.le(ll.clone(), z);
                d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
            };
            c.o.subst(motive, b43.clone(), cube.clone(), h_m1, step4)
        };

        let e = b.mk_lam(hm1_id, BinderInfo::Default, m1_ty, proof);
        let e = b.mk_lam(hm2_id, BinderInfo::Default, m2_ty, e);
        let e = b.mk_lam(hh_id, BinderInfo::Default, holder_ty, e);
        let e = b.mk_lam(hcnt_id, BinderInfo::Default, hcnt_ty, e);
        let e = b.mk_lam(hf4_id, BinderInfo::Default, hf4_ty, e);
        let e = b.mk_lam(hl_id, BinderInfo::Default, hl_ty, e);
        let e = b.mk_lam(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(b43_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(f4_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(l_id, BinderInfo::Default, c.rat(), e);
        let _ = h_l; // h_l (0 ≤ l) is in scope as a parameter but the squared route
                     // uses 0 ≤ l·l (sq_nonneg) directly; keep the hypothesis for the
                     // faithful statement shape.
        b.finish(e)
    };

    (ty, value)
}

/// `0 ≤ (16 : Rat)` as `Rat.le_of_ble_eq_true`-free derivation: `16 = 4·4`
/// is NOT defeq to the `Rat.mk 16 1` literal, so instead use `Rat.sq_nonneg`
/// applied to the literal `4` would give `0 ≤ 4·4`, not `0 ≤ 16`. The robust
/// route is the boolean-order reflection `Rat.le_of_ble_eq_true 0 16 rfl`,
/// where `Rat.ble 0 16` native-reduces to `true` on the concrete `Rat.mk`
/// reps (the idiom used by `hc24_at_third`'s `0 ≤ 9` etc.).
fn h16_nonneg(c: &AssembleConsts) -> Expr {
    let le_of_ble = Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]);
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let eq1 = Expr::const_(
        Name::from_string("Eq"),
        vec![crate::level::Level::succ(crate::level::Level::zero())],
    );
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let rat_ble = Expr::const_(Name::from_string("Rat.ble"), vec![]);
    let ble_app = Expr::apps(rat_ble, [c.zero(), c.lit16()]);
    // Eq.refl.{1} Bool Bool.true : Eq Bool Bool.true Bool.true; the kernel checks
    // `Rat.ble 0 16 = true` by reducing the LHS to `true`, so the refl typechecks
    // against `Eq Bool (Rat.ble 0 16) true` up to defeq.
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        ),
        [bool_ty.clone(), bool_true.clone()],
    );
    let _ = (eq1, ble_app); // documentation of the intended Eq type; refl carries it by defeq.
    Expr::apps(le_of_ble, [c.zero(), c.lit16(), refl])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_two_norm_sq_le_of_holder_chain()
            .expect("register_two_norm_sq_le_of_holder_chain");
        env
    }

    #[test]
    fn test_assemble_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.two_norm_sq_le_of_holder_chain");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_two_norm_sq_le_of_holder_chain()
            .expect("first");
        env.register_two_norm_sq_le_of_holder_chain()
            .expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). The conditional reduction is a
    /// TRUE implication (its conclusion follows from the hypotheses by sound
    /// rational order reasoning), so `refute_conjecture` must NOT manufacture a
    /// counterexample. By-hand: from `(l·l)·(l·l) ≤ f4·b43`, `f4 ≤ b43`,
    /// `b43 = 16·count³` and the nonnegativities, `(l·l)² ≤ b43² ⟹ l·l ≤ b43 =
    /// 16·count³` for every assignment — no carrier instance can break it.
    #[test]
    fn test_assemble_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.two_norm_sq_le_of_holder_chain",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the conditional dual-bound reduction is a TRUE implication; must NOT refute"
        );
    }
}
