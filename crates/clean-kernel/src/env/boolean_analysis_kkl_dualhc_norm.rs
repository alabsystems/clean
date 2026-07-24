// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — the NORMALIZATION-CRITICAL `c`-cancellation core.
//!
//! ## What this proves
//!
//! The make-or-break of the dual-HC connect (#2) is that the measure scale
//! `c = 8^n` cancels EXACTLY between the two per-coordinate facts, leaving an
//! `n`-FREE per-coordinate bound. After the per-`S` derivative collapse (#4)
//! folds the spectral `W` into the band object, the two surviving facts at a
//! fixed coordinate `i` are (with `c := 8^n`, `q := 4·9^k`, `Wb :=
//! W^{≤k}[D_i f]`, `W := ‖T_{1/3} D_i f‖₂²`, `ri := r_i = Inf_i^{3/2}`):
//!
//! ```text
//!   (H1)  c · Wb  ≤  P9 · W                 -- RUNG A @ b=1/9 ∘ spectral-W ∘ #4
//!   (H2)  W       ≤  four · (c · ri)         -- dual-HC (W≤4r) ∘ rpow32_scale (r = c·ri)
//! ```
//!
//! together with the regroup hypothesis `(H3) P9 · (four·(c·ri)) = c · (q·ri)`
//! (`q := four·P9`, the pure-ring `8^n`-pivot — at the call site it is a
//! `mul_mul_mul_comm`/`mul_assoc` chain), `0 ≤ P9`, and `0 < c`. This module
//! proves, with the `c` provably cancelled inside the kernel:
//!
//! ```text
//! BoolAnalysis.dualhc_norm_cancel :
//!   ∀ (Wb W ri P9 q c : Rat),
//!     Rat.lt 0 c → Rat.le 0 P9
//!       → Rat.le (c·Wb) (P9·W)
//!       → Rat.le W (four·(c·ri))
//!       → Rat.eq (P9·(four·(c·ri))) (c·(q·ri))
//!       → Rat.le Wb (q·ri)
//! ```
//!
//! i.e. `Wb ≤ q·ri` with `q = 4·9^k` **and NO `c = 8^n` factor** — the sharp,
//! `n`-free per-coordinate charge. The `c` is cancelled by
//! `Rat.le_of_mul_le_mul_left_pos` (which needs the strict `0 < c`); the
//! regroup `H3` is what makes the cancellation land on `q·ri` rather than on a
//! `c`-scaled residue. This is the EXACT step the assembly's `h_dual` consumes
//! once #4 lands; the `0 < c` obligation for `c := 8^n` is `Rat.powNat_pos`.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! 1. `Rat.mul_le_mul_of_nonneg_left P9 W (four·(c·ri)) H2 (0≤P9)` :
//!    `P9·W ≤ P9·(four·(c·ri))`.
//! 2. `Rat.le_trans (c·Wb) (P9·W) (P9·(four·(c·ri))) H1 step1` :
//!    `c·Wb ≤ P9·(four·(c·ri))`.
//! 3. `Eq.subst` along `H3` (motive `t ↦ c·Wb ≤ t`) : `c·Wb ≤ c·(q·ri)`.
//! 4. `Rat.le_of_mul_le_mul_left_pos Wb (q·ri) c (0<c) step3` : `Wb ≤ q·ri`.
//!
//! Every leaf (`Rat.mul_le_mul_of_nonneg_left`, `Rat.le_trans`,
//! `Rat.le_of_mul_le_mul_left_pos`, `Eq.subst`) is `Constructive` with empty
//! closure, so this is too. NO axiom is added or removed. The bound is stated
//! generically over the positive scale `c` and the `n`-free constant `q`, so it
//! is reusable and the `8^n`-cancellation is verified WITHOUT assuming any
//! property of `c` beyond `0 < c`.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the dual-HC normalization-cancellation core.
struct NormConsts {
    order: OrderConsts,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
}

impl NormConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
        }
    }
    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.order.rat_zero.clone(), a)
    }
    fn lt0(&self, a: Expr) -> Expr {
        self.lt(self.order.rat_zero.clone(), a)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_ma)
    }
    fn nat(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `Rat.powNat (Rat.mk (Int.ofNat 8) 1) n` — the `8^n` measure scale.
    fn pow8(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            [self.eight(), n.clone()],
        )
    }
    /// `Rat.powNat_pos 8 n hpos : 0 < powNat 8 n`.
    fn pow8_pos(&self, n: &Expr, hpos8: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_pos"), vec![]),
            [self.eight(), n.clone(), hpos8],
        )
    }
    /// Apply `BoolAnalysis.dualhc_norm_cancel`.
    fn norm_cancel(
        &self,
        wb: Expr,
        w: Expr,
        ri: Expr,
        p9: Expr,
        q: Expr,
        cv: Expr,
        hpos: Expr,
        h0p9: Expr,
        h1: Expr,
        h2: Expr,
        h3: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.dualhc_norm_cancel"), vec![]),
            [wb, w, ri, p9, q, cv, hpos, h0p9, h1, h2, h3],
        )
    }
    /// `Rat.mk (Int.ofNat k) 1`.
    fn rat_lit(&self, k: u32) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(k)),
                self.nat_lit(1),
            ],
        )
    }
    /// `four := Rat.mk (Int.ofNat 4) 1`.
    fn four(&self) -> Expr {
        self.rat_lit(4)
    }
    /// `eight := Rat.mk (Int.ofNat 8) 1`.
    fn eight(&self) -> Expr {
        self.rat_lit(8)
    }
    /// `@Int.NonNeg.mk k` (the `Int.lt`/`Int.NonNeg` witness for a strict
    /// positivity that ι-reduces to `Int.NonNeg (Int.ofNat k)`).
    fn nonneg_mk(&self, k: u32) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit(k),
        )
    }
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h_ab, h_bc],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_0a : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, h_bc, h_0a],
        )
    }
    /// `Rat.le_of_mul_le_mul_left_pos a b c (0<c) (c·a ≤ c·b) : a ≤ b`.
    fn cancel_left(&self, a: Expr, b: Expr, cc: Expr, h_pos: Expr, h_le: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
            [a, b, cc, h_pos, h_le],
        )
    }
}

impl Environment {
    /// Register the dual-HC normalization-cancellation core. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn register_dualhc_norm_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_norm_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.register_rat_order_proofs()?; // Rat.le_trans, Rat.lt surface
        self.register_rat_le_of_mul_le_mul_left_pos()?; // the c-cancellation
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NormConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_norm_cancel(&c, false),
            value: build_norm_cancel(&c, true),
        })
    }

    /// `BoolAnalysis.rat_zero_lt_ofNat8 : Rat.lt 0 (Rat.mk (Int.ofNat 8) 1)`.
    /// The strict positivity of the literal `8`, the `0 < base` premise for
    /// `Rat.powNat_pos` at the `8^n` measure scale. `Rat.lt 0 8` δ/ι-reduces to
    /// `Int.NonNeg (Int.ofNat 7)`; witness `@Int.NonNeg.mk 7`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_rat_zero_lt_ofnat8(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rat_zero_lt_ofNat8");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_rat_order_proofs()?;
        let c = NormConsts::new();
        let ty = c.lt0(c.eight());
        let value = c.nonneg_mk(7);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.dualhc_norm_cancel_8n` — the dual-HC normalization core with
    /// the measure scale fixed to the LITERAL `8^n = Rat.powNat 8 n` and its
    /// `0 < 8^n` premise discharged internally (by `Rat.powNat_pos` +
    /// `rat_zero_lt_ofNat8`):
    ///
    /// ```text
    /// ∀ (n : Nat) (Wb W ri P9 q : Rat),
    ///   Rat.le 0 P9
    ///     → Rat.le ((powNat 8 n)·Wb) (P9·W)
    ///     → Rat.le W (four·((powNat 8 n)·ri))
    ///     → Rat.eq (P9·(four·((powNat 8 n)·ri))) ((powNat 8 n)·(q·ri))
    ///     → Rat.le Wb (q·ri)
    /// ```
    ///
    /// i.e. the `8^n` measure factor CANCELS, leaving the `n`-free `Wb ≤ q·ri`
    /// (`q = 4·9^k`). This is the exact, fully-concrete normalization the
    /// assembly's `h_dual` consumes once #4 lands. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_dualhc_norm_cancel_8n(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_norm_cancel_8n");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_dualhc_norm_cancel()?;
        self.register_rat_pow_nat_pos()?;
        self.register_rat_zero_lt_ofnat8()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NormConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_norm_cancel_8n(&c, false),
            value: build_norm_cancel_8n(&c, true),
        })
    }
}

fn build_norm_cancel_8n(c: &NormConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let (wb_id, wb) = b.fresh_local(c.rat());
    let (w_id, w) = b.fresh_local(c.rat());
    let (ri_id, ri) = b.fresh_local(c.rat());
    let (p9_id, p9) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());

    let p8 = c.pow8(&n);
    let four = c.four();
    let c_ri = c.mul(p8.clone(), ri.clone());
    let four_c_ri = c.mul(four.clone(), c_ri.clone());
    let q_ri = c.mul(q.clone(), ri.clone());
    let c_wb = c.mul(p8.clone(), wb.clone());
    let p9_w = c.mul(p9.clone(), w.clone());
    let p9_four_c_ri = c.mul(p9.clone(), four_c_ri.clone());
    let c_q_ri = c.mul(p8.clone(), q_ri.clone());

    let h_0p9 = c.le0(p9.clone());
    let h1 = c.le(c_wb.clone(), p9_w.clone());
    let h2 = c.le(w.clone(), four_c_ri.clone());
    let h3 = c.eq(p9_four_c_ri.clone(), c_q_ri.clone());
    let concl = c.le(wb.clone(), q_ri.clone());

    let (h0p9_id, h0p9_v) = b.fresh_local(h_0p9.clone());
    let (h1_id, h1_v) = b.fresh_local(h1.clone());
    let (h2_id, h2_v) = b.fresh_local(h2.clone());
    let (h3_id, h3_v) = b.fresh_local(h3.clone());

    let tail = if for_value {
        // 0 < 8^n  via  powNat_pos 8 n (0 < 8).
        let hpos8 = Expr::const_(Name::from_string("BoolAnalysis.rat_zero_lt_ofNat8"), vec![]);
        let hpos = c.pow8_pos(&n, hpos8);
        c.norm_cancel(
            wb.clone(),
            w.clone(),
            ri.clone(),
            p9.clone(),
            q.clone(),
            p8.clone(),
            hpos,
            h0p9_v,
            h1_v,
            h2_v,
            h3_v,
        )
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
    let e = bind(&b, h3_id, h3, tail);
    let e = bind(&b, h2_id, h2, e);
    let e = bind(&b, h1_id, h1, e);
    let e = bind(&b, h0p9_id, h_0p9, e);
    let e = bind(&b, q_id, c.rat(), e);
    let e = bind(&b, p9_id, c.rat(), e);
    let e = bind(&b, ri_id, c.rat(), e);
    let e = bind(&b, w_id, c.rat(), e);
    let e = bind(&b, wb_id, c.rat(), e);
    let e = bind(&b, n_id, c.nat(), e);
    b.finish(e)
}

fn build_norm_cancel(c: &NormConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (wb_id, wb) = b.fresh_local(c.rat());
    let (w_id, w) = b.fresh_local(c.rat());
    let (ri_id, ri) = b.fresh_local(c.rat());
    let (p9_id, p9) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let (cv_id, cv) = b.fresh_local(c.rat());

    let four = c.four();
    let c_ri = c.mul(cv.clone(), ri.clone()); // c·ri
    let four_c_ri = c.mul(four.clone(), c_ri.clone()); // four·(c·ri)
    let q_ri = c.mul(q.clone(), ri.clone()); // q·ri
    let c_wb = c.mul(cv.clone(), wb.clone()); // c·Wb
    let p9_w = c.mul(p9.clone(), w.clone()); // P9·W
    let p9_four_c_ri = c.mul(p9.clone(), four_c_ri.clone()); // P9·(four·(c·ri))
    let c_q_ri = c.mul(cv.clone(), q_ri.clone()); // c·(q·ri)

    // Hypotheses.
    let h_pos = c.lt0(cv.clone()); // 0 < c
    let h_0p9 = c.le0(p9.clone()); // 0 ≤ P9
    let h1 = c.le(c_wb.clone(), p9_w.clone()); // c·Wb ≤ P9·W
    let h2 = c.le(w.clone(), four_c_ri.clone()); // W ≤ four·(c·ri)
    let h3 = c.eq(p9_four_c_ri.clone(), c_q_ri.clone()); // P9·(four·(c·ri)) = c·(q·ri)
    let concl = c.le(wb.clone(), q_ri.clone()); // Wb ≤ q·ri

    let (hpos_id, hpos_v) = b.fresh_local(h_pos.clone());
    let (h0p9_id, h0p9_v) = b.fresh_local(h_0p9.clone());
    let (h1_id, h1_v) = b.fresh_local(h1.clone());
    let (h2_id, h2_v) = b.fresh_local(h2.clone());
    let (h3_id, h3_v) = b.fresh_local(h3.clone());

    let tail = if for_value {
        // step1 : P9·W ≤ P9·(four·(c·ri)).
        let step1 = c.mul_le_left(p9.clone(), w.clone(), four_c_ri.clone(), h2_v, h0p9_v);
        // step2 : c·Wb ≤ P9·(four·(c·ri)).
        let step2 = c.le_trans(
            c_wb.clone(),
            p9_w.clone(),
            p9_four_c_ri.clone(),
            h1_v,
            step1,
        );
        // step3 : c·Wb ≤ c·(q·ri)   [Eq.subst along H3, motive t ↦ c·Wb ≤ t].
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(c_wb.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let step3 = c.subst(motive, p9_four_c_ri.clone(), c_q_ri.clone(), h3_v, step2);
        // step4 : Wb ≤ q·ri   [cancel the positive c on the left].
        c.cancel_left(wb.clone(), q_ri.clone(), cv.clone(), hpos_v, step3)
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
    let e = bind(&b, h3_id, h3, tail);
    let e = bind(&b, h2_id, h2, e);
    let e = bind(&b, h1_id, h1, e);
    let e = bind(&b, h0p9_id, h_0p9, e);
    let e = bind(&b, hpos_id, h_pos, e);
    let e = bind(&b, cv_id, c.rat(), e);
    let e = bind(&b, q_id, c.rat(), e);
    let e = bind(&b, p9_id, c.rat(), e);
    let e = bind(&b, ri_id, c.rat(), e);
    let e = bind(&b, w_id, c.rat(), e);
    let e = bind(&b, wb_id, c.rat(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_rat_zero_lt_ofnat8_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_zero_lt_ofnat8()
            .expect("register_rat_zero_lt_ofnat8");
        env.register_rat_zero_lt_ofnat8().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.rat_zero_lt_ofNat8");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("rat_zero_lt_ofNat8 must kernel-check: {e:?}"));
        let deps = env.axiom_deps(&nm).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "closure must be empty, got {names:?}");
        assert_eq!(env.proof_quality(&nm), Some(ProofQuality::Constructive));
    }

    #[test]
    fn test_dualhc_norm_cancel_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_dualhc_norm_cancel()
            .expect("register_dualhc_norm_cancel");
        env.register_dualhc_norm_cancel().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.dualhc_norm_cancel");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("dualhc_norm_cancel must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        let deps = env.axiom_deps(&nm).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "closure must be empty, got {names:?}");
    }

    #[test]
    fn test_dualhc_norm_cancel_8n_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_dualhc_norm_cancel_8n()
            .expect("register_dualhc_norm_cancel_8n");
        env.register_dualhc_norm_cancel_8n().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.dualhc_norm_cancel_8n");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("dualhc_norm_cancel_8n must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        let deps = env.axiom_deps(&nm).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "closure must be empty, got {names:?}");
    }
}
