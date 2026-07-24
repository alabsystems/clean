// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL UNCONDITIONAL dichotomy — type/proof builder. `include!`d into
// `boolean_analysis_kkl_maxinf_uncond.rs` so it shares `UncondConsts` and keeps
// the registration module under the 500-line convention. (Regular `//` comments
// only — inner doc `//!` is not allowed at an `include!` site.)

// ── Prop / Eq / order plumbing (mirrors the pigeonhole helpers) ─────────────

fn u_not(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}
fn u_not_pi(parent: &EnvDeclBuilder, p: Expr) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let false_ = Expr::const_(Name::from_string("False"), vec![]);
    let (x_id, _) = ch.fresh_local(p.clone());
    ch.finish_child(ch.mk_pi(x_id, BinderInfo::Default, p, false_))
}
fn u_and(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}
fn u_and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [p, q, hp, hq],
    )
}
fn u_and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [p, q, h],
    )
}
fn u_iff_mp(lhs: Expr, rhs: Expr, hiff: Expr, hlhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lhs, rhs, hiff, hlhs],
    )
}
fn u_lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}
fn u_false_elim(goal: Expr, h_false: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [goal, h_false],
    )
}
/// Case-split on `h_or : Or p q` into a (non-dependent) `goal`.
fn u_or_elim(
    parent: &EnvDeclBuilder,
    p: Expr,
    q: Expr,
    goal: Expr,
    h_or: Expr,
    h_left: Expr,
    h_right: Expr,
) -> Expr {
    let or_c = Expr::const_(Name::from_string("Or"), vec![]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let or_ty = Expr::apps(or_c, [p.clone(), q.clone()]);
        let (h_id, _) = m.fresh_local(or_ty.clone());
        let lam = m.mk_lam(h_id, BinderInfo::Default, or_ty, goal);
        m.finish_child(lam)
    };
    Expr::apps(or_rec, [p, q, motive, h_left, h_right, h_or])
}

impl UncondConsts {
    /// `0 ≤ a` from `h : 0 < a` via `And.left (Iff.mp (lt_iff_le_not_le 0 a) h)`.
    fn le_of_pos(&self, a: Expr, h_pos: Expr) -> Expr {
        let le0a = self.rat_le(self.rat_zero.clone(), a.clone());
        let not_le_a0 = u_not(self.rat_le(a.clone(), self.rat_zero.clone()));
        let and_ty = u_and(le0a.clone(), not_le_a0.clone());
        let lt0a = self.rat_lt(self.rat_zero.clone(), a.clone());
        let iff = u_lt_iff(self.rat_zero.clone(), a.clone());
        let mp = u_iff_mp(lt0a, and_ty, iff, h_pos);
        u_and_left(le0a, not_le_a0, mp)
    }
    /// `Rat.le_refl a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le_refl"), vec![]), [a])
    }
    /// `Rat.le_trans a b c (a≤b)(b≤c) : a≤c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a<c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_of_le_of_lt"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.lt_of_lt_of_le a b c (a<b)(b≤c) : a<c`.
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_of_lt_of_le"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, hbc, ha],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (b≤c)(0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            [a, b, cc, hbc, ha],
        )
    }
    /// `Rat.add_le_add a b c d (a≤b)(c≤d) : a+c ≤ b+d`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, dd: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            [a, b, cc, dd, h1, h2],
        )
    }
    /// `Rat.mul_inv_cancel a (a≠0) : a·inv a = 1`.
    fn mul_inv_cancel(&self, a: Expr, hne: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]),
            [a, hne],
        )
    }
    /// `Rat.ne_zero_of_pos a (0<a) : a = 0 → False`.
    fn ne_of_pos(&self, a: Expr, hpos: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.ne_zero_of_pos"), vec![]),
            [a, hpos],
        )
    }
    /// `Rat.mul_pos a b (0<a)(0<b) : 0 < a·b`.
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_pos"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.inv_pos a (0<a) : 0 < inv a`.
    fn inv_pos(&self, a: Expr, ha: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.inv_pos"), vec![]),
            [a, ha],
        )
    }
    /// `Rat.powNat_pos (ofNat 9) k (0<9) : 0 < 9^k`.
    fn pow9_pos(&self, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_pos"), vec![]),
            [self.nine(), k.clone(), self.zero_lt_nine()],
        )
    }
    /// `Nat.cast_le_of_ble a b (Eq.refl Bool.true) : natCast a ≤ natCast b`,
    /// valid when `Nat.ble a b` ground-reduces to `true`.
    fn cast_le_of_ble(&self, a: Expr, b: Expr) -> Expr {
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.u1.clone()]),
            [
                Expr::const_(Name::from_string("Bool"), vec![]),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
            ],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]),
            [a, b, refl],
        )
    }
    /// `Rat.zero_lt_one : 0 < 1`.
    fn zero_lt_one(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![])
    }
    /// `0 < natCast(succ k)` via `lt_of_lt_of_le 0 1 (natCast(succ k)) (0<1) (1≤natCast(succ k))`.
    /// `1 ≤ natCast(succ k)` is `Nat.cast_le_of_ble 1 (succ k) refl` (`natCast 1 ≡ 1`).
    fn natcast_succ_pos(&self, k: &Expr) -> Expr {
        let nck = self.natcast(&self.succ(k));
        let one_le = self.cast_le_of_ble(self.nat_lit(1), self.succ(k));
        self.lt_of_lt_of_le(
            self.rat_zero.clone(),
            self.rat_one.clone(),
            nck,
            self.zero_lt_one(),
            one_le,
        )
    }
    /// `0 < P` via `mul_pos (natCast(succ k)) (9^k) (0<natCast(succ k)) (0<9^k)`.
    fn p_pos(&self, k: &Expr) -> Expr {
        self.mul_pos(
            self.natcast(&self.succ(k)),
            self.pow9(k),
            self.natcast_succ_pos(k),
            self.pow9_pos(k),
        )
    }
}

include!("boolean_analysis_kkl_maxinf_uncond_build2.rs");
