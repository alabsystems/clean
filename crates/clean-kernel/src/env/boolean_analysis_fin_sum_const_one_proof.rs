// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the symbolic Rat-numeral successor lemma and the
//! constant-one cube sum, the additive twins on the road to the uniform
//! expectation normalization `E[1] = 1` (the last missing fact of the
//! diagonal-character Parseval rung):
//!
//! - `Rat.add_natCast_one : ∀ (k : Nat),`
//!     `Rat.add (Rat.mk (Int.ofNat k) 1) Rat.one = Rat.mk (Int.ofNat (Nat.succ k)) 1`
//!   — the symbolic `(k/1) + 1 = (k+1)/1` step over the `Rat := Quot Rat.Raw.Equiv`
//!   quotient. Proved propositionally by `Quot.sound`: both sides are `Quot.mk`
//!   of denominator-1 raw pairs, so the `Rat.Raw.Equiv` cross-identity reduces to
//!   an `Int` numerator equation closed by `Int.mul_one` (a landed Theorem) plus
//!   the *definitional* `Int.add (ofNat k) (ofNat 1) ≡ ofNat (Nat.succ k)`.
//!
//! - `Fin.sum_const_one : ∀ (n : Nat),`
//!     `Fin.sum n (fun _ => Rat.one) = Rat.mk (Int.ofNat n) 1`
//!   — the additive twin of `Fin.prod_const_one`. A `Nat.rec` induction over the
//!   faithful `Fin.sum` carrier: the base reduces `Fin.sum 0 _ ≡ Rat.zero ≡
//!   Rat.mk (Int.ofNat 0) 1`; the step peels via `Fin.sum_succ`'s ι-step into
//!   `Rat.add (Fin.sum k (const 1)) 1`, rewrites the prefix by the IH (congrArg),
//!   and closes with `Rat.add_natCast_one`.
//!
//! - `Rat.div_self_of_ne_zero : ∀ (a : Rat),`
//!     `(Eq Rat a Rat.zero → False) → Eq Rat (Rat.div a a) Rat.one`
//!   — division of a nonzero rational by itself is `1`. Since `Rat.div a a`
//!   unfolds (reducible) to `Rat.mul a (Rat.inv a)`, the proof is a direct
//!   application of the landed constructive `Rat.mul_inv_cancel a h`.
//!
//! All three are kernel-checked, `ProofQuality::Constructive` (empty admitted-
//! axiom closure): the only leaves are `Quot.sound`/`congrArg`/`Eq.*`/`Nat.rec`
//! built-ins and the landed constructive Theorems `Int.mul_one`,
//! `Rat.add_natCast_one`, `Fin.sum_succ`, `Rat.mul_inv_cancel`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the additive const-one rung.
struct FinSumConstOneConsts {
    nat: Expr,
    int: Expr,
    rat: Expr,
    fin: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mk: Expr,
    fin_sum: Expr,
    int_of_nat: Expr,
    int_mul: Expr,
    int_add: Expr,
    int_mul_one: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    // Eq.{1} toolkit over Rat and Int.
    eq1: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    #[cfg(test)]
    eq_symm: Expr,
    congr_arg: Expr,
    // Quot machinery over the Rat.Raw / Rat.Raw.Equiv carrier.
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    // Rat.add_natCast_one, consumed by the Fin.sum_const_one step.
    rat_add_natcast_one: Expr,
    // A3 field toolkit.
    rat_zero: Expr,
    rat_div: Expr,
    rat_mul_inv_cancel: Expr,
    false_: Expr,
}

impl FinSumConstOneConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            int: Expr::const_(Name::from_string("Int"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_mul_one: Expr::const_(Name::from_string("Int.mul_one"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            #[cfg(test)]
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            raw: Expr::const_(Name::from_string("Rat.Raw"), vec![]),
            raw_mk: Expr::const_(Name::from_string("Rat.Raw.mk"), vec![]),
            raw_equiv: Expr::const_(Name::from_string("Rat.Raw.Equiv"), vec![]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1]),
            rat_add_natcast_one: Expr::const_(Name::from_string("Rat.add_natCast_one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            rat_mul_inv_cancel: Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]),
            false_: Expr::const_(Name::from_string("False"), vec![]),
        }
    }

    // ── Int smart-constructors ──
    fn imul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [a, b])
    }
    fn iadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [a, b])
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    /// `Int.ofNat 1`.
    fn int_one(&self) -> Expr {
        self.of_nat(Expr::app(self.nat_succ.clone(), self.nat_zero.clone()))
    }
    /// `Nat` literal `1` (`Nat.succ Nat.zero`).
    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    /// `@Eq Int x y`.
    #[cfg(test)]
    fn eq_int(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.int.clone(), x, y])
    }
    /// `@Eq.refl Int x`.
    fn refl_int(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int.clone(), x])
    }
    /// `@Eq.trans Int x y z h1 h2`.
    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.int.clone(), x, y, z, h1, h2])
    }
    /// `@congrArg Int Int x y f h`.
    fn congr_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int.clone(), self.int.clone(), x, y, f, h],
        )
    }
    /// `Int.mul_one a : Int.mul a (Int.ofNat 1) = a`.
    fn imul_one(&self, a: Expr) -> Expr {
        Expr::app(self.int_mul_one.clone(), a)
    }

    // ── Rat / Quot smart-constructors ──
    /// `Rat.mk n d`.
    fn rat_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [n, d])
    }
    /// `Rat.mk (Int.ofNat n) 1`.
    fn rat_natcast(&self, n: Expr) -> Expr {
        self.rat_mk(self.of_nat(n), self.nat_one())
    }
    /// `Rat.Raw.mk n d`.
    fn raw_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [n, d])
    }
    /// `@Quot.mk Rat.Raw Rat.Raw.Equiv l`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }
    /// `@Quot.sound Rat.Raw Rat.Raw.Equiv a b h : Quot.mk a = Quot.mk b`.
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), a, b, h],
        )
    }
    /// `@Eq Rat x y`.
    fn eq_rat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), x, y])
    }
    /// `@Eq.refl Rat x`.
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), x])
    }
    /// `@Eq.trans Rat x y z h1 h2`.
    fn trans_rat(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), x, y, z, h1, h2])
    }
    /// `@Eq.symm Rat x y h : Eq Rat y x`.
    #[cfg(test)]
    fn symm_rat(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), x, y, h])
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    #[cfg(test)]
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn sum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    /// `fun (_ : Fin n) => Rat.one`.
    fn const_one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, self.rat_one.clone());
        b.finish_child(lam)
    }
    /// `fun (r : Rat) => Rat.add r Rat.one` — the congrArg closure for the
    /// `Fin.sum_const_one` step (rewrite the prefix sum under `· + 1`).
    fn add_one_right_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (r_id, r) = b.fresh_local(self.rat.clone());
        let body = self.radd(r, self.rat_one.clone());
        let lam = b.mk_lam(r_id, BinderInfo::Default, self.rat.clone(), body);
        b.finish_child(lam)
    }
    /// `@congrArg Rat Rat a b f h`.
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
}

// ── A1: Rat.add_natCast_one ──

fn natcast_one_type(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lhs = c.radd(c.rat_natcast(k.clone()), c.rat_one.clone());
    let rhs = c.rat_natcast(Expr::app(c.nat_succ.clone(), k.clone()));
    let concl = c.eq_rat(lhs, rhs);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl))
}

/// The `Rat.Raw.Equiv` witness for `Rat.add_natCast_one`, given the Nat `k`.
///
/// `Rat.add (mk (ofNat k) 1) Rat.one` reduces (Rat.add lift β/ι + denom-1
/// effDenoms ≡ ofNat 1) to the class of the raw pair
///   `Rat.Raw.mk (ofNat k · ofNat 1  +  ofNat 1 · ofNat 1) (Nat.mul 1 1)`,
/// and `Rat.mk (ofNat (succ k)) 1` is the class of `Rat.Raw.mk (ofNat (succ k)) 1`.
/// `Quot.sound` closes the goal once we exhibit
///   `Rat.Raw.Equiv  (Raw.mk Lnum (1·1))  (Raw.mk (ofNat (succ k)) 1)`,
/// which the kernel unfolds to (both effDenoms ≡ ofNat 1):
///   `Eq Int (Lnum · ofNat 1) (ofNat (succ k) · ofNat 1)`.
/// We prove that by `congrArg (· * ofNat 1)` of the numerator identity
///   `Lnum = ofNat (succ k)`,
/// itself: `ofNat k · 1 + 1 · 1 =[mul_one twice] ofNat k + ofNat 1 ≡ ofNat (succ k)`.
fn natcast_one_value(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());

    let o1 = c.int_one(); // Int.ofNat 1
    let of_k = c.of_nat(k.clone()); // Int.ofNat k
    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let of_succ_k = c.of_nat(succ_k.clone()); // Int.ofNat (succ k) ≡ ofNat k + ofNat 1

    // Lnum := (ofNat k · ofNat 1) + (ofNat 1 · ofNat 1)  — the reduced add numerator.
    let l_a = c.imul(of_k.clone(), o1.clone());
    let l_b = c.imul(o1.clone(), o1.clone());
    let l_num = c.iadd(l_a.clone(), l_b.clone());

    // mid := ofNat k + ofNat 1  (after collapsing both products by mul_one).
    let mid = c.iadd(of_k.clone(), o1.clone());

    // s1 : (ofNat k · 1) + (1 · 1) = ofNat k + (1 · 1)
    //   via congrArg (· + (1·1)) (Int.mul_one (ofNat k)).
    let add_right_lb = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(c.int.clone());
        let body = c.iadd(w, l_b.clone());
        let lam = d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
        d.finish_child(lam)
    };
    let mid_a = c.iadd(of_k.clone(), l_b.clone()); // ofNat k + (1·1)
    let s1 = c.congr_int(
        l_a.clone(),
        of_k.clone(),
        add_right_lb,
        c.imul_one(of_k.clone()),
    );

    // s2 : ofNat k + (1 · 1) = ofNat k + ofNat 1
    //   via congrArg (ofNat k + ·) (Int.mul_one (ofNat 1)).
    let add_left_ofk = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(c.int.clone());
        let body = c.iadd(of_k.clone(), w);
        let lam = d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
        d.finish_child(lam)
    };
    let s2 = c.congr_int(
        l_b.clone(),
        o1.clone(),
        add_left_ofk,
        c.imul_one(o1.clone()),
    );

    // num_eq : Lnum = mid    (s1 ; s2)
    let num_eq_partial = c.trans_int(l_num.clone(), mid_a.clone(), mid.clone(), s1, s2);
    // mid ≡ ofNat (succ k) definitionally (Int.add ofNat+ofNat); so
    //   num_eq : Lnum = ofNat (succ k)
    // is the same proof, retyped via the defeq target. We finish it as a
    // trans against `refl (ofNat (succ k))` whose type the kernel sees as
    // `mid = ofNat (succ k)` (mid ≡ ofNat (succ k)).
    let mid_to_succ = c.refl_int(of_succ_k.clone()); // : mid = ofNat (succ k)  (defeq)
    let num_eq = c.trans_int(
        l_num.clone(),
        mid.clone(),
        of_succ_k.clone(),
        num_eq_partial,
        mid_to_succ,
    );

    // equiv : Eq Int (Lnum · ofNat 1) (ofNat (succ k) · ofNat 1)
    //   via congrArg (· * ofNat 1) num_eq. This is DEFEQ to the unfolded
    //   `Rat.Raw.Equiv (Raw.mk Lnum (1·1)) (Raw.mk (ofNat (succ k)) 1)`.
    let mul_right_o1 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(c.int.clone());
        let body = c.imul(w, o1.clone());
        let lam = d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
        d.finish_child(lam)
    };
    let equiv = c.congr_int(l_num.clone(), of_succ_k.clone(), mul_right_o1, num_eq);

    // The two raw representatives whose classes the Rat.add result and the RHS
    // `Rat.mk (ofNat (succ k)) 1` are definitionally equal to.
    let nat_one = c.nat_one();
    let raw_l = c.raw_mk(
        l_num.clone(),
        Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [nat_one.clone(), nat_one.clone()],
        ),
    );
    let raw_r = c.raw_mk(of_succ_k.clone(), nat_one.clone());

    // Quot.sound raw_l raw_r equiv : Quot.mk raw_l = Quot.mk raw_r.
    // Quot.mk raw_l ≡ Rat.add (mk (ofNat k) 1) Rat.one  (LHS of the goal),
    // Quot.mk raw_r ≡ Rat.mk (ofNat (succ k)) 1         (RHS of the goal).
    let sound = c.quot_sound(raw_l.clone(), raw_r.clone(), equiv);

    // Retarget to the user-facing goal `Rat.add (...) Rat.one = Rat.mk (...) 1`
    // explicitly via trans against refls (both sides defeq), keeping the proof
    // robust to how the kernel orients the Quot.mk classes.
    let lhs_goal = c.radd(c.rat_natcast(k.clone()), c.rat_one.clone());
    let rhs_goal = c.rat_natcast(succ_k.clone());
    let quot_l = c.quot_mk(raw_l);
    let quot_r = c.quot_mk(raw_r);
    // lhs_goal ≡ quot_l, quot_r ≡ rhs_goal.
    let to_quot_l = c.refl_rat(lhs_goal.clone()); // : lhs_goal = quot_l
    let from_quot_r = c.refl_rat(rhs_goal.clone()); // : quot_r = rhs_goal
    let step1 = c.trans_rat(
        lhs_goal.clone(),
        quot_l.clone(),
        quot_r.clone(),
        to_quot_l,
        sound,
    );
    let proof = c.trans_rat(
        lhs_goal.clone(),
        quot_r.clone(),
        rhs_goal.clone(),
        step1,
        from_quot_r,
    );

    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), proof))
}

// ── A3: Rat.div_self_of_ne_zero ──

/// `∀ a : Rat, (Eq Rat a Rat.zero → False) → Eq Rat (Rat.div a a) Rat.one`.
fn div_self_type(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    // ne : Eq Rat a Rat.zero → False.
    let ne = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let eq0 = c.eq_rat(a.clone(), c.rat_zero.clone());
        let (h_id, _h) = d.fresh_local(eq0.clone());
        d.finish_child(d.mk_pi(h_id, BinderInfo::Default, eq0, c.false_.clone()))
    };
    // concl : Eq Rat (Rat.div a a) Rat.one.
    let div_aa = Expr::apps(c.rat_div.clone(), [a.clone(), a.clone()]);
    let concl = c.eq_rat(div_aa, c.rat_one.clone());
    let (h_id, _h) = b.fresh_local(ne.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, ne, concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

/// `fun (a : Rat) (h : a = 0 → False) => Rat.mul_inv_cancel a h`.
///
/// `Rat.div a a ≡ Rat.mul a (Rat.inv a)` (the reducible `Rat.div` definition),
/// and `Rat.mul_inv_cancel a h : Rat.mul a (Rat.inv a) = Rat.one`, so the same
/// term inhabits the `Rat.div a a = Rat.one` goal by definitional unfolding.
fn div_self_value(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let ne = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let eq0 = c.eq_rat(a.clone(), c.rat_zero.clone());
        let (h_id, _h) = d.fresh_local(eq0.clone());
        d.finish_child(d.mk_pi(h_id, BinderInfo::Default, eq0, c.false_.clone()))
    };
    let (h_id, h) = b.fresh_local(ne.clone());
    let body = Expr::apps(c.rat_mul_inv_cancel.clone(), [a.clone(), h]);
    let val = b.mk_lam(h_id, BinderInfo::Default, ne, body);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

// ── A2: Fin.sum_const_one ──

fn sum_const_one_type(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let lhs = c.sum(n.clone(), c.const_one_fn(&b, &n));
    let concl = c.eq_rat(lhs, c.rat_natcast(n.clone()));
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
}

fn sum_const_one_motive(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lhs = c.sum(k.clone(), c.const_one_fn(&b, &k));
    let body = c.eq_rat(lhs, c.rat_natcast(k.clone()));
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
}

/// Base `motive 0`: `Fin.sum 0 (const 1) ≡ Rat.zero ≡ Rat.mk (Int.ofNat 0) 1`.
/// `Rat.zero ≡ Rat.mk Int.zero 1` and `Int.zero ≡ Int.ofNat Nat.zero`, so the
/// goal `Fin.sum 0 (const 1) = Rat.mk (Int.ofNat 0) 1` closes by reflexivity on
/// the RHS.
fn sum_const_one_base(c: &FinSumConstOneConsts) -> Expr {
    c.refl_rat(c.rat_natcast(c.nat_zero.clone()))
}

/// Step `motive k → motive (k+1)`:
///   `Fin.sum (k+1) (const 1) ≡ Rat.add (Fin.sum k (const 1)) 1`   (Fin.sum_succ ι;
///       cast prefix of `const 1` is `const 1`, last factor is `1`)
///   `= Rat.add (Rat.mk (ofNat k) 1) 1`        (congrArg (· + 1) IH)
///   `= Rat.mk (ofNat (succ k)) 1`             (Rat.add_natCast_one k)
fn sum_const_one_step(c: &FinSumConstOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());

    // ih : Fin.sum k (const 1) = Rat.mk (ofNat k) 1
    let ih_ty = {
        let d = EnvDeclBuilder::child_of(&b);
        let lhs = c.sum(k.clone(), c.const_one_fn(&d, &k));
        d.finish_child(c.eq_rat(lhs, c.rat_natcast(k.clone())))
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let sum_k = c.sum(k.clone(), c.const_one_fn(&b, &k));
    // lhs ≡ Rat.add (Fin.sum k (const 1)) Rat.one
    let lhs = c.radd(sum_k.clone(), c.rat_one.clone());
    // mid = Rat.add (Rat.mk (ofNat k) 1) Rat.one
    let natcast_k = c.rat_natcast(k.clone());
    let mid = c.radd(natcast_k.clone(), c.rat_one.clone());
    let rhs = c.rat_natcast(Expr::app(c.nat_succ.clone(), k.clone()));

    // step1 : lhs = mid    via congrArg (· + 1) ih
    let step1 = c.congr_rat(sum_k, natcast_k, c.add_one_right_fn(&b), ih);
    // step2 : mid = rhs    via Rat.add_natCast_one k
    let step2 = Expr::app(c.rat_add_natcast_one.clone(), k.clone());
    let proof = c.trans_rat(lhs, mid, rhs, step1, step2);

    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

fn sum_const_one_value(c: &FinSumConstOneConsts) -> Expr {
    let motive = sum_const_one_motive(c);
    let base = sum_const_one_base(c);
    let step = sum_const_one_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(val)
}

impl Environment {
    /// Register `Rat.add_natCast_one` (A1), `Fin.sum_const_one` (A2), and
    /// `Rat.div_self_of_ne_zero` (A3) as kernel-checked, constructive theorems.
    /// Idempotent.
    pub(crate) fn register_fin_sum_const_one_theorems(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;
        // `Int.mul_one`, `Fin.sum_succ` are pulled by the towers above; ensure
        // `Int.mul_one` explicitly (it gates A1).
        self.register_int_mul_one_proof()?;

        let c = FinSumConstOneConsts::new();
        if self
            .get_const(&Name::from_string("Rat.add_natCast_one"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Rat.add_natCast_one"),
                level_params: vec![],
                type_: natcast_one_type(&c),
                value: natcast_one_value(&c),
            })?;
        }
        if self
            .get_const(&Name::from_string("Fin.sum_const_one"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.sum_const_one"),
                level_params: vec![],
                type_: sum_const_one_type(&c),
                value: sum_const_one_value(&c),
            })?;
        }
        // A3: Rat.div_self_of_ne_zero. `init_rat` (above) registers the field
        // tower including `Rat.div`, `Rat.inv`, and the `Rat.mul_inv_cancel`
        // Theorem this delegates to.
        if self
            .get_const(&Name::from_string("Rat.div_self_of_ne_zero"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Rat.div_self_of_ne_zero"),
                level_params: vec![],
                type_: div_self_type(&c),
                value: div_self_value(&c),
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_fin_sum_const_one_theorems()
            .expect("register_fin_sum_const_one_theorems");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&Name::from_string(name)),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(name))
                .expect("deps")
                .is_empty(),
            "{name}'s transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_rat_add_natcast_one_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Rat.add_natCast_one");
    }

    #[test]
    fn test_fin_sum_const_one_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Fin.sum_const_one");
    }

    #[test]
    fn test_rat_div_self_of_ne_zero_is_constructive_theorem() {
        // A3 delegates to the constructive `Rat.mul_inv_cancel`, so it inherits
        // an empty admitted-axiom closure (Constructive).
        let env = make_env();
        check_constructive(&env, "Rat.div_self_of_ne_zero");
    }
}
