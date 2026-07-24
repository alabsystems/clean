// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive strict-order cross-multiplication transitivity for `Int`,
//! the strict analogue of `Int.le_cross_trans`. Built for the quotient-`Rat`
//! `Rat.lt` lift respect proofs (`algebra_rat_quotient.rs`).
//!
//! Registers four kernel-checked `Declaration::Theorem`s (no `sorry`, no
//! `add_decl_unchecked`, no domain axioms — only CHECKED `self.add_decl`):
//!
//! 1. `Int.lt_of_mul_lt_mul_left_succ : ∀ (n : Nat) (x y : Int),
//!       Int.lt (k·x) (k·y) → Int.lt x y`   where `k := Int.ofNat (Nat.succ n)`.
//! 2. `Int.mul_lt_mul_of_pos_right_succ : ∀ (n : Nat) (a b : Int),
//!       Int.lt a b → Int.lt (a·k) (b·k)`.
//! 3. `Int.lt_cross_trans : ∀ (na nb nc : Int) (da db dc : Nat),
//!       Int.lt (na·E db) (nb·E da) → Int.le (nb·E dc) (nc·E db) →
//!       Int.lt (na·E dc) (nc·E da)`        where `E k := Int.ofNat (Nat.succ k)`.
//! 4. `Int.lt_cross_trans' : ∀ (na nb nc : Int) (da db dc : Nat),
//!       Int.le (na·E db) (nb·E da) → Int.lt (nb·E dc) (nc·E db) →
//!       Int.lt (na·E dc) (nc·E da)`.
//!
//! All four close with an axiom closure ⊆ FOUNDATIONAL (they reduce to the
//! already-constructive `Int.lt_*` / `Int.le_*` / `Int.mul_*` theorems), so
//! `proof_quality == Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the strict cross-multiplication proof terms.
struct LtCrossConsts {
    int: Expr,
    nat: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    nat_succ: Expr,
    int_lt_irrefl: Expr,
    int_lt_trans: Expr,
    int_lt_of_lt_of_le: Expr,
    int_lt_of_le_of_lt: Expr,
    int_le_of_lt: Expr,
    int_lt_trichotomy: Expr,
    int_mul_le_mul_left: Expr,
    int_mul_le_mul_right: Expr,
    int_mul_le_mul_of_nonneg_right: Expr,
    int_ofnat_zero_le: Expr,
    int_mul_assoc: Expr,
    int_mul_comm: Expr,
    int_mul_rearrange: Expr,
    or_rec: Expr,
    false_elim: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl LtCrossConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int: Expr::const_(Name::from_string("Int"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_lt_irrefl: Expr::const_(Name::from_string("Int.lt_irrefl"), vec![]),
            int_lt_trans: Expr::const_(Name::from_string("Int.lt_trans"), vec![]),
            int_lt_of_lt_of_le: Expr::const_(Name::from_string("Int.lt_of_lt_of_le"), vec![]),
            int_lt_of_le_of_lt: Expr::const_(Name::from_string("Int.lt_of_le_of_lt"), vec![]),
            int_le_of_lt: Expr::const_(Name::from_string("Int.le_of_lt"), vec![]),
            int_lt_trichotomy: Expr::const_(Name::from_string("Int.lt_trichotomy"), vec![]),
            int_mul_le_mul_left: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_left"),
                vec![],
            ),
            int_mul_le_mul_right: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_right"),
                vec![],
            ),
            int_mul_le_mul_of_nonneg_right: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_right"),
                vec![],
            ),
            int_ofnat_zero_le: Expr::const_(Name::from_string("Int.ofNat_zero_le"), vec![]),
            int_mul_assoc: Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
            int_mul_comm: Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
            int_mul_rearrange: Expr::const_(Name::from_string("Int.mul_rearrange"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }
    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }
    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_lt.clone(), [x, y])
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    /// `Int.ofNat (Nat.succ n)`.
    fn of_succ(&self, n: Expr) -> Expr {
        self.of_nat(Expr::app(self.nat_succ.clone(), n))
    }
    /// `Int.le 0 (Int.ofNat (Nat.succ n))` via `Int.ofNat_zero_le (Nat.succ n)`.
    fn nonneg_of_succ(&self, n: Expr) -> Expr {
        Expr::app(
            self.int_ofnat_zero_le.clone(),
            Expr::app(self.nat_succ.clone(), n),
        )
    }
    fn subst(&self, motive: Expr, x: Expr, y: Expr, h_eq: Expr, h_mx: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.int.clone(), motive, x, y, h_eq, h_mx],
        )
    }
    fn symm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int.clone(), x, y, h])
    }
    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.int.clone(), x, y, z, h1, h2])
    }
    fn congr_arg(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int.clone(), self.int.clone(), x, y, f, h],
        )
    }
    fn mul_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul_comm.clone(), [x, y])
    }
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.int_lt_of_lt_of_le.clone(), [a, b, cc, h1, h2])
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.int_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    fn le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.int_le_of_lt.clone(), [a, b, h])
    }
    /// `Int.mul_rearrange a b c : Eq ((a·b)·c) (b·(a·c))`.
    fn mul_rearrange(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.int_mul_rearrange.clone(), [a, b, cc])
    }
    /// `fun (w : Int) => Int.le l w`.
    fn le_left_fn(&self, parent: &EnvDeclBuilder, l: Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(self.int.clone());
        let body = self.le(l.clone(), w);
        let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        mb.finish_child(lam)
    }
    /// `fun (w : Int) => Int.le w r`.
    fn le_right_fn(&self, parent: &EnvDeclBuilder, r: Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(self.int.clone());
        let body = self.le(w, r.clone());
        let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        mb.finish_child(lam)
    }
    /// `fun (w : Int) => Int.lt l w`.
    fn lt_left_fn(&self, parent: &EnvDeclBuilder, l: Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(self.int.clone());
        let body = self.lt(l.clone(), w);
        let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        mb.finish_child(lam)
    }
    /// `fun (w : Int) => Int.lt w r`.
    fn lt_right_fn(&self, parent: &EnvDeclBuilder, r: Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(self.int.clone());
        let body = self.lt(w, r.clone());
        let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        mb.finish_child(lam)
    }
}

impl Environment {
    /// Register the four strict cross-multiplication Int theorems (idempotent).
    pub(crate) fn register_int_lt_cross_trans_only(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies — each idempotent / skip-if-present.
        self.register_int_lt_irrefl_proof()?;
        self.register_int_lt_trans_proof()?;
        self.register_int_lt_of_lt_of_le_proof()?;
        self.register_int_lt_of_le_of_lt_proof()?;
        self.register_int_le_of_lt_proof()?;
        self.register_int_lt_trichotomy_proof()?;
        self.register_int_mul_le_mul_of_nonneg_left_proof()?;
        self.register_int_mul_le_mul_of_nonneg_right_proof()?;
        self.register_int_ofnat_zero_le_proof()?;
        self.register_int_mul_assoc_proof()?;
        self.register_int_mul_comm_proof()?;
        // `Int.le_cross_trans` pulls in `Int.mul_rearrange`; register it so we
        // can reuse the regrouping identity.
        self.register_int_le_cross_trans_only()?;

        let c = LtCrossConsts::new();
        self.register_int_lt_of_mul_lt_mul_left_succ(&c)?;
        self.register_int_mul_lt_mul_of_pos_right_succ(&c)?;
        self.register_int_lt_cross_trans(&c)?;
        self.register_int_lt_cross_trans_prime(&c)?;
        Ok(())
    }

    /// `Int.lt_of_mul_lt_mul_left_succ : ∀ (n : Nat) (x y : Int),
    ///     Int.lt (k·x) (k·y) → Int.lt x y`   (`k := ofNat (succ n)`).
    ///
    /// Trichotomy on `x, y`: the `x < y` case is immediate; the `x = y` and
    /// `y < x` cases each derive `k·x < k·x` (via `Eq.subst` / multiplying the
    /// nonneg `k`), contradicting `Int.lt_irrefl`.
    fn register_int_lt_of_mul_lt_mul_left_succ(
        &mut self,
        c: &LtCrossConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.lt_of_mul_lt_mul_left_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let build = |is_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (x_id, x) = b.fresh_local(c.int.clone());
            let (y_id, y) = b.fresh_local(c.int.clone());
            let k = c.of_succ(n.clone());
            let kx = c.mul(k.clone(), x.clone());
            let ky = c.mul(k.clone(), y.clone());
            let hyp = c.lt(kx.clone(), ky.clone());
            let goal = c.lt(x.clone(), y.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            let result = if !is_value {
                goal.clone()
            } else {
                // major : Or (x<y) (Or (x=y) (y<x)) := Int.lt_trichotomy x y
                let lt_xy = c.lt(x.clone(), y.clone());
                let eq_xy = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [c.int.clone(), x.clone(), y.clone()],
                );
                let lt_yx = c.lt(y.clone(), x.clone());
                let or_inner = Expr::apps(
                    Expr::const_(Name::from_string("Or"), vec![]),
                    [eq_xy.clone(), lt_yx.clone()],
                );

                // Inner Or.rec over (x=y) (y<x), motive `fun _ => x<y`.
                let inner_motive = {
                    let mut om = EnvDeclBuilder::child_of(&b);
                    let (hh_id, _hh) = om.fresh_local(or_inner.clone());
                    let lam = om.mk_lam(hh_id, BinderInfo::Default, or_inner.clone(), goal.clone());
                    om.finish_child(lam)
                };
                // case x=y : k·x = k·y, so h : k·x < k·y ≡ k·x < k·x → False.elim.
                let case_eq = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (he_id, he) = ic.fresh_local(eq_xy.clone());
                    // ky_eq_kx : k·y = k·x  via congrArg (k·) (symm he)
                    let mul_k_fn = {
                        let mut mb = EnvDeclBuilder::child_of(&ic);
                        let (w_id, w) = mb.fresh_local(c.int.clone());
                        let body = c.mul(k.clone(), w);
                        let lam = mb.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                        mb.finish_child(lam)
                    };
                    let he_sym = c.symm(x.clone(), y.clone(), he.clone());
                    let ky_eq_kx = c.congr_arg(y.clone(), x.clone(), mul_k_fn, he_sym);
                    // subst h along (k·y = k·x) in motive (fun w => k·x < w):
                    //   from h : k·x < k·y, get k·x < k·x.
                    let lt_motive = c.lt_left_fn(&ic, kx.clone());
                    let kx_lt_kx = c.subst(lt_motive, ky.clone(), kx.clone(), ky_eq_kx, h.clone());
                    // False from lt_irrefl (k·x) kx_lt_kx, then False.elim.
                    let not_kx_lt_kx = Expr::app(c.int_lt_irrefl.clone(), kx.clone());
                    let false_pf = Expr::app(not_kx_lt_kx, kx_lt_kx);
                    let body = Expr::apps(c.false_elim.clone(), [goal.clone(), false_pf]);
                    let lam = ic.mk_lam(he_id, BinderInfo::Default, eq_xy.clone(), body);
                    ic.finish_child(lam)
                };
                // case y<x : k·y ≤ k·x (mul nonneg left), so h : k·x < k·y ≤ k·x
                //   ⇒ k·x < k·x → False.elim.
                let case_yx = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (hyx_id, hyx) = ic.fresh_local(lt_yx.clone());
                    let hk = c.nonneg_of_succ(n.clone()); // 0 ≤ k
                    let hyx_le = c.le_of_lt(y.clone(), x.clone(), hyx); // y ≤ x
                                                                        // k·y ≤ k·x  via mul_le_mul_of_nonneg_left y x k hyx_le hk
                    let ky_le_kx = Expr::apps(
                        c.int_mul_le_mul_left.clone(),
                        [y.clone(), x.clone(), k.clone(), hyx_le, hk],
                    );
                    // k·x < k·x  via lt_of_lt_of_le (k·x)(k·y)(k·x) h ky_le_kx
                    let kx_lt_kx =
                        c.lt_of_lt_of_le(kx.clone(), ky.clone(), kx.clone(), h.clone(), ky_le_kx);
                    let not_kx_lt_kx = Expr::app(c.int_lt_irrefl.clone(), kx.clone());
                    let false_pf = Expr::app(not_kx_lt_kx, kx_lt_kx);
                    let body = Expr::apps(c.false_elim.clone(), [goal.clone(), false_pf]);
                    let lam = ic.mk_lam(hyx_id, BinderInfo::Default, lt_yx.clone(), body);
                    ic.finish_child(lam)
                };
                let inner_or_rec = |major_inner: Expr| -> Expr {
                    Expr::apps(
                        c.or_rec.clone(),
                        [
                            eq_xy.clone(),
                            lt_yx.clone(),
                            inner_motive.clone(),
                            case_eq.clone(),
                            case_yx.clone(),
                            major_inner,
                        ],
                    )
                };

                // Outer Or.rec over (x<y) (Or (x=y)(y<x)), motive `fun _ => x<y`.
                let outer_motive = {
                    let mut om = EnvDeclBuilder::child_of(&b);
                    let or_ty = Expr::apps(
                        Expr::const_(Name::from_string("Or"), vec![]),
                        [lt_xy.clone(), or_inner.clone()],
                    );
                    let (hh_id, _hh) = om.fresh_local(or_ty.clone());
                    let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone());
                    om.finish_child(lam)
                };
                // case x<y : the witness directly.
                let case_lt = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (hxy_id, hxy) = ic.fresh_local(lt_xy.clone());
                    let lam = ic.mk_lam(hxy_id, BinderInfo::Default, lt_xy.clone(), hxy);
                    ic.finish_child(lam)
                };
                // case (Or (x=y)(y<x)) : run the inner Or.rec on the bound disj.
                let case_inner = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (ho_id, ho) = ic.fresh_local(or_inner.clone());
                    let body = inner_or_rec(ho);
                    let lam = ic.mk_lam(ho_id, BinderInfo::Default, or_inner.clone(), body);
                    ic.finish_child(lam)
                };
                let major = Expr::apps(c.int_lt_trichotomy.clone(), [x.clone(), y.clone()]);
                Expr::apps(
                    c.or_rec.clone(),
                    [
                        lt_xy.clone(),
                        or_inner.clone(),
                        outer_motive,
                        case_lt,
                        case_inner,
                        major,
                    ],
                )
            };

            let mk = |b: &EnvDeclBuilder, id, bi, ty, body| {
                if is_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = mk(&b, h_id, BinderInfo::Default, hyp, result);
            let e = mk(&b, y_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, x_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `Int.mul_lt_mul_of_pos_right_succ : ∀ (n : Nat) (a b : Int),
    ///     Int.lt a b → Int.lt (a·k) (b·k)`   (`k := ofNat (succ n)`).
    ///
    /// Trichotomy on `a·k, b·k`: the `a·k < b·k` case is immediate. In the
    /// other two cases we cancel `k` (after `mul_comm`) via
    /// `Int.lt_of_mul_lt_mul_left_succ` / antisymmetry, obtaining `b ≤ a` or
    /// `b < a`, which contradicts `a < b`.
    fn register_int_mul_lt_mul_of_pos_right_succ(
        &mut self,
        c: &LtCrossConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.mul_lt_mul_of_pos_right_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let cancel = Expr::const_(Name::from_string("Int.lt_of_mul_lt_mul_left_succ"), vec![]);

        let build = |is_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let k = c.of_succ(n.clone());
            let ak = c.mul(a.clone(), k.clone());
            let bk = c.mul(bv.clone(), k.clone());
            let hyp = c.lt(a.clone(), bv.clone());
            let goal = c.lt(ak.clone(), bk.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            let result = if !is_value {
                goal.clone()
            } else {
                // major : Or (ak<bk) (Or (ak=bk) (bk<ak)) := lt_trichotomy ak bk
                let lt_akbk = c.lt(ak.clone(), bk.clone());
                let eq_akbk = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [c.int.clone(), ak.clone(), bk.clone()],
                );
                let lt_bkak = c.lt(bk.clone(), ak.clone());
                let or_inner = Expr::apps(
                    Expr::const_(Name::from_string("Or"), vec![]),
                    [eq_akbk.clone(), lt_bkak.clone()],
                );

                // helper: k·a < k·b  from h, via mul_comm rewrites, then cancel.
                // We will instead directly produce `b < a` / `a = b` and clash.
                //
                // case ak=bk : cancel to a=b, then a<b ≡ a<a → irrefl.
                let inner_motive = {
                    let mut om = EnvDeclBuilder::child_of(&b);
                    let (hh_id, _hh) = om.fresh_local(or_inner.clone());
                    let lam = om.mk_lam(hh_id, BinderInfo::Default, or_inner.clone(), goal.clone());
                    om.finish_child(lam)
                };
                let case_eq = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (he_id, he) = ic.fresh_local(eq_akbk.clone());
                    // From he : a·k = b·k, transport h : a < b along `b = a`?
                    // We need a contradiction. Get `a·k < b·k` is false-ish, but
                    // cleaner: from he, a·k = b·k. We have h : a < b. Multiply h
                    // is what we want to PROVE, so instead clash by cancelling:
                    //   ka = kb via mul_comm twice, then cancel → a = b, subst
                    //   into h to get a < a, irrefl.
                    // ka_eq_kb : k·a = k·b
                    let ka = c.mul(k.clone(), a.clone());
                    let kb = c.mul(k.clone(), bv.clone());
                    // k·a = a·k [mul_comm], a·k = b·k [he], b·k = k·b [mul_comm]
                    let cm1 = c.mul_comm(k.clone(), a.clone()); // k·a = a·k
                    let cm2 = c.mul_comm(bv.clone(), k.clone()); // b·k = k·b
                    let t1 = c.trans(ka.clone(), ak.clone(), bk.clone(), cm1, he.clone());
                    let ka_eq_kb = c.trans(ka.clone(), bk.clone(), kb.clone(), t1, cm2);
                    // Cancel via mul_left_cancel_ofNat_succ n a b ka_eq_kb : a = b
                    let a_eq_b = Expr::apps(
                        Expr::const_(Name::from_string("Int.mul_left_cancel_ofNat_succ"), vec![]),
                        [n.clone(), a.clone(), bv.clone(), ka_eq_kb],
                    );
                    // subst h : a < b along (b = a) → a < a. We have a = b; need
                    // b = a = symm.
                    let b_eq_a = c.symm(a.clone(), bv.clone(), a_eq_b);
                    let lt_motive = c.lt_left_fn(&ic, a.clone());
                    let a_lt_a = c.subst(lt_motive, bv.clone(), a.clone(), b_eq_a, h.clone());
                    let not_a_lt_a = Expr::app(c.int_lt_irrefl.clone(), a.clone());
                    let false_pf = Expr::app(not_a_lt_a, a_lt_a);
                    let body = Expr::apps(c.false_elim.clone(), [goal.clone(), false_pf]);
                    let lam = ic.mk_lam(he_id, BinderInfo::Default, eq_akbk.clone(), body);
                    ic.finish_child(lam)
                };
                // case bk<ak : cancel (after mul_comm) to b<a, then a<b<a→a<a.
                let case_bkak = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (hba_id, hba) = ic.fresh_local(lt_bkak.clone());
                    // hba : b·k < a·k. Rewrite to k·b < k·a via mul_comm, then
                    // cancel via Int.lt_of_mul_lt_mul_left_succ to get b < a.
                    let ka = c.mul(k.clone(), a.clone());
                    let kb = c.mul(k.clone(), bv.clone());
                    // bk_eq_kb : b·k = k·b ; ak_eq_ka : a·k = k·a
                    let bk_eq_kb = c.mul_comm(bv.clone(), k.clone());
                    let ak_eq_ka = c.mul_comm(a.clone(), k.clone());
                    // step1 : k·b < a·k   [subst hba along b·k = k·b in (· < a·k)]
                    let lt_r_motive = c.lt_right_fn(&ic, ak.clone());
                    let kb_lt_ak = c.subst(lt_r_motive, bk.clone(), kb.clone(), bk_eq_kb, hba);
                    // step2 : k·b < k·a   [subst step1 along a·k = k·a in (k·b < ·)]
                    let lt_l_motive = c.lt_left_fn(&ic, kb.clone());
                    let kb_lt_ka = c.subst(lt_l_motive, ak.clone(), ka.clone(), ak_eq_ka, kb_lt_ak);
                    // cancel : b < a
                    let b_lt_a =
                        Expr::apps(cancel.clone(), [n.clone(), bv.clone(), a.clone(), kb_lt_ka]);
                    // a < a via lt_trans a b a h b_lt_a
                    let a_lt_a = Expr::apps(
                        c.int_lt_trans.clone(),
                        [a.clone(), bv.clone(), a.clone(), h.clone(), b_lt_a],
                    );
                    let not_a_lt_a = Expr::app(c.int_lt_irrefl.clone(), a.clone());
                    let false_pf = Expr::app(not_a_lt_a, a_lt_a);
                    let body = Expr::apps(c.false_elim.clone(), [goal.clone(), false_pf]);
                    let lam = ic.mk_lam(hba_id, BinderInfo::Default, lt_bkak.clone(), body);
                    ic.finish_child(lam)
                };
                let inner_or_rec = |major_inner: Expr| -> Expr {
                    Expr::apps(
                        c.or_rec.clone(),
                        [
                            eq_akbk.clone(),
                            lt_bkak.clone(),
                            inner_motive.clone(),
                            case_eq.clone(),
                            case_bkak.clone(),
                            major_inner,
                        ],
                    )
                };
                let outer_motive = {
                    let mut om = EnvDeclBuilder::child_of(&b);
                    let or_ty = Expr::apps(
                        Expr::const_(Name::from_string("Or"), vec![]),
                        [lt_akbk.clone(), or_inner.clone()],
                    );
                    let (hh_id, _hh) = om.fresh_local(or_ty.clone());
                    let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone());
                    om.finish_child(lam)
                };
                let case_lt = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (hlt_id, hlt) = ic.fresh_local(lt_akbk.clone());
                    let lam = ic.mk_lam(hlt_id, BinderInfo::Default, lt_akbk.clone(), hlt);
                    ic.finish_child(lam)
                };
                let case_inner = {
                    let mut ic = EnvDeclBuilder::child_of(&b);
                    let (ho_id, ho) = ic.fresh_local(or_inner.clone());
                    let body = inner_or_rec(ho);
                    let lam = ic.mk_lam(ho_id, BinderInfo::Default, or_inner.clone(), body);
                    ic.finish_child(lam)
                };
                let major = Expr::apps(c.int_lt_trichotomy.clone(), [ak.clone(), bk.clone()]);
                Expr::apps(
                    c.or_rec.clone(),
                    [
                        lt_akbk.clone(),
                        or_inner.clone(),
                        outer_motive,
                        case_lt,
                        case_inner,
                        major,
                    ],
                )
            };

            let mk = |b: &EnvDeclBuilder, id, bi, ty, body| {
                if is_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = mk(&b, h_id, BinderInfo::Default, hyp, result);
            let e = mk(&b, bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, a_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `Int.lt_cross_trans` (lt, le → lt). See module docs for the type.
    fn register_int_lt_cross_trans(&mut self, c: &LtCrossConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.lt_cross_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.build_cross(c, &name, /*h1_strict=*/ true)
    }

    /// `Int.lt_cross_trans'` (le, lt → lt). See module docs for the type.
    fn register_int_lt_cross_trans_prime(&mut self, c: &LtCrossConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.lt_cross_trans'");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.build_cross(c, &name, /*h1_strict=*/ false)
    }

    /// Shared builder for `Int.lt_cross_trans` / `Int.lt_cross_trans'`.
    ///
    /// When `h1_strict`, `h1 : Int.lt (na·eb)(nb·ea)`, `h2 : Int.le (nb·ec)(nc·eb)`.
    /// Otherwise `h1 : Int.le (na·eb)(nb·ea)`, `h2 : Int.lt (nb·ec)(nc·eb)`.
    /// Conclusion (always strict): `Int.lt (na·ec)(nc·ea)`.
    fn build_cross(
        &mut self,
        c: &LtCrossConsts,
        name: &Name,
        h1_strict: bool,
    ) -> Result<(), EnvError> {
        let mul_lt_right = Expr::const_(
            Name::from_string("Int.mul_lt_mul_of_pos_right_succ"),
            vec![],
        );

        let build = |is_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (na_id, na) = b.fresh_local(c.int.clone());
            let (nb_id, nb) = b.fresh_local(c.int.clone());
            let (nc_id, nc) = b.fresh_local(c.int.clone());
            let (da_id, da) = b.fresh_local(c.nat.clone());
            let (db_id, db) = b.fresh_local(c.nat.clone());
            let (dc_id, dc) = b.fresh_local(c.nat.clone());
            let ea = c.of_succ(da.clone());
            let eb = c.of_succ(db.clone());
            let ec = c.of_succ(dc.clone());

            let na_eb = c.mul(na.clone(), eb.clone());
            let nb_ea = c.mul(nb.clone(), ea.clone());
            let nb_ec = c.mul(nb.clone(), ec.clone());
            let nc_eb = c.mul(nc.clone(), eb.clone());

            // h1 type/value differs by strictness; h2 the complement.
            let h1_ty = if h1_strict {
                c.lt(na_eb.clone(), nb_ea.clone())
            } else {
                c.le(na_eb.clone(), nb_ea.clone())
            };
            let h2_ty = if h1_strict {
                c.le(nb_ec.clone(), nc_eb.clone())
            } else {
                c.lt(nb_ec.clone(), nc_eb.clone())
            };
            let goal = c.lt(c.mul(na.clone(), ec.clone()), c.mul(nc.clone(), ea.clone()));
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());

            let result = if !is_value {
                goal.clone()
            } else {
                // s1 : (na·eb)·ec  R1  (nb·ea)·ec   (R1 = < if h1_strict else ≤)
                //   multiply h1 by ec.
                let na_eb_ec = c.mul(na_eb.clone(), ec.clone());
                let nb_ea_ec = c.mul(nb_ea.clone(), ec.clone());
                let s1 = if h1_strict {
                    // mul_lt_mul_of_pos_right_succ dc (na·eb) (nb·ea) h1
                    Expr::apps(
                        mul_lt_right.clone(),
                        [dc.clone(), na_eb.clone(), nb_ea.clone(), h1.clone()],
                    )
                } else {
                    // mul_le_mul_of_nonneg_right (na·eb)(nb·ea) ec h1 (0≤ec)
                    let hec = c.nonneg_of_succ(dc.clone());
                    Expr::apps(
                        c.int_mul_le_mul_of_nonneg_right.clone(),
                        [na_eb.clone(), nb_ea.clone(), ec.clone(), h1.clone(), hec],
                    )
                };
                // s2 : (nb·ec)·ea  R2  (nc·eb)·ea   (R2 = ≤ if h1_strict else <)
                //   multiply h2 by ea.
                let nb_ec_ea = c.mul(nb_ec.clone(), ea.clone());
                let nc_eb_ea = c.mul(nc_eb.clone(), ea.clone());
                let s2 = if h1_strict {
                    let hea = c.nonneg_of_succ(da.clone());
                    Expr::apps(
                        c.int_mul_le_mul_of_nonneg_right.clone(),
                        [nb_ec.clone(), nc_eb.clone(), ea.clone(), h2.clone(), hea],
                    )
                } else {
                    Expr::apps(
                        mul_lt_right.clone(),
                        [da.clone(), nb_ec.clone(), nc_eb.clone(), h2.clone()],
                    )
                };

                // bridge : (nb·ea)·ec = (nb·ec)·ea
                //   mr1 : (nb·ea)·ec = ea·(nb·ec)  [mul_rearrange nb ea ec]
                //   cm  : ea·(nb·ec) = (nb·ec)·ea  [mul_comm ea (nb·ec)]
                let ea_nbec = c.mul(ea.clone(), nb_ec.clone());
                let mr1 = c.mul_rearrange(nb.clone(), ea.clone(), ec.clone());
                let cm = c.mul_comm(ea.clone(), nb_ec.clone());
                let bridge = c.trans(nb_ea_ec.clone(), ea_nbec.clone(), nb_ec_ea.clone(), mr1, cm);

                // s1' : (na·eb)·ec  R1  (nb·ec)·ea   (rewrite s1's RHS via bridge)
                let s1p = {
                    let motive = if h1_strict {
                        c.lt_left_fn(&b, na_eb_ec.clone())
                    } else {
                        c.le_left_fn(&b, na_eb_ec.clone())
                    };
                    c.subst(motive, nb_ea_ec.clone(), nb_ec_ea.clone(), bridge, s1)
                };

                // chained : (na·eb)·ec < (nc·eb)·ea
                //   one of s1p/s2 is strict, the other ≤; combine accordingly.
                let chained = if h1_strict {
                    // s1p : lt ; s2 : le  → lt_of_lt_of_le
                    c.lt_of_lt_of_le(
                        na_eb_ec.clone(),
                        nb_ec_ea.clone(),
                        nc_eb_ea.clone(),
                        s1p,
                        s2,
                    )
                } else {
                    // s1p : le ; s2 : lt  → lt_of_le_of_lt
                    c.lt_of_le_of_lt(
                        na_eb_ec.clone(),
                        nb_ec_ea.clone(),
                        nc_eb_ea.clone(),
                        s1p,
                        s2,
                    )
                };

                // Regroup eb to the left and cancel:
                //   (na·eb)·ec = eb·(na·ec)  [mul_rearrange na eb ec]
                //   (nc·eb)·ea = eb·(nc·ea)  [mul_rearrange nc eb ea]
                let na_ec = c.mul(na.clone(), ec.clone());
                let nc_ea = c.mul(nc.clone(), ea.clone());
                let eb_na_ec = c.mul(eb.clone(), na_ec.clone());
                let eb_nc_ea = c.mul(eb.clone(), nc_ea.clone());
                let mr_l = c.mul_rearrange(na.clone(), eb.clone(), ec.clone());
                let mr_r = c.mul_rearrange(nc.clone(), eb.clone(), ea.clone());
                // rewrite LHS of `chained`
                let motive_l = c.lt_right_fn(&b, nc_eb_ea.clone());
                let step_l = c.subst(motive_l, na_eb_ec.clone(), eb_na_ec.clone(), mr_l, chained);
                // rewrite RHS
                let motive_r = c.lt_left_fn(&b, eb_na_ec.clone());
                let grouped = c.subst(motive_r, nc_eb_ea.clone(), eb_nc_ea.clone(), mr_r, step_l);
                // cancel eb = ofNat(succ db) strictly:
                //   Int.lt_of_mul_lt_mul_left_succ db (na·ec)(nc·ea) grouped
                Expr::apps(
                    Expr::const_(Name::from_string("Int.lt_of_mul_lt_mul_left_succ"), vec![]),
                    [db.clone(), na_ec.clone(), nc_ea.clone(), grouped],
                )
            };

            let mk = |b: &EnvDeclBuilder, id, bi, ty, body| {
                if is_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = mk(&b, h2_id, BinderInfo::Default, h2_ty, result);
            let e = mk(&b, h1_id, BinderInfo::Default, h1_ty, e);
            let e = mk(&b, dc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = mk(&b, db_id, BinderInfo::Default, c.nat.clone(), e);
            let e = mk(&b, da_id, BinderInfo::Default, c.nat.clone(), e);
            let e = mk(&b, nc_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, nb_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, na_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }
}
