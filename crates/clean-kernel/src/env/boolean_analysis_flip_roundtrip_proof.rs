// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Route (a) toward `influence_fourier`: the XOR roundtrip
//! `hcFlip n (hcDecode n jx) i = hcDecode n (flipIdx i jx)`, the keystone that
//! promotes `subsetSum_inversion_core` from decoded points to the FLIPPED point
//! `hcFlip n (hcDecode n jx) i` (the single irreducible gap documented in
//! `influence_fourier_proof.rs`).
//!
//! The bit-level identity that drives the roundtrip is, per coordinate `j`:
//!   `testBit (Nat.xor (val jx) (2^(val i))) (val j)`
//!     = Bool.xor (testBit (val jx) (val j)) (testBit (2^(val i)) (val j))   (testBit_xor)
//!     = Bool.xor (hcDecode jx j) (Nat.beq (val j) (val i))                   (testBit_two_pow)
//!     = hcFlip n (hcDecode n jx) i j                                          (xor_eq_flip_gate)
//!
//! Pieces LANDED here (all kernel-checked, axiom-free / `ProofQuality::Constructive`):
//!
//! - `Nat.two_pow_lt_two_pow_of_lt : ∀ i j, Nat.lt i j → Nat.lt (2^i) (2^j)`
//!   — strict monotonicity of `2^·`. From `i < j` (≡ `succ i ≤ j`),
//!   `pow_le_pow_right 2 (succ i) j (1≤2) h : 2^(succ i) ≤ 2^j`, and
//!   `2^i < 2^(succ i)` from `add_lt_add_left 0 (2^i) (one_le_two_pow i) (2^i)`
//!   (`2^i + 0 ≡ 2^i` defeq) transported along `pow_two_succ i`. `le_trans` on
//!   `succ (2^i)` chains them (`lt x y ≡ le (succ x) y`).
//!
//! - `Nat.testBit_two_pow : ∀ i j, @Eq Bool (Nat.testBit (2^i) j) (Nat.beq j i)`
//!   — bit `j` of `2^i` is `true` iff `j = i`. Trichotomy via two nested
//!   `Nat.le_or_lt` / `Nat.lt_or_eq_of_le` splits:
//!     * `j = i` (diagonal): `testBit_add_two_pow_self i 0 (0<2^i)`
//!       (`2^i + 0 ≡ 2^i`), `Nat.beq i i = true` (`beq_refl`);
//!     * `i < j` (high): `testBit_lt_pow j (2^i) (2^i<2^j)` = false,
//!       `Nat.beq j i = false` (`beq_eq_false_of_ne`, `j ≠ i` from `i < j`);
//!     * `j < i` (low): `testBit_add_two_pow_lo i 0 j (0<2^i)(j<i)`
//!       = `testBit 0 j ≡ false`, `Nat.beq j i = false` (`j ≠ i` from `j < i`).
//!
//! All `Nat.lt`-trichotomy splitting goes through the CONSTRUCTIVE `Nat.le_or_lt`
//! / `Nat.lt_or_eq_of_le` (NOT the admitted `Nat.lt_trichotomy` axiom), so the
//! admitted-axiom closure stays empty.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the flip-roundtrip proofs.
struct RtConsts {
    nat: Expr,
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    pow: Expr,
    two: Expr,
    nat_lt: Expr,
    nat_le: Expr,
    nat_beq: Expr,
    testbit: Expr,
    bool_xor: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst: Expr,
    #[cfg(test)]
    false_c: Expr,
    #[cfg(test)]
    false_elim0: Expr,
    or_c: Expr,
    or_rec: Expr,
}

impl RtConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let two = Expr::app(succ.clone(), Expr::app(succ.clone(), zero.clone()));
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            zero,
            succ,
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two,
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![one]),
            #[cfg(test)]
            false_c: Expr::const_(Name::from_string("False"), vec![]),
            #[cfg(test)]
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            or_c: Expr::const_(Name::from_string("Or"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
        }
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    fn add_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    fn div2_of(&self, x: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Nat.div2"), vec![]), x)
    }
    fn div2par_of(&self, x: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Nat.div2Par"), vec![]), x)
    }
    fn pow2(&self, e: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [self.two.clone(), e])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn beq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_beq.clone(), [a, b])
    }
    fn testbit(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, i])
    }
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), l, r])
    }
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), a])
    }
    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nat.clone(), a, b, h])
    }
    /// `@Eq.subst.{1} Nat motive a b (h : a = b) (pa : motive a) : motive b`.
    fn subst_nat(&self, motive: Expr, a: Expr, b: Expr, h: Expr, pa: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat.clone(), motive, a, b, h, pa],
        )
    }
    fn or_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.or_c.clone(), [a, b])
    }
    /// `(h : a = b → False)`-shaped pi (a `Nat`-disequality).
    #[cfg(test)]
    fn ne_nat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.eq_nat(a, b), self.false_c.clone())
    }
}

// ===========================================================================
// Nat.two_pow_lt_two_pow_of_lt : ∀ i j, Nat.lt i j → Nat.lt (2^i) (2^j)
// ===========================================================================
fn build_two_pow_lt_two_pow_of_lt(c: &RtConsts) -> (Expr, Expr) {
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let (j_id, j) = b.fresh_local(c.nat.clone());
        let h_ty = c.lt(i.clone(), j.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.lt(c.pow2(i.clone()), c.pow2(j.clone()));
        let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let e = b.mk_pi(j_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let (j_id, j) = b.fresh_local(c.nat.clone());
        let h_ty = c.lt(i.clone(), j.clone()); // ≡ le (succ i) j
        let (h_id, h) = b.fresh_local(h_ty.clone());

        let p_i = c.pow2(i.clone()); // 2^i
        let si = c.succ_of(i.clone()); // succ i
        let p_si = c.pow2(si.clone()); // 2^(succ i)
        let p_j = c.pow2(j.clone()); // 2^j

        // one_le_two : Nat.le 1 2 := Nat.le.step (Nat.le.refl 1) ... build via le_succ_of_le
        //   1 ≤ 2 ≡ Nat.le (succ 0) (succ (succ 0)). Use Nat.succ_le_succ 0 1 (Nat.zero_le 1)?
        //   Simpler: Nat.le_succ_of_le (Nat.le.refl 1).  We use Nat.one_le_two_pow 0 : 1 ≤ 2^0 ≡ 1,
        //   which is NOT 1 ≤ 2. Instead: pow_le_pow_right needs (1 ≤ 2). Build it directly.
        let one = c.succ_of(c.zero.clone());
        let two = c.two.clone();
        // Nat.le.refl 1 : le 1 1 (the `Nat.le` reflexivity constructor).
        let le_refl_one = Expr::apps(
            Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            [one.clone()],
        );
        // @Nat.le.step 1 1 (le 1 1) : le 1 (succ 1) ≡ le 1 2  (the step constructor,
        //   `{n m : Nat} → Nat.le n m → Nat.le n (succ m)`; both indices explicit here).
        let one_le_two = Expr::apps(
            Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            [one.clone(), one.clone(), le_refl_one],
        );

        // step1 : 2^(succ i) ≤ 2^j := pow_le_pow_right 2 (succ i) j one_le_two h
        let step1 = Expr::apps(
            Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
            [two.clone(), si.clone(), j.clone(), one_le_two, h.clone()],
        );

        // h0 : 0 < 2^i ≡ le 1 (2^i) := Nat.one_le_two_pow i
        let h0 = Expr::app(
            Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
            i.clone(),
        );
        // add_lt_add_left 0 (2^i) h0 (2^i) : lt (2^i + 0) (2^i + 2^i)   [2^i + 0 ≡ 2^i defeq]
        let step2_raw = Expr::apps(
            Expr::const_(Name::from_string("Nat.add_lt_add_left"), vec![]),
            [c.zero.clone(), p_i.clone(), h0, p_i.clone()],
        );
        // pow_two_succ i : 2^(succ i) = 2^i + 2^i ; transport the RHS bound to 2^(succ i).
        // step2_raw : lt (2^i) (2^i + 2^i) ≡ le (succ (2^i)) (2^i + 2^i)
        // motive z := le (succ (2^i)) z ; subst along (pow_two_succ i).symm : (2^i+2^i) = 2^(succ i)
        let pp = c.add_of(p_i.clone(), p_i.clone());
        let pts = Expr::app(
            Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            i.clone(),
        ); // : 2^(succ i) = 2^i + 2^i
        let pts_symm = c.symm_nat(p_si.clone(), pp.clone(), pts); // : (2^i+2^i) = 2^(succ i)
        let succ_pi = c.succ_of(p_i.clone());
        let m_le_succ_pi = {
            let mut lb = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = lb.fresh_local(c.nat.clone());
            let body = c.le(succ_pi.clone(), z);
            lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
        };
        // step2 : le (succ (2^i)) (2^(succ i)) ≡ lt (2^i) (2^(succ i))
        let step2 = c.subst_nat(m_le_succ_pi, pp.clone(), p_si.clone(), pts_symm, step2_raw);

        // le_trans (succ (2^i)) (2^(succ i)) (2^j) step2 step1 : le (succ (2^i)) (2^j) ≡ lt (2^i) (2^j)
        let out = Expr::apps(
            Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            [succ_pi, p_si, p_j, step2, step1],
        );

        let lam = b.mk_lam(h_id, BinderInfo::Default, h_ty, out);
        let lam = b.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = b.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
        b.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Nat.testBit_two_pow : ∀ i j, @Eq Bool (Nat.testBit (2^i) j) (Nat.beq j i)
// ===========================================================================
fn build_testbit_two_pow(c: &RtConsts) -> (Expr, Expr) {
    // goal(i,j) := testBit (2^i) j = Nat.beq j i
    let goal = |i: &Expr, j: &Expr| {
        c.eq_bool(
            c.testbit(c.pow2(i.clone()), j.clone()),
            c.beq(j.clone(), i.clone()),
        )
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let (j_id, j) = b.fresh_local(c.nat.clone());
        let concl = goal(&i, &j);
        let e = b.mk_pi(j_id, BinderInfo::Default, c.nat.clone(), concl);
        let e = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let (j_id, j) = b.fresh_local(c.nat.clone());

        // h0 : 0 < 2^i ≡ le 1 (2^i)  (for add_two_pow lemmas, which need lt k (2^i) with k=0)
        let h0 = Expr::app(
            Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
            i.clone(),
        );

        // ---- DIAGONAL leaf: given heq : i = j, prove goal(i,j) ----
        // testBit (2^i) i = true  via testBit_add_two_pow_self i 0 h0  (2^i + 0 ≡ 2^i)
        // Nat.beq i i = true via Nat.beq_refl i. Then transport i↦j on both occurrences.
        let diag_leaf = {
            let mut db = EnvDeclBuilder::child_of(&b);
            let (heq_id, heq) = db.fresh_local(c.eq_nat(i.clone(), j.clone())); // i = j
                                                                                // lhs_i : testBit (2^i) i = true
            let lhs_i = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_add_two_pow_self"), vec![]),
                [i.clone(), c.zero.clone(), h0.clone()],
            );
            // beq_i : Nat.beq i i = true
            let beq_i = Expr::app(
                Expr::const_(Name::from_string("Nat.beq_refl"), vec![]),
                i.clone(),
            );
            // base goal at j:=i : testBit (2^i) i = Nat.beq i i
            //   = Eq.trans (lhs_i) (Eq.symm beq_i) : testBit (2^i) i = Nat.beq i i
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            let beq_i_symm = Expr::apps(
                c.eq_symm1.clone(),
                [
                    c.bool_ty.clone(),
                    c.beq(i.clone(), i.clone()),
                    c.btrue.clone(),
                    beq_i,
                ],
            );
            let base = Expr::apps(
                eq_trans,
                [
                    c.bool_ty.clone(),
                    c.testbit(c.pow2(i.clone()), i.clone()),
                    c.btrue.clone(),
                    c.beq(i.clone(), i.clone()),
                    lhs_i,
                    beq_i_symm,
                ],
            );
            // motive z := testBit (2^i) z = Nat.beq z i  (transport i ↦ z)
            let m = {
                let mut lb = EnvDeclBuilder::child_of(&db);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_bool(
                    c.testbit(c.pow2(i.clone()), z.clone()),
                    c.beq(z.clone(), i.clone()),
                );
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // subst_nat m i j heq base : goal(i,j)
            let out = c.subst_nat(m, i.clone(), j.clone(), heq, base);
            db.finish_child(db.mk_lam(
                heq_id,
                BinderInfo::Default,
                c.eq_nat(i.clone(), j.clone()),
                out,
            ))
        };

        // ---- helper: from hne : (j = i → False), build  Nat.beq j i = false ----
        let beq_false_of_jne_i = |hne: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Nat.beq_eq_false_of_ne"), vec![]),
                [j.clone(), i.clone(), hne],
            )
        };

        // ---- helper: glue  (lhs_false : testBit (2^i) j = false) and
        //   (beq_false : Nat.beq j i = false)  into goal(i,j) via Eq.trans + symm ----
        let glue_false = |db: &EnvDeclBuilder, lhs_false: Expr, beq_false: Expr| {
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            // beq_false.symm : false = Nat.beq j i
            let beq_false_symm = Expr::apps(
                c.eq_symm1.clone(),
                [
                    c.bool_ty.clone(),
                    c.beq(j.clone(), i.clone()),
                    c.bfalse.clone(),
                    beq_false,
                ],
            );
            // Eq.trans (lhs_false) (beq_false.symm) : testBit (2^i) j = Nat.beq j i
            let _ = db;
            Expr::apps(
                eq_trans,
                [
                    c.bool_ty.clone(),
                    c.testbit(c.pow2(i.clone()), j.clone()),
                    c.bfalse.clone(),
                    c.beq(j.clone(), i.clone()),
                    lhs_false,
                    beq_false_symm,
                ],
            )
        };

        // ---- HIGH leaf: given hij : lt i j (so i < j, bit j is above) ----
        // testBit (2^i) j = false via testBit_lt_pow j (2^i) (2^i < 2^j).
        // Nat.beq j i = false: j ≠ i from i<j, i.e. (e : j = i) → lt_irrefl j (lt i j transported)?
        //   from hij : lt i j and e : j = i, subst gives lt j j (replace i by j in hij?) — careful:
        //   hij : lt i j. e : j = i. We want lt j j: subst i↦j into hij needs e : i = j (have j=i).
        //   Use e.symm : i = j. motive z := lt z j. subst i j e.symm hij : lt j j. lt_irrefl j → False.
        let high_leaf = {
            let mut hb = EnvDeclBuilder::child_of(&b);
            let (hij_id, hij) = hb.fresh_local(c.lt(i.clone(), j.clone()));
            // 2^i < 2^j
            let lt_pow = Expr::apps(
                Expr::const_(Name::from_string("Nat.two_pow_lt_two_pow_of_lt"), vec![]),
                [i.clone(), j.clone(), hij.clone()],
            );
            // testBit_lt_pow j (2^i) lt_pow : testBit (2^i) j = false
            let lhs_false = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
                [j.clone(), c.pow2(i.clone()), lt_pow],
            );
            // hne : (j = i) → False
            let hne = {
                let mut nb = EnvDeclBuilder::child_of(&hb);
                let (e_id, e) = nb.fresh_local(c.eq_nat(j.clone(), i.clone())); // j = i
                let e_symm = c.symm_nat(j.clone(), i.clone(), e); // i = j
                                                                  // motive z := lt z j ; subst i j e_symm hij : lt j j
                let m = {
                    let mut lb = EnvDeclBuilder::child_of(&nb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.lt(z.clone(), j.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let lt_jj = c.subst_nat(m, i.clone(), j.clone(), e_symm, hij.clone());
                let false_pf = Expr::apps(
                    Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
                    [j.clone(), lt_jj],
                );
                nb.finish_child(nb.mk_lam(
                    e_id,
                    BinderInfo::Default,
                    c.eq_nat(j.clone(), i.clone()),
                    false_pf,
                ))
            };
            let beq_false = beq_false_of_jne_i(hne);
            let out = glue_false(&hb, lhs_false, beq_false);
            hb.finish_child(hb.mk_lam(hij_id, BinderInfo::Default, c.lt(i.clone(), j.clone()), out))
        };

        // ---- LOW leaf: given hji : lt j i (so j < i, bit j below) ----
        // testBit (2^i) j = false via testBit_add_two_pow_lo i 0 j h0 hji
        //   : testBit (2^i + 0) j = testBit 0 j ; testBit 0 j ≡ false (rfl), 2^i+0 ≡ 2^i.
        //   So Eq.trans (that) (refl_bool false) : testBit (2^i) j = false.
        // Nat.beq j i = false: j ≠ i from j<i: (e: j=i) → lt_irrefl j (subst j i? ) ...
        //   hji : lt j i. e : j = i. motive z := lt j z. subst j i ... need e : j = i and replace
        //   the SECOND occurrence: subst with a=j,b=i? We have lt j i; want lt j j by i↦j i.e. e.symm.
        //   motive z := lt j z. subst i j e.symm hji : lt j j. lt_irrefl.
        let low_leaf = {
            let mut lb0 = EnvDeclBuilder::child_of(&b);
            let (hji_id, hji) = lb0.fresh_local(c.lt(j.clone(), i.clone()));
            // testBit_add_two_pow_lo i 0 (h0 : lt 0 (2^i)) j (hji : lt j i)
            //   : testBit (2^i + 0) j = testBit 0 j
            //   (signature: (n) (k) (lt k (2^n)) (i) (lt i n) → testBit ((2^n)+k) i = testBit k i)
            let lo = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_add_two_pow_lo"), vec![]),
                [
                    i.clone(),
                    c.zero.clone(),
                    h0.clone(),
                    j.clone(),
                    hji.clone(),
                ],
            );
            // `testBit 0 j = false` is NOT `rfl` for symbolic `j` (testBit recurses on the
            //   index): use the registered `Nat.testBit_zero_eq_false j`.
            let zero_false = Expr::app(
                Expr::const_(Name::from_string("Nat.testBit_zero_eq_false"), vec![]),
                j.clone(),
            );
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            // lhs_false : testBit (2^i + 0) j = false  [≡ testBit (2^i) j = false]
            //   = Eq.trans (lo : testBit (2^i+0) j = testBit 0 j) (zero_false : testBit 0 j = false)
            let lhs_false = Expr::apps(
                eq_trans,
                [
                    c.bool_ty.clone(),
                    c.testbit(c.add_of(c.pow2(i.clone()), c.zero.clone()), j.clone()),
                    c.testbit(c.zero.clone(), j.clone()),
                    c.bfalse.clone(),
                    lo,
                    zero_false,
                ],
            );
            // hne : (j = i) → False  from hji : lt j i
            let hne = {
                let mut nb = EnvDeclBuilder::child_of(&lb0);
                let (e_id, e) = nb.fresh_local(c.eq_nat(j.clone(), i.clone())); // j = i
                let e_symm = c.symm_nat(j.clone(), i.clone(), e); // i = j
                                                                  // motive z := lt j z ; subst i j e_symm hji : lt j j
                let m = {
                    let mut lb = EnvDeclBuilder::child_of(&nb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.lt(j.clone(), z.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let lt_jj = c.subst_nat(m, i.clone(), j.clone(), e_symm, hji.clone());
                let false_pf = Expr::apps(
                    Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
                    [j.clone(), lt_jj],
                );
                nb.finish_child(nb.mk_lam(
                    e_id,
                    BinderInfo::Default,
                    c.eq_nat(j.clone(), i.clone()),
                    false_pf,
                ))
            };
            let beq_false = beq_false_of_jne_i(hne);
            let out = glue_false(&lb0, lhs_false, beq_false);
            lb0.finish_child(lb0.mk_lam(
                hji_id,
                BinderInfo::Default,
                c.lt(j.clone(), i.clone()),
                out,
            ))
        };

        // ---- inner Or.rec on (lt_or_eq_of_le i j h_le_ij) : Or (lt i j) (eq i j) ----
        //   given h_le_ij : le i j, dispatch high_leaf / diag_leaf.
        let inl_branch = {
            let mut ib = EnvDeclBuilder::child_of(&b);
            let (hle_id, hle) = ib.fresh_local(c.le(i.clone(), j.clone()));
            // disj := lt_or_eq_of_le i j hle : Or (lt i j) (eq i j)
            let lt_ij = c.lt(i.clone(), j.clone());
            let eq_ij = c.eq_nat(i.clone(), j.clone());
            let disj = Expr::apps(
                Expr::const_(Name::from_string("Nat.lt_or_eq_of_le"), vec![]),
                [i.clone(), j.clone(), hle],
            );
            // motive (_ : Or (lt i j)(eq i j)) := goal(i,j)
            let or_m = {
                let mut ob = EnvDeclBuilder::child_of(&ib);
                let or_ty = c.or_ty(lt_ij.clone(), eq_ij.clone());
                let (d_id, _d) = ob.fresh_local(or_ty.clone());
                ob.finish_child(ob.mk_lam(d_id, BinderInfo::Default, or_ty, goal(&i, &j)))
            };
            let inner = Expr::apps(
                c.or_rec.clone(),
                [lt_ij, eq_ij, or_m, high_leaf, diag_leaf, disj],
            );
            ib.finish_child(ib.mk_lam(
                hle_id,
                BinderInfo::Default,
                c.le(i.clone(), j.clone()),
                inner,
            ))
        };

        // inr branch : given hji : lt j i, dispatch low_leaf.
        let inr_branch = {
            let mut rb = EnvDeclBuilder::child_of(&b);
            let (hji_id, _hji) = rb.fresh_local(c.lt(j.clone(), i.clone()));
            // low_leaf is `fun (hji : lt j i) => goal`; apply directly is cleaner:
            //   Or.rec's inr expects (lt j i → motive), and low_leaf already has that shape,
            //   so we use low_leaf as the inr directly (below). This branch unused; keep low_leaf.
            let _ = hji_id;
            rb.finish_child(low_leaf.clone())
        };
        let _ = inr_branch;

        // ---- outer Or.rec on (le_or_lt i j) : Or (le i j) (lt j i) ----
        let le_ij = c.le(i.clone(), j.clone());
        let lt_ji = c.lt(j.clone(), i.clone());
        let outer_disj = Expr::apps(
            Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
            [i.clone(), j.clone()],
        );
        let outer_m = {
            let mut ob = EnvDeclBuilder::child_of(&b);
            let or_ty = c.or_ty(le_ij.clone(), lt_ji.clone());
            let (d_id, _d) = ob.fresh_local(or_ty.clone());
            ob.finish_child(ob.mk_lam(d_id, BinderInfo::Default, or_ty, goal(&i, &j)))
        };
        let body = Expr::apps(
            c.or_rec.clone(),
            [le_ij, lt_ji, outer_m, inl_branch, low_leaf, outer_disj],
        );

        let lam = b.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), body);
        let lam = b.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
        b.finish(lam)
    };
    (type_, value)
}

// ===========================================================================
// Nat.lt_two_pow_of_testBit_ge :
//   ∀ (n m : Nat), (∀ k, Nat.le n k → @Eq Bool (testBit m k) false) → Nat.lt m (2^n)
// "If all bits of m at positions ≥ n vanish, then m < 2^n." Bits-determine-bound.
// ===========================================================================
fn build_lt_two_pow_of_testbit_ge(c: &RtConsts) -> (Expr, Expr) {
    // hyp(n,m) := ∀ k, le n k → testBit m k = false
    let hyp_ty = |n: &Expr, m: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut hb = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = hb.fresh_local(c.nat.clone());
        let le_nk = c.le(n.clone(), k.clone());
        let (h_id, _h) = hb.fresh_local(le_nk.clone());
        let bit = c.eq_bool(c.testbit(m.clone(), k.clone()), c.bfalse.clone());
        let imp = hb.mk_pi(h_id, BinderInfo::Default, le_nk, bit);
        hb.finish_child(hb.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), imp))
    };
    // P(n) := ∀ m, hyp(n,m) → lt m (2^n)
    let p_of = |n: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = pb.fresh_local(c.nat.clone());
        let h_ty = hyp_ty(n, &m, &pb);
        let (h_id, _h) = pb.fresh_local(h_ty.clone());
        let concl = c.lt(m.clone(), c.pow2(n.clone()));
        let imp = pb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        pb.finish_child(pb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), imp))
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = p_of(&n, &b);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (n_id, n) = mb.fresh_local(c.nat.clone());
            let body = p_of(&n, &mb);
            mb.finish_child(mb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // ---- base : P 0 := fun m hyp => ... lt m (2^0 ≡ 1) ----
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&vb);
            let (m_id, m) = bb.fresh_local(c.nat.clone());
            let h_ty = hyp_ty(&c.zero, &m, &bb);
            let (h_id, h) = bb.fresh_local(h_ty.clone());
            // all_false : ∀ k, testBit m k = false := fun k => h k (Nat.zero_le k)
            let all_false = {
                let mut ab = EnvDeclBuilder::child_of(&bb);
                let (k_id, k) = ab.fresh_local(c.nat.clone());
                let zero_le_k = Expr::app(
                    Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                    k.clone(),
                );
                let body = Expr::apps(h.clone(), [k.clone(), zero_le_k]);
                ab.finish_child(ab.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // m = 0
            let m_eq_0 = Expr::apps(
                Expr::const_(
                    Name::from_string("Nat.eq_zero_of_testBit_all_false"),
                    vec![],
                ),
                [m.clone(), all_false],
            );
            // lt 0 1 ≡ le (succ 0) (succ 0) = Nat.le.refl 1   (2^0 ≡ 1 ≡ succ 0)
            let one = c.succ_of(c.zero.clone());
            let lt_0_1 = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                [one.clone()],
            );
            // transport 0 ↦ m: motive z := lt z (2^0). subst 0 m (m_eq_0.symm) lt_0_1 : lt m (2^0)
            let m_eq_0_symm = c.symm_nat(m.clone(), c.zero.clone(), m_eq_0);
            let mt = {
                let mut lb = EnvDeclBuilder::child_of(&bb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.lt(z.clone(), c.pow2(c.zero.clone()));
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let out = c.subst_nat(mt, c.zero.clone(), m.clone(), m_eq_0_symm, lt_0_1);
            let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        // ---- step : (n') → P n' → P (succ n') ----
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (np_id, np) = sb.fresh_local(c.nat.clone());
            let ih_ty = p_of(&np, &sb);
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            let sn = c.succ_of(np.clone());

            let (m_id, m) = sb.fresh_local(c.nat.clone());
            let h_ty = hyp_ty(&sn, &m, &sb);
            let (h_id, h) = sb.fresh_local(h_ty.clone());

            let r = c.div2_of(m.clone()); // div2 m
            let p = c.div2par_of(m.clone()); // div2Par m
            let pn = c.pow2(np.clone()); // 2^n'
            let rr = c.add_of(r.clone(), r.clone()); // r+r
            let rrp = c.add_of(rr.clone(), p.clone()); // (r+r)+p

            // hyp' : ∀ k, le n' k → testBit r k = false
            //   := fun k hle => h (succ k) (succ_le_succ n' k hle)
            //   (testBit r k ≡ testBit (div2 m) k ≡ testBit m (succ k) by iterDiv2 peel)
            let hyp_r = {
                let mut hb = EnvDeclBuilder::child_of(&sb);
                let (k_id, k) = hb.fresh_local(c.nat.clone());
                let le_npk = c.le(np.clone(), k.clone());
                let (hle_id, hle) = hb.fresh_local(le_npk.clone());
                // succ_le_succ n' k hle : le (succ n') (succ k)
                let sls = Expr::apps(
                    Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
                    [np.clone(), k.clone(), hle],
                );
                // h (succ k) sls : testBit m (succ k) = false ≡ testBit r k = false
                let body = Expr::apps(h.clone(), [c.succ_of(k.clone()), sls]);
                let lam = hb.mk_lam(hle_id, BinderInfo::Default, le_npk, body);
                hb.finish_child(hb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            // ih_r : lt r (2^n') ≡ le (succ r) (2^n')
            let ih_r = Expr::apps(ih.clone(), [r.clone(), hyp_r]);

            // hp_le_1 : le p 1  (from div2Par_zero_or_one m)
            let one = c.succ_of(c.zero.clone());
            let hp_le_1 = {
                // disj := div2Par_zero_or_one m : Or (p = 0) (p = 1)
                let disj = Expr::app(
                    Expr::const_(Name::from_string("Nat.div2Par_zero_or_one"), vec![]),
                    m.clone(),
                );
                let p_eq_0 = c.eq_nat(p.clone(), c.zero.clone());
                let p_eq_1 = c.eq_nat(p.clone(), one.clone());
                // motive (_ : Or ..) := le p 1
                let or_m = {
                    let mut ob = EnvDeclBuilder::child_of(&sb);
                    let or_ty = c.or_ty(p_eq_0.clone(), p_eq_1.clone());
                    let (d_id, _d) = ob.fresh_local(or_ty.clone());
                    ob.finish_child(ob.mk_lam(
                        d_id,
                        BinderInfo::Default,
                        or_ty,
                        c.le(p.clone(), one.clone()),
                    ))
                };
                // inl (he : p = 0) → le p 1 : transport p:=0; base le 0 1 = le.step (le.refl 0)
                //   subst with motive z := le z 1, a=0,b=p, h:(0=p)=he.symm, pa: le 0 1.
                let inl = {
                    let mut ib = EnvDeclBuilder::child_of(&sb);
                    let (he_id, he) = ib.fresh_local(p_eq_0.clone());
                    let le_0_1 = Expr::apps(
                        Expr::const_(Name::from_string("Nat.le.step"), vec![]),
                        [
                            c.zero.clone(),
                            c.zero.clone(),
                            Expr::apps(
                                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                                [c.zero.clone()],
                            ),
                        ],
                    ); // le 0 (succ 0) ≡ le 0 1
                    let he_symm = c.symm_nat(p.clone(), c.zero.clone(), he);
                    let mz = {
                        let mut lb = EnvDeclBuilder::child_of(&ib);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        lb.finish_child(lb.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            c.nat.clone(),
                            c.le(z.clone(), one.clone()),
                        ))
                    };
                    let out = c.subst_nat(mz, c.zero.clone(), p.clone(), he_symm, le_0_1);
                    ib.finish_child(ib.mk_lam(he_id, BinderInfo::Default, p_eq_0.clone(), out))
                };
                // inr (he : p = 1) → le p 1 : transport p:=1; base le 1 1 = le.refl 1.
                let inr = {
                    let mut rb = EnvDeclBuilder::child_of(&sb);
                    let (he_id, he) = rb.fresh_local(p_eq_1.clone());
                    let le_1_1 = Expr::apps(
                        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                        [one.clone()],
                    );
                    let he_symm = c.symm_nat(p.clone(), one.clone(), he);
                    let mz = {
                        let mut lb = EnvDeclBuilder::child_of(&rb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        lb.finish_child(lb.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            c.nat.clone(),
                            c.le(z.clone(), one.clone()),
                        ))
                    };
                    let out = c.subst_nat(mz, one.clone(), p.clone(), he_symm, le_1_1);
                    rb.finish_child(rb.mk_lam(he_id, BinderInfo::Default, p_eq_1.clone(), out))
                };
                Expr::apps(c.or_rec.clone(), [p_eq_0, p_eq_1, or_m, inl, inr, disj])
            };

            // step_a : le ((r+r)+p) ((r+r)+1)
            //   := add_le_add (r+r) (r+r) p 1 (le.refl (r+r)) hp_le_1
            //   ((r+r)+1 ≡ succ (r+r))
            let le_refl_rr = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                [rr.clone()],
            );
            let step_a = Expr::apps(
                Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
                [
                    rr.clone(),
                    rr.clone(),
                    p.clone(),
                    one.clone(),
                    le_refl_rr,
                    hp_le_1,
                ],
            ); // : le ((r+r)+p) ((r+r)+1) ≡ le ((r+r)+p) (succ (r+r))
               // step_b : le (succ ((r+r)+p)) (succ (succ (r+r)))
               //   := succ_le_succ ((r+r)+p) (succ (r+r)) step_a
               //   (((r+r)+1) ≡ succ (r+r) defeq, so step_a : le ((r+r)+p) (succ (r+r)))
            let succ_rr = c.succ_of(rr.clone());
            let step_b = Expr::apps(
                Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
                [rrp.clone(), succ_rr.clone(), step_a],
            ); // : le (succ ((r+r)+p)) (succ (succ (r+r)))

            // step_c0 : le ((succ r)+(succ r)) (2^n' + 2^n')
            //   := add_le_add (succ r) (2^n') (succ r) (2^n') ih_r ih_r
            let succ_r = c.succ_of(r.clone());
            let step_c0 = Expr::apps(
                Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
                [
                    succ_r.clone(),
                    pn.clone(),
                    succ_r.clone(),
                    pn.clone(),
                    ih_r.clone(),
                    ih_r.clone(),
                ],
            ); // : le ((succ r)+(succ r)) (2^n' + 2^n')
               // (succ r)+(succ r) = succ (succ (r+r))  via succ_add r (succ r) :
               //   (succ r)+(succ r) = succ (r + succ r) ; r + succ r ≡ succ (r+r) defeq.
            let succ_add = Expr::apps(
                Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
                [r.clone(), succ_r.clone()],
            ); // : (succ r)+(succ r) = succ (r + succ r) ≡ succ (succ (r+r))
               // transport step_c0's LHS to succ (succ (r+r)) : motive z := le z (2^n'+2^n')
            let pn_pn = c.add_of(pn.clone(), pn.clone());
            let succ_succ_rr = c.succ_of(succ_rr.clone());
            let m_le_z = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                lb.finish_child(lb.mk_lam(
                    z_id,
                    BinderInfo::Default,
                    c.nat.clone(),
                    c.le(z.clone(), pn_pn.clone()),
                ))
            };
            let ss_rr = c.add_of(succ_r.clone(), succ_r.clone());
            let step_c = c.subst_nat(m_le_z, ss_rr, succ_succ_rr.clone(), succ_add, step_c0);
            // step_c : le (succ (succ (r+r))) (2^n' + 2^n')

            // chain : le (succ ((r+r)+p)) (2^n'+2^n') := le_trans (succ ((r+r)+p)) (succ (succ (r+r))) (2^n'+2^n') step_b step_c
            let chain = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                [
                    c.succ_of(rrp.clone()),
                    succ_succ_rr.clone(),
                    pn_pn.clone(),
                    step_b,
                    step_c,
                ],
            ); // : le (succ ((r+r)+p)) (2^n'+2^n') ≡ lt ((r+r)+p) (2^n'+2^n')

            // transport (r+r)+p ↦ m via div2_rejoin m : m = (r+r)+p  (so rejoin.symm : (r+r)+p = m)
            //   motive z := lt z (2^n'+2^n'). subst ((r+r)+p) m rejoin chain : lt m (2^n'+2^n')
            let rejoin = Expr::app(
                Expr::const_(Name::from_string("Nat.div2_rejoin"), vec![]),
                m.clone(),
            ); // : m = (r+r)+p
            let rejoin_symm = c.symm_nat(m.clone(), rrp.clone(), rejoin); // : (r+r)+p = m
            let m_lt_z = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                lb.finish_child(lb.mk_lam(
                    z_id,
                    BinderInfo::Default,
                    c.nat.clone(),
                    c.lt(z.clone(), pn_pn.clone()),
                ))
            };
            let lt_m_pnpn = c.subst_nat(m_lt_z, rrp.clone(), m.clone(), rejoin_symm, chain);
            // : lt m (2^n'+2^n')

            // transport 2^n'+2^n' ↦ 2^(succ n') via (pow_two_succ n').symm
            //   pow_two_succ n' : 2^(succ n') = 2^n'+2^n' ; symm : (2^n'+2^n') = 2^(succ n')
            //   motive z := lt m z.  subst (2^n'+2^n') (2^(succ n')) symm lt_m_pnpn : lt m (2^(succ n'))
            let pts = Expr::app(
                Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
                np.clone(),
            ); // : 2^(succ n') = 2^n'+2^n'
            let pts_symm = c.symm_nat(c.pow2(sn.clone()), pn_pn.clone(), pts); // : (2^n'+2^n') = 2^(succ n')
            let m_lt_z2 = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                lb.finish_child(lb.mk_lam(
                    z_id,
                    BinderInfo::Default,
                    c.nat.clone(),
                    c.lt(m.clone(), z.clone()),
                ))
            };
            let out = c.subst_nat(
                m_lt_z2,
                pn_pn.clone(),
                c.pow2(sn.clone()),
                pts_symm,
                lt_m_pnpn,
            );

            let lam = sb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
            sb.finish_child(sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        // Nat.rec.{0} motive base step n
        let rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(rec0, [motive, base, step, n.clone()]);
        vb.finish(vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app))
    };
    (type_, value)
}

// ===========================================================================
// BoolAnalysis.xor_eq_cond : ∀ (a g : Bool),
//   @Eq Bool (Bool.xor a g) (@Bool.rec (fun _ => Bool) a (Bool.not a) g)
// The pure-Bool identity matching `Bool.xor` to the `hcFlip` conditional.
// ===========================================================================
fn build_xor_eq_cond(c: &RtConsts) -> (Expr, Expr) {
    let bool_rec1 = Expr::const_(
        Name::from_string("Bool.rec"),
        vec![Level::succ(Level::zero())],
    );
    let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let motive_bb = || Expr::lam(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone());
    // cond(a, g) := @Bool.rec (fun _ => Bool) a (Bool.not a) g
    let cond = |a: Expr, g: Expr| {
        Expr::apps(
            bool_rec1.clone(),
            [motive_bb(), a.clone(), Expr::app(bool_not.clone(), a), g],
        )
    };
    let xor = |a: Expr, g: Expr| Expr::apps(c.bool_xor.clone(), [a, g]);
    let goal =
        |a: &Expr, g: &Expr| c.eq_bool(xor(a.clone(), g.clone()), cond(a.clone(), g.clone()));

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.bool_ty.clone());
        let (g_id, g) = b.fresh_local(c.bool_ty.clone());
        let concl = goal(&a, &g);
        let e = b.mk_pi(g_id, BinderInfo::Default, c.bool_ty.clone(), concl);
        b.finish(b.mk_pi(a_id, BinderInfo::Default, c.bool_ty.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.bool_ty.clone());
        let (g_id, g) = b.fresh_local(c.bool_ty.clone());

        // recurse on g; for each concrete gv, recurse on a; 4 ground rfl leaves.
        let inner_rec = |gv: Expr, parent: &EnvDeclBuilder| {
            let d = EnvDeclBuilder::child_of(parent);
            // motive_a : fun (a' : Bool) => goal a' gv
            let motive_a = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (ap_id, ap) = e.fresh_local(c.bool_ty.clone());
                let body = goal(&ap, &gv);
                e.finish_child(e.mk_lam(ap_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            let leaf = |av: Expr| c.refl_bool(xor(av, gv.clone()));
            let a_false = leaf(c.bfalse.clone());
            let a_true = leaf(c.btrue.clone());
            let e = Expr::apps(bool_rec0.clone(), [motive_a, a_false, a_true, a.clone()]);
            d.finish_child(e)
        };

        // motive_g : fun (g' : Bool) => goal a g'
        let motive_g = {
            let mut e = EnvDeclBuilder::child_of(&b);
            let (gp_id, gp) = e.fresh_local(c.bool_ty.clone());
            let body = goal(&a, &gp);
            e.finish_child(e.mk_lam(gp_id, BinderInfo::Default, c.bool_ty.clone(), body))
        };
        let g_false = inner_rec(c.bfalse.clone(), &b);
        let g_true = inner_rec(c.btrue.clone(), &b);
        let rec_g = Expr::apps(bool_rec0.clone(), [motive_g, g_false, g_true, g.clone()]);

        let lam = b.mk_lam(g_id, BinderInfo::Default, c.bool_ty.clone(), rec_g);
        b.finish(b.mk_lam(a_id, BinderInfo::Default, c.bool_ty.clone(), lam))
    };
    (type_, value)
}

// ===========================================================================
// Nat.lt_two_pow_xor_two_pow : ∀ (n a i : Nat),
//   Nat.lt a (2^n) → Nat.lt i n → Nat.lt (Nat.xor a (2^i)) (2^n)
// XOR with a sub-n bit preserves the n-bit bound (all bits ≥ n stay false).
// ===========================================================================
fn build_lt_two_pow_xor_two_pow(c: &RtConsts) -> (Expr, Expr) {
    let nat_xor = Expr::const_(Name::from_string("Nat.xor"), vec![]);
    let xor = |a: Expr, b: Expr| Expr::apps(nat_xor.clone(), [a, b]);

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let h_a = c.lt(a.clone(), c.pow2(n.clone()));
        let (ha_id, _ha) = b.fresh_local(h_a.clone());
        let h_i = c.lt(i.clone(), n.clone());
        let (hi_id, _hi) = b.fresh_local(h_i.clone());
        let concl = c.lt(xor(a.clone(), c.pow2(i.clone())), c.pow2(n.clone()));
        let e = b.mk_pi(hi_id, BinderInfo::Default, h_i, concl);
        let e = b.mk_pi(ha_id, BinderInfo::Default, h_a, e);
        let e = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.nat.clone());
        let h_a = c.lt(a.clone(), c.pow2(n.clone()));
        let (ha_id, ha) = b.fresh_local(h_a.clone());
        let h_i = c.lt(i.clone(), n.clone());
        let (hi_id, hi) = b.fresh_local(h_i.clone());

        let m = xor(a.clone(), c.pow2(i.clone())); // m := xor a (2^i)

        // bits_high : ∀ k, le n k → testBit m k = false
        let bits_high = {
            let mut kb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = kb.fresh_local(c.nat.clone());
            let le_nk = c.le(n.clone(), k.clone());
            let (hle_id, hle) = kb.fresh_local(le_nk.clone());

            // e_xor : testBit m k = Bool.xor (testBit a k) (testBit (2^i) k)
            let e_xor = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_xor"), vec![]),
                [a.clone(), c.pow2(i.clone()), k.clone()],
            );
            // ta_false : testBit a k = false
            //   need a < 2^k from a < 2^n and 2^n ≤ 2^k (n ≤ k via pow_le_pow_right).
            let one = c.succ_of(c.zero.clone());
            let two = c.two.clone();
            let le_refl_one = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                [one.clone()],
            );
            let one_le_two = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.step"), vec![]),
                [one.clone(), one.clone(), le_refl_one],
            );
            // pow_le : 2^n ≤ 2^k  := pow_le_pow_right 2 n k one_le_two hle
            let pow_le = Expr::apps(
                Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
                [
                    two.clone(),
                    n.clone(),
                    k.clone(),
                    one_le_two.clone(),
                    hle.clone(),
                ],
            );
            // a_lt_2k : lt a (2^k) := lt_of_lt_of_le a (2^n) (2^k) ha pow_le
            let a_lt_2k = Expr::apps(
                Expr::const_(Name::from_string("Nat.lt_of_lt_of_le"), vec![]),
                [
                    a.clone(),
                    c.pow2(n.clone()),
                    c.pow2(k.clone()),
                    ha.clone(),
                    pow_le,
                ],
            );
            // ta_false : testBit a k = false := testBit_lt_pow k a a_lt_2k
            let ta_false = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
                [k.clone(), a.clone(), a_lt_2k],
            );
            // tb : testBit (2^i) k = Nat.beq k i := testBit_two_pow i k
            let tb = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_two_pow"), vec![]),
                [i.clone(), k.clone()],
            );
            // beq_false : Nat.beq k i = false  (k ≠ i, since i < n ≤ k ⇒ i < k)
            //   i_lt_k : lt i k := lt_of_lt_of_le i n k hi hle
            let i_lt_k = Expr::apps(
                Expr::const_(Name::from_string("Nat.lt_of_lt_of_le"), vec![]),
                [i.clone(), n.clone(), k.clone(), hi.clone(), hle.clone()],
            );
            // hne : (k = i) → False : fun e => lt_irrefl k (subst i k (e.symm) i_lt_k)
            //   wait: i_lt_k : lt i k. e : k = i. want lt k k. subst i↦k in i_lt_k via e.symm?
            //   motive z := lt z k. subst i k (e.symm : i = k) i_lt_k : lt k k.
            let hne = {
                let mut nb = EnvDeclBuilder::child_of(&kb);
                let (e_id, e) = nb.fresh_local(c.eq_nat(k.clone(), i.clone())); // k = i
                let e_symm = c.symm_nat(k.clone(), i.clone(), e); // i = k
                let mz = {
                    let mut lb = EnvDeclBuilder::child_of(&nb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    lb.finish_child(lb.mk_lam(
                        z_id,
                        BinderInfo::Default,
                        c.nat.clone(),
                        c.lt(z.clone(), k.clone()),
                    ))
                };
                let lt_kk = c.subst_nat(mz, i.clone(), k.clone(), e_symm, i_lt_k);
                let false_pf = Expr::apps(
                    Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
                    [k.clone(), lt_kk],
                );
                nb.finish_child(nb.mk_lam(
                    e_id,
                    BinderInfo::Default,
                    c.eq_nat(k.clone(), i.clone()),
                    false_pf,
                ))
            };
            let beq_ki_false = Expr::apps(
                Expr::const_(Name::from_string("Nat.beq_eq_false_of_ne"), vec![]),
                [k.clone(), i.clone(), hne],
            );
            // tb_false : testBit (2^i) k = false := Eq.trans tb beq_ki_false
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            let beq = c.beq(k.clone(), i.clone());
            let tb_false = Expr::apps(
                eq_trans.clone(),
                [
                    c.bool_ty.clone(),
                    c.testbit(c.pow2(i.clone()), k.clone()),
                    beq.clone(),
                    c.bfalse.clone(),
                    tb,
                    beq_ki_false,
                ],
            );
            // Now combine: testBit m k = xor (testBit a k)(testBit (2^i) k) = xor false false = false.
            //   congr: xor (testBit a k)(testBit (2^i) k) = xor false false via congrArg₂.
            //   Use two congrArgs: first rewrite testBit a k → false, then testBit (2^i) k → false.
            //   step1 : xor (testBit a k)(testBit (2^i) k) = xor false (testBit (2^i) k)
            //     := congrArg (fun w => xor w (testBit (2^i) k)) ta_false
            let f_left = {
                let mut lb = EnvDeclBuilder::child_of(&kb);
                let (w_id, w) = lb.fresh_local(c.bool_ty.clone());
                let body = Expr::apps(
                    c.bool_xor.clone(),
                    [w, c.testbit(c.pow2(i.clone()), k.clone())],
                );
                lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            let congr_arg = Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            );
            let step1 = Expr::apps(
                congr_arg.clone(),
                [
                    c.bool_ty.clone(),
                    c.bool_ty.clone(),
                    c.testbit(a.clone(), k.clone()),
                    c.bfalse.clone(),
                    f_left,
                    ta_false,
                ],
            ); // : xor (testBit a k)(testBit (2^i) k) = xor false (testBit (2^i) k)
               // step2 : xor false (testBit (2^i) k) = xor false false
               //   := congrArg (fun w => xor false w) tb_false
            let f_right = {
                let mut lb = EnvDeclBuilder::child_of(&kb);
                let (w_id, w) = lb.fresh_local(c.bool_ty.clone());
                let body = Expr::apps(c.bool_xor.clone(), [c.bfalse.clone(), w]);
                lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            let step2 = Expr::apps(
                congr_arg.clone(),
                [
                    c.bool_ty.clone(),
                    c.bool_ty.clone(),
                    c.testbit(c.pow2(i.clone()), k.clone()),
                    c.bfalse.clone(),
                    f_right,
                    tb_false,
                ],
            ); // : xor false (testBit (2^i) k) = xor false false
               // xor false false ≡ false (ground). chain: e_xor ; step1 ; step2 ; (refl false).
               //   testBit m k = xor (..)(..) = xor false (..) = xor false false ≡ false.
            let xor_tt = Expr::apps(
                c.bool_xor.clone(),
                [
                    c.testbit(a.clone(), k.clone()),
                    c.testbit(c.pow2(i.clone()), k.clone()),
                ],
            );
            let xor_ft = Expr::apps(
                c.bool_xor.clone(),
                [c.bfalse.clone(), c.testbit(c.pow2(i.clone()), k.clone())],
            );
            let xor_ff = Expr::apps(c.bool_xor.clone(), [c.bfalse.clone(), c.bfalse.clone()]);
            // t12 : xor (..)(..) = xor false false
            let t12 = Expr::apps(
                eq_trans.clone(),
                [
                    c.bool_ty.clone(),
                    xor_tt.clone(),
                    xor_ft.clone(),
                    xor_ff.clone(),
                    step1,
                    step2,
                ],
            );
            // ff_false : xor false false = false  (rfl, ground)
            let ff_false = c.refl_bool(c.bfalse.clone()); // @Eq.refl Bool false : false = false ≡ xor false false = false
                                                          // t_all : xor (..)(..) = false
            let t_all = Expr::apps(
                eq_trans.clone(),
                [
                    c.bool_ty.clone(),
                    xor_tt.clone(),
                    xor_ff.clone(),
                    c.bfalse.clone(),
                    t12,
                    ff_false,
                ],
            );
            // out : testBit m k = false := Eq.trans e_xor t_all
            let out = Expr::apps(
                eq_trans,
                [
                    c.bool_ty.clone(),
                    c.testbit(m.clone(), k.clone()),
                    xor_tt,
                    c.bfalse.clone(),
                    e_xor,
                    t_all,
                ],
            );
            let lam = kb.mk_lam(hle_id, BinderInfo::Default, le_nk, out);
            kb.finish_child(kb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        // lt_two_pow_of_testBit_ge n m bits_high : lt m (2^n)
        let out = Expr::apps(
            Expr::const_(Name::from_string("Nat.lt_two_pow_of_testBit_ge"), vec![]),
            [n.clone(), m.clone(), bits_high],
        );

        let lam = b.mk_lam(hi_id, BinderInfo::Default, h_i, out);
        let lam = b.mk_lam(ha_id, BinderInfo::Default, h_a, lam);
        let lam = b.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam))
    };
    (type_, value)
}

// ===========================================================================
// BoolAnalysis.flipIdx : (n : Nat) → (i : Fin n) → (jx : Fin (2^n)) → Fin (2^n)
//   flipIdx n i jx := @Fin.mk (2^n) (Nat.xor (val jx) (2^(val i)))
//                       (lt_two_pow_xor_two_pow n (val jx) (val i)
//                          (Fin.isLt (2^n) jx) (Fin.isLt n i))
// The XOR index: jx with its `(val i)`-th bit toggled, kept in range.
// ===========================================================================
fn build_flip_idx(c: &RtConsts) -> (Expr, Expr) {
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
    let nat_xor = Expr::const_(Name::from_string("Nat.xor"), vec![]);
    let fin_of = |m: Expr| Expr::app(fin.clone(), m);

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, _i) = b.fresh_local(fin_of(n.clone()));
        let (jx_id, _jx) = b.fresh_local(fin_of(c.pow2(n.clone())));
        let e = b.mk_pi(
            jx_id,
            BinderInfo::Default,
            fin_of(c.pow2(n.clone())),
            fin_of(c.pow2(n.clone())),
        );
        let e = b.mk_pi(i_id, BinderInfo::Default, fin_of(n.clone()), e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(fin_of(c.pow2(n.clone())));

        let val_jx = Expr::apps(fin_val.clone(), [c.pow2(n.clone()), jx.clone()]); // val jx
        let val_i = Expr::apps(fin_val.clone(), [n.clone(), i.clone()]); // val i
        let newval = Expr::apps(nat_xor.clone(), [val_jx.clone(), c.pow2(val_i.clone())]);
        // bounds
        let islt_jx = Expr::apps(fin_islt.clone(), [c.pow2(n.clone()), jx.clone()]); // lt (val jx) (2^n)
        let islt_i = Expr::apps(fin_islt.clone(), [n.clone(), i.clone()]); // lt (val i) n
        let bound = Expr::apps(
            Expr::const_(Name::from_string("Nat.lt_two_pow_xor_two_pow"), vec![]),
            [n.clone(), val_jx.clone(), val_i.clone(), islt_jx, islt_i],
        ); // : lt (xor (val jx)(2^(val i))) (2^n)
        let body = Expr::apps(fin_mk.clone(), [c.pow2(n.clone()), newval, bound]);

        let lam = b.mk_lam(jx_id, BinderInfo::Default, fin_of(c.pow2(n.clone())), body);
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_of(n.clone()), lam);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam))
    };
    (type_, value)
}

// ===========================================================================
// BoolAnalysis.hcFlip_decode_roundtrip : ∀ (n : Nat) (i : Fin n) (jx : Fin (2^n)),
//   @Eq (HCPoint n) (hcDecode n (flipIdx n i jx)) (hcFlip n (hcDecode n jx) i)
// THE keystone: the flipped decoded point is the decode of the XOR index.
// `funext` over Fin n; per-coordinate j via testBit_xor ; testBit_two_pow ; xor_eq_cond.
// ===========================================================================
fn build_hcflip_decode_roundtrip(c: &RtConsts) -> (Expr, Expr) {
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let nat_xor = Expr::const_(Name::from_string("Nat.xor"), vec![]);
    let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
    let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let hc_flip = Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]);
    let flip_idx = Expr::const_(Name::from_string("BoolAnalysis.flipIdx"), vec![]);
    let funext = Expr::const_(
        Name::from_string("funext"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let bool_rec1 = Expr::const_(
        Name::from_string("Bool.rec"),
        vec![Level::succ(Level::zero())],
    );
    let eq1 = c.eq1.clone();
    let fin_of = |m: Expr| Expr::app(fin.clone(), m);

    // lhs(n,i,jx) := hcDecode n (flipIdx n i jx) ; rhs := hcFlip n (hcDecode n jx) i
    let lhs_fn = |n: Expr, i: Expr, jx: Expr| {
        Expr::apps(
            hc_decode.clone(),
            [n.clone(), Expr::apps(flip_idx.clone(), [n, i, jx])],
        )
    };
    let rhs_fn = |n: Expr, i: Expr, jx: Expr| {
        Expr::apps(
            hc_flip.clone(),
            [n.clone(), Expr::apps(hc_decode.clone(), [n.clone(), jx]), i],
        )
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(fin_of(c.pow2(n.clone())));
        let hcp = Expr::app(hcpoint.clone(), n.clone());
        let concl = Expr::apps(
            eq1.clone(),
            [
                hcp,
                lhs_fn(n.clone(), i.clone(), jx.clone()),
                rhs_fn(n.clone(), i.clone(), jx.clone()),
            ],
        );
        let e = b.mk_pi(jx_id, BinderInfo::Default, fin_of(c.pow2(n.clone())), concl);
        let e = b.mk_pi(i_id, BinderInfo::Default, fin_of(n.clone()), e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(fin_of(c.pow2(n.clone())));

        let val_jx = Expr::apps(fin_val.clone(), [c.pow2(n.clone()), jx.clone()]); // val jx
        let val_i = Expr::apps(fin_val.clone(), [n.clone(), i.clone()]); // val i

        // pointwise : ∀ (j : Fin n), lhs j = rhs j
        let pointwise = {
            let mut pb = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = pb.fresh_local(fin_of(n.clone()));
            let val_j = Expr::apps(fin_val.clone(), [n.clone(), j.clone()]); // val j
                                                                             // d_j := testBit (val jx) (val j)  (≡ hcDecode n jx j)
            let d_j = c.testbit(val_jx.clone(), val_j.clone());
            let two_pow_vi = c.pow2(val_i.clone());
            let xor_arg = Expr::apps(nat_xor.clone(), [val_jx.clone(), two_pow_vi.clone()]);

            // e1 : testBit (xor (val jx)(2^(val i))) (val j)
            //        = Bool.xor (testBit (val jx)(val j)) (testBit (2^(val i))(val j))
            let e1 = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_xor"), vec![]),
                [val_jx.clone(), two_pow_vi.clone(), val_j.clone()],
            );
            // e2 : testBit (2^(val i)) (val j) = Nat.beq (val j)(val i)
            let e2 = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_two_pow"), vec![]),
                [val_i.clone(), val_j.clone()],
            );
            let tb_vi_vj = c.testbit(two_pow_vi.clone(), val_j.clone());
            let beq_vj_vi = c.beq(val_j.clone(), val_i.clone());
            // e3 : Bool.xor (d_j) (testBit (2^(val i))(val j)) = Bool.xor (d_j) (Nat.beq (val j)(val i))
            //   := congrArg (fun w => Bool.xor d_j w) e2
            let f_e3 = {
                let mut lb = EnvDeclBuilder::child_of(&pb);
                let (w_id, w) = lb.fresh_local(c.bool_ty.clone());
                let body = Expr::apps(c.bool_xor.clone(), [d_j.clone(), w]);
                lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };
            let congr_arg = Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            );
            let e3 = Expr::apps(
                congr_arg.clone(),
                [
                    c.bool_ty.clone(),
                    c.bool_ty.clone(),
                    tb_vi_vj.clone(),
                    beq_vj_vi.clone(),
                    f_e3,
                    e2,
                ],
            );
            // e4 : Bool.xor d_j (Nat.beq (val j)(val i))
            //        = @Bool.rec (fun _=>Bool) d_j (Bool.not d_j) (Nat.beq (val j)(val i))
            let e4 = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.xor_eq_cond"), vec![]),
                [d_j.clone(), beq_vj_vi.clone()],
            );
            // chain RHS: Bool.xor d_j (tb) → Bool.xor d_j (beq) → Bool.rec ...
            let xor_d_tb = Expr::apps(c.bool_xor.clone(), [d_j.clone(), tb_vi_vj.clone()]);
            let xor_d_beq = Expr::apps(c.bool_xor.clone(), [d_j.clone(), beq_vj_vi.clone()]);
            let motive_bb = Expr::lam(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone());
            let cond = Expr::apps(
                bool_rec1.clone(),
                [
                    motive_bb,
                    d_j.clone(),
                    Expr::app(bool_not.clone(), d_j.clone()),
                    beq_vj_vi.clone(),
                ],
            );
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            // e34 : xor d_j tb = cond  := Eq.trans e3 e4
            let e34 = Expr::apps(
                eq_trans.clone(),
                [
                    c.bool_ty.clone(),
                    xor_d_tb.clone(),
                    xor_d_beq.clone(),
                    cond.clone(),
                    e3,
                    e4,
                ],
            );
            // out : testBit (xor ..)(val j) = cond := Eq.trans e1 e34
            //   LHS ≡ hcDecode n (flipIdx n i jx) j ; cond ≡ hcFlip n (hcDecode n jx) i j  (defeq).
            let out = Expr::apps(
                eq_trans,
                [
                    c.bool_ty.clone(),
                    c.testbit(xor_arg.clone(), val_j.clone()),
                    xor_d_tb,
                    cond,
                    e1,
                    e34,
                ],
            );
            pb.finish_child(pb.mk_lam(j_id, BinderInfo::Default, fin_of(n.clone()), out))
        };

        // @funext.{1,1} (Fin n) (fun _ => Bool) lhs rhs pointwise : lhs = rhs
        let bool_codomain = Expr::lam(BinderInfo::Default, fin_of(n.clone()), c.bool_ty.clone());
        let proof = Expr::apps(
            funext.clone(),
            [
                fin_of(n.clone()),
                bool_codomain,
                lhs_fn(n.clone(), i.clone(), jx.clone()),
                rhs_fn(n.clone(), i.clone(), jx.clone()),
                pointwise,
            ],
        );

        let lam = b.mk_lam(jx_id, BinderInfo::Default, fin_of(c.pow2(n.clone())), proof);
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_of(n.clone()), lam);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam))
    };
    (type_, value)
}

// ===========================================================================
// BoolAnalysis.subsetSum_inversion_core_flip : ∀ (n) (b : HCPoint n → Rat)
//   (i : Fin n) (jx : Fin (2^n)),
//   @Eq Rat
//     (subsetSum n (fun S => Rat.mul (subsetSum n (fun y => Rat.mul (b y) (chi n S y)))
//                                    (chi n S (hcFlip n (hcDecode n jx) i))))
//     (Rat.mul (2^n) (b (hcFlip n (hcDecode n jx) i)))
// FOURIER INVERSION AT THE FLIPPED POINT — `subsetSum_inversion_core` at
// `flipIdx n i jx`, transported along the roundtrip to the `hcFlip` point.
// ===========================================================================
fn build_inversion_core_flip(c: &RtConsts) -> (Expr, Expr) {
    let l1 = Level::succ(Level::zero());
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let one_nat = c.succ_of(c.zero.clone());
    let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let hc_flip = Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]);
    let flip_idx = Expr::const_(Name::from_string("BoolAnalysis.flipIdx"), vec![]);
    let chi = Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]);
    let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
    let inv_core = Expr::const_(
        Name::from_string("BoolAnalysis.subsetSum_inversion_core"),
        vec![],
    );
    let roundtrip = Expr::const_(
        Name::from_string("BoolAnalysis.hcFlip_decode_roundtrip"),
        vec![],
    );
    let eq_subst1 = Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let eq_rat = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);

    let fin_of = |m: Expr| Expr::app(fin.clone(), m);
    let hcp_of = |n: Expr| Expr::app(hcpoint.clone(), n);
    let mul = |a: Expr, bb: Expr| Expr::apps(rat_mul.clone(), [a, bb]);
    let ssum = |n: Expr, g: Expr| Expr::apps(subset_sum.clone(), [n, g]);
    let chi_ = |n: Expr, s: Expr, x: Expr| Expr::apps(chi.clone(), [n, s, x]);
    // 2^n as a Rat: Rat.mk (Int.ofNat (Nat.pow 2 n)) 1
    let cube = |n: Expr| {
        Expr::apps(
            rat_mk.clone(),
            [Expr::app(int_of_nat.clone(), c.pow2(n)), one_nat.clone()],
        )
    };

    // stmt(n, b, x) := @Eq Rat (ssum n (fun S => mul (ssum n (fun y => mul (b y)(chi n S y))) (chi n S x)))
    //                          (mul (2^n) (b x))
    let stmt = |n: &Expr, bf: &Expr, x: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let hcp = hcp_of(n.clone());
        let lhs_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let inner_fn = {
                let mut yb = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = mul(
                    Expr::app(bf.clone(), y.clone()),
                    chi_(n.clone(), s.clone(), y.clone()),
                );
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let inner = ssum(n.clone(), inner_fn);
            let body = mul(inner, chi_(n.clone(), s.clone(), x.clone()));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let lhs = ssum(n.clone(), lhs_fn);
        let rhs = mul(cube(n.clone()), Expr::app(bf.clone(), x.clone()));
        Expr::apps(eq_rat.clone(), [rat.clone(), lhs, rhs])
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let b_ty = Expr::pi(BinderInfo::Default, hcp_of(n.clone()), rat.clone());
        let (bf_id, bf) = b.fresh_local(b_ty.clone());
        let (i_id, i) = b.fresh_local(fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(fin_of(c.pow2(n.clone())));
        // x' := hcFlip n (hcDecode n jx) i
        let xprime = Expr::apps(
            hc_flip.clone(),
            [
                n.clone(),
                Expr::apps(hc_decode.clone(), [n.clone(), jx.clone()]),
                i.clone(),
            ],
        );
        let concl = stmt(&n, &bf, &xprime, &b);
        let e = b.mk_pi(jx_id, BinderInfo::Default, fin_of(c.pow2(n.clone())), concl);
        let e = b.mk_pi(i_id, BinderInfo::Default, fin_of(n.clone()), e);
        let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let b_ty = Expr::pi(BinderInfo::Default, hcp_of(n.clone()), rat.clone());
        let (bf_id, bf) = b.fresh_local(b_ty.clone());
        let (i_id, i) = b.fresh_local(fin_of(n.clone()));
        let (jx_id, jx) = b.fresh_local(fin_of(c.pow2(n.clone())));

        // x_a := hcDecode n (flipIdx n i jx) ; x' := hcFlip n (hcDecode n jx) i
        let xa = Expr::apps(
            hc_decode.clone(),
            [
                n.clone(),
                Expr::apps(flip_idx.clone(), [n.clone(), i.clone(), jx.clone()]),
            ],
        );
        let xprime = Expr::apps(
            hc_flip.clone(),
            [
                n.clone(),
                Expr::apps(hc_decode.clone(), [n.clone(), jx.clone()]),
                i.clone(),
            ],
        );
        // proof_at_xa := inv_core n b (flipIdx n i jx) : stmt(n,b,xa)
        let proof_xa = Expr::apps(
            inv_core.clone(),
            [
                n.clone(),
                bf.clone(),
                Expr::apps(flip_idx.clone(), [n.clone(), i.clone(), jx.clone()]),
            ],
        );
        // rt := roundtrip n i jx : xa = x'
        let rt = Expr::apps(roundtrip.clone(), [n.clone(), i.clone(), jx.clone()]);
        // motive : fun (x : HCPoint n) => stmt(n,b,x)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = mb.fresh_local(hcp_of(n.clone()));
            let body = stmt(&n, &bf, &x, &mb);
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, hcp_of(n.clone()), body))
        };
        // @Eq.subst.{1} (HCPoint n) motive xa x' rt proof_xa : motive x' = stmt(n,b,x')
        let out = Expr::apps(
            eq_subst1.clone(),
            [hcp_of(n.clone()), motive, xa, xprime, rt, proof_xa],
        );

        let lam = b.mk_lam(jx_id, BinderInfo::Default, fin_of(c.pow2(n.clone())), out);
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_of(n.clone()), lam);
        let lam = b.mk_lam(bf_id, BinderInfo::Default, b_ty, lam);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam))
    };
    (type_, value)
}

impl Environment {
    /// Register `Nat.two_pow_lt_two_pow_of_lt` and `Nat.testBit_two_pow` as
    /// kernel-checked, axiom-free `Declaration::Theorem`s. Idempotent.
    pub(crate) fn register_testbit_two_pow_proof(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_lt()?;
        self.init_le()?;
        self.init_classical()?; // Or, Or.rec
        self.init_nat_cmp()?; // Nat.beq

        // Dependencies (all idempotent, all axiom-free Theorems / Definitions).
        self.register_nat_testbit_lt_pow_proof()?; // testBit_lt_pow + testBit foundation
        self.register_nat_testbit_add_two_pow_proof()?; // add_two_pow_self / _lo, pow_two_succ
        self.register_nat_beq_lemmas()?; // beq_refl
        self.register_nat_beq_eq_false_of_ne()?; // beq_eq_false_of_ne
        self.register_nat_lt_irrefl_theorem()?; // lt_irrefl
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow
        self.register_nat_arith_order_proofs()?; // add_lt_add_left, add_le_add, succ_le_succ, le_trans
                                                 // Only `Nat.pow_le_pow_right` is needed here; register its constructive
                                                 // Theorem directly rather than the full `init_nat_pow_ord` tower, which
                                                 // also admits the UNUSED sibling axiom `Nat.pow_lt_pow_left` and pulls
                                                 // `init_nat_linear_order` (admitting `instLinearOrderNat` /
                                                 // `instPartialOrderNat`). Avoiding those keeps the trusted base from
                                                 // growing when this keystone is wired into the always-on env (e.g. via
                                                 // the `influence_fourier` retirement). See data/soundness_tcb.json.
        self.register_nat_pow_le_pow_right_proof()?; // pow_le_pow_right (Theorem)
        self.init_nat_lt_or_eq_of_le()?; // lt_or_eq_of_le
        self.register_nat_mul_left_cancel_succ_proof()?; // registers Nat.le_or_lt
                                                         // Bits-determine-bound dependencies.
        self.register_nat_eq_of_testbit_proof()?; // eq_zero_of_testBit_all_false, div2_rejoin, div2Par_zero_or_one
        self.register_nat_succ_add_proof()?; // Nat.succ_add
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.init_nat_trans_lt_le_lt()?; // Nat.lt_of_lt_of_le
        self.register_nat_testbit_bitwise_proof()?; // Nat.xor def + Nat.testBit_xor

        let c = RtConsts::new();

        if self
            .get_const(&Name::from_string("Nat.two_pow_lt_two_pow_of_lt"))
            .is_none()
        {
            let (type_, value) = build_two_pow_lt_two_pow_of_lt(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.two_pow_lt_two_pow_of_lt"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.testBit_two_pow"))
            .is_none()
        {
            let (type_, value) = build_testbit_two_pow(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.testBit_two_pow"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.lt_two_pow_of_testBit_ge"))
            .is_none()
        {
            let (type_, value) = build_lt_two_pow_of_testbit_ge(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.lt_two_pow_of_testBit_ge"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("BoolAnalysis.xor_eq_cond"))
            .is_none()
        {
            let (type_, value) = build_xor_eq_cond(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.xor_eq_cond"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string("Nat.lt_two_pow_xor_two_pow"))
            .is_none()
        {
            let (type_, value) = build_lt_two_pow_xor_two_pow(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.lt_two_pow_xor_two_pow"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }

    /// Register `BoolAnalysis.flipIdx` (the XOR index, a reducible Definition)
    /// and the keystone `BoolAnalysis.hcFlip_decode_roundtrip` theorem
    /// (`hcDecode n (flipIdx n i jx) = hcFlip n (hcDecode n jx) i`). Idempotent.
    pub(crate) fn register_hcflip_decode_roundtrip(&mut self) -> Result<(), EnvError> {
        self.register_testbit_two_pow_proof()?; // testBit_two_pow, xor_eq_cond, lt_two_pow_xor_two_pow
        self.init_funext()?; // funext (FOUNDATIONAL)
        self.init_boolean_analysis()?; // HCPoint, hcDecode, hcFlip, Fin, Fin.mk/val/isLt
        self.register_subset_sum_inversion_core_theorem()?; // inversion at decoded points

        let c = RtConsts::new();

        if self
            .get_const(&Name::from_string("BoolAnalysis.flipIdx"))
            .is_none()
        {
            let (type_, value) = build_flip_idx(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("BoolAnalysis.flipIdx"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        if self
            .get_const(&Name::from_string("BoolAnalysis.hcFlip_decode_roundtrip"))
            .is_none()
        {
            let (type_, value) = build_hcflip_decode_roundtrip(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.hcFlip_decode_roundtrip"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        if self
            .get_const(&Name::from_string(
                "BoolAnalysis.subsetSum_inversion_core_flip",
            ))
            .is_none()
        {
            let (type_, value) = build_inversion_core_flip(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.subsetSum_inversion_core_flip"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn env_with() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_testbit_two_pow_proof()
            .expect("register testbit_two_pow proof");
        env
    }

    fn assert_axiom_free_theorem(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_two_pow_lt_two_pow_of_lt_constructive() {
        let mut env = env_with();
        env.register_testbit_two_pow_proof().expect("idempotent");
        assert_axiom_free_theorem(&env, "Nat.two_pow_lt_two_pow_of_lt");
    }

    #[test]
    fn test_testbit_two_pow_constructive() {
        let env = env_with();
        assert_axiom_free_theorem(&env, "Nat.testBit_two_pow");
    }

    #[test]
    fn test_lt_two_pow_of_testbit_ge_constructive() {
        let env = env_with();
        assert_axiom_free_theorem(&env, "Nat.lt_two_pow_of_testBit_ge");
    }

    #[test]
    fn test_xor_eq_cond_constructive() {
        let env = env_with();
        assert_axiom_free_theorem(&env, "BoolAnalysis.xor_eq_cond");
    }

    #[test]
    fn test_lt_two_pow_xor_two_pow_constructive() {
        let env = env_with();
        assert_axiom_free_theorem(&env, "Nat.lt_two_pow_xor_two_pow");
    }

    #[test]
    fn test_hcflip_decode_roundtrip_constructive() {
        let mut env = Environment::with_prelude();
        env.register_hcflip_decode_roundtrip()
            .expect("register hcFlip_decode_roundtrip");
        env.register_hcflip_decode_roundtrip().expect("idempotent");

        // flipIdx is a reducible Definition.
        let flip = Name::from_string("BoolAnalysis.flipIdx");
        assert_eq!(
            env.get_const(&flip).expect("flipIdx registered").kind,
            ConstantKind::Definition
        );

        // The roundtrip is an axiom-free (funext FOUNDATIONAL) Constructive Theorem.
        let name = Name::from_string("BoolAnalysis.hcFlip_decode_roundtrip");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .unwrap_or_else(|e| panic!("roundtrip should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&name).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&name).expect("registered");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "roundtrip closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_inversion_core_flip_constructive() {
        let mut env = Environment::with_prelude();
        env.register_hcflip_decode_roundtrip()
            .expect("register hcflip roundtrip + inversion flip");
        let name = Name::from_string("BoolAnalysis.subsetSum_inversion_core_flip");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .unwrap_or_else(|e| panic!("inversion_core_flip should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&name).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&name).expect("registered");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "inversion_core_flip closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    /// Ground sanity: bit 1 of 2^0 = 1 is false (1 ≠ 0). `Nat.beq 1 0 ≡ false`,
    /// and `testBit 1 1 ≡ false`, so `@Eq.refl Bool false` checks both ways.
    #[test]
    fn test_testbit_two_pow_ground() {
        let env = env_with();
        let c = RtConsts::new();
        let one = c.succ_of(c.zero.clone());
        // testBit (2^0) 1 = Nat.beq 1 0  -- instantiate the theorem at i=0, j=1
        let thm = Expr::apps(
            Expr::const_(Name::from_string("Nat.testBit_two_pow"), vec![]),
            [c.zero.clone(), one.clone()],
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&thm).expect("instantiation type-checks");
        // The inferred type is `testBit (2^0) 1 = Nat.beq 1 0`; confirm it is an Eq.
        let expected = c.eq_bool(
            c.testbit(c.pow2(c.zero.clone()), one.clone()),
            c.beq(one.clone(), c.zero.clone()),
        );
        assert!(
            tc.is_def_eq(&ty, &expected),
            "instantiated type should match testBit (2^0) 1 = Nat.beq 1 0"
        );
    }
}
