// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut v3 SIZE polynomial bound — `BoolAnalysis.friedgut_size_poly_bound`.
//!
//! ```text
//! BoolAnalysis.friedgut_size_poly_bound : ∀ (e : Nat) (K eps : Rat),
//!   Rat.le 0 K →
//!   Rat.lt 0 eps → Rat.lt eps 1 →
//!   Rat.le K (Rat.mul (natCast (Nat.pow 2 (Nat.add e 1))) eps) →
//!   Rat.le
//!     (Rat.mul (natCast (Nat.mul 4 (Nat.pow 9 (Nat.mul 2 (Nat.pow 2 (Nat.add e 2))))))
//!              (Rat.mul K (Rat.mul K K)))
//!     (Rat.mul (Rat.mul eps eps)
//!              (natCast (Nat.pow 2 (Nat.mul 48 (Nat.pow 2 e)))))
//! ```
//!
//! i.e. with `d := 2^(e+2)`, `4·9^(2d)·K³ ≤ eps²·2^(48·2^e)`, with the
//! right-nested cube `K·(K·K)` (matching `Rat.pow3_le_pow3_of_le_nonneg`).
//!
//! Carries the extra hypothesis `0 ≤ K`: in every consumer `K` bounds a
//! nonnegative total-influence quantity, so `0 ≤ K` always holds; it is required
//! to cube the two-sided guard via `Rat.pow3_le_pow3_of_le_nonneg`.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! All `Rat` order facts are written through `@LE.le Rat instLERat` (the
//! Friedgut/KKL surface), defeq to the raw `Rat.le` of the consumed
//! `Rat.le_trans` / `Rat.mul_nonneg` theorems.
//!
//! Let `P := natCast(9^(2d))`, `Q := natCast(2^(e+1))`, `B32 := natCast
//! (2^(32·2^e))`, `B16 := natCast(2^(16·2^e))`, `B48 := natCast(2^(48·2^e))`,
//! `B33 := natCast(2^(3e+3))`, `nc4 := natCast 4`, `Kc := K·(K·K)`, `G := Q·eps`,
//! `Gc := G·(G·G)`, `epsc := eps·(eps·eps)`, `epssq := eps·eps`,
//! `head := natCast(4·9^(2d))`.
//!
//! 1. HEAD `P ≤ B32`: `9^(2d) ≤ 2^(8·2^(e+2))` (`pow_nine`), `8·2^(e+2) ≤ 32·2^e`
//!    (`Nat.eight_mul_pow_two_add_two_le_thirty_two`, built below) lifts via
//!    `pow_le_pow_right`+`Nat.le_trans` to `9^(2d) ≤ 2^(32·2^e)`, transported by
//!    `Rat.ofNat_le_ofNat_of_le`.
//! 2. CUBE `Kc ≤ Gc` by `pow3` (`0≤K`, guard).
//! 3. CORE `P·Kc ≤ B32·Gc` (`Rat.mul_le_mul`), then `nc4·(P·Kc) ≤ nc4·(B32·Gc)`
//!    (`mul_le_mul_of_nonneg_left`).
//! 4. LEFT id `head·Kc = nc4·(P·Kc)` (`mul_natCast` symm + `mul_assoc`).
//! 5. RIGHT ids + bounds: `Gc = B33·epsc`; `nc4·(B32·(B33·epsc))` regrouped to
//!    `(B32·nc(2^(3e+5)))·epsc` (`mul_assoc`/`mul_comm`/`mul_natCast` +
//!    `Nat.four_mul_pow_eq`); `nc(2^(3e+5)) ≤ B16` (`three_e` + `pow_le_pow_right`);
//!    `epsc ≤ epssq` (`cube_le_sq`, `eps≤1` from `le_of_lt`); combine via
//!    `Rat.mul_le_mul` to `(B32·B16)·epssq`; `(B32·B16) = B48`
//!    (`mul_natCast`+`Nat.pow_add`+`Nat.forty_eight_pow_eq_split`) and
//!    `(B48)·epssq = epssq·B48` (`mul_comm`).
//!
//! # Axiom closure
//!
//! Every consumed declaration is a constructive `Declaration::Theorem` with an
//! empty domain-axiom closure, so the proof quality is `Constructive`. No
//! `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the Friedgut SIZE poly bound.
struct C {
    l1: Level,
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    pow_nine: Expr,
    pow_le_pow_right: Expr,
    nat_le_trans: Expr,
    e8_le_e32: Expr,
    ofnat_le_ofnat: Expr,
    pow3: Expr,
    cube_le_sq: Expr,
    mul_le_mul: Expr,
    mul_le_left: Expr,
    rat_le_trans: Expr,
    rat_mul_nonneg: Expr,
    natcast_nonneg: Expr,
    rat_le_of_lt: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    mmmc: Expr,
    mul_natcast: Expr,
    pow_e1_cubed: Expr,
    four_mul_pow: Expr,
    forty_eight_split: Expr,
    nat_pow_add: Expr,
    three_e: Expr,
}

impl C {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |n: &str| Expr::const_(Name::from_string(n), vec![]);
        Self {
            l1: l1.clone(),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_mul: k("Nat.mul"),
            nat_pow: k("Nat.pow"),
            nat_le: k("Nat.le"),
            nat_le_refl: k("Nat.le.refl"),
            nat_le_step: k("Nat.le.step"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            pow_nine: k("Nat.pow_nine_le_pow_two_eightfold"),
            pow_le_pow_right: k("Nat.pow_le_pow_right"),
            nat_le_trans: k("Nat.le_trans"),
            e8_le_e32: k("Nat.eight_mul_pow_two_add_two_le_thirty_two"),
            ofnat_le_ofnat: k("Rat.ofNat_le_ofNat_of_le"),
            pow3: k("Rat.pow3_le_pow3_of_le_nonneg"),
            cube_le_sq: k("Rat.cube_le_sq_of_le_one_nonneg"),
            mul_le_mul: k("Rat.mul_le_mul"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_le_trans: k("Rat.le_trans"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            natcast_nonneg: k("BoolAnalysis.natCast_nonneg"),
            rat_le_of_lt: k("Rat.le_of_lt"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            mul_natcast: k("Rat.mul_natCast"),
            pow_e1_cubed: k("Nat.pow_two_e_plus_one_cubed"),
            four_mul_pow: k("Nat.four_mul_pow_eq"),
            forty_eight_split: k("Nat.forty_eight_pow_eq_split"),
            nat_pow_add: k("Nat.pow_add"),
            three_e: k("Nat.three_e_add_five_le_sixteen_pow_two"),
        }
    }

    // ── Nat ──────────────────────────────────────────────────────────────────
    fn lit(&self, n: u64) -> Expr {
        let mut acc = self.nat_zero.clone();
        for _ in 0..n {
            acc = Expr::app(self.nat_succ.clone(), acc);
        }
        acc
    }
    fn nadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [x, y])
    }
    fn nmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [x, y])
    }
    fn npow(&self, a: Expr, x: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [a, x])
    }
    fn nle(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [x, y])
    }
    /// `Nat.le 1 2` witness.
    fn h12(&self) -> Expr {
        let one = self.lit(1);
        let refl1 = Expr::app(self.nat_le_refl.clone(), one.clone());
        Expr::apps(self.nat_le_step.clone(), [one.clone(), one.clone(), refl1])
    }
    fn nsymm(&self, a: Expr, bb: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nat.clone(), a, bb, h],
        )
    }
    fn ntrans(&self, a: Expr, bb: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.nat.clone(), a, bb, cc, h1, h2],
        )
    }

    // ── Rat ──────────────────────────────────────────────────────────────────
    fn rmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [x, y])
    }
    fn rle(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), x, y],
        )
    }
    fn rlt(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [x, y])
    }
    /// `natCast m ≡ Rat.mk (Int.ofNat m) (Nat.succ Nat.zero)`.
    fn nc(&self, m: Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), one],
        )
    }
    fn symm(&self, a: Expr, bb: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, bb, h])
    }
    fn trans(&self, a: Expr, bb: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, bb, cc, h1, h2])
    }
    /// `congrArg Rat Rat a b f h`.
    fn cong(&self, a: Expr, bb: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, bb, f, h],
        )
    }
    /// `congrArg Nat Rat a b natCast h` (a,b : Nat) giving `nc a = nc b`.
    fn cong_nc(&self, b: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let f = {
            let mut mb = EnvDeclBuilder::child_of(b);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.nc(m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.rat.clone(), a, bb, f, h],
        )
    }
    /// `congrArg Nat Nat a b (Nat.pow 2 ·) h`.
    fn cong_pow2(&self, b: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let two = self.lit(2);
        let f = {
            let mut mb = EnvDeclBuilder::child_of(b);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.npow(two.clone(), m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.nat.clone(), a, bb, f, h],
        )
    }
    fn le_trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [x, y, z, h1, h2])
    }
    /// `λ z => f·z`.
    fn lam_l(&self, b: &EnvDeclBuilder, f: Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(b);
        let (z_id, z) = zb.fresh_local(self.rat.clone());
        let body = self.rmul(f, z);
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `λ z => z·f`.
    fn lam_r(&self, b: &EnvDeclBuilder, f: Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(b);
        let (z_id, z) = zb.fresh_local(self.rat.clone());
        let body = self.rmul(z, f);
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// Rewrite RHS of `h : lo ≤ x` along `eq : x = y` → `lo ≤ y`.
    fn rw_rhs(&self, b: &EnvDeclBuilder, lo: Expr, x: Expr, y: Expr, eq: Expr, h: Expr) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(b);
            let (z_id, z) = mb.fresh_local(self.rat.clone());
            let body = self.rle(lo.clone(), z);
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, x, y, eq, h],
        )
    }
    /// Rewrite LHS of `h : x ≤ hi` along `eq : x = y` → `y ≤ hi`.
    fn rw_lhs(&self, b: &EnvDeclBuilder, x: Expr, y: Expr, hi: Expr, eq: Expr, h: Expr) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(b);
            let (z_id, z) = mb.fresh_local(self.rat.clone());
            let body = self.rle(z, hi.clone());
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, x, y, eq, h],
        )
    }
    fn mul_natcast(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.mul_natcast.clone(), [a, bb])
    }
    fn assoc(&self, a: Expr, bb: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, bb, cc])
    }
    fn comm(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, bb])
    }
    fn nonneg(&self, a: Expr, bb: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, bb, ha, hb])
    }
    fn nc_nn(&self, m: Expr) -> Expr {
        Expr::apps(self.natcast_nonneg.clone(), [m])
    }
}

impl Environment {
    /// Register `BoolAnalysis.friedgut_size_poly_bound` (see module docs).
    pub(crate) fn register_friedgut_size_poly_bound(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_size_poly_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_le()?;
        self.init_rat()?;
        self.register_nat_pow_add_proof()?;
        self.register_nat_mul_comm_proof()?;
        self.register_nat_mul_assoc_proof()?;
        self.register_nat_one_mul_proof()?;
        self.register_nat_arith_order_proofs()?;
        self.register_nat_pow_le_pow_right_proof()?;
        self.register_nat_pow_nine_le_pow_two_eightfold_proof()?;
        self.register_nat_pow_two_e_plus_one_cubed_proof()?;
        self.register_nat_four_mul_pow_eq_proof()?;
        self.register_nat_forty_eight_pow_eq_split_proof()?;
        self.register_nat_three_e_add_five_bound_proof()?;
        self.register_rat_ofnat_le_ofnat_of_le()?;
        self.register_rat_pow3_le_pow3_proof()?;
        self.register_rat_cube_le_sq_proof()?;
        self.register_rat_mul_le_mul_proof()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.register_rat_le_trans_proof()?;
        self.register_rat_order_proofs()?;
        self.register_natcast_nonneg()?;
        self.init_algebra_rat_inv_pos()?; // Rat.le_of_lt
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_mul_natcast()?;
        self.register_nat_eight_mul_pow_two_add_two_le_thirty_two()?;

        let c = C::new();
        let ty = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term, no `sorry`, no
        // self-reference, no domain-axiom dependency — see module docs.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Local Nat brick `∀ e, Nat.le (8·2^(e+2)) (32·2^e)`.
    ///
    /// Same structure as `Nat.eight_mul_pow_two_add_two_le` but the final
    /// monotone step is `Nat.le.refl ((8·2²)·2^e)` (since `(8·2²)·2^e ≡ 32·2^e`
    /// by kernel defeq), giving the tight `≤ 32·2^e` head exponent the SIZE
    /// budget split needs. Constructive, empty domain-axiom closure.
    pub(crate) fn register_nat_eight_mul_pow_two_add_two_le_thirty_two(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.eight_mul_pow_two_add_two_le_thirty_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_le()?;
        self.register_nat_pow_add_proof()?;
        self.register_nat_mul_comm_proof()?;
        self.register_nat_mul_assoc_proof()?;

        let c = C::new();
        let two = c.lit(2);
        let eight = c.lit(8);
        let thirtytwo = c.lit(32);
        let nat = c.nat.clone();
        let pow_two_2 = c.npow(two.clone(), two.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let lhs = c.nmul(
                eight.clone(),
                c.npow(two.clone(), c.nadd(e.clone(), two.clone())),
            );
            let rhs = c.nmul(thirtytwo.clone(), c.npow(two.clone(), e.clone()));
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), c.nle(lhs, rhs)))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let q = c.npow(two.clone(), e.clone());
            let pow_e2 = c.npow(two.clone(), c.nadd(e.clone(), two.clone()));
            let q_mul_p2 = c.nmul(q.clone(), pow_two_2.clone());
            let p2_mul_q = c.nmul(pow_two_2.clone(), q.clone());
            let eight_p2_q = c.nmul(c.nmul(eight.clone(), pow_two_2.clone()), q.clone());

            let pow_add = Expr::const_(Name::from_string("Nat.pow_add"), vec![]);
            let mul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);
            let mul_assoc = Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]);

            let h1 = Expr::apps(pow_add, [two.clone(), e.clone(), two.clone()]);
            let mul8 = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = zb.fresh_local(nat.clone());
                let body = c.nmul(eight.clone(), z);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
            };
            let c1 = Expr::apps(
                c.congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    pow_e2.clone(),
                    q_mul_p2.clone(),
                    mul8.clone(),
                    h1,
                ],
            );
            let h_comm = Expr::apps(mul_comm, [q.clone(), pow_two_2.clone()]);
            let c2 = Expr::apps(
                c.congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    q_mul_p2.clone(),
                    p2_mul_q.clone(),
                    mul8,
                    h_comm,
                ],
            );
            let h_assoc = Expr::apps(mul_assoc, [eight.clone(), pow_two_2.clone(), q.clone()]);
            let eight_mul_p2q = c.nmul(eight.clone(), p2_mul_q.clone());
            let c3 = c.nsymm(eight_p2_q.clone(), eight_mul_p2q.clone(), h_assoc);
            let eight_mul_e2 = c.nmul(eight.clone(), pow_e2.clone());
            let eight_mul_qp2 = c.nmul(eight.clone(), q_mul_p2.clone());
            let c12 = c.ntrans(
                eight_mul_e2.clone(),
                eight_mul_qp2.clone(),
                eight_mul_p2q.clone(),
                c1,
                c2,
            );
            let key = c.ntrans(
                eight_mul_e2.clone(),
                eight_mul_p2q.clone(),
                eight_p2_q.clone(),
                c12,
                c3,
            );

            let rhs_32q = c.nmul(thirtytwo.clone(), q.clone());
            let refl = Expr::app(c.nat_le_refl.clone(), eight_p2_q.clone());
            let motive = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = zb.fresh_local(nat.clone());
                let body = c.nle(z, rhs_32q.clone());
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
            };
            let symm_key = c.nsymm(eight_mul_e2.clone(), eight_p2_q.clone(), key);
            let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![c.l1.clone()]);
            let body = Expr::apps(
                eq_subst,
                [
                    nat.clone(),
                    motive,
                    eight_p2_q.clone(),
                    eight_mul_e2.clone(),
                    symm_key,
                    refl,
                ],
            );
            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
        };

        // SOUNDNESS: kernel-checked; `(8·2²)·2^e ≡ 32·2^e` is kernel defeq, so
        // `Nat.le.refl` closes the final step. No `sorry`, no self-reference,
        // no domain-axiom dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

fn build_type(c: &C) -> Expr {
    let two = c.lit(2);
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(c.nat.clone());
    let (kk_id, kk) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let hk0_ty = c.rle(c.rat_zero.clone(), kk.clone());
    let (hk0_id, _) = b.fresh_local(hk0_ty.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, _) = b.fresh_local(hpos_ty.clone());
    let hlt1_ty = c.rlt(eps.clone(), c.rat_one.clone());
    let (hlt1_id, _) = b.fresh_local(hlt1_ty.clone());
    let q = c.nc(c.npow(two.clone(), c.nadd(e.clone(), c.lit(1))));
    let guard_ty = c.rle(kk.clone(), c.rmul(q.clone(), eps.clone()));
    let (g_id, _) = b.fresh_local(guard_ty.clone());

    let d = c.npow(two.clone(), c.nadd(e.clone(), two.clone()));
    let nine2d = c.npow(c.lit(9), c.nmul(two.clone(), d));
    let head = c.nc(c.nmul(c.lit(4), nine2d));
    let kc = c.rmul(kk.clone(), c.rmul(kk.clone(), kk.clone()));
    let lhs = c.rmul(head, kc);
    let epssq = c.rmul(eps.clone(), eps.clone());
    let ee48 = c.nmul(c.lit(48), c.npow(two.clone(), e.clone()));
    let b48 = c.nc(c.npow(two.clone(), ee48));
    let rhs = c.rmul(epssq, b48);
    let concl = c.rle(lhs, rhs);

    let e0 = b.mk_pi(g_id, BinderInfo::Default, guard_ty, concl);
    let e0 = b.mk_pi(hlt1_id, BinderInfo::Default, hlt1_ty, e0);
    let e0 = b.mk_pi(hpos_id, BinderInfo::Default, hpos_ty, e0);
    let e0 = b.mk_pi(hk0_id, BinderInfo::Default, hk0_ty, e0);
    let e0 = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e0);
    let e0 = b.mk_pi(kk_id, BinderInfo::Default, c.rat.clone(), e0);
    let e0 = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), e0);
    b.finish(e0)
}

#[allow(clippy::too_many_lines)]
fn build_value(c: &C) -> Expr {
    let two = c.lit(2);
    let three = c.lit(3);
    let four = c.lit(4);
    let five = c.lit(5);
    let eight = c.lit(8);
    let nine = c.lit(9);
    let sixteen = c.lit(16);
    let thirtytwo = c.lit(32);
    let fortyeight = c.lit(48);

    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(c.nat.clone());
    let (kk_id, kk) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hk0_ty = c.rle(c.rat_zero.clone(), kk.clone());
    let (hk0_id, hk0) = b.fresh_local(hk0_ty.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let hlt1_ty = c.rlt(eps.clone(), c.rat_one.clone());
    let (hlt1_id, hlt1) = b.fresh_local(hlt1_ty.clone());
    let pe = c.npow(two.clone(), e.clone());
    let qexp = c.npow(two.clone(), c.nadd(e.clone(), c.lit(1)));
    let qq = c.nc(qexp.clone());
    let guard_ty = c.rle(kk.clone(), c.rmul(qq.clone(), eps.clone()));
    let (g_id, hguard) = b.fresh_local(guard_ty.clone());

    // Nat exponents
    let d = c.npow(two.clone(), c.nadd(e.clone(), two.clone()));
    let two_d = c.nmul(two.clone(), d.clone());
    let nine2d = c.npow(nine.clone(), two_d);
    let e8 = c.nmul(eight.clone(), d.clone());
    let ee32 = c.nmul(thirtytwo.clone(), pe.clone());
    let ee16 = c.nmul(sixteen.clone(), pe.clone());
    let ee48 = c.nmul(fortyeight.clone(), pe.clone());
    let g33 = c.nadd(c.nmul(three.clone(), e.clone()), three.clone());
    let g35 = c.nadd(c.nmul(three.clone(), e.clone()), five.clone());
    let pow_e8 = c.npow(two.clone(), e8.clone());
    let pow_e32 = c.npow(two.clone(), ee32.clone());
    let pow_e16 = c.npow(two.clone(), ee16.clone());
    let pow_e48 = c.npow(two.clone(), ee48.clone());
    let pow_g33 = c.npow(two.clone(), g33.clone());
    let pow_g35 = c.npow(two.clone(), g35.clone());

    // Rat carriers
    let p = c.nc(nine2d.clone());
    let b32 = c.nc(pow_e32.clone());
    let b16 = c.nc(pow_e16.clone());
    let b48 = c.nc(pow_e48.clone());
    let b33 = c.nc(pow_g33.clone());
    let bg35 = c.nc(pow_g35.clone());
    let nc4 = c.nc(four.clone());
    let kk_sq = c.rmul(kk.clone(), kk.clone());
    let kc = c.rmul(kk.clone(), kk_sq.clone());
    let gg = c.rmul(qq.clone(), eps.clone());
    let g_sq = c.rmul(gg.clone(), gg.clone());
    let gc = c.rmul(gg.clone(), g_sq.clone());
    let eps_sq = c.rmul(eps.clone(), eps.clone());
    let epsc = c.rmul(eps.clone(), eps_sq.clone());
    let epssq = eps_sq.clone();
    let head = c.nc(c.nmul(four.clone(), nine2d.clone()));

    // Nonneg facts
    let p_nn = c.nc_nn(nine2d.clone());
    let nc4_nn = c.nc_nn(four.clone());
    let kk_sq_nn = c.nonneg(kk.clone(), kk.clone(), hk0.clone(), hk0.clone());
    let kc_nn = c.nonneg(kk.clone(), kk_sq.clone(), hk0.clone(), kk_sq_nn);
    let h_eps0 = Expr::apps(
        c.rat_le_of_lt.clone(),
        [c.rat_zero.clone(), eps.clone(), hpos.clone()],
    );
    let h_eps1 = Expr::apps(
        c.rat_le_of_lt.clone(),
        [eps.clone(), c.rat_one.clone(), hlt1.clone()],
    );

    // ── HEAD: P ≤ B32 ────────────────────────────────────────────────────────
    let h_pow_nine = Expr::apps(c.pow_nine.clone(), [d.clone()]);
    let h_e8_e32 = Expr::apps(c.e8_le_e32.clone(), [e.clone()]);
    let h_pow_mono = Expr::apps(
        c.pow_le_pow_right.clone(),
        [two.clone(), e8.clone(), ee32.clone(), c.h12(), h_e8_e32],
    );
    let h_nat_head = Expr::apps(
        c.nat_le_trans.clone(),
        [
            nine2d.clone(),
            pow_e8.clone(),
            pow_e32.clone(),
            h_pow_nine,
            h_pow_mono,
        ],
    );
    let h_head_rat = Expr::apps(
        c.ofnat_le_ofnat.clone(),
        [nine2d.clone(), pow_e32.clone(), h_nat_head],
    );

    // ── CUBE: Kc ≤ Gc ────────────────────────────────────────────────────────
    let h_cube = Expr::apps(
        c.pow3.clone(),
        [kk.clone(), gg.clone(), hk0.clone(), hguard.clone()],
    );

    // ── CORE: nc4·(P·Kc) ≤ nc4·(B32·Gc) ─────────────────────────────────────
    let core = Expr::apps(
        c.mul_le_mul.clone(),
        [
            p.clone(),
            b32.clone(),
            kc.clone(),
            gc.clone(),
            p_nn,
            kc_nn,
            h_head_rat,
            h_cube,
        ],
    );
    let p_kc = c.rmul(p.clone(), kc.clone());
    let b32_gc = c.rmul(b32.clone(), gc.clone());
    let core_l = Expr::apps(
        c.mul_le_left.clone(),
        [
            nc4.clone(),
            p_kc.clone(),
            b32_gc.clone(),
            core,
            nc4_nn.clone(),
        ],
    );
    // core_l : nc4·(P·Kc) ≤ nc4·(B32·Gc)

    // ── LEFT id: head·Kc = nc4·(P·Kc) ───────────────────────────────────────
    let eq_nc4p = c.mul_natcast(four.clone(), nine2d.clone()); // nc4·P = head
    let nc4_p = c.rmul(nc4.clone(), p.clone());
    let nc4p_kc = c.rmul(nc4_p.clone(), kc.clone());
    let head_kc = c.rmul(head.clone(), kc.clone());
    let nc4_pkc = c.rmul(nc4.clone(), p_kc.clone());
    // (nc4·P)·Kc = head·Kc
    let eq_l1 = c.cong(
        nc4_p.clone(),
        head.clone(),
        c.lam_r(&b, kc.clone()),
        eq_nc4p,
    );
    // head·Kc = (nc4·P)·Kc
    let eq_head_nc4pkc = c.symm(nc4p_kc.clone(), head_kc.clone(), eq_l1);
    // (nc4·P)·Kc = nc4·(P·Kc)
    let eq_assoc_l = c.assoc(nc4.clone(), p.clone(), kc.clone());
    // head·Kc = nc4·(P·Kc)
    let eq_left = c.trans(
        head_kc.clone(),
        nc4p_kc.clone(),
        nc4_pkc.clone(),
        eq_head_nc4pkc,
        eq_assoc_l,
    );
    let eq_left_sym = c.symm(head_kc.clone(), nc4_pkc.clone(), eq_left);
    let nc4_b32gc = c.rmul(nc4.clone(), b32_gc.clone());
    let after_left = c.rw_lhs(
        &b,
        nc4_pkc.clone(),
        head_kc.clone(),
        nc4_b32gc.clone(),
        eq_left_sym,
        core_l,
    );
    // after_left : head·Kc ≤ nc4·(B32·Gc)

    // ── RIGHT id (1): Gc = B33·epsc ─────────────────────────────────────────
    let qq_qq = c.rmul(qq.clone(), qq.clone());
    let q_qq = c.rmul(qq.clone(), qq_qq.clone());
    let eps_epseps = epsc.clone(); // eps·(eps·eps)
    let qcube_epscube = c.rmul(q_qq.clone(), eps_epseps.clone());
    // G·G = (Q·Q)·(eps·eps)
    let qq2_eps2 = c.rmul(qq_qq.clone(), eps_sq.clone());
    let eq_gg = Expr::apps(
        c.mmmc.clone(),
        [qq.clone(), eps.clone(), qq.clone(), eps.clone()],
    );
    // G·(G·G) = G·((Q·Q)·(eps·eps))
    let g_qq2eps2 = c.rmul(gg.clone(), qq2_eps2.clone());
    let eq_g_gg = c.cong(
        g_sq.clone(),
        qq2_eps2.clone(),
        c.lam_l(&b, gg.clone()),
        eq_gg,
    );
    // G·((Q·Q)·(eps·eps)) = (Q·(Q·Q))·(eps·(eps·eps))   [mmmc Q eps (Q·Q) (eps·eps)]
    let eq_inter = Expr::apps(
        c.mmmc.clone(),
        [qq.clone(), eps.clone(), qq_qq.clone(), eps_sq.clone()],
    );
    let eq_gc_mid = c.trans(
        gc.clone(),
        g_qq2eps2.clone(),
        qcube_epscube.clone(),
        eq_g_gg,
        eq_inter,
    );
    // Q·(Q·Q) = B33 :
    let eq_qq_qq = c.mul_natcast(qexp.clone(), qexp.clone()); // Q·Q = nc(qexp·qexp)
    let qexp_qexp = c.nmul(qexp.clone(), qexp.clone());
    let nc_qq = c.nc(qexp_qexp.clone());
    let eq_q_qq = c.cong(
        qq_qq.clone(),
        nc_qq.clone(),
        c.lam_l(&b, qq.clone()),
        eq_qq_qq,
    );
    let eq_q_ncqq = c.mul_natcast(qexp.clone(), qexp_qexp.clone()); // Q·nc(qexp·qexp)=nc(qexp·(qexp·qexp))
    let qexp_cube = c.nmul(qexp.clone(), qexp_qexp.clone());
    let nc_qcube = c.nc(qexp_cube.clone());
    let q_nc = c.rmul(qq.clone(), nc_qq.clone());
    let eq_qcube_nat = c.trans(
        q_qq.clone(),
        q_nc.clone(),
        nc_qcube.clone(),
        eq_q_qq,
        eq_q_ncqq,
    );
    // Nat bridge: qexp·(qexp·qexp) = Nat.pow qexp 3.
    //   Nat.pow qexp 3 ≡ ((1·qexp)·qexp)·qexp by defeq (left-nested, 1 = succ 0).
    //   Build: qexp·(qexp·qexp) = (qexp·qexp)·qexp   [symm mul_assoc qexp qexp qexp]
    //          (qexp·qexp)·qexp = ((1·qexp)·qexp)·qexp [congr ·qexp on qexp·qexp=(1·qexp)·qexp]
    //   where qexp·qexp = (1·qexp)·qexp is congr ·qexp on (qexp = 1·qexp = symm one_mul).
    let nat_one_mul = Expr::const_(Name::from_string("Nat.one_mul"), vec![]);
    let nat_mul_assoc = Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]);
    let one = c.lit(1);
    let one_qexp = c.nmul(one.clone(), qexp.clone()); // 1·qexp
    let qq_nat = c.nmul(qexp.clone(), qexp.clone()); // qexp·qexp
    let oneq_q = c.nmul(one_qexp.clone(), qexp.clone()); // (1·qexp)·qexp
    let assoc_qqq = Expr::apps(nat_mul_assoc, [qexp.clone(), qexp.clone(), qexp.clone()]); // (q·q)·q = q·(q·q)
    let qq_q = c.nmul(qq_nat.clone(), qexp.clone()); // (qexp·qexp)·qexp
    let assoc_sym = c.nsymm(qq_q.clone(), qexp_cube.clone(), assoc_qqq); // q·(q·q) = (q·q)·q
    let h_one_mul = Expr::apps(nat_one_mul, [qexp.clone()]); // 1·qexp = qexp
    let h_one_mul_sym = c.nsymm(one_qexp.clone(), qexp.clone(), h_one_mul); // qexp = 1·qexp
                                                                            // λx. x·qexp
    let lam_xq = {
        let mut zb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = zb.fresh_local(c.nat.clone());
        let body = c.nmul(z, qexp.clone());
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
    };
    // congr ·qexp : qexp·qexp = (1·qexp)·qexp  (lift qexp = 1·qexp in first factor)
    let eq_qq_to_1qq = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat.clone(),
            c.nat.clone(),
            qexp.clone(),
            one_qexp.clone(),
            lam_xq.clone(),
            h_one_mul_sym,
        ],
    );
    // congr ·qexp again : (qexp·qexp)·qexp = ((1·qexp)·qexp)·qexp
    let eq_qqq_to_1qqq = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat.clone(),
            c.nat.clone(),
            qq_nat.clone(),
            oneq_q.clone(),
            lam_xq,
            eq_qq_to_1qq,
        ],
    );
    // nat_bridge : qexp·(qexp·qexp) = ((1·qexp)·qexp)·qexp  (≡ Nat.pow qexp 3 by defeq)
    let pow_qexp_3 = c.npow(qexp.clone(), three.clone());
    let oneqq_q = c.nmul(oneq_q.clone(), qexp.clone()); // ((1·qexp)·qexp)·qexp
    let nat_bridge = c.ntrans(
        qexp_cube.clone(),
        qq_q.clone(),
        oneqq_q.clone(),
        assoc_sym,
        eq_qqq_to_1qqq,
    );
    // pow_e1_cubed : Nat.pow qexp 3 = 2^(3e+3) ; nat_bridge RHS ≡ Nat.pow qexp 3 defeq
    let h_nat_cube = Expr::apps(c.pow_e1_cubed.clone(), [e.clone()]);
    let _ = pow_qexp_3;
    // h_qcube : qexp·(qexp·qexp) = 2^(3e+3)
    let h_qcube = c.ntrans(
        qexp_cube.clone(),
        oneqq_q.clone(),
        pow_g33.clone(),
        nat_bridge,
        h_nat_cube,
    );
    // cast: nc(qexp·(qexp·qexp)) = nc(2^(3e+3)) = B33
    let eq_cast_cube = c.cong_nc(&b, qexp_cube.clone(), pow_g33.clone(), h_qcube);
    let eq_q_qq_b33 = c.trans(
        q_qq.clone(),
        nc_qcube.clone(),
        b33.clone(),
        eq_qcube_nat,
        eq_cast_cube,
    );
    // (Q·(Q·Q))·(eps·(eps·eps)) = B33·epsc
    let eq_left_factor = c.cong(
        q_qq.clone(),
        b33.clone(),
        c.lam_r(&b, eps_epseps.clone()),
        eq_q_qq_b33,
    );
    let b33_epsc = c.rmul(b33.clone(), epsc.clone());
    let eq_gc = c.trans(
        gc.clone(),
        qcube_epscube.clone(),
        b33_epsc.clone(),
        eq_gc_mid,
        eq_left_factor,
    );

    // rewrite RHS: nc4·(B32·Gc) -> nc4·(B32·(B33·epsc))
    let lam_nc4_b32 = {
        let mut zb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = zb.fresh_local(c.rat.clone());
        let body = c.rmul(nc4.clone(), c.rmul(b32.clone(), z));
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let eq_step_gc = c.cong(gc.clone(), b33_epsc.clone(), lam_nc4_b32, eq_gc);
    let nc4_b32_b33epsc = c.rmul(nc4.clone(), c.rmul(b32.clone(), b33_epsc.clone()));
    let after_gc = c.rw_rhs(
        &b,
        head_kc.clone(),
        nc4_b32gc.clone(),
        nc4_b32_b33epsc.clone(),
        eq_step_gc,
        after_left,
    );
    // after_gc : head·Kc ≤ nc4·(B32·(B33·epsc))

    // ── RIGHT id (2): nc4·(B32·(B33·epsc)) = (nc4·(B32·B33))·epsc ────────────
    let b32_b33 = c.rmul(b32.clone(), b33.clone());
    let b32_b33epsc = c.rmul(b32.clone(), b33_epsc.clone());
    let b32b33_epsc = c.rmul(b32_b33.clone(), epsc.clone());
    let nc4_b32b33 = c.rmul(nc4.clone(), b32_b33.clone());
    let nc4_b32b33_epsc = c.rmul(nc4_b32b33.clone(), epsc.clone());
    let nc4_b32b33epsc = c.rmul(nc4.clone(), b32b33_epsc.clone());
    // assoc B32 B33 epsc : (B32·B33)·epsc = B32·(B33·epsc) ; symm
    let assoc_b = c.assoc(b32.clone(), b33.clone(), epsc.clone());
    let assoc_b_sym = c.symm(b32b33_epsc.clone(), b32_b33epsc.clone(), assoc_b);
    let eq_a = c.cong(
        b32_b33epsc.clone(),
        b32b33_epsc.clone(),
        c.lam_l(&b, nc4.clone()),
        assoc_b_sym,
    );
    // assoc nc4 (B32·B33) epsc : (nc4·(B32·B33))·epsc = nc4·((B32·B33)·epsc) ; symm
    let assoc_nc4 = c.assoc(nc4.clone(), b32_b33.clone(), epsc.clone());
    let assoc_nc4_sym = c.symm(nc4_b32b33_epsc.clone(), nc4_b32b33epsc.clone(), assoc_nc4);
    let eq_right_assoc = c.trans(
        nc4_b32_b33epsc.clone(),
        nc4_b32b33epsc.clone(),
        nc4_b32b33_epsc.clone(),
        eq_a,
        assoc_nc4_sym,
    );
    let after_assoc = c.rw_rhs(
        &b,
        head_kc.clone(),
        nc4_b32_b33epsc.clone(),
        nc4_b32b33_epsc.clone(),
        eq_right_assoc,
        after_gc,
    );
    // after_assoc : head·Kc ≤ (nc4·(B32·B33))·epsc

    // ── RIGHT id (3): nc4·(B32·B33) = B32·nc(2^(3e+5)) ──────────────────────
    let nc4_b32 = c.rmul(nc4.clone(), b32.clone());
    let b32_nc4 = c.rmul(b32.clone(), nc4.clone());
    let nc4_b33 = c.rmul(nc4.clone(), b33.clone());
    let nc4_b32_b33 = c.rmul(nc4_b32.clone(), b33.clone());
    let b32_nc4_b33 = c.rmul(b32_nc4.clone(), b33.clone());
    let b32_nc4b33 = c.rmul(b32.clone(), nc4_b33.clone());
    let assoc1 = c.assoc(nc4.clone(), b32.clone(), b33.clone());
    let assoc1_sym = c.symm(nc4_b32_b33.clone(), nc4_b32b33.clone(), assoc1);
    let comm_nc4b32 = c.comm(nc4.clone(), b32.clone());
    let eq_c1 = c.cong(
        nc4_b32.clone(),
        b32_nc4.clone(),
        c.lam_r(&b, b33.clone()),
        comm_nc4b32,
    );
    let assoc2 = c.assoc(b32.clone(), nc4.clone(), b33.clone());
    let t1 = c.trans(
        nc4_b32b33.clone(),
        nc4_b32_b33.clone(),
        b32_nc4_b33.clone(),
        assoc1_sym,
        eq_c1,
    );
    let t2 = c.trans(
        nc4_b32b33.clone(),
        b32_nc4_b33.clone(),
        b32_nc4b33.clone(),
        t1,
        assoc2,
    );
    // nc4·B33 = nc(4·2^(3e+3)) = nc(2^(3e+5)) = bg35
    let eq_nc4b33 = c.mul_natcast(four.clone(), pow_g33.clone());
    let nc_4_233 = c.nc(c.nmul(four.clone(), pow_g33.clone()));
    let h_four = Expr::apps(c.four_mul_pow.clone(), [e.clone()]);
    let four_233 = c.nmul(four.clone(), pow_g33.clone());
    let eq_cast_four = c.cong_nc(&b, four_233.clone(), pow_g35.clone(), h_four);
    let eq_nc4b33_full = c.trans(
        nc4_b33.clone(),
        nc_4_233.clone(),
        bg35.clone(),
        eq_nc4b33,
        eq_cast_four,
    );
    let b32_bg35 = c.rmul(b32.clone(), bg35.clone());
    let eq_b32z = c.cong(
        nc4_b33.clone(),
        bg35.clone(),
        c.lam_l(&b, b32.clone()),
        eq_nc4b33_full,
    );
    let eq_coef = c.trans(
        nc4_b32b33.clone(),
        b32_nc4b33.clone(),
        b32_bg35.clone(),
        t2,
        eq_b32z,
    );
    // congr ·epsc
    let lhs_coef_epsc = c.rmul(nc4_b32b33.clone(), epsc.clone());
    let rhs_coef_epsc = c.rmul(b32_bg35.clone(), epsc.clone());
    let eq_coef_epsc = c.cong(
        nc4_b32b33.clone(),
        b32_bg35.clone(),
        c.lam_r(&b, epsc.clone()),
        eq_coef,
    );
    let after_coef = c.rw_rhs(
        &b,
        head_kc.clone(),
        lhs_coef_epsc.clone(),
        rhs_coef_epsc.clone(),
        eq_coef_epsc,
        after_assoc,
    );
    // after_coef : head·Kc ≤ (B32·nc(2^(3e+5)))·epsc

    // ── monotone bounds: (B32·bg35)·epsc ≤ (B32·B16)·epssq ──────────────────
    let h_three_e = Expr::apps(c.three_e.clone(), [e.clone()]);
    let h_pow_g35_mono = Expr::apps(
        c.pow_le_pow_right.clone(),
        [two.clone(), g35.clone(), ee16.clone(), c.h12(), h_three_e],
    );
    let h_g35_le_b16 = Expr::apps(
        c.ofnat_le_ofnat.clone(),
        [pow_g35.clone(), pow_e16.clone(), h_pow_g35_mono],
    );
    let h_cube_le_sq = Expr::apps(c.cube_le_sq.clone(), [eps.clone(), h_eps0.clone(), h_eps1]);
    let b32_nn = c.nc_nn(pow_e32.clone());
    let bg35_nn = c.nc_nn(pow_g35.clone());
    let x_nn = c.nonneg(b32.clone(), bg35.clone(), b32_nn.clone(), bg35_nn);
    let eps_sq_nn = c.nonneg(eps.clone(), eps.clone(), h_eps0.clone(), h_eps0.clone());
    let z_nn = c.nonneg(eps.clone(), eps_sq.clone(), h_eps0.clone(), eps_sq_nn);
    let h_xy = Expr::apps(
        c.mul_le_left.clone(),
        [
            b32.clone(),
            bg35.clone(),
            b16.clone(),
            h_g35_le_b16,
            b32_nn.clone(),
        ],
    );
    let b32_b16 = c.rmul(b32.clone(), b16.clone());
    let core2 = Expr::apps(
        c.mul_le_mul.clone(),
        [
            b32_bg35.clone(),
            b32_b16.clone(),
            epsc.clone(),
            epssq.clone(),
            x_nn,
            z_nn,
            h_xy,
            h_cube_le_sq,
        ],
    );
    let lhs_x_epsc = c.rmul(b32_bg35.clone(), epsc.clone());
    let rhs_xy_epssq = c.rmul(b32_b16.clone(), epssq.clone());
    let chained = c.le_trans(
        head_kc.clone(),
        lhs_x_epsc.clone(),
        rhs_xy_epssq.clone(),
        after_coef,
        core2,
    );
    // chained : head·Kc ≤ (B32·B16)·epssq

    // ── final id: (B32·B16)·epssq = epssq·B48 ──────────────────────────────
    let eq_b32b16 = c.mul_natcast(pow_e32.clone(), pow_e16.clone()); // B32·B16 = nc(2^E32·2^E16)
    let prod = c.nmul(pow_e32.clone(), pow_e16.clone());
    let nc_prod = c.nc(prod.clone());
    let e32_e16 = c.nadd(ee32.clone(), ee16.clone());
    let pow_sum = c.npow(two.clone(), e32_e16.clone());
    let h_pow_add = Expr::apps(
        c.nat_pow_add.clone(),
        [two.clone(), ee32.clone(), ee16.clone()],
    ); // 2^(E32+E16)=2^E32·2^E16
    let h_pow_add_sym = c.nsymm(pow_sum.clone(), prod.clone(), h_pow_add); // 2^E32·2^E16=2^(E32+E16)
    let h_split = Expr::apps(c.forty_eight_split.clone(), [e.clone()]); // 48·2^e=32·2^e+16·2^e
    let h_split_sym = c.nsymm(ee48.clone(), e32_e16.clone(), h_split); // E32+E16=48·2^e
    let h_pow_eq = c.cong_pow2(&b, e32_e16.clone(), ee48.clone(), h_split_sym); // 2^(E32+E16)=2^E48
    let h_nat_prod = c.ntrans(
        prod.clone(),
        pow_sum.clone(),
        pow_e48.clone(),
        h_pow_add_sym,
        h_pow_eq,
    );
    let eq_cast_prod = c.cong_nc(&b, prod.clone(), pow_e48.clone(), h_nat_prod); // nc(2^E32·2^E16)=B48
    let eq_b32b16_b48 = c.trans(
        b32_b16.clone(),
        nc_prod.clone(),
        b48.clone(),
        eq_b32b16,
        eq_cast_prod,
    );
    let b48_epssq = c.rmul(b48.clone(), epssq.clone());
    let eq_rhs1 = c.cong(
        b32_b16.clone(),
        b48.clone(),
        c.lam_r(&b, epssq.clone()),
        eq_b32b16_b48,
    );
    let eq_comm_final = c.comm(b48.clone(), epssq.clone());
    let epssq_b48 = c.rmul(epssq.clone(), b48.clone());
    let eq_final = c.trans(
        rhs_xy_epssq.clone(),
        b48_epssq.clone(),
        epssq_b48.clone(),
        eq_rhs1,
        eq_comm_final,
    );
    let result = c.rw_rhs(
        &b,
        head_kc.clone(),
        rhs_xy_epssq.clone(),
        epssq_b48.clone(),
        eq_final,
        chained,
    );
    // result : head·Kc ≤ epssq·B48

    // ── close binders ───────────────────────────────────────────────────────
    let lam_g = b.mk_lam(g_id, BinderInfo::Default, guard_ty, result);
    let lam_h1 = b.mk_lam(hlt1_id, BinderInfo::Default, hlt1_ty, lam_g);
    let lam_hp = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, lam_h1);
    let lam_hk = b.mk_lam(hk0_id, BinderInfo::Default, hk0_ty, lam_hp);
    let lam_eps = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), lam_hk);
    let lam_kk = b.mk_lam(kk_id, BinderInfo::Default, c.rat.clone(), lam_eps);
    let lam_e = b.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), lam_kk);
    b.finish(lam_e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_eight_mul_pow_two_add_two_le_thirty_two_checks() {
        let mut env = Environment::with_prelude();
        env.register_nat_eight_mul_pow_two_add_two_le_thirty_two()
            .expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.eight_mul_pow_two_add_two_le_thirty_two");
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("helper should type-check: {e:?}"));
        let deps = env.axiom_deps(&n).expect("registered");
        assert!(deps.is_empty(), "helper must be axiom-free");
    }

    #[test]
    fn test_friedgut_size_poly_bound_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_size_poly_bound().expect("register");
        env.register_friedgut_size_poly_bound().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("BoolAnalysis.friedgut_size_poly_bound");
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("lemma should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }
}
