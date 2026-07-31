// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T61 (#3648 Branch B): constructive proof term for
//! `NNVerify.Block.blockwise_complexity`.
//!
//! Statement:
//! ```text
//! ∀ (k : Nat) (bd : Nat -> Nat),
//!   crown_cost k bd ≤ total_dim k bd * total_dim k bd
//! ```
//! With the FAITHFUL carriers
//! `crown_cost k bd = Nat.rec 0 (fun m ih => ih + bd m * bd m) k` and
//! `total_dim k bd = Nat.rec 0 (fun m ih => ih + bd m) k`, this is the genuine
//! combinatorial fact `Σ_{m<k} bd(m)² ≤ (Σ_{m<k} bd(m))²`.
//!
//! ## Proof (induction on `k` via `Nat.rec.{0}`)
//!
//! Motive `P k := Nat.le (crown_cost k bd) (total_dim k bd * total_dim k bd)`.
//! Because both carriers are reducible, the kernel δ+ι-reduces `P Nat.zero` and
//! `P (Nat.succ m)` to the concrete folds below.
//!
//! - **Base `P 0`:** `crown_cost 0 bd ↝ 0`, `total_dim 0 bd ↝ 0`, and
//!   `0 * 0 ↝ 0`, so the goal is `Nat.le 0 0`, witnessed by `Nat.le.refl 0`.
//!
//! - **Step `P m → P (succ m)`:** writing `C := crown_cost m bd`,
//!   `T := total_dim m bd`, `b := bd m`, the goal reduces to
//!   `Nat.le (C + b*b) ((T + b) * (T + b))`. From the IH `ih : Nat.le C (T*T)`:
//!   1. `Nat.add_le_add C (T*T) (b*b) (b*b) ih (Nat.le.refl (b*b))`
//!      : `Nat.le (C + b*b) (T*T + b*b)`.
//!   2. `sq_super : Nat.le (T*T + b*b) ((T + b) * (T + b))`, built from
//!      `Nat.le_add_right` on each summand + `Nat.add_le_add`, then transported
//!      across the distributivity identity
//!      `(T*T + T*b) + (b*T + b*b) = (T+b)*(T+b)` (via `Eq.subst`).
//!   3. `Nat.le_trans` chains (1) and (2).
//!
//! All leaf lemmas are constructive `Declaration::Theorem`s (no `sorry`, no
//! axiom): `Nat.add_le_add`, `Nat.le_add_right`, `Nat.le_trans`,
//! `Nat.left_distrib`, `Nat.right_distrib`, plus the `Nat.le.refl` constructor
//! and `Eq.subst` / `Eq.symm` / `Eq.trans` / `congrArg` core lemmas.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Constants used by the T61 proof term.
struct T61ProofConsts {
    nat: Expr,
    nat_zero: Expr,
    #[cfg(test)]
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_rec0: Expr,
    nat_le: Expr,
    le_refl_ctor: Expr,
    crown_cost: Expr,
    total_dim: Expr,
    add_le_add: Expr,
    le_add_right: Expr,
    le_trans: Expr,
    left_distrib: Expr,
    right_distrib: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl T61ProofConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            #[cfg(test)]
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            // Nat.rec.{0}: motive lands in Prop for the induction over k.
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            crown_cost: Expr::const_(Name::from_string("NNVerify.Block.crown_cost"), vec![]),
            total_dim: Expr::const_(Name::from_string("NNVerify.Block.total_dim"), vec![]),
            add_le_add: Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
            le_add_right: Expr::const_(Name::from_string("Nat.le_add_right"), vec![]),
            le_trans: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            left_distrib: Expr::const_(Name::from_string("Nat.left_distrib"), vec![]),
            right_distrib: Expr::const_(Name::from_string("Nat.right_distrib"), vec![]),
            // Eq.subst.{1}: α = Nat lives in Sort 1.
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![one.clone()]),
            // Eq.symm.{1} / Eq.trans.{1} over Nat.
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
            // congrArg.{1,1}: Nat -> Nat.
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        }
    }

    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a.clone(), b.clone()])
    }

    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a.clone(), b.clone()])
    }

    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a.clone(), b.clone()])
    }

    /// `crown_cost k bd`.
    fn cost(&self, k: &Expr, bd: &Expr) -> Expr {
        Expr::apps(self.crown_cost.clone(), [k.clone(), bd.clone()])
    }

    /// `total_dim k bd`.
    fn total(&self, k: &Expr, bd: &Expr) -> Expr {
        Expr::apps(self.total_dim.clone(), [k.clone(), bd.clone()])
    }

    /// `@Nat.left_distrib a b c : a*(b+c) = a*b + a*c`.
    fn left_distrib(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::apps(self.left_distrib.clone(), [a.clone(), b.clone(), c.clone()])
    }

    /// `@Nat.right_distrib a b c : (a+b)*c = a*c + b*c`.
    fn right_distrib(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::apps(
            self.right_distrib.clone(),
            [a.clone(), b.clone(), c.clone()],
        )
    }

    /// `@congrArg.{1,1} Nat Nat from to f h : f from = f to`.
    fn congr_arg(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.nat.clone(),
                self.nat.clone(),
                from.clone(),
                to.clone(),
                f,
                h,
            ],
        )
    }

    /// `@Eq.trans.{1} Nat x y z hxy hyz : x = z`.
    fn eq_trans(&self, x: &Expr, y: &Expr, z: &Expr, hxy: Expr, hyz: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.nat.clone(), x.clone(), y.clone(), z.clone(), hxy, hyz],
        )
    }

    /// `@Eq.symm.{1} Nat a b h : b = a`.
    fn eq_symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm.clone(),
            [self.nat.clone(), a.clone(), b.clone(), h],
        )
    }

    /// `@Eq.subst.{1} Nat motive from to h p : motive to`, with `motive : Nat -> Prop`.
    fn eq_subst(&self, motive: Expr, from: &Expr, to: &Expr, h: Expr, p: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat.clone(), motive, from.clone(), to.clone(), h, p],
        )
    }

    /// `@Nat.add_le_add a b c d h1 h2 : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), h1, h2],
        )
    }

    /// `@Nat.le_add_right n k : n ≤ n + k`.
    fn le_add_right(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.le_add_right.clone(), [n.clone(), k.clone()])
    }

    /// `@Nat.le_trans a b c hab hbc : a ≤ c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl(&self, n: &Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n.clone())
    }
}

/// Build the proof value for `NNVerify.Block.blockwise_complexity`:
/// `fun (k : Nat) (bd : Nat -> Nat) => Nat.rec.{0} P base step k`.
pub(super) fn build_t61_proof_value() -> Expr {
    let c = T61ProofConsts::new();

    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
    let (bd_id, bd) = b.fresh_local(block_dim_ty.clone());

    // motive P : Nat -> Prop :=
    //   fun (j : Nat) => Nat.le (crown_cost j bd) (total_dim j bd * total_dim j bd)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = mb.fresh_local(c.nat.clone());
        let cost_j = c.cost(&j, &bd);
        let tot_j = c.total(&j, &bd);
        let body = c.le(&cost_j, &c.mul(&tot_j, &tot_j));
        let lam = mb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };

    // base : P 0.  P 0 reduces to `Nat.le 0 (0 * 0)` ≡ `Nat.le 0 0`.
    let base = c.le_refl(&c.nat_zero);

    // step : ∀ (m : Nat), P m -> P (Nat.succ m).
    let step = build_step(&c, &b, &bd);

    let rec_app = Expr::apps(c.nat_rec0.clone(), [motive, base, step, k.clone()]);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, rec_app);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the `Nat.rec` step branch:
/// `fun (m : Nat) (ih : P m) => (proof of P (succ m))`.
fn build_step(c: &T61ProofConsts, parent: &EnvDeclBuilder, bd: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = sb.fresh_local(c.nat.clone());

    // C := crown_cost m bd,  T := total_dim m bd,  b := bd m.
    let cc = c.cost(&m, bd);
    let t = c.total(&m, bd);
    let bm = Expr::app(bd.clone(), m.clone());

    // ih : P m  ≡  Nat.le C (T*T).
    let tt = c.mul(&t, &t);
    let ih_type = c.le(&cc, &tt);
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());

    // Goal P (succ m) reduces (δ+ι on the carriers) to:
    //   Nat.le (C + b*b) ((T + b) * (T + b)).
    let bb = c.mul(&bm, &bm);
    let t_plus_b = c.add(&t, &bm);
    let sq = c.mul(&t_plus_b, &t_plus_b);
    let c_plus_bb = c.add(&cc, &bb);
    let tt_plus_bb = c.add(&tt, &bb);

    // step1 : Nat.le (C + b*b) (T*T + b*b)
    //   via add_le_add C (T*T) (b*b) (b*b) ih (Nat.le.refl (b*b)).
    let step1 = c.add_le_add(&cc, &tt, &bb, &bb, ih, c.le_refl(&bb));

    // step2 : Nat.le (T*T + b*b) ((T + b) * (T + b)).
    let step2 = build_sq_super(c, &sb, &t, &bm);

    // body : Nat.le (C + b*b) ((T + b) * (T + b)) via le_trans.
    let body = c.le_trans(&c_plus_bb, &tt_plus_bb, &sq, step1, step2);

    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
    let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam_ih);
    sb.finish_child(lam_m)
}

/// Build `sq_super : Nat.le (T*T + b*b) ((T+b)*(T+b))`.
///
/// Let `D := (T*T + T*b) + (b*T + b*b)`. We first show
/// `Nat.le (T*T + b*b) D` from `T*T ≤ T*T + T*b` and `b*b ≤ b*T + b*b`, then
/// transport across `hED : D = (T+b)*(T+b)` with `Eq.subst`.
fn build_sq_super(c: &T61ProofConsts, parent: &EnvDeclBuilder, t: &Expr, bm: &Expr) -> Expr {
    let tt = c.mul(t, t);
    let tb = c.mul(t, bm);
    let bt = c.mul(bm, t);
    let bb = c.mul(bm, bm);

    let tt_plus_tb = c.add(&tt, &tb); // T*T + T*b   = T*(T+b)
    let bt_plus_bb = c.add(&bt, &bb); // b*T + b*b   = b*(T+b)
    let big_d = c.add(&tt_plus_tb, &bt_plus_bb); // D
    let tt_plus_bb = c.add(&tt, &bb);

    // p1 : Nat.le (T*T) (T*T + T*b)   via le_add_right (T*T) (T*b).
    let p1 = c.le_add_right(&tt, &tb);
    // p2 : Nat.le (b*b) (b*T + b*b).  le_add_right gives b*b ≤ b*b + b*T;
    // we instead want b*b ≤ b*T + b*b, so build that summand order directly
    // and rely on the matching D below. Use add_le_add to assemble:
    //   add_le_add (T*T) (T*T+T*b) (b*b) (b*T+b*b) p1 p2'
    // with p2' : Nat.le (b*b) (b*T + b*b).
    let p2 = build_le_add_left(c, parent, bm, t); // b*b ≤ b*T + b*b

    // p_le_d : Nat.le (T*T + b*b) D.
    let p_le_d = c.add_le_add(&tt, &tt_plus_tb, &bb, &bt_plus_bb, p1, p2);

    // hED : D = (T+b)*(T+b).  Build via the distributivity Eq chain, then symm.
    let t_plus_b = c.add(t, bm);
    let sq = c.mul(&t_plus_b, &t_plus_b);
    // h_sq_eq_d : (T+b)*(T+b) = D.
    let h_sq_eq_d = build_square_eq_d(c, parent, t, bm);
    // hED : D = (T+b)*(T+b) via Eq.symm.
    let h_ed = c.eq_symm(&sq, &big_d, h_sq_eq_d);

    // motive_sub : fun (x : Nat) => Nat.le (T*T + b*b) x.
    let motive_sub = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(c.nat.clone());
        let body = c.le(&tt_plus_bb, &x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    // Eq.subst motive_sub D (T+b)*(T+b) hED p_le_d : Nat.le (T*T+b*b) ((T+b)*(T+b)).
    c.eq_subst(motive_sub, &big_d, &sq, h_ed, p_le_d)
}

/// Build `b*b ≤ b*T + b*b`.
///
/// `le_add_right` gives `b*b ≤ b*b + (b*T)`. We rewrite the RHS to `b*T + b*b`
/// via `Nat.add_comm`-free reasoning: instead build it directly by
/// `Eq.subst` on the commutativity identity. To avoid pulling `Nat.add_comm`,
/// we obtain the bound through `Nat.add_le_add` from the trivial summands.
fn build_le_add_left(c: &T61ProofConsts, parent: &EnvDeclBuilder, bm: &Expr, t: &Expr) -> Expr {
    // b*b ≤ b*T + b*b :  from 0 ≤ b*T and b*b ≤ b*b is not directly an
    // add_le_add of the right shape. Use le_add_right on the SECOND summand by
    // commuting via Eq.subst on Nat.add_comm.
    let bt = c.mul(bm, t);
    let bb = c.mul(bm, bm);
    // p : b*b ≤ b*b + b*T  (le_add_right (b*b) (b*T)).
    let p = c.le_add_right(&bb, &bt);
    let bb_plus_bt = c.add(&bb, &bt);
    let bt_plus_bb = c.add(&bt, &bb);
    // h_comm : (b*b + b*T) = (b*T + b*b)  via Nat.add_comm.
    let add_comm = Expr::const_(Name::from_string("Nat.add_comm"), vec![]);
    let h_comm = Expr::apps(add_comm, [bb.clone(), bt.clone()]);
    // motive : fun x => Nat.le (b*b) x.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(c.nat.clone());
        let body = c.le(&bb, &x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    c.eq_subst(motive, &bb_plus_bt, &bt_plus_bb, h_comm, p)
}

/// Build `h_sq_eq_d : (T+b)*(T+b) = (T*T + T*b) + (b*T + b*b)`.
///
/// Chain:
///   (T+b)*(T+b)
///     = T*(T+b) + b*(T+b)              [right_distrib T b (T+b)]
///     = (T*T + T*b) + b*(T+b)          [congrArg (·+ b*(T+b)) (left_distrib T T b)]
///     = (T*T + T*b) + (b*T + b*b)      [congrArg ((T*T+T*b) +·) (left_distrib b T b)]
fn build_square_eq_d(c: &T61ProofConsts, parent: &EnvDeclBuilder, t: &Expr, bm: &Expr) -> Expr {
    let t_plus_b = c.add(t, bm);
    let sq = c.mul(&t_plus_b, &t_plus_b);

    // e1 : (T+b)*(T+b) = T*(T+b) + b*(T+b).
    let t_tb = c.mul(t, &t_plus_b);
    let b_tb = c.mul(bm, &t_plus_b);
    let rhs1 = c.add(&t_tb, &b_tb);
    let e1 = c.right_distrib(t, bm, &t_plus_b);

    // e2a : T*(T+b) = T*T + T*b.
    let tt = c.mul(t, t);
    let tb = c.mul(t, bm);
    let tt_plus_tb = c.add(&tt, &tb);
    let e2a = c.left_distrib(t, t, bm);
    // e2 : (T*(T+b) + b*(T+b)) = ((T*T+T*b) + b*(T+b))   via congrArg (·+ b*(T+b)).
    let f_add_b_tb = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(c.nat.clone());
        let body = c.add(&x, &b_tb);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    let e2 = c.congr_arg(&t_tb, &tt_plus_tb, f_add_b_tb, e2a);
    let rhs2 = c.add(&tt_plus_tb, &b_tb);

    // e3a : b*(T+b) = b*T + b*b.
    let bt = c.mul(bm, t);
    let bb = c.mul(bm, bm);
    let bt_plus_bb = c.add(&bt, &bb);
    let e3a = c.left_distrib(bm, t, bm);
    // e3 : ((T*T+T*b) + b*(T+b)) = ((T*T+T*b) + (b*T+b*b))  via congrArg ((T*T+T*b)+·).
    let f_tt_tb_add = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(c.nat.clone());
        let body = c.add(&tt_plus_tb, &x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    let e3 = c.congr_arg(&b_tb, &bt_plus_bb, f_tt_tb_add, e3a);
    let rhs3 = c.add(&tt_plus_tb, &bt_plus_bb);

    // Chain: sq =(e1)= rhs1 =(e2)= rhs2 =(e3)= rhs3.
    let chain12 = c.eq_trans(&sq, &rhs1, &rhs2, e1, e2);
    c.eq_trans(&sq, &rhs2, &rhs3, chain12, e3)
}
