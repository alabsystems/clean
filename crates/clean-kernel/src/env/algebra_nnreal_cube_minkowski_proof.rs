// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof bodies for `algebra_nnreal_cube_minkowski.rs` (`include!`d there).

impl Environment {
    fn register_cube_split_a(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_split_A");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_split(c, SplitSide::A);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_cube_split_b(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_split_B");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_split(c, SplitSide::B);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_cube_minkowski(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_minkowski");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_cube_minkowski(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[derive(Clone, Copy)]
enum SplitSide {
    A,
    B,
}

/// The common `∀ U₁ S₁ T₁ U₂ S₂ T₂` + `h1 h2` binder frame; `body` builds the
/// conclusion proof given the six vars and the two cube hyps.
fn split_frame(
    c: &MinkowskiConsts,
    concl_of: &dyn Fn(&Expr, &Expr, &Expr, &Expr, &Expr, &Expr) -> Expr,
    body_of: &dyn Fn(&EnvDeclBuilder, &Expr, &Expr, &Expr, &Expr, &Expr, &Expr, Expr, Expr) -> Expr,
) -> (Expr, Expr) {
    let h1_ty = |u1: &Expr, s1: &Expr, t1: &Expr| c.nnle(&c.cube(u1), &c.sq_t(s1, t1));
    let h2_ty = |u2: &Expr, s2: &Expr, t2: &Expr| c.nnle(&c.cube(u2), &c.sq_t(s2, t2));

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
        let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
        let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
        let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
        let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
        let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
        let h1t = h1_ty(&u1, &s1, &t1);
        let (h1_id, _) = b.fresh_local(h1t.clone());
        let h2t = h2_ty(&u2, &s2, &t2);
        let (h2_id, _) = b.fresh_local(h2t.clone());
        let concl = concl_of(&u1, &s1, &t1, &u2, &s2, &t2);
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2t, concl);
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1t, e);
        let e = b.mk_pi(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
        let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
        let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
        let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
        let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
        let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
        let h1t = h1_ty(&u1, &s1, &t1);
        let (h1_id, h1) = b.fresh_local(h1t.clone());
        let h2t = h2_ty(&u2, &s2, &t2);
        let (h2_id, h2) = b.fresh_local(h2t.clone());
        let proof = body_of(&b, &u1, &s1, &t1, &u2, &s2, &t2, h1, h2);
        let e = b.mk_lam(h2_id, BinderInfo::Default, h2t, proof);
        let e = b.mk_lam(h1_id, BinderInfo::Default, h1t, e);
        let e = b.mk_lam(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

/// `cube_split_A` / `cube_split_B` builder (the cubed chain + de-cube).
fn build_split(c: &MinkowskiConsts, side: SplitSide) -> (Expr, Expr) {
    // monomial roles per side.
    //   A: lhs_base = (U₁·U₁)·U₂ ;  P=S₁S₂T₁, Q=S₁²T₂.
    //   B: lhs_base = (U₁·U₂)·U₂ ;  P'=S₁S₂T₂, Q'=S₂²T₁.
    let lhs_base = move |c: &MinkowskiConsts, u1: &Expr, u2: &Expr| match side {
        SplitSide::A => c.mul(&c.mul(u1, u1), u2), // (U₁·U₁)·U₂
        SplitSide::B => c.mul(&c.mul(u1, u2), u2), // (U₁·U₂)·U₂
    };
    let p_q = move |c: &MinkowskiConsts, s1: &Expr, s2: &Expr, t1: &Expr, t2: &Expr| match side {
        SplitSide::A => (c.prod3(s1, s2, t1), c.sq_t(s1, t2)), // (P, Q)
        SplitSide::B => (c.prod3(s1, s2, t2), c.sq_t(s2, t1)), // (P', Q')
    };

    let concl_of = move |u1: &Expr, s1: &Expr, t1: &Expr, u2: &Expr, s2: &Expr, t2: &Expr| {
        let lb = lhs_base(c, u1, u2);
        let (p, q) = p_q(c, s1, s2, t1, t2);
        c.nnle(&c.three(&lb), &c.two_plus(&p, &q))
    };

    let body_of = move |b: &EnvDeclBuilder,
                        u1: &Expr,
                        s1: &Expr,
                        t1: &Expr,
                        u2: &Expr,
                        s2: &Expr,
                        t2: &Expr,
                        h1: Expr,
                        h2: Expr| {
        let lb = lhs_base(c, u1, u2); // U₁²U₂ / U₁U₂²
        let (p, q) = p_q(c, s1, s2, t1, t2);
        let ppq = c.mul(&c.mul(&p, &p), &q); // (P·P)·Q
        let two_plus = c.two_plus(&p, &q);

        // h_amgm : add27((P·P)·Q) ≤ (2P+Q)³.
        let h_amgm = Expr::apps(c.cubed_amgm.clone(), [p.clone(), q.clone()]);
        let add27_ppq = c.add_n(&ppq, AMGM_COEFF);
        let cube_two_plus = c.cube(&two_plus);

        // holder3 corner value `(U₁³·U₁³)·U₂³` (A) / `(U₂³·U₂³)·U₁³` (B) and bound.
        let (hol_val, hol_bound, holder) = match side {
            SplitSide::A => {
                let v = c.mul(&c.mul(&c.cube(u1), &c.cube(u1)), &c.cube(u2));
                let bd = c.mul(&c.mul(&c.sq_t(s1, t1), &c.sq_t(s1, t1)), &c.sq_t(s2, t2));
                let h = Expr::apps(
                    c.holder3_cross_mono.clone(),
                    [
                        u1.clone(),
                        s1.clone(),
                        t1.clone(),
                        u2.clone(),
                        s2.clone(),
                        t2.clone(),
                        h1,
                        h2,
                    ],
                );
                (v, bd, h)
            }
            SplitSide::B => {
                let v = c.mul(&c.mul(&c.cube(u2), &c.cube(u2)), &c.cube(u1));
                let bd = c.mul(&c.mul(&c.sq_t(s2, t2), &c.sq_t(s2, t2)), &c.sq_t(s1, t1));
                let h = Expr::apps(
                    c.holder3_cross_mono.clone(),
                    [
                        u2.clone(),
                        s2.clone(),
                        t2.clone(),
                        u1.clone(),
                        s1.clone(),
                        t1.clone(),
                        h2,
                        h1,
                    ],
                );
                (v, bd, h)
            }
        };

        // add27_mono holder : add27(hol_val) ≤ add27(hol_bound).
        let h_mono = Expr::apps(
            c.add27_mono.clone(),
            [hol_val.clone(), hol_bound.clone(), holder],
        );
        let add27_hol_val = c.add_n(&hol_val, AMGM_COEFF);
        let add27_hol_bound = c.add_n(&hol_bound, AMGM_COEFF);

        // e_rhs : hol_bound = (P·P)·Q   (reassoc_rhs / _b).
        let e_rhs = match side {
            SplitSide::A => Expr::apps(
                c.reassoc_rhs.clone(),
                [s1.clone(), s2.clone(), t1.clone(), t2.clone()],
            ),
            SplitSide::B => Expr::apps(
                c.reassoc_rhs_b.clone(),
                [s1.clone(), s2.clone(), t1.clone(), t2.clone()],
            ),
        };
        // congr add27 e_rhs : add27(hol_bound) = add27((P·P)·Q).
        let e_rhs27 = c.congr_add27(b, &hol_bound, &ppq, e_rhs);
        // transport h_mono's RHS  add27(hol_bound) → add27(PPQ).
        let h_mono_ppq = c.subst(
            c.motive_le_right(b, &add27_hol_val),
            &add27_hol_bound,
            &add27_ppq,
            e_rhs27,
            h_mono,
        ); // add27(hol_val) ≤ add27(PPQ)

        // step_le : add27(hol_val) ≤ (2P+Q)³.
        let step_le = c.le_trans(
            &add27_hol_val,
            &add27_ppq,
            &cube_two_plus,
            h_mono_ppq,
            h_amgm,
        );

        // e_lhs_full : cube(three lb) = add27(hol_val).
        //   three_cube lb : cube(three lb) = add27(cube lb).
        //   reassoc(_b) :    cube lb = hol_val.  ⇒ congr add27 ⇒ add27(cube lb)=add27(hol_val).
        let cube_lb = c.cube(&lb);
        let three_lb = c.three(&lb);
        let cube_three_lb = c.cube(&three_lb);
        let add27_cube_lb = c.add_n(&cube_lb, AMGM_COEFF);
        let e_three = Expr::apps(c.three_cube.clone(), [lb.clone()]); // cube(three lb)=add27(cube lb)
        let e_lhs = match side {
            SplitSide::A => Expr::apps(c.reassoc_lhs.clone(), [u1.clone(), u2.clone()]),
            SplitSide::B => Expr::apps(c.reassoc_lhs_b.clone(), [u1.clone(), u2.clone()]),
        }; // cube lb = hol_val
        let e_lhs27 = c.congr_add27(b, &cube_lb, &hol_val, e_lhs); // add27(cube lb)=add27(hol_val)
        let e_lhs_full = eq_trans_nn(
            c,
            &cube_three_lb,
            &add27_cube_lb,
            &add27_hol_val,
            e_three,
            e_lhs27,
        );

        // transport step_le's LHS  add27(hol_val) → cube(three lb)  along symm e_lhs_full.
        let h_cube = c.subst(
            c.motive_le_left(b, &cube_two_plus),
            &add27_hol_val,
            &cube_three_lb,
            c.symm(&cube_three_lb, &add27_hol_val, e_lhs_full),
            step_le,
        ); // cube(three lb) ≤ cube(two_plus)

        // de-cube : three lb ≤ two_plus.
        c.le_of_cube(&three_lb, &two_plus, h_cube)
    };

    split_frame(c, &concl_of, &body_of)
}

/// `@Eq.trans NNReal a b c h1 h2`.
fn eq_trans_nn(c: &MinkowskiConsts, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
    let trans = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(
        trans,
        [c.nnreal.clone(), a.clone(), b.clone(), cc.clone(), h1, h2],
    )
}

/// `NNReal.cube_minkowski` — instantiate the MERGE with the two derived splits.
fn build_cube_minkowski(c: &MinkowskiConsts) -> (Expr, Expr) {
    let split_a = Expr::const_(Name::from_string("NNReal.cube_split_A"), vec![]);
    let split_b = Expr::const_(Name::from_string("NNReal.cube_split_B"), vec![]);

    let h1_ty = |u1: &Expr, s1: &Expr, t1: &Expr| c.nnle(&c.cube(u1), &c.sq_t(s1, t1));
    let h2_ty = |u2: &Expr, s2: &Expr, t2: &Expr| c.nnle(&c.cube(u2), &c.sq_t(s2, t2));
    let concl_of = |u1: &Expr, u2: &Expr, s1: &Expr, s2: &Expr, t1: &Expr, t2: &Expr| {
        let us = c.add(u1, u2);
        let ss = c.add(s1, s2);
        let tt = c.add(t1, t2);
        c.nnle(&c.cube(&us), &c.mul(&c.mul(&ss, &ss), &tt))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
        let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
        let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
        let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
        let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
        let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
        let h1t = h1_ty(&u1, &s1, &t1);
        let (h1_id, _) = b.fresh_local(h1t.clone());
        let h2t = h2_ty(&u2, &s2, &t2);
        let (h2_id, _) = b.fresh_local(h2t.clone());
        let concl = concl_of(&u1, &u2, &s1, &s2, &t1, &t2);
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2t, concl);
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1t, e);
        let e = b.mk_pi(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
        let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
        let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
        let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
        let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
        let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
        let h1t = h1_ty(&u1, &s1, &t1);
        let (h1_id, h1) = b.fresh_local(h1t.clone());
        let h2t = h2_ty(&u2, &s2, &t2);
        let (h2_id, h2) = b.fresh_local(h2t.clone());

        // h_splitA := cube_split_A u1 s1 t1 u2 s2 t2 h1 h2.
        let ha = Expr::apps(
            split_a.clone(),
            [
                u1.clone(),
                s1.clone(),
                t1.clone(),
                u2.clone(),
                s2.clone(),
                t2.clone(),
                h1.clone(),
                h2.clone(),
            ],
        );
        let hb = Expr::apps(
            split_b.clone(),
            [
                u1.clone(),
                s1.clone(),
                t1.clone(),
                u2.clone(),
                s2.clone(),
                t2.clone(),
                h1.clone(),
                h2.clone(),
            ],
        );
        // merge u1 s1 t1 u2 s2 t2 h1 h2 ha hb.
        let proof = Expr::apps(
            c.merge.clone(),
            [
                u1.clone(),
                s1.clone(),
                t1.clone(),
                u2.clone(),
                s2.clone(),
                t2.clone(),
                h1,
                h2,
                ha,
                hb,
            ],
        );

        let e = b.mk_lam(h2_id, BinderInfo::Default, h2t, proof);
        let e = b.mk_lam(h1_id, BinderInfo::Default, h1t, e);
        let e = b.mk_lam(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(e)
    };
    (ty, value)
}
