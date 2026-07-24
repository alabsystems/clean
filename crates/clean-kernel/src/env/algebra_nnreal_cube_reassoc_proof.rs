// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof bodies for `algebra_nnreal_cube_reassoc.rs` (`include!`d there).

// ── the pointwise equality-lift engine (the `three_cube` recipe, generalised) ──

/// Build `Equiv cau_l cau_r` from a POINTWISE `Rat` equality at every index.
///
/// `rat_l`/`rat_r` build the reduced `Rat` value of `val(seq cau_l n)` /
/// `val(seq cau_r n)` (defeq to them), and `atoms` the prover atom list, all
/// from the bound index local `m`. The two reduced values must be a `Rat`
/// polynomial identity in `atoms` (closed by `RatPolyProver`).
fn build_pointwise_equiv(
    c: &ReassocConsts,
    parent: &EnvDeclBuilder,
    cau_l: &Expr,
    cau_r: &Expr,
    rat_l: &dyn Fn(&ReassocConsts, &Expr) -> Expr,
    rat_r: &dyn Fn(&ReassocConsts, &Expr) -> Expr,
    atoms: &dyn Fn(&ReassocConsts, &Expr) -> Vec<Expr>,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(&c.rat_zero, &eps);
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let body_fn = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bn.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(&c.nat_zero, &m);
        let (hle_id, _hle) = bn.fresh_local(hle_ty.clone());

        let vl = rat_l(c, &m);
        let vr = rat_r(c, &m);
        let pr = RatPolyProver::new(atoms(c, &m));
        let eq_n = pr
            .prove_poly_eq(&bn, &vl, &vr)
            .expect("reassoc identity must be a Rat polynomial identity");

        // h_self : vR < vR + ε.
        let vr_eps = c.radd(&vr, &eps);
        let step = c.add_lt_add_left(&c.rat_zero, &eps, &vr, hpos.clone());
        let vr_zero = c.radd(&vr, &c.rat_zero);
        let motive_self = {
            let mut mb = EnvDeclBuilder::child_of(&bn);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(&t, &vr_eps);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_self = c.subst(motive_self, &vr_zero, &vr, c.add_zero(&vr), step);

        // left : vL < vR + ε  (subst vR→vL in `<` LHS along symm eq_n).
        let left = {
            let motive_l = {
                let mut mb = EnvDeclBuilder::child_of(&bn);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.rlt(&t, &vr_eps);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            c.subst(
                motive_l,
                &vr,
                &vl,
                c.eq_symm(&vl, &vr, eq_n.clone()),
                h_self.clone(),
            )
        };
        // right : vR < vL + ε  (subst vR→vL in the `+ε` base along symm eq_n).
        let right = {
            let motive_r = {
                let mut mb = EnvDeclBuilder::child_of(&bn);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.rlt(&vr, &c.radd(&t, &eps));
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            c.subst(motive_r, &vr, &vl, c.eq_symm(&vl, &vr, eq_n), h_self)
        };

        let conj_left = c.rlt(&vl, &vr_eps);
        let conj_right = c.rlt(&vr, &c.radd(&vl, &eps));
        let proof = c.and_intro(&conj_left, &conj_right, left, right);

        let e = bn.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        bn.finish_child(bn.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let pred = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bm = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bm.fresh_local(c.nat.clone());
            let hle = c.nat_le(&cap, &m);
            let (hle_id, _h) = bm.fresh_local(hle.clone());
            let concl = c.bound_pair(&c.vseq(cau_l, &m), &c.vseq(cau_r, &m), &eps);
            let e = bm.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            bm.finish_child(bm.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
        };
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
    };
    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, c.nat_zero.clone(), body_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

// `(((a·a)·b)·((a·a)·b))·((a·a)·b)`-style cube of a CauSeq monomial. Generic
// over a unary "build the base from a slice of reps" closure is unnecessary
// here; callers pass explicit shapes.
//
// ── I_B : ((a·a)·b)³ = (a³·a³)·b³  (2 carrier variables) ──

impl Environment {
    pub(super) fn register_reassoc_lhs(&mut self, c: &ReassocConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_reassoc_lhs");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // shapes (NNReal): a²b := (a·a)·b ; cube z := (z·z)·z ; a³ := (a·a)·a.
        let nn_sq_t = |a: &Expr, bb: &Expr| c.nn_mul(&c.nn_mul(a, a), bb);
        let nn_cube = |z: &Expr| c.nn_mul(&c.nn_mul(z, z), z);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (b2_id, b2) = b.fresh_local(c.nnreal.clone());
            let lhs = nn_cube(&nn_sq_t(&a, &b2)); // ((a·a)·b)³
            let a3 = nn_cube(&a);
            let b3 = nn_cube(&b2);
            let rhs = c.nn_mul(&c.nn_mul(&a3, &a3), &b3); // (a³·a³)·b³
            let concl = c.eq_nnreal(&lhs, &rhs);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_reassoc_lhs_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    pub(super) fn register_reassoc_rhs(&mut self, c: &ReassocConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_reassoc_rhs");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
            let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
            let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
            let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
            let (lhs, rhs) = reassoc_rhs_shapes_nn(c, &s1, &s2, &t1, &t2);
            let concl = c.eq_nnreal(&lhs, &rhs);
            let e = b.mk_pi(t2_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_reassoc_rhs_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    pub(super) fn register_reassoc_lhs_b(&mut self, c: &ReassocConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_reassoc_lhs_b");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // ((a·b)·b)³ = (b³·b³)·a³   (the U₁U₂² split-B shape).
        let nn_cube = |z: &Expr| c.nn_mul(&c.nn_mul(z, z), z);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (b2_id, b2) = b.fresh_local(c.nnreal.clone());
            let abb = c.nn_mul(&c.nn_mul(&a, &b2), &b2); // (a·b)·b
            let lhs = nn_cube(&abb);
            let a3 = nn_cube(&a);
            let b3 = nn_cube(&b2);
            let rhs = c.nn_mul(&c.nn_mul(&b3, &b3), &a3); // (b³·b³)·a³
            let concl = c.eq_nnreal(&lhs, &rhs);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_reassoc_lhs_b_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    pub(super) fn register_reassoc_rhs_b(&mut self, c: &ReassocConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_reassoc_rhs_b");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
            let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
            let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
            let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
            let (lhs, rhs) = reassoc_rhs_b_shapes_nn(c, &s1, &s2, &t1, &t2);
            let concl = c.eq_nnreal(&lhs, &rhs);
            let e = b.mk_pi(t2_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_reassoc_rhs_b_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    pub(super) fn register_add27_mono(&mut self, c: &ReassocConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add27_mono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let h_ty = c.nn_le(&a, &bv);
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let concl = c.nn_le(&c.nn_add_n(&a, AMGM_COEFF), &c.nn_add_n(&bv, AMGM_COEFF));
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_add27_mono_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// NNReal shapes for I_C: `lhs = ((s1²t1)·(s1²t1))·(s2²t2)`,
/// `rhs = ((s1s2t1)·(s1s2t1))·(s1²t2)`.
fn reassoc_rhs_shapes_nn(
    c: &ReassocConsts,
    s1: &Expr,
    s2: &Expr,
    t1: &Expr,
    t2: &Expr,
) -> (Expr, Expr) {
    let sq_t = |s: &Expr, t: &Expr| c.nn_mul(&c.nn_mul(s, s), t); // (s·s)·t
    let prod3 = |a: &Expr, b: &Expr, cc: &Expr| c.nn_mul(&c.nn_mul(a, b), cc); // (a·b)·c
    let s1sq_t1 = sq_t(s1, t1); // S₁²T₁
    let s2sq_t2 = sq_t(s2, t2); // S₂²T₂
    let lhs = c.nn_mul(&c.nn_mul(&s1sq_t1, &s1sq_t1), &s2sq_t2); // (S₁²T₁)²·S₂²T₂
    let p = prod3(s1, s2, t1); // S₁S₂T₁
    let q = sq_t(s1, t2); // S₁²T₂
    let rhs = c.nn_mul(&c.nn_mul(&p, &p), &q); // (P·P)·Q
    (lhs, rhs)
}

/// NNReal shapes for I_C-B: `lhs = ((s2²t2)·(s2²t2))·(s1²t1)`,
/// `rhs = ((s1s2t2)·(s1s2t2))·(s2²t1)`.
fn reassoc_rhs_b_shapes_nn(
    c: &ReassocConsts,
    s1: &Expr,
    s2: &Expr,
    t1: &Expr,
    t2: &Expr,
) -> (Expr, Expr) {
    let sq_t = |s: &Expr, t: &Expr| c.nn_mul(&c.nn_mul(s, s), t);
    let prod3 = |a: &Expr, b: &Expr, cc: &Expr| c.nn_mul(&c.nn_mul(a, b), cc);
    let s2sq_t2 = sq_t(s2, t2); // S₂²T₂
    let s1sq_t1 = sq_t(s1, t1); // S₁²T₁
    let lhs = c.nn_mul(&c.nn_mul(&s2sq_t2, &s2sq_t2), &s1sq_t1); // (S₂²T₂)²·S₁²T₁
    let pp = prod3(s1, s2, t2); // S₁S₂T₂  (P')
    let qp = sq_t(s2, t1); // S₂²T₁  (Q')
    let rhs = c.nn_mul(&c.nn_mul(&pp, &pp), &qp); // (P'·P')·Q'
    (lhs, rhs)
}

/// `NNReal.cube_reassoc_lhs_b` value: `((a·b)·b)³ = (b³·b³)·a³` (Quot.ind² lift).
fn build_reassoc_lhs_b_value(c: &ReassocConsts) -> Expr {
    let goal_at = |vs: &[Expr]| {
        let (a, bb) = (&vs[0], &vs[1]);
        let nn_cube = |z: &Expr| c.nn_mul(&c.nn_mul(z, z), z);
        let abb = c.nn_mul(&c.nn_mul(a, bb), bb);
        let lhs = nn_cube(&abb);
        let a3 = nn_cube(a);
        let b3 = nn_cube(bb);
        let rhs = c.nn_mul(&c.nn_mul(&b3, &b3), &a3);
        c.eq_nnreal(&lhs, &rhs)
    };
    let leaf = move |c: &ReassocConsts, parent: &EnvDeclBuilder, reps: &[Expr]| -> Expr {
        let fa = reps[0].clone();
        let fb = reps[1].clone();
        let cau_abb = c.cau_mul(&c.cau_mul(&fa, &fb), &fb);
        let cau_l = c.cau_mul(&c.cau_mul(&cau_abb, &cau_abb), &cau_abb);
        let cau_a3 = c.cau_mul(&c.cau_mul(&fa, &fa), &fa);
        let cau_b3 = c.cau_mul(&c.cau_mul(&fb, &fb), &fb);
        let cau_r = c.cau_mul(&c.cau_mul(&cau_b3, &cau_b3), &cau_a3);
        let r = [fa, fb];
        let rat_l = {
            let r = r.clone();
            move |c: &ReassocConsts, m: &Expr| {
                let va = c.vseq(&r[0], m);
                let vb = c.vseq(&r[1], m);
                let abb = c.rmul(&c.rmul(&va, &vb), &vb);
                c.rmul(&c.rmul(&abb, &abb), &abb)
            }
        };
        let rat_r = {
            let r = r.clone();
            move |c: &ReassocConsts, m: &Expr| {
                let va = c.vseq(&r[0], m);
                let vb = c.vseq(&r[1], m);
                let a3 = c.rmul(&c.rmul(&va, &va), &va);
                let b3 = c.rmul(&c.rmul(&vb, &vb), &vb);
                c.rmul(&c.rmul(&b3, &b3), &a3)
            }
        };
        let atoms = {
            let r = r.clone();
            move |c: &ReassocConsts, m: &Expr| vec![c.vseq(&r[0], m), c.vseq(&r[1], m)]
        };
        let equiv = build_pointwise_equiv(c, parent, &cau_l, &cau_r, &rat_l, &rat_r, &atoms);
        c.quot_sound(&cau_l, &cau_r, equiv)
    };
    build_quot_ind_eq(c, 2, &goal_at, &leaf)
}

/// `NNReal.cube_reassoc_rhs_b` value: `Quot.ind`⁴ + `Quot.sound`.
fn build_reassoc_rhs_b_value(c: &ReassocConsts) -> Expr {
    let goal_at = |vs: &[Expr]| {
        let (lhs, rhs) = reassoc_rhs_b_shapes_nn(c, &vs[0], &vs[1], &vs[2], &vs[3]);
        c.eq_nnreal(&lhs, &rhs)
    };
    let leaf = move |c: &ReassocConsts, parent: &EnvDeclBuilder, reps: &[Expr]| -> Expr {
        let cau_sq_t = |s: &Expr, t: &Expr| c.cau_mul(&c.cau_mul(s, s), t);
        let cau_prod3 = |a: &Expr, b: &Expr, cc: &Expr| c.cau_mul(&c.cau_mul(a, b), cc);
        let (s1, s2, t1, t2) = (&reps[0], &reps[1], &reps[2], &reps[3]);
        let s2sq_t2 = cau_sq_t(s2, t2);
        let s1sq_t1 = cau_sq_t(s1, t1);
        let cau_l = c.cau_mul(&c.cau_mul(&s2sq_t2, &s2sq_t2), &s1sq_t1);
        let pp = cau_prod3(s1, s2, t2);
        let qp = cau_sq_t(s2, t1);
        let cau_r = c.cau_mul(&c.cau_mul(&pp, &pp), &qp);

        let r = reps.to_vec();
        let rat_l = move |c: &ReassocConsts, m: &Expr| {
            let v: Vec<Expr> = r.iter().map(|x| c.vseq(x, m)).collect();
            let sq_t = |s: &Expr, t: &Expr| c.rmul(&c.rmul(s, s), t);
            let s2sq_t2 = sq_t(&v[1], &v[3]);
            let s1sq_t1 = sq_t(&v[0], &v[2]);
            c.rmul(&c.rmul(&s2sq_t2, &s2sq_t2), &s1sq_t1)
        };
        let r2 = reps.to_vec();
        let rat_r = move |c: &ReassocConsts, m: &Expr| {
            let v: Vec<Expr> = r2.iter().map(|x| c.vseq(x, m)).collect();
            let sq_t = |s: &Expr, t: &Expr| c.rmul(&c.rmul(s, s), t);
            let prod3 = |a: &Expr, b: &Expr, cc: &Expr| c.rmul(&c.rmul(a, b), cc);
            let pp = prod3(&v[0], &v[1], &v[3]);
            let qp = sq_t(&v[1], &v[2]);
            c.rmul(&c.rmul(&pp, &pp), &qp)
        };
        let r3 = reps.to_vec();
        let atoms = move |c: &ReassocConsts, m: &Expr| r3.iter().map(|x| c.vseq(x, m)).collect();
        let equiv = build_pointwise_equiv(c, parent, &cau_l, &cau_r, &rat_l, &rat_r, &atoms);
        c.quot_sound(&cau_l, &cau_r, equiv)
    };
    build_quot_ind_eq(c, 4, &goal_at, &leaf)
}

/// `NNReal.cube_reassoc_lhs` value: `Quot.ind`² + `Quot.sound`.
fn build_reassoc_lhs_value(c: &ReassocConsts) -> Expr {
    let goal_at = |vs: &[Expr]| {
        let (a, bb) = (&vs[0], &vs[1]);
        let nn_cube = |z: &Expr| c.nn_mul(&c.nn_mul(z, z), z);
        let nn_sq_t = c.nn_mul(&c.nn_mul(a, a), bb);
        let lhs = nn_cube(&nn_sq_t);
        let a3 = nn_cube(a);
        let b3 = nn_cube(bb);
        let rhs = c.nn_mul(&c.nn_mul(&a3, &a3), &b3);
        c.eq_nnreal(&lhs, &rhs)
    };
    // CauSeq leaf shapes + reduced Rat forms at index m.
    let leaf = move |c: &ReassocConsts, parent: &EnvDeclBuilder, reps: &[Expr]| -> Expr {
        let fa = reps[0].clone();
        let fb = reps[1].clone();
        let cau_sq_t = c.cau_mul(&c.cau_mul(&fa, &fa), &fb);
        let cau_l = c.cau_mul(&c.cau_mul(&cau_sq_t, &cau_sq_t), &cau_sq_t);
        let cau_a3 = c.cau_mul(&c.cau_mul(&fa, &fa), &fa);
        let cau_b3 = c.cau_mul(&c.cau_mul(&fb, &fb), &fb);
        let cau_r = c.cau_mul(&c.cau_mul(&cau_a3, &cau_a3), &cau_b3);
        let r = [fa, fb];
        let rat_l = {
            let r = r.clone();
            move |c: &ReassocConsts, m: &Expr| {
                let va = c.vseq(&r[0], m);
                let vb = c.vseq(&r[1], m);
                let sq_t = c.rmul(&c.rmul(&va, &va), &vb);
                c.rmul(&c.rmul(&sq_t, &sq_t), &sq_t)
            }
        };
        let rat_r = {
            let r = r.clone();
            move |c: &ReassocConsts, m: &Expr| {
                let va = c.vseq(&r[0], m);
                let vb = c.vseq(&r[1], m);
                let a3 = c.rmul(&c.rmul(&va, &va), &va);
                let b3 = c.rmul(&c.rmul(&vb, &vb), &vb);
                c.rmul(&c.rmul(&a3, &a3), &b3)
            }
        };
        let atoms = {
            let r = r.clone();
            move |c: &ReassocConsts, m: &Expr| vec![c.vseq(&r[0], m), c.vseq(&r[1], m)]
        };
        let equiv = build_pointwise_equiv(c, parent, &cau_l, &cau_r, &rat_l, &rat_r, &atoms);
        c.quot_sound(&cau_l, &cau_r, equiv)
    };
    build_quot_ind_eq(c, 2, &goal_at, &leaf)
}

/// `NNReal.cube_reassoc_rhs` value: `Quot.ind`⁴ + `Quot.sound`.
fn build_reassoc_rhs_value(c: &ReassocConsts) -> Expr {
    let goal_at = |vs: &[Expr]| {
        let (lhs, rhs) = reassoc_rhs_shapes_nn(c, &vs[0], &vs[1], &vs[2], &vs[3]);
        c.eq_nnreal(&lhs, &rhs)
    };
    let leaf = move |c: &ReassocConsts, parent: &EnvDeclBuilder, reps: &[Expr]| -> Expr {
        // CauSeq shapes mirroring reassoc_rhs_shapes_nn.
        let cau_sq_t = |s: &Expr, t: &Expr| c.cau_mul(&c.cau_mul(s, s), t);
        let cau_prod3 = |a: &Expr, b: &Expr, cc: &Expr| c.cau_mul(&c.cau_mul(a, b), cc);
        let (s1, s2, t1, t2) = (&reps[0], &reps[1], &reps[2], &reps[3]);
        let s1sq_t1 = cau_sq_t(s1, t1);
        let s2sq_t2 = cau_sq_t(s2, t2);
        let cau_l = c.cau_mul(&c.cau_mul(&s1sq_t1, &s1sq_t1), &s2sq_t2);
        let p = cau_prod3(s1, s2, t1);
        let q = cau_sq_t(s1, t2);
        let cau_r = c.cau_mul(&c.cau_mul(&p, &p), &q);

        let r = reps.to_vec();
        let rat_l = move |c: &ReassocConsts, m: &Expr| {
            let v: Vec<Expr> = r.iter().map(|x| c.vseq(x, m)).collect();
            let sq_t = |s: &Expr, t: &Expr| c.rmul(&c.rmul(s, s), t);
            let s1sq_t1 = sq_t(&v[0], &v[2]);
            let s2sq_t2 = sq_t(&v[1], &v[3]);
            c.rmul(&c.rmul(&s1sq_t1, &s1sq_t1), &s2sq_t2)
        };
        let r2 = reps.to_vec();
        let rat_r = move |c: &ReassocConsts, m: &Expr| {
            let v: Vec<Expr> = r2.iter().map(|x| c.vseq(x, m)).collect();
            let sq_t = |s: &Expr, t: &Expr| c.rmul(&c.rmul(s, s), t);
            let prod3 = |a: &Expr, b: &Expr, cc: &Expr| c.rmul(&c.rmul(a, b), cc);
            let p = prod3(&v[0], &v[1], &v[2]);
            let q = sq_t(&v[0], &v[3]);
            c.rmul(&c.rmul(&p, &p), &q)
        };
        let r3 = reps.to_vec();
        let atoms = move |c: &ReassocConsts, m: &Expr| r3.iter().map(|x| c.vseq(x, m)).collect();
        let equiv = build_pointwise_equiv(c, parent, &cau_l, &cau_r, &rat_l, &rat_r, &atoms);
        c.quot_sound(&cau_l, &cau_r, equiv)
    };
    build_quot_ind_eq(c, 4, &goal_at, &leaf)
}

/// Generic `Quot.ind`ⁿ over `n` `NNReal` variables, closing each fully-applied
/// leaf with `leaf(raw_reps)`. `goal_at(args)` is the `Prop` goal as a function
/// of the `n` carrier arguments (used to build each level's motive); the args it
/// receives are `Quot.mk rep` for the already-introduced levels and the still-
/// abstract outer `NNReal` locals for the rest.
fn build_quot_ind_eq(
    c: &ReassocConsts,
    n: usize,
    goal_at: &dyn Fn(&[Expr]) -> Expr,
    leaf: &dyn Fn(&ReassocConsts, &EnvDeclBuilder, &[Expr]) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let vars: Vec<_> = (0..n).map(|_| b.fresh_local(c.nnreal.clone())).collect();
    let var_exprs: Vec<Expr> = vars.iter().map(|(_, e)| e.clone()).collect();
    let ind = build_ind_level(c, &b, n, &var_exprs, &[], &[], goal_at, leaf);
    let mut e = ind;
    for (id, _) in vars.iter().rev() {
        e = b.mk_lam(*id, BinderInfo::Default, c.nnreal.clone(), e);
    }
    b.finish(e)
}

/// Recursive `Quot.ind` builder threading BOTH the `mk f` values (`fixed_mks`,
/// for the motive/goal) and the raw `f` reps (`fixed_raw`, for the leaf). The
/// current level is `level = fixed_mks.len()`.
#[allow(clippy::too_many_arguments)]
fn build_ind_level(
    c: &ReassocConsts,
    parent: &EnvDeclBuilder,
    n: usize,
    outer_vars: &[Expr],
    fixed_mks: &[Expr],
    fixed_raw: &[Expr],
    goal_at: &dyn Fn(&[Expr]) -> Expr,
    leaf: &dyn Fn(&ReassocConsts, &EnvDeclBuilder, &[Expr]) -> Expr,
) -> Expr {
    let level = fixed_mks.len();
    if level == n {
        return leaf(c, parent, fixed_raw);
    }
    // motive over the current variable `x`: M x := goal_at(mks ++ [x] ++ rest).
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(c.nnreal.clone());
        let mut args: Vec<Expr> = fixed_mks.to_vec();
        args.push(x.clone());
        args.extend_from_slice(&outer_vars[level + 1..]);
        let body = goal_at(&args);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mk_f = Expr::apps(
            Expr::const_(
                Name::from_string("Quot.mk"),
                vec![Level::succ(Level::zero())],
            ),
            [c.causeq.clone(), c.causeq_equiv.clone(), f.clone()],
        );
        let mut next_mks = fixed_mks.to_vec();
        next_mks.push(mk_f);
        let mut next_raw = fixed_raw.to_vec();
        next_raw.push(f.clone());
        let inner = build_ind_level(c, &mf, n, outer_vars, &next_mks, &next_raw, goal_at, leaf);
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), inner))
    };
    Expr::apps(
        c.quot_ind().clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            outer_vars[level].clone(),
        ],
    )
}

/// `NNReal.add27_mono` value: 26 left-nested `NNReal.add_le_add`s.
fn build_add27_mono_value(c: &ReassocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nnreal.clone());
    let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
    let h_ty = c.nn_le(&a, &bv);
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // acc_a/acc_b track the running left-nested sums; acc_proof : acc_a ≤ acc_b.
    let mut acc_a = a.clone();
    let mut acc_b = bv.clone();
    let mut acc_proof = h.clone();
    for _ in 1..AMGM_COEFF {
        // add_le_add acc_a acc_b a bv acc_proof h : (acc_a + a) ≤ (acc_b + bv).
        acc_proof = c.nn_add_le_add(&acc_a, &acc_b, &a, &bv, acc_proof, h.clone());
        acc_a = c.nn_add(&acc_a, &a);
        acc_b = c.nn_add(&acc_b, &bv);
    }
    let _ = (acc_a, acc_b);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, acc_proof);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}
