// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// `include!`d by `boolean_analysis_flip_involution_proof.rs`. Holds the larger
// `build_hc_flip_involutive` term builder (the coordinate-wise `funext` proof of
// `hcFlip n (hcFlip n x i) i = x`), split out to keep each file under the
// 500-line convention. Shares the parent module's `FiConsts`, imports, and
// `EnvDeclBuilder` — no separate `use` block.

// ===========================================================================
// BoolAnalysis.hcFlip_involutive :
//   (n : Nat) (x : HCPoint n) (i : Fin n) → hcFlip n (hcFlip n x i) i = x
// ===========================================================================
fn build_hc_flip_involutive(c: &FiConsts) -> (Expr, Expr) {
    let hcflip = |n: Expr, x: Expr, i: Expr| Expr::apps(c.hc_flip.clone(), [n, x, i]);

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let hcp = c.hcpoint_of(n.clone());
        let (x_id, x) = b.fresh_local(hcp.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(n.clone()));
        let lhs = hcflip(
            n.clone(),
            hcflip(n.clone(), x.clone(), i.clone()),
            i.clone(),
        );
        let concl = c.eq_at(hcp.clone(), lhs, x.clone());
        let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(n.clone()), concl);
        let e = b.mk_pi(x_id, BinderInfo::Default, hcp, e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let hcp = c.hcpoint_of(n.clone());
        let (x_id, x) = b.fresh_local(hcp.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(n.clone()));

        let lhs = hcflip(
            n.clone(),
            hcflip(n.clone(), x.clone(), i.clone()),
            i.clone(),
        );

        // per-coordinate proof : fun (j : Fin n) => lhs j = x j
        // lhs j ≡ Bool.rec ((hcFlip x i) j) (not ((hcFlip x i) j)) gate
        //   where gate := Nat.beq (val j) (val i),
        //         (hcFlip x i) j ≡ Bool.rec (x j) (not (x j)) gate.
        // Remember-the-discriminant Bool.rec on `gate`:
        //   motive z := (gate = z) → (lhs j = x j)
        //   z=false: (hgate : gate=false). Then both Bool.rec collapse to the
        //            `false`/first branch: (hcFlip x i) j → x j (transport along hgate),
        //            and lhs j → (hcFlip x i) j → x j. Net: lhs j = x j.
        //   z=true:  (hgate : gate=true). lhs j → not ((hcFlip x i) j),
        //            (hcFlip x i) j → not (x j). So lhs j = not (not (x j)) = x j (not_not).
        let coord_pf = {
            let mut jb = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = jb.fresh_local(c.fin_of(n.clone()));

            let x_j = Expr::app(x.clone(), j.clone());
            let val_j = c.val(n.clone(), j.clone());
            let val_i = c.val(n.clone(), i.clone());
            let gate = Expr::apps(c.nat_beq.clone(), [val_j.clone(), val_i.clone()]);

            // inner f := hcFlip n x i  (the once-flipped point)
            let inner = hcflip(n.clone(), x.clone(), i.clone());
            let inner_j = Expr::app(inner.clone(), j.clone());
            // lhs_j := lhs j  (def-eq to Bool.rec inner_j (not inner_j) gate)
            let lhs_j = Expr::app(lhs.clone(), j.clone());

            let goal_j = c.eq_at(c.bool_ty.clone(), lhs_j.clone(), x_j.clone());

            // motive P : fun (z : Bool) => (gate = z) → (lhs j = x j)
            let motive_p = {
                let mut mb = EnvDeclBuilder::child_of(&jb);
                let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
                let hyp = c.eq_at(c.bool_ty.clone(), gate.clone(), z.clone());
                // Non-dependent arrow `(gate = z) → (lhs j = x j)`: the body does
                // not reference the hypothesis binder, so a bare `Expr::pi` is sound.
                let imp = Expr::pi(BinderInfo::Default, hyp, goal_j.clone());
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), imp))
            };

            // helper congrArg for `not`
            let congr_arg = Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            );
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );

            // ---- false branch: fun (hgate : gate = false) => lhs j = x j ----
            // With gate=false (transported), lhs_j ≡ inner_j and inner_j ≡ x j.
            // Build by rewriting gate to false in both Bool.recs is unnecessary:
            // instead use the discriminant equation hgate to specialize.
            // Concretely: define motive over the gate value to turn `lhs_j` into
            // `Bool.rec inner_j (not inner_j) gate`. With hgate : gate = false,
            // `Eq.subst` along hgate (motive w := lhs_j' ... ) — simpler: both
            // sides reduce once gate is the literal false, so prove:
            //   lhs_j = x_j  by transporting along hgate.
            // step_false_inner : inner_j = x_j  given gate=false.
            //   inner_j ≡ Bool.rec (x j)(not (x j)) gate. With hgate, rewrite gate→false:
            //   congrArg (fun w => Bool.rec (x j)(not (x j)) w) hgate : inner_j = Bool.rec (x j)(not(x j)) false
            //   and Bool.rec _ _ false ≡ x j (rfl). So Eq.trans gives inner_j = x j.
            // step_false_lhs : lhs_j = inner_j given gate=false (same shape, outer Bool.rec).
            let false_branch = {
                let mut fb = EnvDeclBuilder::child_of(&jb);
                let (hg_id, hg) =
                    fb.fresh_local(c.eq_at(c.bool_ty.clone(), gate.clone(), c.bfalse.clone()));

                // g_inner w := Bool.rec (fun _ => Bool) (x j) (not (x j)) w
                let g_inner = {
                    let mut gb = EnvDeclBuilder::child_of(&fb);
                    let (w_id, w) = gb.fresh_local(c.bool_ty.clone());
                    let motive_bb =
                        Expr::lam(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone());
                    let body = Expr::apps(
                        c.bool_rec1.clone(),
                        [motive_bb, x_j.clone(), c.not_(x_j.clone()), w],
                    );
                    gb.finish_child(gb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
                };
                // inner_at_false := Bool.rec (x j)(not (x j)) false  (≡ x j by rfl)
                let motive_bb =
                    Expr::lam(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone());
                let inner_at_false = Expr::apps(
                    c.bool_rec1.clone(),
                    [
                        motive_bb.clone(),
                        x_j.clone(),
                        c.not_(x_j.clone()),
                        c.bfalse.clone(),
                    ],
                );
                // c_inner : inner_j = inner_at_false  := congrArg g_inner hg
                let c_inner = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.bool_ty.clone(),
                        c.bool_ty.clone(),
                        gate.clone(),
                        c.bfalse.clone(),
                        g_inner.clone(),
                        hg.clone(),
                    ],
                );
                // inner_at_false = x_j by rfl
                let r_inner = c.refl_at(c.bool_ty.clone(), x_j.clone());
                // inner_eq_xj : inner_j = x_j
                let inner_eq_xj = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        inner_j.clone(),
                        inner_at_false.clone(),
                        x_j.clone(),
                        c_inner,
                        r_inner,
                    ],
                );

                // g_outer w := Bool.rec (fun _ => Bool) inner_j (not inner_j) w
                let g_outer = {
                    let mut gb = EnvDeclBuilder::child_of(&fb);
                    let (w_id, w) = gb.fresh_local(c.bool_ty.clone());
                    let body = Expr::apps(
                        c.bool_rec1.clone(),
                        [
                            motive_bb.clone(),
                            inner_j.clone(),
                            c.not_(inner_j.clone()),
                            w,
                        ],
                    );
                    gb.finish_child(gb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
                };
                let lhs_at_false = Expr::apps(
                    c.bool_rec1.clone(),
                    [
                        motive_bb,
                        inner_j.clone(),
                        c.not_(inner_j.clone()),
                        c.bfalse.clone(),
                    ],
                );
                // c_outer : lhs_j = lhs_at_false := congrArg g_outer hg
                let c_outer = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.bool_ty.clone(),
                        c.bool_ty.clone(),
                        gate.clone(),
                        c.bfalse.clone(),
                        g_outer,
                        hg.clone(),
                    ],
                );
                // lhs_at_false = inner_j by rfl
                let r_outer = c.refl_at(c.bool_ty.clone(), inner_j.clone());
                let lhs_eq_inner = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        lhs_j.clone(),
                        lhs_at_false.clone(),
                        inner_j.clone(),
                        c_outer,
                        r_outer,
                    ],
                );
                // out : lhs_j = x_j := Eq.trans lhs_eq_inner inner_eq_xj
                let out = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        lhs_j.clone(),
                        inner_j.clone(),
                        x_j.clone(),
                        lhs_eq_inner,
                        inner_eq_xj,
                    ],
                );
                fb.finish_child(fb.mk_lam(
                    hg_id,
                    BinderInfo::Default,
                    c.eq_at(c.bool_ty.clone(), gate.clone(), c.bfalse.clone()),
                    out,
                ))
            };

            // ---- true branch: fun (hgate : gate = true) => lhs j = x j ----
            // With gate=true: lhs_j ≡ not inner_j, inner_j ≡ not (x j).
            //   lhs_j = not inner_j        (congrArg g_outer hg ; Bool.rec _ _ true ≡ not inner_j)
            //   inner_j = not (x j)        (congrArg g_inner hg ; Bool.rec _ _ true ≡ not (x j))
            //   not inner_j = not (not (x j))   (congrArg not (inner_j = not (x j)))
            //   not (not (x j)) = x j      (Bool.not_not (x j))
            let true_branch = {
                let mut tb = EnvDeclBuilder::child_of(&jb);
                let (hg_id, hg) =
                    tb.fresh_local(c.eq_at(c.bool_ty.clone(), gate.clone(), c.btrue.clone()));
                let motive_bb =
                    Expr::lam(BinderInfo::Default, c.bool_ty.clone(), c.bool_ty.clone());

                // g_inner w := Bool.rec (x j) (not (x j)) w
                let g_inner = {
                    let mut gb = EnvDeclBuilder::child_of(&tb);
                    let (w_id, w) = gb.fresh_local(c.bool_ty.clone());
                    let body = Expr::apps(
                        c.bool_rec1.clone(),
                        [motive_bb.clone(), x_j.clone(), c.not_(x_j.clone()), w],
                    );
                    gb.finish_child(gb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
                };
                let inner_at_true = Expr::apps(
                    c.bool_rec1.clone(),
                    [
                        motive_bb.clone(),
                        x_j.clone(),
                        c.not_(x_j.clone()),
                        c.btrue.clone(),
                    ],
                );
                // c_inner : inner_j = inner_at_true := congrArg g_inner hg
                let c_inner = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.bool_ty.clone(),
                        c.bool_ty.clone(),
                        gate.clone(),
                        c.btrue.clone(),
                        g_inner,
                        hg.clone(),
                    ],
                );
                // inner_at_true = not (x j) by rfl
                let r_inner = c.refl_at(c.bool_ty.clone(), c.not_(x_j.clone()));
                // inner_eq_notxj : inner_j = not (x j)
                let inner_eq_notxj = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        inner_j.clone(),
                        inner_at_true.clone(),
                        c.not_(x_j.clone()),
                        c_inner,
                        r_inner,
                    ],
                );

                // g_outer w := Bool.rec inner_j (not inner_j) w
                let g_outer = {
                    let mut gb = EnvDeclBuilder::child_of(&tb);
                    let (w_id, w) = gb.fresh_local(c.bool_ty.clone());
                    let body = Expr::apps(
                        c.bool_rec1.clone(),
                        [
                            motive_bb.clone(),
                            inner_j.clone(),
                            c.not_(inner_j.clone()),
                            w,
                        ],
                    );
                    gb.finish_child(gb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
                };
                let lhs_at_true = Expr::apps(
                    c.bool_rec1.clone(),
                    [
                        motive_bb,
                        inner_j.clone(),
                        c.not_(inner_j.clone()),
                        c.btrue.clone(),
                    ],
                );
                let c_outer = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.bool_ty.clone(),
                        c.bool_ty.clone(),
                        gate.clone(),
                        c.btrue.clone(),
                        g_outer,
                        hg.clone(),
                    ],
                );
                // lhs_at_true = not inner_j by rfl
                let r_outer = c.refl_at(c.bool_ty.clone(), c.not_(inner_j.clone()));
                // lhs_eq_notinner : lhs_j = not inner_j
                let lhs_eq_notinner = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        lhs_j.clone(),
                        lhs_at_true.clone(),
                        c.not_(inner_j.clone()),
                        c_outer,
                        r_outer,
                    ],
                );

                // notinner_eq_notnotxj : not inner_j = not (not (x j))  (congrArg not inner_eq_notxj)
                let notinner_eq = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.bool_ty.clone(),
                        c.bool_ty.clone(),
                        inner_j.clone(),
                        c.not_(x_j.clone()),
                        c.bool_not.clone(),
                        inner_eq_notxj,
                    ],
                );
                // notnotxj_eq_xj : not (not (x j)) = x j  (Bool.not_not (x j))
                let notnot = Expr::apps(
                    Expr::const_(Name::from_string("Bool.not_not"), vec![]),
                    [x_j.clone()],
                );
                // chain: lhs_j = not inner_j = not (not (x j)) = x j
                let p1 = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        lhs_j.clone(),
                        c.not_(inner_j.clone()),
                        c.not_(c.not_(x_j.clone())),
                        lhs_eq_notinner,
                        notinner_eq,
                    ],
                );
                let out = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.bool_ty.clone(),
                        lhs_j.clone(),
                        c.not_(c.not_(x_j.clone())),
                        x_j.clone(),
                        p1,
                        notnot,
                    ],
                );
                let _ = (&eq_symm,);
                tb.finish_child(tb.mk_lam(
                    hg_id,
                    BinderInfo::Default,
                    c.eq_at(c.bool_ty.clone(), gate.clone(), c.btrue.clone()),
                    out,
                ))
            };

            // Bool.rec.{0} motive_p false_branch true_branch gate (refl gate) : lhs j = x j
            let rec = Expr::apps(
                c.bool_rec0.clone(),
                [motive_p, false_branch, true_branch, gate.clone()],
            );
            let refl_gate = c.refl_at(c.bool_ty.clone(), gate.clone());
            let applied = Expr::app(rec, refl_gate);

            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, c.fin_of(n.clone()), applied))
        };

        // funext : (lhs = x)  over HCPoint n = Fin n -> Bool
        // @funext.{1,1} (Fin n) (fun _ => Bool) lhs x coord_pf
        let bool_fam = Expr::lam(BinderInfo::Default, c.fin_of(n.clone()), c.bool_ty.clone());
        let out = Expr::apps(
            c.funext.clone(),
            [
                c.fin_of(n.clone()),
                bool_fam,
                lhs.clone(),
                x.clone(),
                coord_pf,
            ],
        );

        let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(n.clone()), out);
        let e = b.mk_lam(x_id, BinderInfo::Default, hcp, e);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };
    (type_, value)
}
