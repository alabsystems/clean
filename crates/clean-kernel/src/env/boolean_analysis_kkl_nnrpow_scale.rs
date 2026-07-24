// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_nnrpow.rs — the STEP-3 spectral-bridge
// scaling lemma `rpow32_scale`.

// STEP-3 of the spectral bridge: the `IsRpow32` measure-scaling identity.
//
// The per-coordinate dual-HC `dualhc_final_le` consumes `IsRpow32 (m·2^n) r`
// with `m·2^n = 4^n·Inf_i`. The KKL charge `kkl_sum_rpow32_influence_le`
// supplies the NORMALIZED `IsRpow32 (Inf_i) (r_i)` (`r_i = Inf_i^{3/2}`). The
// gap is a `2^n`-measure rescaling: if `r` is the `3/2`-power of `x`, then
// `(2^n·2^n·2^n)·r` is the `3/2`-power of `(2^n·2^n)·x`. Phrased abstractly over
// a nonnegative scale `c` (instantiated at `c := 2^n`, `0 ≤ 2^n` from
// `powNat_nonneg`):
//
//   BoolAnalysis.rpow32_scale :
//     ∀ (c x r : Rat), Rat.le Rat.zero c → IsRpow32 x r
//                    → IsRpow32 (Rat.mul (Rat.mul c c) x)
//                               (Rat.mul (Rat.mul (Rat.mul c c) c) r)
//
// The ring content is `((c³)·r)² = c⁶·(r²) = c⁶·x³ = ((c²)·x)³`. Proven from
// `Rat.mul_mul_mul_comm` (the `(a·b)·(c·d)=(a·c)·(b·d)` regroup), the defining
// relation `r·r = (x·x)·x` (`rpow32_sq`), `Rat.mul_nonneg` for the `0 ≤ c³·r`
// component, and `congrArg`/`Eq.trans`/`Eq.symm`. Every leaf is `Constructive`
// with empty closure, so this lemma is too. NO axiom is added or removed.
//
// NOTE: this is the load-bearing rung-3 of the bridge plan; rungs 1 (noiseOp
// Parseval diagonalization) and 2 (per-`S` derivative-coefficient collapse)
// remain unbuilt — see the build report. `rpow32_scale` is provable in
// isolation and is wired here.
//
// Recovered (kkl-dualhc-rational): `include!`d by boolean_analysis_kkl_nnrpow.rs
// (which defines `NnRpowConsts` and the shared imports) so the unconditional
// dual-HC chain can reach `register_rpow32_scale`.

impl Environment {
    /// `BoolAnalysis.rpow32_scale :
    ///   ∀ c x r, 0 ≤ c → IsRpow32 x r → IsRpow32 ((c·c)·x) (((c·c)·c)·r)`.
    /// The `2^n`-measure scaling bridge for the `3/2`-power graph relation.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_rpow32_scale(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rpow32_scale");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_is_rpow32()?;
        self.register_rpow32_sq()?; // r·r = (x·x)·x
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        self.init_rat()?; // Rat.mul_nonneg, congrArg
        let c = NnRpowConsts::new();

        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        // `@congrArg.{1,1} Rat Rat a b g h : g a = g b`.
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![
                crate::level::Level::succ(crate::level::Level::zero()),
                crate::level::Level::succ(crate::level::Level::zero()),
            ],
        );
        let congr = |a: Expr, b: Expr, g: Expr, h: Expr| -> Expr {
            Expr::apps(
                congr_arg.clone(),
                [c.rat.clone(), c.rat.clone(), a, b, g, h],
            )
        };
        // `Eq.trans.{1} Rat a b cc h1 h2`.
        let trans = |a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr| -> Expr {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.trans"),
                    vec![crate::level::Level::succ(crate::level::Level::zero())],
                ),
                [c.rat.clone(), a, b, cc, h1, h2],
            )
        };

        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let h0c = c.le0(cv.clone());
            let hrp = c.is_rpow32_of(&x, &r);

            // The scaled endpoints.
            let cc = c.mul(cv.clone(), cv.clone()); // c·c   (= Q)
            let ccc = c.mul(cc.clone(), cv.clone()); // (c·c)·c  (= P)
            let big_x = c.mul(cc.clone(), x.clone()); // (c·c)·x  = Q·x
            let big_r = c.mul(ccc.clone(), r.clone()); // ((c·c)·c)·r = P·r
            let concl = c.is_rpow32_of(&big_x, &big_r);

            let (h0c_id, h0c_v) = b.fresh_local(h0c.clone());
            let (hrp_id, hrp_v) = b.fresh_local(hrp.clone());

            let tail = if for_value {
                // ── part1 : 0 ≤ P·r ─────────────────────────────────────────
                // 0 ≤ c·c
                let h0cc = c.mul_nonneg_of(cv.clone(), cv.clone(), h0c_v.clone(), h0c_v.clone());
                // 0 ≤ (c·c)·c
                let h0ccc = c.mul_nonneg_of(cc.clone(), cv.clone(), h0cc, h0c_v.clone());
                // 0 ≤ r   (And.left of hyp, def-eq unfold)
                let (nn, rel) = c.rpow32_parts(&x, &r);
                let h0r = c.and_left_of(nn.clone(), rel.clone(), hrp_v.clone());
                // 0 ≤ P·r
                let part1 = c.mul_nonneg_of(ccc.clone(), r.clone(), h0ccc, h0r);

                // ── part2 : (P·r)·(P·r) = ((Q·x)·(Q·x))·(Q·x) ───────────────
                let pr = big_r.clone(); // P·r
                let qx = big_x.clone(); // Q·x
                let pp = c.mul(ccc.clone(), ccc.clone()); // P·P
                let rr = c.mul(r.clone(), r.clone()); // r·r
                let cube_x = c.cube(&x); // (x·x)·x
                let qq = c.mul(cc.clone(), cc.clone()); // Q·Q
                let qqq = c.mul(qq.clone(), cc.clone()); // (Q·Q)·Q
                let xx = c.mul(x.clone(), x.clone()); // x·x
                let qqq_cube = c.mul(qqq.clone(), cube_x.clone()); // (Q·Q)·Q · (x·x·x)

                // e1 : (P·r)·(P·r) = (P·P)·(r·r)   [mul_mul_mul_comm P r P r]
                let e1 = c.mul_mul_mul_comm_of(ccc.clone(), r.clone(), ccc.clone(), r.clone());
                // e2 : (P·P)·(r·r) = (P·P)·((x·x)·x)
                //   congrArg (fun t => (P·P)·t) (rpow32_sq x r hyp)
                let rpow32_sq = Expr::const_(Name::from_string("BoolAnalysis.rpow32_sq"), vec![]);
                let h_rel = Expr::apps(rpow32_sq, [x.clone(), r.clone(), hrp_v.clone()]); // r·r = (x·x)·x
                let g_pp = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(pp.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let e2 = congr(rr.clone(), cube_x.clone(), g_pp, h_rel);
                // hPP : P·P = (Q·Q)·Q   [mul_mul_mul_comm (c·c) c (c·c) c]
                //   ((c·c)·c)·((c·c)·c) = ((c·c)·(c·c))·(c·c) = (Q·Q)·Q
                let h_pp = c.mul_mul_mul_comm_of(cc.clone(), cv.clone(), cc.clone(), cv.clone());
                // e3 : (P·P)·((x·x)·x) = ((Q·Q)·Q)·((x·x)·x)
                //   congrArg (fun t => t·((x·x)·x)) hPP
                let g_cube = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(t, cube_x.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let e3 = congr(pp.clone(), qqq.clone(), g_cube, h_pp);

                // lhs_chain : (P·r)·(P·r) = ((Q·Q)·Q)·((x·x)·x)
                let pp_cube = c.mul(pp.clone(), cube_x.clone());
                let pp_rr = c.mul(pp.clone(), rr.clone());
                let prpr = c.mul(pr.clone(), pr.clone());
                let lhs_12 = trans(prpr.clone(), pp_rr.clone(), pp_cube.clone(), e1, e2);
                let lhs_chain = trans(prpr.clone(), pp_cube.clone(), qqq_cube.clone(), lhs_12, e3);

                // rhs_chain : ((Q·x)·(Q·x))·(Q·x) = ((Q·Q)·Q)·((x·x)·x)
                // f1 : (Q·x)·(Q·x) = (Q·Q)·(x·x)   [mul_mul_mul_comm Q x Q x]
                let f1 = c.mul_mul_mul_comm_of(cc.clone(), x.clone(), cc.clone(), x.clone());
                let qxqx = c.mul(qx.clone(), qx.clone()); // (Q·x)·(Q·x)
                let qq_xx = c.mul(qq.clone(), xx.clone()); // (Q·Q)·(x·x)
                                                           // f2 : ((Q·x)·(Q·x))·(Q·x) = ((Q·Q)·(x·x))·(Q·x)
                                                           //   congrArg (fun t => t·(Q·x)) f1
                let g_qx = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(t, qx.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let f2 = congr(qxqx.clone(), qq_xx.clone(), g_qx, f1);
                // f3 : ((Q·Q)·(x·x))·(Q·x) = ((Q·Q)·Q)·((x·x)·x)
                //   mul_mul_mul_comm (Q·Q) (x·x) Q x
                let f3 = c.mul_mul_mul_comm_of(qq.clone(), xx.clone(), cc.clone(), x.clone());
                // rhs_cube_base := ((Q·Q)·(x·x))·(Q·x)
                let rhs_cube_base = c.mul(qq_xx.clone(), qx.clone());
                let rhs_full = c.mul(qxqx.clone(), qx.clone()); // ((Q·x)·(Q·x))·(Q·x)
                let rhs_chain = trans(
                    rhs_full.clone(),
                    rhs_cube_base.clone(),
                    qqq_cube.clone(),
                    f2,
                    f3,
                );
                // part2 : (P·r)·(P·r) = ((Q·x)·(Q·x))·(Q·x)
                //   trans lhs_chain (symm rhs_chain)
                let rhs_chain_sym = c.symm(rhs_full.clone(), qqq_cube.clone(), rhs_chain);
                let part2 = trans(
                    prpr.clone(),
                    qqq_cube.clone(),
                    rhs_full.clone(),
                    lhs_chain,
                    rhs_chain_sym,
                );

                // And.intro (0 ≤ P·r) ((P·r)·(P·r) = ((Q·x)·(Q·x))·(Q·x)) part1 part2
                //   : IsRpow32 ((c·c)·x) (((c·c)·c)·r)   (def-eq unfold of IsRpow32).
                let (nn_big, rel_big) = c.rpow32_parts(&big_x, &big_r);
                Expr::apps(and_intro.clone(), [nn_big, rel_big, part1, part2])
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, bi, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = bind(&b, hrp_id, BinderInfo::Default, hrp, tail);
            let e = bind(&b, h0c_id, BinderInfo::Default, h0c, e);
            let e = bind(&b, r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, x_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, cv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }
}
