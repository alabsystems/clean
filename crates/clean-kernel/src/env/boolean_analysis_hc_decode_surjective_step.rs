// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// The `Nat.rec` step case of `hcDecode_surjective` (include!d into the build).

impl SurjConsts {
    /// `castP n (mapped) : Fin (2^(n+1))` — the split transport
    /// `@Eq.ndrec Nat (2^n+2^n) (fun m => Fin m) mapped (2^(n+1))
    ///   (Eq.symm (Nat.pow_two_succ n))`, byte-identical to the
    /// `hcDecode_castP_*` / bridge spelling so the bridge lemmas apply.
    #[cfg(test)]
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let sum_pow = Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            [p2n.clone(), p2n.clone()],
        );
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(
            Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            n.clone(),
        );
        let e = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.nat.clone(), sum_pow, motive, mapped.clone(), p2sn, e],
        )
    }
}

/// step : ∀ (k : Nat), (∀ S', ∃ j', hcDecode k j' = S')
///          → ∀ (S : HCPoint (k+1)), ∃ jS, hcDecode (k+1) jS = S.
#[cfg(test)]
fn build_step(c: &SurjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let ih_ty = c.motive_body(&b, &k);
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());
    let sk = c.succ(&k);
    let (s_id, s) = b.fresh_local(c.hcpoint_of(&sk));

    // S' := fun (i : Fin k) => S (Fin.castSucc k i)  : HCPoint k.
    let s_restrict = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(c.fin_of(&k));
        let body = Expr::app(s.clone(), c.cast_succ(&k, &i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&k), body))
    };

    // goal_succ := ∃ jS, hcDecode (k+1) jS = S.
    let goal_succ = c.exists_decode(&sk, c.pred(&b, &sk, &s));

    // ih S' : ∃ j', hcDecode k j' = S'.
    let ih_at = Expr::app(ih.clone(), s_restrict.clone());

    // elim handler : ∀ (j' : Fin (2^k)), (hcDecode k j' = S') → goal_succ.
    let handler = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (jp_id, jp) = d.fresh_local(c.fin_of(&c.pow2(&k)));
        let hj_ty = c.eq_point(&k, c.decode(&k, &jp), s_restrict.clone());
        let (hj_id, hj) = d.fresh_local(hj_ty.clone());

        // Bool.casesOn on `S (last k)` via a `(S (last k) = bv) → goal_succ` motive,
        // applied to Eq.refl (S (last k)), so each branch gets hb : S (last k) = bv.
        let s_last = Expr::app(s.clone(), c.last(&k));
        // bool_motive : fun (bv : Bool) => (S (last k) = bv) → goal_succ.
        let bool_motive = {
            let mut m = EnvDeclBuilder::child_of(&d);
            let (bv_id, bv) = m.fresh_local(c.bool_.clone());
            let prem = c.eq_bool(s_last.clone(), bv.clone());
            let body = Expr::pi(BinderInfo::Default, prem, goal_succ.clone());
            m.finish_child(m.mk_lam(bv_id, BinderInfo::Default, c.bool_.clone(), body))
        };

        let false_branch = build_branch(c, &d, &k, &s, &jp, &hj, &s_restrict, Half::Low);
        let true_branch = build_branch(c, &d, &k, &s, &jp, &hj, &s_restrict, Half::High);

        // @Bool.casesOn.{0} bool_motive (S (last k)) false_branch true_branch
        //   : (S (last k) = S (last k)) → goal_succ.
        let cases = Expr::apps(
            c.bool_cases.clone(),
            [bool_motive, s_last.clone(), false_branch, true_branch],
        );
        // applied to Eq.refl (S (last k)).
        let refl = Expr::apps(c.eq_refl.clone(), [c.bool_.clone(), s_last]);
        let body = Expr::app(cases, refl);

        let r = d.mk_lam(hj_id, BinderInfo::Default, hj_ty, body);
        let r = d.mk_lam(jp_id, BinderInfo::Default, c.fin_of(&c.pow2(&k)), r);
        d.finish_child(r)
    };

    // @Exists.elim.{1} {Fin (2^k)} {pred_k} {goal_succ} (ih S') handler : goal_succ.
    let pred_k = c.pred(&b, &k, &s_restrict);
    let elim = Expr::apps(
        Expr::const_(Name::from_string("Exists.elim"), vec![c.l1.clone()]),
        [c.fin_of(&c.pow2(&k)), pred_k, goal_succ, ih_at, handler],
    );

    let r = b.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(&sk), elim);
    let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

#[derive(Clone, Copy)]
#[cfg(test)]
enum Half {
    Low,  // top bit false, idx = castP (castAdd j'), bridge → extendF
    High, // top bit true,  idx = castP (addNat  j'), bridge → extendT
}

#[cfg(test)]
impl Half {
    #[cfg(test)]
    fn idx_map<'a>(&self, c: &'a SurjConsts) -> &'a Expr {
        match self {
            Half::Low => &c.cast_add,
            Half::High => &c.add_nat,
        }
    }
    #[cfg(test)]
    fn bridge(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.hcDecode_castP_castAdd_extendF",
            Half::High => "BoolAnalysis.hcDecode_castP_addNat_extendT",
        }
    }
    #[cfg(test)]
    fn extend<'a>(&self, c: &'a SurjConsts) -> &'a Expr {
        match self {
            Half::Low => &c.extend_f,
            Half::High => &c.extend_t,
        }
    }
    #[cfg(test)]
    fn ext_castsucc(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.extendF_castSucc",
            Half::High => "BoolAnalysis.extendT_castSucc",
        }
    }
    #[cfg(test)]
    fn ext_last(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.extendF_last",
            Half::High => "BoolAnalysis.extendT_last",
        }
    }
    #[cfg(test)]
    fn top_bit<'a>(&self, c: &'a SurjConsts) -> &'a Expr {
        match self {
            Half::Low => &c.bool_false,
            Half::High => &c.bool_true,
        }
    }
}

/// One `Bool.casesOn` branch: `fun (hb : S (last k) = <bit>) => Exists.intro ...`.
/// Builds the witness `jS := castP (idx_map j')` and the proof
/// `hcDecode (k+1) jS = S` via the bridge + `extend* k S' = S` reconstruction.
#[cfg(test)]
fn build_branch(
    c: &SurjConsts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    s: &Expr,
    jp: &Expr,
    hj: &Expr,
    s_restrict: &Expr,
    half: Half,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let sk = c.succ(k);
    let p2k = c.pow2(k);
    let top = half.top_bit(c).clone();

    // hb : S (last k) = <bit>.
    let s_last = Expr::app(s.clone(), c.last(k));
    let hb_ty = c.eq_bool(s_last.clone(), top.clone());
    let (hb_id, hb) = d.fresh_local(hb_ty.clone());

    // witness jS := castP (idx_map (2^k) (2^k) j')  : Fin (2^(k+1)).
    let mapped = Expr::apps(
        half.idx_map(c).clone(),
        [p2k.clone(), p2k.clone(), jp.clone()],
    );
    let witness = c.cast_p(&d, k, &mapped);

    // dec_k_jp := hcDecode k j'  : HCPoint k.
    let dec_k_jp = c.decode(k, jp);
    // decoded := hcDecode (k+1) jS  : HCPoint (k+1).
    let decoded = c.decode(&sk, &witness);
    // ext_dec := extend* k (hcDecode k j')  : HCPoint (k+1)   (bridge RHS).
    let ext_dec = Expr::apps(half.extend(c).clone(), [k.clone(), dec_k_jp.clone()]);
    // ext_s := extend* k S'  : HCPoint (k+1).
    let ext_s = Expr::apps(half.extend(c).clone(), [k.clone(), s_restrict.clone()]);

    // (A) bridge : hcDecode (k+1) jS = extend* k (hcDecode k j').
    let bridge = Expr::apps(
        Expr::const_(Name::from_string(half.bridge()), vec![]),
        [k.clone(), jp.clone()],
    );

    // (B) congrArg (extend* k ·) hj : extend* k (hcDecode k j') = extend* k S'.
    //     via funext is overkill; use congrArg over the function slot.
    //     congrArg.{1,1} (HCPoint k) (HCPoint (k+1)) (hcDecode k j') S'
    //        (fun p => extend* k p) hj.
    let ext_fn = {
        let mut g = EnvDeclBuilder::child_of(&d);
        let (p_id, p) = g.fresh_local(c.hcpoint_of(k));
        let body = Expr::apps(half.extend(c).clone(), [k.clone(), p]);
        g.finish_child(g.mk_lam(p_id, BinderInfo::Default, c.hcpoint_of(k), body))
    };
    let congr = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![c.l1.clone(), c.l1.clone()],
        ),
        [
            c.hcpoint_of(k),
            c.hcpoint_of(&sk),
            dec_k_jp.clone(),
            s_restrict.clone(),
            ext_fn,
            hj.clone(),
        ],
    );

    // (C) recon : extend* k S' = S   (funext + Fin.lastCases, using hb at last).
    let recon = build_recon(c, &d, k, s, s_restrict, &hb, half);

    // chain: decoded = ext_dec = ext_s = S.
    let t1 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.hcpoint_of(&sk),
            decoded.clone(),
            ext_dec.clone(),
            ext_s.clone(),
            bridge,
            congr,
        ],
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [
            c.hcpoint_of(&sk),
            decoded.clone(),
            ext_s.clone(),
            s.clone(),
            t1,
            recon,
        ],
    );

    let intro = c.intro(&sk, c.pred(&d, &sk, s), witness, proof);
    d.finish_child(d.mk_lam(hb_id, BinderInfo::Default, hb_ty, intro))
}

/// recon : extend* k S' = S, by `funext` over `Fin (k+1)` + `Fin.lastCases`:
///   - castSucc i : extend* k S' (castSucc i) = S' i ≡ S (castSucc i)  (extend*_castSucc);
///   - last       : extend* k S' (last k)     = <bit> = S (last k)     (extend*_last, hb.symm).
#[cfg(test)]
fn build_recon(
    c: &SurjConsts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    s: &Expr,
    s_restrict: &Expr,
    hb: &Expr,
    half: Half,
) -> Expr {
    let sk = c.succ(k);
    let top = half.top_bit(c).clone();
    // lhs_fn := extend* k S'  ; rhs_fn := S.
    let lhs_fn = Expr::apps(half.extend(c).clone(), [k.clone(), s_restrict.clone()]);
    let rhs_fn = s.clone();

    // lc_motive : fun (j : Fin (k+1)) => Eq Bool (lhs_fn j) (rhs_fn j).
    let lc_motive = {
        let mut g = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = g.fresh_local(c.fin_of(&sk));
        let body = c.eq_bool(
            Expr::app(lhs_fn.clone(), j.clone()),
            Expr::app(rhs_fn.clone(), j.clone()),
        );
        g.finish_child(g.mk_lam(j_id, BinderInfo::Default, c.fin_of(&sk), body))
    };

    // last branch: lhs_fn (last k) = <bit> = S (last k).
    let last = c.last(k);
    let lhs_at_last = Expr::app(lhs_fn.clone(), last.clone());
    let rhs_at_last = Expr::app(rhs_fn.clone(), last.clone());
    // ext_last : extend* k S' (last k) = <bit>.
    let ext_last = Expr::apps(
        Expr::const_(Name::from_string(half.ext_last()), vec![]),
        [k.clone(), s_restrict.clone()],
    );
    // hb.symm : <bit> = S (last k).
    let hb_symm = c.symm_bool(rhs_at_last.clone(), top.clone(), hb.clone());
    let last_proof = c.trans_bool(lhs_at_last, top.clone(), rhs_at_last, ext_last, hb_symm);

    // castSucc branch: fun (i : Fin k) => lhs_fn (castSucc i) = rhs_fn (castSucc i).
    //   ext_cs : extend* k S' (castSucc i) = S' i ≡ S (castSucc i).
    //   Since S' i ≡ S (castSucc i) by δ on s_restrict, ext_cs IS the proof.
    let cast_proof = {
        let mut g = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = g.fresh_local(c.fin_of(k));
        // ext_cs : extend* k S' (castSucc i) = S' i.
        let ext_cs = Expr::apps(
            Expr::const_(Name::from_string(half.ext_castsucc()), vec![]),
            [k.clone(), s_restrict.clone(), i.clone()],
        );
        g.finish_child(g.mk_lam(i_id, BinderInfo::Default, c.fin_of(k), ext_cs))
    };

    // @Fin.lastCases.{0} k lc_motive last_proof cast_proof : ∀ j, lhs_fn j = rhs_fn j.
    let pointwise = Expr::apps(
        c.fin_last_cases.clone(),
        [k.clone(), lc_motive, last_proof, cast_proof],
    );

    let funext_motive = const_bool_motive(c, parent, &sk);
    Expr::apps(
        c.funext.clone(),
        [c.fin_of(&sk), funext_motive, lhs_fn, rhs_fn, pointwise],
    )
}
