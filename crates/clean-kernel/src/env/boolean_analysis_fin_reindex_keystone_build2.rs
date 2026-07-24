// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Keystone `step` (the `Nat.rec` step case) + final `keystone_value`.
// `include!`d (transitively) into the module owning `KeystoneConsts`.

/// `C kk := ∀ (σ : Fin (kk+1) → Fin (kk+1)) (hinv : ∀x, σ(σ x)=x)
///            (F : Fin (kk+1) → Rat) (p : Fin kk)
///            (hcase : σ (last kk) = castSucc kk p) (ih : M kk),
///          Σ_{kk+1} (F∘σ) = Σ_{kk+1} F`
/// — the generalized motive for the inner `Nat.rec` on `k` that exposes the
/// successor structure the 2-cycle removal needs.
fn cast_gen_motive_body(c: &KeystoneConsts, parent: &EnvDeclBuilder, kk: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let kk1 = c.succ(kk);
    let fin_kk1 = c.fin_of(&kk1);
    let fin_kk = c.fin_of(kk);

    let sigma_ty = Expr::pi(BinderInfo::Default, fin_kk1.clone(), fin_kk1.clone());
    let (sigma_id, sigma) = d.fresh_local(sigma_ty.clone());
    let hinv_ty = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (x_id, x) = e.fresh_local(fin_kk1.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&kk1, ssx, x.clone());
        e.finish_child(e.mk_pi(x_id, BinderInfo::Default, fin_kk1.clone(), body))
    };
    let (hinv_id, _hinv) = d.fresh_local(hinv_ty.clone());
    let f_ty = c.fin_to_rat(&kk1);
    let (f_id, f) = d.fresh_local(f_ty.clone());
    let (p_id, p) = d.fresh_local(fin_kk.clone());
    let hcase_ty = c.eq_fin(
        &kk1,
        Expr::app(sigma.clone(), c.last(kk)),
        c.cast_succ(kk, &p),
    );
    let (hcase_id, _hcase) = d.fresh_local(hcase_ty.clone());
    let ih_ty = c.motive_body(&d, kk); // M kk
    let (ih_id, _ih) = d.fresh_local(ih_ty.clone());

    let reindexed = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (jx_id, jx) = e.fresh_local(fin_kk1.clone());
        let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
        e.finish_child(e.mk_lam(jx_id, BinderInfo::Default, fin_kk1.clone(), body))
    };
    let concl = c.eq_rat(c.sum(&kk1, &reindexed), c.sum(&kk1, &f));

    let r = d.mk_pi(ih_id, BinderInfo::Default, ih_ty, concl);
    let r = d.mk_pi(hcase_id, BinderInfo::Default, hcase_ty, r);
    let r = d.mk_pi(p_id, BinderInfo::Default, fin_kk.clone(), r);
    let r = d.mk_pi(f_id, BinderInfo::Default, f_ty, r);
    let r = d.mk_pi(hinv_id, BinderInfo::Default, hinv_ty, r);
    d.finish_child(d.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, r))
}

/// step : (k : Nat) → M k → M (k+1).
fn keystone_step(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let k1 = c.succ(&k);
    let fin_k1 = c.fin_of(&k1);
    let fin_k = c.fin_of(&k);
    let ih_ty = c.motive_body(&b, &k); // M k
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    // Introduce σ, hinv, F (the M (k+1) prefix).
    let sigma_ty = Expr::pi(BinderInfo::Default, fin_k1.clone(), fin_k1.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());
    let hinv_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = e.fresh_local(fin_k1.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&k1, ssx, x.clone());
        e.finish_child(e.mk_pi(x_id, BinderInfo::Default, fin_k1.clone(), body))
    };
    let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());
    let f_ty = c.fin_to_rat(&k1);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    let reindexed = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = e.fresh_local(fin_k1.clone());
        let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
        e.finish_child(e.mk_lam(jx_id, BinderInfo::Default, fin_k1.clone(), body))
    };
    let goal = c.eq_rat(c.sum(&k1, &reindexed), c.sum(&k1, &f));
    let sig_last = Expr::app(sigma.clone(), c.last(&k)); // σ (last k)

    // lcMotive : Fin (k+1) → Prop := fun w => @Eq (Fin (k+1)) (σ (last k)) w → goal
    let lc_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(fin_k1.clone());
        let eq_w = c.eq_fin(&k1, sig_last.clone(), w.clone());
        let body = Expr::pi(BinderInfo::Default, eq_w, goal.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, fin_k1.clone(), body))
    };

    // last-minor : motive (last k) = (σ(last)=last → goal)
    //   := fun (hfix : σ(last)=last) => fixed_step k σ hinv hfix ih F
    let last_min = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hfix_ty = c.eq_fin(&k1, sig_last.clone(), c.last(&k));
        let (hfix_id, hfix) = d.fresh_local(hfix_ty.clone());
        let body = Expr::apps(
            c.fixed_step.clone(),
            [
                k.clone(),
                sigma.clone(),
                hinv.clone(),
                hfix.clone(),
                ih.clone(),
                f.clone(),
            ],
        );
        d.finish_child(d.mk_lam(hfix_id, BinderInfo::Default, hfix_ty, body))
    };

    // cast-minor : (p : Fin k) → motive (castSucc p) = (σ(last)=castSucc p → goal)
    //   := fun p (hcase : σ(last)=castSucc p) =>
    //        (@Nat.rec.{0} C zero_branch succ_branch k) σ hinv F p hcase ih
    let cast_min = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = d.fresh_local(fin_k.clone());
        let hcase_ty = c.eq_fin(&k1, sig_last.clone(), c.cast_succ(&k, &p));
        let (hcase_id, hcase) = d.fresh_local(hcase_ty.clone());

        // C : Nat → Prop := fun kk => cast_gen_motive_body kk
        let cgen = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (kk_id, kk) = e.fresh_local(c.nat.clone());
            let body = cast_gen_motive_body(c, &e, &kk);
            e.finish_child(e.mk_lam(kk_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // zero_branch : C 0 = ∀ σ0 hinv0 F0 (p0:Fin 0) hcase0 ih0, Σ_1(F0∘σ0)=Σ_1 F0
        //   vacuous: p0 : Fin 0 is empty.
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let zero_branch = build_cast_zero_branch(c, &d, &zero);

        // succ_branch : (k0:Nat) → C k0 → C (k0+1)
        //   := fun k0 _ihc σ0 hinv0 F0 p0 hcase0 ih0 =>
        //        twocycle_step k0 σ0 hinv0 p0 hcase0 ih0 F0
        let succ_branch = build_cast_succ_branch(c, &d);

        // @Nat.rec.{0} C zero_branch succ_branch k : C k
        let rec_at_k = Expr::apps(
            c.nat_rec0.clone(),
            [cgen, zero_branch, succ_branch, k.clone()],
        );
        // (C k) applied to σ hinv F p hcase ih : goal
        let body = Expr::apps(
            rec_at_k,
            [
                sigma.clone(),
                hinv.clone(),
                f.clone(),
                p.clone(),
                hcase.clone(),
                ih.clone(),
            ],
        );
        let body = d.mk_lam(hcase_id, BinderInfo::Default, hcase_ty, body);
        d.finish_child(d.mk_lam(p_id, BinderInfo::Default, fin_k.clone(), body))
    };

    // @Fin.lastCases.{0} k lcMotive last_min cast_min (σ (last k)) : motive (σ(last))
    //   = (σ(last)=σ(last) → goal).  Apply Eq.refl (σ(last)) → goal.
    let lc = Expr::apps(
        c.fin_last_cases.clone(),
        [k.clone(), lc_motive, last_min, cast_min, sig_last.clone()],
    );
    let refl_siglast = Expr::apps(c.eq_refl1.clone(), [fin_k1.clone(), sig_last.clone()]);
    let dispatched = Expr::app(lc, refl_siglast); // : goal

    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, dispatched);
    let e = b.mk_lam(hinv_id, BinderInfo::Default, hinv_ty, e);
    let e = b.mk_lam(sigma_id, BinderInfo::Default, sigma_ty, e);
    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `zero_branch : C 0`.  All-binders prefix `σ0 hinv0 F0 (p0:Fin 0) hcase0 ih0`,
/// then `False.elim goal (Nat.not_succ_le_zero (val p0) (Fin.isLt 0 p0))`.
fn build_cast_zero_branch(c: &KeystoneConsts, parent: &EnvDeclBuilder, zero: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let one = c.succ(zero);
    let fin1 = c.fin_of(&one);
    let fin0 = c.fin_of(zero);
    let sigma_ty = Expr::pi(BinderInfo::Default, fin1.clone(), fin1.clone());
    let (sigma_id, sigma) = d.fresh_local(sigma_ty.clone());
    let hinv_ty = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (x_id, x) = e.fresh_local(fin1.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&one, ssx, x.clone());
        e.finish_child(e.mk_pi(x_id, BinderInfo::Default, fin1.clone(), body))
    };
    let (hinv_id, _hinv) = d.fresh_local(hinv_ty.clone());
    let f_ty = c.fin_to_rat(&one);
    let (f_id, f) = d.fresh_local(f_ty.clone());
    let (p_id, p) = d.fresh_local(fin0.clone());
    let hcase_ty = c.eq_fin(
        &one,
        Expr::app(sigma.clone(), c.last(zero)),
        c.cast_succ(zero, &p),
    );
    let (hcase_id, _hcase) = d.fresh_local(hcase_ty.clone());
    let ih_ty = c.motive_body(&d, zero);
    let (ih_id, _ih) = d.fresh_local(ih_ty.clone());

    // goal at kk=0
    let reindexed = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (jx_id, jx) = e.fresh_local(fin1.clone());
        let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
        e.finish_child(e.mk_lam(jx_id, BinderInfo::Default, fin1.clone(), body))
    };
    let goal = c.eq_rat(c.sum(&one, &reindexed), c.sum(&one, &f));
    // Nat.not_succ_le_zero (val p) (Fin.isLt 0 p) : False  [Fin.isLt 0 p : val p < 0 ≡ succ(val p) ≤ 0]
    let val_p = c.val(zero, &p);
    let islt = Expr::apps(c.fin_islt.clone(), [zero.clone(), p.clone()]);
    let false_pf = Expr::apps(c.nat_not_succ_le_zero.clone(), [val_p, islt]);
    let body = Expr::apps(c.false_elim0.clone(), [goal, false_pf]);

    let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
    let r = d.mk_lam(hcase_id, BinderInfo::Default, hcase_ty, r);
    let r = d.mk_lam(p_id, BinderInfo::Default, fin0.clone(), r);
    let r = d.mk_lam(f_id, BinderInfo::Default, f_ty, r);
    let r = d.mk_lam(hinv_id, BinderInfo::Default, hinv_ty, r);
    d.finish_child(d.mk_lam(sigma_id, BinderInfo::Default, sigma_ty, r))
}

/// `succ_branch : (k0 : Nat) → C k0 → C (k0+1)`.
///   `fun k0 _ihc σ0 hinv0 F0 p0 hcase0 ih0 => twocycle_step k0 σ0 hinv0 p0 hcase0 ih0 F0`.
fn build_cast_succ_branch(c: &KeystoneConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (k0_id, k0) = d.fresh_local(c.nat.clone());
    let ck0_ty = cast_gen_motive_body(c, &d, &k0); // C k0
    let (ihc_id, _ihc) = d.fresh_local(ck0_ty.clone());

    let k1 = c.succ(&k0); // k0+1
    let k2 = c.succ(&k1); // k0+2
    let fin_k1 = c.fin_of(&k1);
    let fin_k2 = c.fin_of(&k2);
    let sigma_ty = Expr::pi(BinderInfo::Default, fin_k2.clone(), fin_k2.clone());
    let (sigma_id, sigma) = d.fresh_local(sigma_ty.clone());
    let hinv_ty = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (x_id, x) = e.fresh_local(fin_k2.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&k2, ssx, x.clone());
        e.finish_child(e.mk_pi(x_id, BinderInfo::Default, fin_k2.clone(), body))
    };
    let (hinv_id, hinv) = d.fresh_local(hinv_ty.clone());
    let f_ty = c.fin_to_rat(&k2);
    let (f_id, f) = d.fresh_local(f_ty.clone());
    let (p_id, p) = d.fresh_local(fin_k1.clone());
    let hcase_ty = c.eq_fin(
        &k2,
        Expr::app(sigma.clone(), c.last(&k1)),
        c.cast_succ(&k1, &p),
    );
    let (hcase_id, hcase) = d.fresh_local(hcase_ty.clone());
    let ih_ty = c.motive_body(&d, &k1); // M (k0+1)
    let (ih_id, ih) = d.fresh_local(ih_ty.clone());

    // twocycle_step k0 σ hinv p hcase ih F : Σ_{k0+2}(F∘σ)=Σ_{k0+2} F
    let body = Expr::apps(
        c.twocycle_step.clone(),
        [
            k0.clone(),
            sigma.clone(),
            hinv.clone(),
            p.clone(),
            hcase.clone(),
            ih.clone(),
            f.clone(),
        ],
    );

    let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
    let r = d.mk_lam(hcase_id, BinderInfo::Default, hcase_ty, r);
    let r = d.mk_lam(p_id, BinderInfo::Default, fin_k1.clone(), r);
    let r = d.mk_lam(f_id, BinderInfo::Default, f_ty, r);
    let r = d.mk_lam(hinv_id, BinderInfo::Default, hinv_ty, r);
    let r = d.mk_lam(sigma_id, BinderInfo::Default, sigma_ty, r);
    let r = d.mk_lam(ihc_id, BinderInfo::Default, ck0_ty, r);
    d.finish_child(d.mk_lam(k0_id, BinderInfo::Default, c.nat.clone(), r))
}

fn keystone_value(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let motive = keystone_motive(c);
    let base = keystone_base(c);
    let step = keystone_step(c);
    // @Nat.rec.{0} M base step m : M m
    let rec_app = Expr::apps(c.nat_rec0.clone(), [motive, base, step, m.clone()]);
    b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), rec_app))
}
