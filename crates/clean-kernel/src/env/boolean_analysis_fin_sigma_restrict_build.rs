// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for the σ' restriction bundle (Step 1 of the keystone).
// `include!`d into `boolean_analysis_fin_sigma_restrict.rs`; shares its
// `SigmaRestrictConsts` + imports. Each builder returns a closed Expr.

// ===========================================================================
// Fin.sigmaRestrict_ne_last :
//   (k)(σ : Fin (k+1) → Fin (k+1))(hinv : ∀ jx, σ (σ jx) = jx)
//     (hfix : σ (last k) = last k)(j : Fin k)
//   → @Eq (Fin (k+1)) (σ (castSucc k j)) (last k) → False
// ===========================================================================

/// Shared binder prefix: introduces `k, σ, hinv, hfix` and returns the builder
/// plus those fvars and the common derived types (`fin_succ`, `fin_k`).
struct Prefix {
    b: EnvDeclBuilder,
    k: Expr,
    k_id: crate::expr::FVarId,
    sigma: Expr,
    sigma_id: crate::expr::FVarId,
    sigma_ty: Expr,
    hinv: Expr,
    hinv_id: crate::expr::FVarId,
    hinv_ty: Expr,
    hfix: Expr,
    hfix_id: crate::expr::FVarId,
    hfix_ty: Expr,
    fin_succ: Expr,
    fin_k: Expr,
    nat: Expr,
}

fn make_prefix(c: &SigmaRestrictConsts) -> Prefix {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);

    let sigma_ty = Expr::pi(BinderInfo::Default, fin_succ.clone(), fin_succ.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());

    // hinv : ∀ jx : Fin (k+1), σ (σ jx) = jx
    let hinv_ty = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = hb.fresh_local(fin_succ.clone());
        let ssjx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), jx.clone()));
        let body = c.eq_fin(&succ_k, ssjx, jx.clone());
        hb.finish_child(hb.mk_pi(jx_id, BinderInfo::Default, fin_succ.clone(), body))
    };
    let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());

    // hfix : σ (last k) = last k
    let hfix_ty = c.eq_fin(&succ_k, Expr::app(sigma.clone(), c.last(&k)), c.last(&k));
    let (hfix_id, hfix) = b.fresh_local(hfix_ty.clone());

    Prefix {
        b,
        k,
        k_id,
        sigma,
        sigma_id,
        sigma_ty,
        hinv,
        hinv_id,
        hinv_ty,
        hfix,
        hfix_id,
        hfix_ty,
        fin_succ,
        fin_k,
        nat: c.nat.clone(),
    }
}

/// Close `k, σ, hinv, hfix` over `body` with the given binder constructor.
fn close_prefix(p: &Prefix, body: Expr, pi: bool) -> Expr {
    let bind = |id, ty: Expr, inner: Expr| -> Expr {
        if pi {
            p.b.mk_pi(id, BinderInfo::Default, ty, inner)
        } else {
            p.b.mk_lam(id, BinderInfo::Default, ty, inner)
        }
    };
    let e = bind(p.hfix_id, p.hfix_ty.clone(), body);
    let e = bind(p.hinv_id, p.hinv_ty.clone(), e);
    let e = bind(p.sigma_id, p.sigma_ty.clone(), e);
    let e = bind(p.k_id, p.nat.clone(), e);
    p.b.finish(e)
}

fn ne_last_type(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let succ_k = c.succ(&p.k);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());
    // e : σ (castSucc k j) = last k
    let e_ty = c.eq_fin(
        &succ_k,
        Expr::app(p.sigma.clone(), c.cast_succ(&p.k, &j)),
        c.last(&p.k),
    );
    let (e_id, _e) = p.b.fresh_local(e_ty.clone());
    let body =
        p.b.mk_pi(e_id, BinderInfo::Default, e_ty, c.false_c.clone());
    let body = p.b.mk_pi(j_id, BinderInfo::Default, p.fin_k.clone(), body);
    close_prefix(&p, body, true)
}

fn ne_last_value(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let succ_k = c.succ(&p.k);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());
    let cs_j = c.cast_succ(&p.k, &j); // castSucc k j : Fin (k+1)
    let sig_cs = Expr::app(p.sigma.clone(), cs_j.clone()); // σ (castSucc j)
    let last_k = c.last(&p.k);
    let e_ty = c.eq_fin(&succ_k, sig_cs.clone(), last_k.clone());
    let (e_id, e) = p.b.fresh_local(e_ty.clone());

    // hfix.symm : last k = σ (last k)
    let hfix_sym = Expr::apps(
        c.eq_symm.clone(),
        [
            p.fin_succ.clone(),
            Expr::app(p.sigma.clone(), last_k.clone()),
            last_k.clone(),
            p.hfix.clone(),
        ],
    );
    // e1 : σ (castSucc j) = σ (last k)   [e.trans hfix.symm]
    let sig_last = Expr::app(p.sigma.clone(), last_k.clone());
    let e1 = Expr::apps(
        c.eq_trans.clone(),
        [
            p.fin_succ.clone(),
            sig_cs.clone(),
            last_k.clone(),
            sig_last.clone(),
            e.clone(),
            hfix_sym,
        ],
    );
    // congrArg σ e1 : σ (σ (castSucc j)) = σ (σ (last k))
    let ss_cs = Expr::app(p.sigma.clone(), sig_cs.clone());
    let ss_last = Expr::app(p.sigma.clone(), sig_last.clone());
    let cong = Expr::apps(
        c.congr_arg.clone(),
        [
            p.fin_succ.clone(),
            p.fin_succ.clone(),
            sig_cs.clone(),
            sig_last.clone(),
            p.sigma.clone(),
            e1,
        ],
    );
    // hinv (castSucc j) : σ (σ (castSucc j)) = castSucc j  → symm: castSucc j = σ(σ(castSucc j))
    let hinv_cs = Expr::app(p.hinv.clone(), cs_j.clone());
    let hinv_cs_sym = Expr::apps(
        c.eq_symm.clone(),
        [p.fin_succ.clone(), ss_cs.clone(), cs_j.clone(), hinv_cs],
    );
    // hinv (last k) : σ (σ (last k)) = last k
    let hinv_last = Expr::app(p.hinv.clone(), last_k.clone());
    // chain: castSucc j = σ(σ(castSucc j)) = σ(σ(last)) = last
    //   step A: castSucc j = σ(σ(castSucc j))   [hinv_cs_sym]
    //   step B: σ(σ(castSucc j)) = σ(σ(last))    [cong]
    //   step C: σ(σ(last)) = last                [hinv_last]
    let ab = Expr::apps(
        c.eq_trans.clone(),
        [
            p.fin_succ.clone(),
            cs_j.clone(),
            ss_cs.clone(),
            ss_last.clone(),
            hinv_cs_sym,
            cong,
        ],
    );
    let cs_eq_last = Expr::apps(
        c.eq_trans.clone(),
        [
            p.fin_succ.clone(),
            cs_j.clone(),
            ss_last.clone(),
            last_k.clone(),
            ab,
            hinv_last,
        ],
    );
    // Fin.castSucc_ne_last k j cs_eq_last : False
    let false_pf = Expr::apps(
        c.cast_succ_ne_last.clone(),
        [p.k.clone(), j.clone(), cs_eq_last],
    );

    let body = p.b.mk_lam(e_id, BinderInfo::Default, e_ty, false_pf);
    let body = p.b.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), body);
    close_prefix(&p, body, false)
}

// ===========================================================================
// Fin.sigmaRestrict :
//   (k)(σ)(hinv)(hfix)(j : Fin k) → Fin k
//   := Fin.mk k (Fin.val (k+1) (σ (castSucc k j))) (hlt)
// where hlt : Nat.lt (Fin.val (k+1) (σ (castSucc k j))) k.
//
// hlt := Nat.lt_of_le_of_ne v k hle hne where
//   v   := Fin.val (k+1) (σ (castSucc k j))
//   hle : Nat.le v k     := Nat.le_of_succ_le_succ v k (Fin.isLt (k+1) (σ (castSucc k j)))
//                           [Fin.isLt … : Nat.lt v (k+1) ≡ Nat.le (succ v) (succ k)]
//   hne : Eq v k → False := fun (hvk : v = k) =>
//           Fin.sigmaRestrict_ne_last k σ hinv hfix j
//             (Fin.eq_of_val_eq (k+1) (σ (castSucc j)) (last k) hvk)
//     -- val (σ (castSucc j)) ≡ v ; val (last k) ≡ k ; so hvk : val lhs = val rhs.
// ===========================================================================
fn restrict_type(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let (j_id, _j) = p.b.fresh_local(p.fin_k.clone());
    let body =
        p.b.mk_pi(j_id, BinderInfo::Default, p.fin_k.clone(), p.fin_k.clone());
    close_prefix(&p, body, true)
}

fn restrict_value(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let succ_k = c.succ(&p.k);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());
    let cs_j = c.cast_succ(&p.k, &j);
    let sig_cs = Expr::app(p.sigma.clone(), cs_j.clone());
    let v = c.val(&succ_k, &sig_cs); // Fin.val (k+1) (σ (castSucc j))
    let last_k = c.last(&p.k);

    // hislt : Fin.isLt (k+1) (σ (castSucc j)) : Nat.lt v (k+1) ≡ Nat.le (succ v) (succ k)
    let hislt = Expr::apps(c.fin_islt.clone(), [succ_k.clone(), sig_cs.clone()]);
    // hle : Nat.le_of_succ_le_succ v k hislt : Nat.le v k
    let hle = Expr::apps(c.nat_le_of_ss.clone(), [v.clone(), p.k.clone(), hislt]);

    // hne : Eq v k → False
    let hne = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let eq_vk = c.eq_nat(v.clone(), p.k.clone());
        let (hvk_id, hvk) = d.fresh_local(eq_vk.clone());
        // hvk : v = k ; v ≡ Fin.val (k+1) (σ (castSucc j)), k ≡ Fin.val (k+1) (last k).
        // Fin.eq_of_val_eq (k+1) (σ (castSucc j)) (last k) hvk : σ (castSucc j) = last k
        let e_fin = Expr::apps(
            c.fin_eq_of_val.clone(),
            [succ_k.clone(), sig_cs.clone(), last_k.clone(), hvk.clone()],
        );
        // Fin.sigmaRestrict_ne_last k σ hinv hfix j e_fin : False
        let ne_last = Expr::apps(
            Expr::const_(Name::from_string("Fin.sigmaRestrict_ne_last"), vec![]),
            [
                p.k.clone(),
                p.sigma.clone(),
                p.hinv.clone(),
                p.hfix.clone(),
                j.clone(),
                e_fin,
            ],
        );
        d.finish_child(d.mk_lam(hvk_id, BinderInfo::Default, eq_vk, ne_last))
    };

    // hlt : Nat.lt_of_le_of_ne v k hle hne : Nat.lt v k
    let hlt = Expr::apps(
        c.nat_lt_of_le_ne.clone(),
        [v.clone(), p.k.clone(), hle, hne],
    );
    // Fin.mk k v hlt : Fin k
    let mk = Expr::apps(c.fin_mk.clone(), [p.k.clone(), v.clone(), hlt]);

    let body = p.b.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), mk);
    close_prefix(&p, body, false)
}

// ===========================================================================
// Fin.sigmaRestrict_coherence :
//   (k)(σ)(hinv)(hfix)(j : Fin k)
//   → @Eq (Fin (k+1)) (σ (castSucc k j)) (castSucc k (Fin.sigmaRestrict k σ hinv hfix j))
//
// Both sides have the same `val`: lhs val ≡ Fin.val (k+1) (σ (castSucc j)) = v,
// rhs = castSucc k σ' where σ' = Fin.mk k v hlt, so val rhs ≡ Fin.val k σ' ≡ v.
// So `Fin.eq_of_val_eq (k+1) lhs rhs (Eq.refl Nat v)`.
// ===========================================================================
fn coherence_type(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let succ_k = c.succ(&p.k);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());
    let lhs = Expr::app(p.sigma.clone(), c.cast_succ(&p.k, &j));
    let sp = c.restrict(&p.k, &p.sigma, &p.hinv, &p.hfix, &j);
    let rhs = c.cast_succ(&p.k, &sp);
    let concl = c.eq_fin(&succ_k, lhs, rhs);
    let body = p.b.mk_pi(j_id, BinderInfo::Default, p.fin_k.clone(), concl);
    close_prefix(&p, body, true)
}

fn coherence_value(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let succ_k = c.succ(&p.k);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());
    let cs_j = c.cast_succ(&p.k, &j);
    let sig_cs = Expr::app(p.sigma.clone(), cs_j.clone());
    let v = c.val(&succ_k, &sig_cs);
    let sp = c.restrict(&p.k, &p.sigma, &p.hinv, &p.hfix, &j);
    let rhs = c.cast_succ(&p.k, &sp);

    // hval : Fin.val (k+1) (σ (castSucc j)) = Fin.val (k+1) (castSucc k σ')
    //   both reduce to v, so Eq.refl Nat v.
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let hval = Expr::apps(eq_refl, [c.nat.clone(), v]);
    // Fin.eq_of_val_eq (k+1) (σ (castSucc j)) (castSucc k σ') hval
    let body = Expr::apps(
        c.fin_eq_of_val.clone(),
        [succ_k.clone(), sig_cs.clone(), rhs.clone(), hval],
    );

    let body = p.b.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), body);
    close_prefix(&p, body, false)
}

// ===========================================================================
// Fin.sigmaRestrict_involutive :
//   (k)(σ)(hinv)(hfix)(j : Fin k)
//   → @Eq (Fin k) (Fin.sigmaRestrict k σ hinv hfix (Fin.sigmaRestrict k σ hinv hfix j)) j
//
// Let σ' := Fin.sigmaRestrict k σ hinv hfix.  Coherence gives, for any x,
//   σ (castSucc x) = castSucc (σ' x).
// With x := σ' j:  σ (castSucc (σ' j)) = castSucc (σ' (σ' j))      ...(I)
// Coherence at j:  σ (castSucc j)      = castSucc (σ' j)            ...(II)
// Apply σ to (II) and use the involution:
//   castSucc j = σ (σ (castSucc j)) = σ (castSucc (σ' j))           ...(III)
//     [hinv (castSucc j) symm ; congrArg σ (II)]
// Combine (III) and (I):  castSucc j = castSucc (σ' (σ' j))         ...(IV)
// `Fin.castSucc_inj k (σ' (σ' j)) j (IV.symm)` : σ' (σ' j) = j.
// ===========================================================================
fn involutive_type(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());
    let sp = c.restrict(&p.k, &p.sigma, &p.hinv, &p.hfix, &j);
    let spsp = c.restrict(&p.k, &p.sigma, &p.hinv, &p.hfix, &sp);
    let concl = c.eq_fin(&p.k, spsp, j.clone());
    let body = p.b.mk_pi(j_id, BinderInfo::Default, p.fin_k.clone(), concl);
    close_prefix(&p, body, true)
}

fn involutive_value(c: &SigmaRestrictConsts) -> Expr {
    let mut p = make_prefix(c);
    let (j_id, j) = p.b.fresh_local(p.fin_k.clone());

    let coh = Expr::const_(Name::from_string("Fin.sigmaRestrict_coherence"), vec![]);
    let coh_at = |x: &Expr| -> Expr {
        Expr::apps(
            coh.clone(),
            [
                p.k.clone(),
                p.sigma.clone(),
                p.hinv.clone(),
                p.hfix.clone(),
                x.clone(),
            ],
        )
    };

    let sp_j = c.restrict(&p.k, &p.sigma, &p.hinv, &p.hfix, &j); // σ' j
    let spsp = c.restrict(&p.k, &p.sigma, &p.hinv, &p.hfix, &sp_j); // σ' (σ' j)

    let cs_j = c.cast_succ(&p.k, &j); // castSucc j
    let cs_spj = c.cast_succ(&p.k, &sp_j); // castSucc (σ' j)
    let cs_spsp = c.cast_succ(&p.k, &spsp); // castSucc (σ' (σ' j))

    let sig_cs_j = Expr::app(p.sigma.clone(), cs_j.clone()); // σ (castSucc j)
    let sig_cs_spj = Expr::app(p.sigma.clone(), cs_spj.clone()); // σ (castSucc (σ' j))

    // (II) coh j : σ (castSucc j) = castSucc (σ' j)
    let coh_j = coh_at(&j);
    // (I) coh (σ' j) : σ (castSucc (σ' j)) = castSucc (σ' (σ' j))
    let coh_spj = coh_at(&sp_j);

    // hinv (castSucc j) : σ (σ (castSucc j)) = castSucc j  → symm
    let ss_cs_j = Expr::app(p.sigma.clone(), sig_cs_j.clone());
    let hinv_cs_j = Expr::app(p.hinv.clone(), cs_j.clone());
    let hinv_cs_j_sym = Expr::apps(
        c.eq_symm.clone(),
        [p.fin_succ.clone(), ss_cs_j.clone(), cs_j.clone(), hinv_cs_j],
    );
    // congrArg σ (coh_j) : σ (σ (castSucc j)) = σ (castSucc (σ' j))
    let cong_coh_j = Expr::apps(
        c.congr_arg.clone(),
        [
            p.fin_succ.clone(),
            p.fin_succ.clone(),
            sig_cs_j.clone(),
            cs_spj.clone(),
            p.sigma.clone(),
            coh_j,
        ],
    );
    // (III) castSucc j = σ (castSucc (σ' j))
    //   [hinv_cs_j_sym : castSucc j = σ(σ(castSucc j)); cong_coh_j : ... = σ(castSucc (σ' j))]
    let iii = Expr::apps(
        c.eq_trans.clone(),
        [
            p.fin_succ.clone(),
            cs_j.clone(),
            ss_cs_j.clone(),
            sig_cs_spj.clone(),
            hinv_cs_j_sym,
            cong_coh_j,
        ],
    );
    // (IV) castSucc j = castSucc (σ' (σ' j))   [iii ; coh_spj]
    let iv = Expr::apps(
        c.eq_trans.clone(),
        [
            p.fin_succ.clone(),
            cs_j.clone(),
            sig_cs_spj.clone(),
            cs_spsp.clone(),
            iii,
            coh_spj,
        ],
    );
    // iv.symm : castSucc (σ' (σ' j)) = castSucc j
    let iv_sym = Expr::apps(
        c.eq_symm.clone(),
        [p.fin_succ.clone(), cs_j.clone(), cs_spsp.clone(), iv],
    );
    // Fin.castSucc_inj k (σ' (σ' j)) j iv_sym : σ' (σ' j) = j
    let cinj = Expr::const_(Name::from_string("Fin.castSucc_inj"), vec![]);
    let body = Expr::apps(cinj, [p.k.clone(), spsp.clone(), j.clone(), iv_sym]);

    let body = p.b.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), body);
    close_prefix(&p, body, false)
}
