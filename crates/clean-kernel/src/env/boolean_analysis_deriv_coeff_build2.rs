// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Summand-lambda constructors + STEP 4 (the subsetSum_flip_invariant leg) for
// `deriv_coeff_eq`. `include!`d (transitively) into the module owning
// `DerivCoeffConsts`.

/// `fun y => (b y)·χ_S y`.
fn make_bchi(c: &DerivCoeffConsts, parent: &EnvDeclBuilder, n: &Expr, bf: &Expr, s: &Expr) -> Expr {
    let mut yb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (y_id, y) = yb.fresh_local(hcp.clone());
    let body = c.mul(Expr::app(bf.clone(), y.clone()), c.chi_(n, s, &y));
    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
}

/// `fun y => (b (hcFlip n y i))·χ_S y`.
fn make_bfchi(
    c: &DerivCoeffConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    bf: &Expr,
    s: &Expr,
    i: &Expr,
) -> Expr {
    let mut yb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (y_id, y) = yb.fresh_local(hcp.clone());
    let bfy = Expr::app(bf.clone(), c.hc_flip_(n, &y, i));
    let body = c.mul(bfy, c.chi_(n, s, &y));
    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
}

/// `fun y => (b y)·χ_S y − (b (hcFlip n y i))·χ_S y`.
fn make_split(
    c: &DerivCoeffConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    bf: &Expr,
    s: &Expr,
    i: &Expr,
) -> Expr {
    let mut yb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (y_id, y) = yb.fresh_local(hcp.clone());
    let by_chi = c.mul(Expr::app(bf.clone(), y.clone()), c.chi_(n, s, &y));
    let bfy = Expr::app(bf.clone(), c.hc_flip_(n, &y, i));
    let bfy_chi = c.mul(bfy, c.chi_(n, s, &y));
    let body = c.sub(by_chi, bfy_chi);
    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
}

/// STEP 4: `sum_bfchi = fs·capA`.
fn build_step4(
    c: &DerivCoeffConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    bf: &Expr,
    s: &Expr,
    i: &Expr,
    fs: &Expr,
    cap_a: &Expr,
    bchi: &Expr,
    bfchi: &Expr,
    sum_bfchi: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);

    // g := fun z => (b z)·χ_S (hcFlip n z i).
    let g = {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let body = c.mul(
            Expr::app(bf.clone(), z.clone()),
            c.chi_(n, s, &c.hc_flip_(n, &z, i)),
        );
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
    };
    // g_flip := fun x => g (hcFlip n x i)  (the LHS summand of flip_invariant).
    let g_flip = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = Expr::app(g.clone(), c.hc_flip_(n, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let sum_g = c.ssum(n, g.clone());
    let sum_gflip = c.ssum(n, g_flip.clone());

    // flip_inv : Σ g_flip = Σ g   [subsetSum_flip_invariant n g i].
    let flip_inv = Expr::apps(
        c.subset_sum_flip_invariant.clone(),
        [n.clone(), g.clone(), i.clone()],
    );

    // congr_gflip_bfchi : Σ g_flip = Σ bfchi   [subsetSum_congr; pointwise via hcFlip_involutive].
    //   g_flip x = (b (flip x))·χ_S (flip (flip x)) ; bfchi x = (b (flip x))·χ_S x.
    //   hcFlip_involutive n x i : flip (flip x) = x ;
    //   congrArg (fun w => (b (flip x))·χ_S w) hinv : g_flip x = bfchi x.
    let pw_gflip = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let flipx = c.hc_flip_(n, &x, i);
        let b_flipx = Expr::app(bf.clone(), flipx.clone());
        let flip_flip = c.hc_flip_(n, &flipx, i); // flip (flip x)
        let chi_ff = c.chi_(n, s, &flip_flip);
        let chi_x = c.chi_(n, s, &x);
        let gflip_x = c.mul(b_flipx.clone(), chi_ff.clone()); // = g_flip x (β)
        let bfchi_x = c.mul(b_flipx.clone(), chi_x.clone()); // = bfchi x (β)
                                                             // hinv : flip (flip x) = x
        let hinv = Expr::apps(
            c.hc_flip_involutive.clone(),
            [n.clone(), x.clone(), i.clone()],
        );
        // congrArg (fun w => (b (flip x))·χ_S w) hinv  — over HCPoint n (Sort 1) → Rat.
        let g_fn = {
            let mut d = EnvDeclBuilder::child_of(&xb);
            let (w_id, w) = d.fresh_local(hcp.clone());
            let body = c.mul(b_flipx.clone(), c.chi_(n, s, &w));
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        // congrArg.{1,1} (HCPoint n) Rat (flip(flip x)) x g_fn hinv : gflip_x = bfchi_x
        let body = Expr::apps(
            c.congr_arg.clone(),
            [hcp.clone(), c.rat.clone(), flip_flip, x.clone(), g_fn, hinv],
        );
        let _ = (&gflip_x, &bfchi_x);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let congr_gflip_bfchi = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), g_flip.clone(), bfchi.clone(), pw_gflip],
    );
    // congr_gflip_bfchi : Σ g_flip = Σ bfchi ; symm → Σ bfchi = Σ g_flip
    let bfchi_eq_gflip = c.symm(sum_gflip.clone(), sum_bfchi.clone(), congr_gflip_bfchi);

    // sum_g = fs·capA :
    //   pw_g : g z = fs·(bchi z)   [chi_flip_spectral + mul rearrange]
    //   scaled := fun z => fs·(bchi z) = fun z => fs·((b z)·χ_S z)
    let scaled = {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let bchi_z = c.mul(Expr::app(bf.clone(), z.clone()), c.chi_(n, s, &z));
        let body = c.mul(fs.clone(), bchi_z);
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
    };
    let sum_scaled = c.ssum(n, scaled.clone());

    let pw_g = {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let bz = Expr::app(bf.clone(), z.clone());
        let chi_z = c.chi_(n, s, &z);
        let chi_flip = c.chi_(n, s, &c.hc_flip_(n, &z, i));
        let fs_chi = c.mul(fs.clone(), chi_z.clone());
        let g_z = c.mul(bz.clone(), chi_flip.clone()); // = g z (β)
                                                       // cfs : χ_S(flip z) = fs·χ_S z  [chi_flip_spectral n S z i]
        let cfs = Expr::apps(
            c.chi_flip_spectral.clone(),
            [n.clone(), s.clone(), z.clone(), i.clone()],
        );
        // e1 : (b z)·χ_S(flip z) = (b z)·(fs·χ_S z)   [congrArg (b z·) cfs]
        let bz_fschi = c.mul(bz.clone(), fs_chi.clone());
        let e1 = c.mul_left_congr(&zb, &bz, chi_flip.clone(), fs_chi.clone(), cfs);
        // e2 : (b z)·(fs·χ_S z) = (b z·fs)·χ_S z       [symm (mul_assoc (b z) fs χ_S z)]
        let bz_fs = c.mul(bz.clone(), fs.clone());
        let bzfs_chi = c.mul(bz_fs.clone(), chi_z.clone());
        let assoc = Expr::apps(
            c.rat_mul_assoc.clone(),
            [bz.clone(), fs.clone(), chi_z.clone()],
        ); // (b z·fs)·χ = (b z)·(fs·χ)
        let e2 = c.symm(bzfs_chi.clone(), bz_fschi.clone(), assoc);
        // e3 : (b z·fs)·χ_S z = (fs·b z)·χ_S z         [congrArg (·χ) (mul_comm (b z) fs)]
        let fs_bz = c.mul(fs.clone(), bz.clone());
        let fsbz_chi = c.mul(fs_bz.clone(), chi_z.clone());
        let comm = Expr::apps(c.rat_mul_comm.clone(), [bz.clone(), fs.clone()]); // b z·fs = fs·b z
        let g_mulr = {
            let mut d = EnvDeclBuilder::child_of(&zb);
            let (w_id, w) = d.fresh_local(c.rat.clone());
            let body = c.mul(w.clone(), chi_z.clone());
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let e3 = c.congr(bz_fs.clone(), fs_bz.clone(), g_mulr, comm);
        // e4 : (fs·b z)·χ_S z = fs·((b z)·χ_S z)       [mul_assoc fs (b z) χ_S z]
        let bchi_z = c.mul(bz.clone(), chi_z.clone());
        let fs_bchi = c.mul(fs.clone(), bchi_z.clone());
        let e4 = Expr::apps(
            c.rat_mul_assoc.clone(),
            [fs.clone(), bz.clone(), chi_z.clone()],
        ); // (fs·b z)·χ = fs·(b z·χ)
           // chain: g z = (b z)·(fs·χ) = (b z·fs)·χ = (fs·b z)·χ = fs·(b z·χ)
        let p1 = c.trans(g_z.clone(), bz_fschi.clone(), bzfs_chi.clone(), e1, e2);
        let p2 = c.trans(g_z.clone(), bzfs_chi.clone(), fsbz_chi.clone(), p1, e3);
        let body = c.trans(g_z, fsbz_chi, fs_bchi, p2, e4);
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
    };
    // congr_g_scaled : Σ g = Σ scaled   [subsetSum_congr]
    let congr_g_scaled = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), g.clone(), scaled.clone(), pw_g],
    );
    // smul : Σ scaled = fs·Σ bchi = fs·capA   [subsetSum_smul n fs bchi]
    let smul = Expr::apps(
        c.subset_sum_smul.clone(),
        [n.clone(), fs.clone(), bchi.clone()],
    );
    let fs_a = c.mul(fs.clone(), cap_a.clone());
    // sum_g = Σ scaled = fs·capA
    let sum_g_eq_fsa = c.trans(
        sum_g.clone(),
        sum_scaled.clone(),
        fs_a.clone(),
        congr_g_scaled,
        smul,
    );

    // bfchi = g_flip = g = fs·capA
    let bfchi_eq_g = c.trans(
        sum_bfchi.clone(),
        sum_gflip.clone(),
        sum_g.clone(),
        bfchi_eq_gflip,
        flip_inv,
    );
    c.trans(sum_bfchi.clone(), sum_g, fs_a, bfchi_eq_g, sum_g_eq_fsa)
}
