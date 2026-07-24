// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_compose_legs.rs — the ring-heavy legs
// D (pull-out), E (keystone), F (decoded δ-extraction) of `noiseDensityW_compose`.
// Split out for the 500-line-per-file convention; not a standalone module.

// ── per-y ring identity for legD ─────────────────────────────────────────────
//
// natural(S,T,y) = K_{S,T}·(χ_S y · χ_T y), i.e.
//   (a·(p·q))·(b·(r·s)) = ((a·p)·(b·s))·(q·r)
// with a=wS, p=χ_S x, q=χ_S y, b=wT, r=χ_T y, s=χ_T z.
//
// Chain (all `Rat.mul_*`, kernel-checked, empty closure):
//   (a·(p·q))·(b·(r·s))
//     →[mmmc a (p·q) b (r·s)]            (a·b)·((p·q)·(r·s))
//     →[congr-right ((a·b)·) : (p·q)·(r·s) = (p·s)·(q·r)]   (a·b)·((p·s)·(q·r))
//          [(p·q)·(r·s) →[mmmc p q r s] (p·r)·(q·s) — NO; we need (p·s)·(q·r).
//           Use mmmc p q r s gives (p·r)·(q·s). Instead pair differently:
//           (p·q)·(r·s) →[mmmc p q r s] (p·r)·(q·s) is wrong target. We want
//           the q,r adjacent and p,s adjacent. Use:
//             (p·q)·(r·s) →[congr-right comm r s] (p·q)·(s·r)
//                         →[mmmc p q s r] (p·s)·(q·r). ]
//     →[symm mmmc (a·p) (a? ) ...]  regroup (a·b)·((p·s)·(q·r)) into ((a·p)·(b·s))·(q·r):
//          (a·b)·((p·s)·(q·r))
//            →[symm assoc (a·b) (p·s) (q·r)]  ((a·b)·(p·s))·(q·r)
//            →[congr-left (·(q·r)) : (a·b)·(p·s) = (a·p)·(b·s)]  ((a·p)·(b·s))·(q·r)
//               [(a·b)·(p·s) →[mmmc a b p s] (a·p)·(b·s)]
fn legd_ring(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    p: &Expr,
    q: &Expr,
    b: &Expr,
    r: &Expr,
    s: &Expr,
) -> Expr {
    let pq = c.mul(p.clone(), q.clone());
    let rs = c.mul(r.clone(), s.clone());
    let sr = c.mul(s.clone(), r.clone());
    let qr = c.mul(q.clone(), r.clone());
    let ps = c.mul(p.clone(), s.clone());
    let ab = c.mul(a.clone(), b.clone());
    let ap = c.mul(a.clone(), p.clone());
    let bs = c.mul(b.clone(), s.clone());

    let lhs = c.mul(c.mul(a.clone(), pq.clone()), c.mul(b.clone(), rs.clone()));

    // step1 : (a·(p·q))·(b·(r·s)) = (a·b)·((p·q)·(r·s))    [mmmc a (p·q) b (r·s)]
    let s1 = c.mmmc(a, &pq, b, &rs);
    let after1 = c.mul(ab.clone(), c.mul(pq.clone(), rs.clone()));

    // inner : (p·q)·(r·s) = (p·s)·(q·r)
    //   →[congr-right ((p·q)·) comm r s] (p·q)·(s·r)
    //   →[mmmc p q s r]                  (p·s)·(q·r)
    let comm_rs = c.mul_comm(r, s); // r·s = s·r
    let m_inner_cr = c.mul_right_motive(parent, &pq); // fun w => (p·q)·w
    let inner_c1 = c.congr(rs.clone(), sr.clone(), m_inner_cr, comm_rs);
    let inner_mid = c.mul(pq.clone(), sr.clone());
    let inner_mm = c.mmmc(p, q, s, r); // (p·q)·(s·r) = (p·s)·(q·r)
    let inner = c.trans(
        c.mul(pq.clone(), rs.clone()),
        inner_mid,
        c.mul(ps.clone(), qr.clone()),
        inner_c1,
        inner_mm,
    );

    // step2 : (a·b)·((p·q)·(r·s)) = (a·b)·((p·s)·(q·r))    [congr-right ((a·b)·) inner]
    let m_ab = c.mul_right_motive(parent, &ab);
    let s2 = c.congr(
        c.mul(pq.clone(), rs.clone()),
        c.mul(ps.clone(), qr.clone()),
        m_ab,
        inner,
    );
    let after2 = c.mul(ab.clone(), c.mul(ps.clone(), qr.clone()));

    // step3 : (a·b)·((p·s)·(q·r)) = ((a·b)·(p·s))·(q·r)    [symm assoc (a·b) (p·s) (q·r)]
    let assoc = c.mul_assoc(&ab, &ps, &qr); // ((a·b)·(p·s))·(q·r) = (a·b)·((p·s)·(q·r))
    let after3 = c.mul(c.mul(ab.clone(), ps.clone()), qr.clone());
    let s3 = c.symm(after3.clone(), after2.clone(), assoc);

    // step4 : ((a·b)·(p·s))·(q·r) = ((a·p)·(b·s))·(q·r)
    //   [congr-left (·(q·r)) : (a·b)·(p·s) = (a·p)·(b·s)  (mmmc a b p s)]
    let mm_abps = c.mmmc(a, b, p, s); // (a·b)·(p·s) = (a·p)·(b·s)
    let m_qr = c.mul_left_motive(parent, &qr); // fun w => w·(q·r)
    let s4 = c.congr(
        c.mul(ab.clone(), ps.clone()),
        c.mul(ap.clone(), bs.clone()),
        m_qr,
        mm_abps,
    );
    let target = c.mul(c.mul(ap.clone(), bs.clone()), qr.clone());

    // chain
    let t1 = c.trans(lhs.clone(), after1.clone(), after2.clone(), s1, s2);
    let t2 = c.trans(lhs.clone(), after2.clone(), after3.clone(), t1, s3);
    c.trans(lhs, after3, target, t2, s4)
}

// ── legD : E3 = E4  (per S per T, pull K out of the y-sum) ────────────────────
//
// Per S, per T:  Σ_y natural(S,T,y) = K_{S,T}·(Σ_y χ_S y · χ_T y).
//   →[subsetSum_congr over y, leaf legd_ring]   Σ_y K_{S,T}·(χ_S y · χ_T y)
//   →[subsetSum_smul n K (chi_pair_y_fn)]        K_{S,T}·(Σ_y χ_S y · χ_T y)
fn leg_d(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let h_s = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        // per-S hypothesis: ∀ T, (Σ_y natural) = K·(Σ_y χ_S y χ_T y)   (ss_congr over T)
        let h_t = {
            let mut tb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            // natural y-integrand fn and K·chipair y-integrand fn.
            let nat_y_fn = {
                let mut yb = EnvDeclBuilder::child_of(&tb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = c.nat_summand(&yb, rho, n, x, z, &s, &t, &y);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let kk = c.k_coeff(&tb, rho, n, x, z, &s, &t);
            let kchi_y_fn = {
                let mut yb = EnvDeclBuilder::child_of(&tb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = c.mul(kk.clone(), c.chi_pair(n, &s, &t, &y));
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            // leaf : ∀ y, natural(S,T,y) = K·(χ_S y · χ_T y)   (legd_ring per y)
            let leaf = {
                let mut yb = EnvDeclBuilder::child_of(&tb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let ws = c.weight(&yb, rho, n, &s);
                let wt = c.weight(&yb, rho, n, &t);
                let p = c.chi_(n, &s, x); // χ_S x
                let q = c.chi_(n, &s, &y); // χ_S y
                let r = c.chi_(n, &t, &y); // χ_T y
                let ss = c.chi_(n, &t, z); // χ_T z
                let body = legd_ring(c, &yb, &ws, &p, &q, &wt, &r, &ss);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            // legD-1 : Σ_y natural = Σ_y K·chipair
            let congr_y = c.ss_congr(n, &nat_y_fn, &kchi_y_fn, leaf);
            // legD-2 : Σ_y K·chipair = K·Σ_y chipair   (subsetSum_smul n K chi_pair_y_fn)
            let chipair_fn = c.chi_pair_y_fn(&tb, n, &s, &t);
            let smul = c.ss_smul(n, &kk, &chipair_fn);
            let lhs_t = c.ssum(n, nat_y_fn);
            let mid_t = c.ssum(n, kchi_y_fn);
            let rhs_t = c.mul(kk.clone(), c.ssum(n, chipair_fn));
            let body = c.trans(lhs_t, mid_t, rhs_t, congr_y, smul);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
        };
        // per-S: ss_congr over T from E3's T-integrand to E4's T-integrand.
        let e3_t_fn = e3_t_fn(c, &sb, rho, n, x, z, &s);
        let e4_t_fn = e4_t_fn(c, &sb, rho, n, x, z, &s);
        let body = c.ss_congr(n, &e3_t_fn, &e4_t_fn, h_t);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    c.ss_congr(
        n,
        &c.e3_s_fn(parent, rho, n, x, z),
        &c.e4_s_fn(parent, rho, n, x, z),
        h_s,
    )
}

/// E3 inner T-integrand `fun T => Σ_y natural(S,T,y)` at fixed `S`.
fn e3_t_fn(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
    s: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let mut tb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = tb.fresh_local(hcp.clone());
    let y_fn = {
        let mut yb = EnvDeclBuilder::child_of(&tb);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = c.nat_summand(&yb, rho, n, x, z, s, &t, &y);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let body = c.ssum(n, y_fn);
    tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, body))
}

/// E4 inner T-integrand `fun T => K_{S,T}·(Σ_y χ_S y · χ_T y)` at fixed `S`.
fn e4_t_fn(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
    s: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let mut tb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = tb.fresh_local(hcp.clone());
    let kk = c.k_coeff(&tb, rho, n, x, z, s, &t);
    let ysum = c.ssum(n, c.chi_pair_y_fn(&tb, n, s, &t));
    let body = c.mul(kk, ysum);
    tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, body))
}

// ── legE : E4 = E5  (per S per T, keystone) ──────────────────────────────────
//
// Per S, per T:  K_{S,T}·(Σ_y χ_S y · χ_T y) = K_{S,T}·(cube·ind[SΔT=∅])
//   [congr-right (K·) (subsetSum_chi_pair_diag n S T)].
fn leg_e(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let h_s = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let h_t = {
            let mut tb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let kk = c.k_coeff(&tb, rho, n, x, z, &s, &t);
            let ysum = c.ssum(n, c.chi_pair_y_fn(&tb, n, &s, &t));
            let diag = c.mul(c.cube(n), c.empty_ind(&tb, n, &s, &t));
            // keystone : Σ_y χ_S y·χ_T y = cube·ind[SΔT=∅]
            let ks = c.keystone(n, &s, &t);
            let m_k = c.mul_right_motive(&tb, &kk); // fun w => K·w
            let body = c.congr(ysum, diag, m_k, ks);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
        };
        let e4_t = e4_t_fn(c, &sb, rho, n, x, z, &s);
        let e5_t = c.e5_t_fn(&sb, rho, n, x, z, &s);
        let body = c.ss_congr(n, &e4_t, &e5_t, h_t);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    c.ss_congr(
        n,
        &c.e4_s_fn(parent, rho, n, x, z),
        &c.e5_s_fn(parent, rho, n, x, z),
        h_s,
    )
}

// ── legF : E5 = E6  (decoded δ-extraction over T, per S = hcDecode jS) ────────
//
// E5 = subsetSum n (e5_s_fn)  ≡ Fin.sum (2^n) (fun jS => e5_s_fn (hcDecode jS))
// E6 = subsetSum n (e6_s_fn)  ≡ Fin.sum (2^n) (fun jS => e6_s_fn (hcDecode jS))
// `Fin.sum_congr (2^n) (e5∘decode) (e6∘decode) (fun jS => per-jS)` bridges them;
// both subsetSum endpoints are def-eq to the Fin.sum forms (subsetSum reducible).
//
// Per jS (S := hcDecode n jS):
//   Σ_T K_{S,T}·(cube·ind[SΔT=∅]) = cube·K_{S,S}.
//   This is `subsetSum_subset_diag_extract_scaled n jS (fun T => K_{S,T})`:
//   its LHS integrand `fun T => (fun T => K_{S,T}) T · (cube·ind[(hcDecode jS)ΔT=∅])`
//   is def-eq to e5_s_fn (hcDecode jS), and its RHS `cube·(fun T => K_{S,T})(hcDecode jS)`
//   = cube·K_{S,S} is def-eq to e6_s_fn (hcDecode jS).
fn leg_f(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);

    // decoded E5 / E6 integrands : fun (jS : Fin 2^n) => eX_s_fn (hcDecode jS).
    let dec5 = decoded_s_fn(c, parent, rho, n, x, z, true);
    let dec6 = decoded_s_fn(c, parent, rho, n, x, z, false);

    // per-jS proof.
    let pw = {
        let mut jb = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = jb.fresh_local(fin_p.clone());
        let s = c.hc_decode(n, &j);
        // f := fun (T : HCPoint n) => K_{S,T}   (the coefficient as a function of T).
        let kf = {
            let mut tb = EnvDeclBuilder::child_of(&jb);
            let hcp = c.hcpoint_of(n);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let body = c.k_coeff(&tb, rho, n, x, z, &s, &t);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, body))
        };
        // scaled extraction at pivot jS, function kf.
        let pf = c.diag_scaled(n, &j, &kf);
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), pf))
    };

    c.fin_sum_congr(&pp, &dec5, &dec6, pw)
}

/// `fun (jS : Fin 2^n) => eX_s_fn (hcDecode n jS)` — the decoded outer integrand.
/// `is_e5 = true` builds the E5 integrand; `false` the E6 integrand.
fn decoded_s_fn(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
    is_e5: bool,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let mut jb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = jb.fresh_local(fin_p.clone());
    let s = c.hc_decode(n, &j);
    let body = if is_e5 {
        c.ssum(n, c.e5_t_fn(&jb, rho, n, x, z, &s))
    } else {
        let kk = c.k_coeff(&jb, rho, n, x, z, &s, &s);
        c.mul(c.cube(n), kk)
    };
    jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p, body))
}
