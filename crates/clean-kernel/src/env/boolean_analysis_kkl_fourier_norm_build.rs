// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Term builders for the Fourier-normalization bridge. `include!`d into
// boolean_analysis_kkl_fourier_norm.rs — shares its `FourierNormConsts` and
// imports. Split out only for the 500-line-per-file convention; not a standalone
// module. (Regular `//` comments: inner doc `//!` is not allowed at an
// `include!` site.)

/// `∀ (n : Nat) (f : BoolFn n) (S : HCPoint n),
///    subsetSum n (fun x => pm(f x)·χ_S x) = (powNat 2 n)·FourierCoefficient n f S`.
fn bridge_type(c: &FourierNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let z = c.z_sum(&b, &n, &f, &s);
    let p = c.pow2(&n);
    let fhat = c.fourier_of(&n, &f, &s);
    let concl = c.eq_rat(z, c.mul(p, fhat));

    let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `λ n f S => symm <P·(Z·inv L) = Z>`. The kernel accepts it against
/// `Z = P·f̂(S)` because `P·(Z·inv L)` is def-eq to `P·f̂(S)`.
fn bridge_value(c: &FourierNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    // ── named quantities ──
    let z = c.z_sum(&b, &n, &f, &s); // Z := subsetSum (pm∘f · χ_S)
    let p = c.pow2(&n); // P := powNat 2 n
    let lit = c.lit_pow2(&n); // L := mk(ofNat (Nat.pow 2 n)) 1
    let inv_l = c.inv(lit.clone()); // inv L
    let inv_p = c.inv(p.clone()); // inv P
    let one = c.one();

    // intermediate products.
    let z_invl = c.mul(z.clone(), inv_l.clone()); // Z·inv L  (≡ f̂(S))
    let z_invp = c.mul(z.clone(), inv_p.clone()); // Z·inv P
    let p_z_invl = c.mul(p.clone(), z_invl.clone()); // P·(Z·inv L)  (≡ P·f̂(S))
    let p_z_invp = c.mul(p.clone(), z_invp.clone()); // P·(Z·inv P)
    let p_invp = c.mul(p.clone(), inv_p.clone()); // P·inv P
    let z_p_invp = c.mul(z.clone(), p_invp.clone()); // Z·(P·inv P)
    let z_one = c.mul(z.clone(), one.clone()); // Z·1

    // ── leaves ──
    // h_PL : P = L  (powNat_two_eq_natCast n).
    let h_pl = c.pow_two_natcast_at(&n);
    // h_invLP : inv L = inv P  := symm (congrArg inv h_PL : inv P = inv L).
    let h_invpl = c.congr_inv(p.clone(), lit.clone(), h_pl); // inv P = inv L
    let h_invlp = c.symm_rat(inv_p.clone(), inv_l.clone(), h_invpl); // inv L = inv P

    // P > 0, P ≠ 0, P·inv P = 1.
    let h_p_pos = c.pow_two_pos(&n);
    let h_p_ne = c.ne_at(p.clone(), h_p_pos);
    let p_invp_one = c.mul_inv_cancel_at(p.clone(), h_p_ne); // P·inv P = 1

    // ── chain : P·(Z·inv L) → P·(Z·inv P) → Z·(P·inv P) → Z·1 → Z ──
    // s1 : P·(Z·inv L) = P·(Z·inv P)   congr P·_ (congr Z·_ (inv L = inv P)).
    let inner_s1 = c.congr_l(&b, &z, inv_l.clone(), inv_p.clone(), h_invlp); // Z·inv L = Z·inv P
    let s1 = c.congr_l(&b, &p, z_invl.clone(), z_invp.clone(), inner_s1);
    // s2 : P·(Z·inv P) = Z·(P·inv P)   reassoc c·(b·d)=b·(c·d), c:=P b:=Z d:=inv P.
    let s2 = reassoc_cbd_bcd(c, &b, &p, &z, &inv_p);
    // s3 : Z·(P·inv P) = Z·1   congr Z·_ (P·inv P = 1).
    let s3 = c.congr_l(&b, &z, p_invp.clone(), one.clone(), p_invp_one);
    // s4 : Z·1 = Z   mul_one Z.
    let s4 = c.mul_one_at(z.clone());

    // assemble : P·(Z·inv L) = Z.
    let fwd = {
        let ch = c.trans_rat(p_z_invl.clone(), p_z_invp.clone(), z_p_invp.clone(), s1, s2);
        let ch = c.trans_rat(p_z_invl.clone(), z_p_invp.clone(), z_one.clone(), ch, s3);
        c.trans_rat(p_z_invl.clone(), z_one.clone(), z.clone(), ch, s4)
    };
    // symm : Z = P·(Z·inv L)  ≡  Z = P·f̂(S)  (def-eq retype accepted by kernel).
    //   fwd : P·(Z·inv L) = Z ; symm_rat(a=P·(Z·inv L), b=Z, fwd) : Z = P·(Z·inv L).
    let proof = c.symm_rat(p_z_invl.clone(), z.clone(), fwd);

    let e = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `c·(b·d) = b·(c·d)` — move the outer factor `c` inward past `b`.
///   `c·(b·d) →[symm assoc c b d] (c·b)·d →[congr (_·d) comm c b] (b·c)·d
///          →[assoc b c d] b·(c·d)`.
fn reassoc_cbd_bcd(
    c: &FourierNormConsts,
    parent: &EnvDeclBuilder,
    cc: &Expr,
    bb: &Expr,
    d: &Expr,
) -> Expr {
    let cbd = c.mul(cc.clone(), c.mul(bb.clone(), d.clone())); // c·(b·d)
    let cb_d = c.mul(c.mul(cc.clone(), bb.clone()), d.clone()); // (c·b)·d
    let bc_d = c.mul(c.mul(bb.clone(), cc.clone()), d.clone()); // (b·c)·d
    let bcd = c.mul(bb.clone(), c.mul(cc.clone(), d.clone())); // b·(c·d)
                                                               // s1 : c·(b·d) = (c·b)·d   symm (assoc c b d).
    let s1 = c.symm_rat(
        cb_d.clone(),
        cbd.clone(),
        c.assoc(cc.clone(), bb.clone(), d.clone()),
    );
    // s2 : (c·b)·d = (b·c)·d   congr (_·d) (comm c b).
    let s2 = {
        let f = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = dd.fresh_local(c.rat.clone());
            let body = c.mul(z, d.clone());
            dd.finish_child(dd.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        Expr::apps(
            c.congr_arg1.clone(),
            [
                c.rat.clone(),
                c.rat.clone(),
                c.mul(cc.clone(), bb.clone()),
                c.mul(bb.clone(), cc.clone()),
                f,
                c.comm(cc.clone(), bb.clone()),
            ],
        )
    };
    // s3 : (b·c)·d = b·(c·d)   assoc b c d.
    let s3 = c.assoc(bb.clone(), cc.clone(), d.clone());
    let t = c.trans_rat(cbd.clone(), cb_d.clone(), bc_d.clone(), s1, s2);
    c.trans_rat(cbd, bc_d, bcd, t, s3)
}
