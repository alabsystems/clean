// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose.rs — RUNG 1 NORMALIZED: the
// `W_norm = Σ_S levelWt·Ahat²` form, reconciling the un-normalized `cube = 2^n`
// footprint of `noise_two_norm_spectral_third` with the `inv(8^n)` normalization
// the dual-HC aggregate consumes. Shares `ComposeConsts`. Split out only for the
// 500-line-per-file convention; not a standalone module. (Regular `//`
// comments: inner doc `//!` is not allowed at an `include!` site.)
//
// ## What this proves
//
//   BoolAnalysis.noise_two_norm_spectral_third_norm :
//     ∀ (n : Nat) (g : HCPoint n → Rat),
//       Rat.mul (subsetSum n (fun y => noiseOp(1/3) n g y · noiseOp(1/3) n g y))
//               (Rat.inv (Rat.powNat 8 n))
//         = subsetSum n (fun S => levelWt (1/3) n S · (Ahat g S · Ahat g S))
//
// where `Ahat g S := (A g S)·inv(2^n)` and `A g S := subsetSum n (fun x => g x·χ_S x)`
// is the un-normalized Fourier coefficient. i.e. `W_norm = Σ_S levelWt·Ahat²`.
//
// ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//
// From RUNG 1 (`noise_two_norm_spectral_third`):
//   `LHS_un := Σ_y (T g y)² = cube · P`,  `P := Σ_S w_pow·(A·A)`,
//   `cube := mk(ofNat(Nat.pow 2 n)) 1`,  `w_pow := (1/3)^|S|·(1/3)^|S|`.
//
//   1. `cube = 2^n` — `Rat.powNat_two_eq_natCast n` (symm). [2^n := powNat 2 n.]
//   2. per-S `A·A = 4^n·(Ahat·Ahat)` (`aa_eq`):
//        `4^n·(Ahat·Ahat) = 4^n·((A·A)·(inv2·inv2))`   congr (4^n·_) mmmc
//                         = (A·A)·(4^n·(inv2·inv2))     reassoc c·(b·d)=b·(c·d)
//                         = (A·A)·1                     congr ((A·A)·_) four_inv_two_sq_cancel
//                         = A·A                          mul_one
//      symm ⟹ `A·A = 4^n·(Ahat·Ahat)`.
//   3. per-S `w_pow = levelWt (1/3) n S` (`wl_eq`):
//        `(1/3)^|S|·(1/3)^|S| = powNat((1/3)·(1/3)) |S|`  symm (powNat_mul_base)
//                            = levelWt (1/3) n S          symm (levelWt_eq_powNat)
//      (`|S| := popcount_inline ≡ setSizeNat n S` def-eq).
//   4. `P = 4^n · Q`,  `Q := Σ_S levelWt·(Ahat·Ahat)`:
//        P = Σ_S w_pow·(A·A) = Σ_S 4^n·(w_pow·(Ahat·Ahat))   ss_congr (aa per S + reassoc)
//          = 4^n · Σ_S w_pow·(Ahat·Ahat)                     ss_smul
//          = 4^n · Q                                          ss_congr (wl per S)
//   5. `W_norm = (cube·P)·inv8 = ((cube·4^n)·Q)·inv8
//             = ((2^n·4^n)·inv8)·Q = 1·Q = Q`               (powNat_two_eq_natCast,
//      ring reassoc, `powNat_two_four_inv_eight_cancel`, `one_mul`).
//
// Every leaf (`noise_two_norm_spectral_third`, `Rat.powNat_two_eq_natCast`,
// `Rat.powNat_mul_base`, `BoolAnalysis.levelWt_eq_powNat`,
// `BoolAnalysis.four_inv_two_sq_cancel`, `BoolAnalysis.powNat_two_four_inv_eight_cancel`,
// `subsetSum_smul`, `subsetSum_congr`, `Rat.mul_mul_mul_comm`, `Rat.mul_one`,
// `Rat.one_mul`, `Rat.mul_assoc`/`mul_comm`, `congrArg`/`Eq.*`) is `Constructive`
// with empty admitted-axiom closure, so the normalized rung is too. No axiom is
// added or removed. Idempotent.

impl ComposeConsts {
    /// `2^n := Rat.powNat (mk(ofNat 2) 1) n` (powNat carrier — matches the
    /// cancellation lemmas + the dual-HC aggregate's `8^n`).
    fn pownat_lit(&self, k: usize, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.rat_lit(k), n.clone()])
    }
    /// `Rat.mk (Int.ofNat k) 1`.
    fn rat_lit(&self, k: usize) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nat), one],
        )
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.inv"), vec![]), a)
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul_at(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), a)
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one_at(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), a)
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc_at(&self, a: Expr, b: Expr, cc: Expr, dd: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a, b, cc, dd],
        )
    }
    /// `levelWt (1/3) n S`.
    fn levelwt(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.levelWt"), vec![]),
            [self.third(), n.clone(), s.clone()],
        )
    }
    /// `Ahat g S := (A g S)·inv(2^n)` — the normalized Fourier coefficient.
    fn ahat(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let a = self.a_coeff(parent, n, g, s);
        self.mul(a, self.inv(self.pownat_lit(2, n)))
    }

    /// Per-S leaf `wl_eq S : (1/3)^|S|·(1/3)^|S| = levelWt (1/3) n S`.
    /// `(1/3)^pc·(1/3)^pc = powNat((1/3)·(1/3)) pc` (symm powNat_mul_base) =
    /// `levelWt (1/3) n S` (symm levelWt_eq_powNat; pc ≡ setSizeNat def-eq).
    fn wl_eq(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let pc = self.popcount_inline(parent, n, s);
        let third = self.third();
        let w_third = self.pow(&third, &pc); // (1/3)^pc
        let w_pow = self.mul(w_third.clone(), w_third.clone()); // (1/3)^pc·(1/3)^pc
        let third_sq = self.mul(third.clone(), third.clone()); // (1/3)·(1/3)
        let psq = self.pow(&third_sq, &pc); // powNat((1/3)·(1/3)) pc
                                            // pmb : powNat((1/3)·(1/3)) pc = (1/3)^pc·(1/3)^pc  (powNat_mul_base third third pc).
        let pmb = Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_mul_base"), vec![]),
            [third.clone(), third.clone(), pc.clone()],
        );
        // symm pmb : (1/3)^pc·(1/3)^pc = powNat((1/3)·(1/3)) pc.
        let pmb_symm = self.symm(psq.clone(), w_pow.clone(), pmb);
        // lep : levelWt (1/3) n S = powNat((1/3)·(1/3)) (setSizeNat n S)  ≡ psq (pc≡setSizeNat).
        let lvl = self.levelwt(n, s);
        let lep = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.levelWt_eq_powNat"), vec![]),
            [third.clone(), n.clone(), s.clone()],
        );
        // symm lep : powNat((1/3)·(1/3)) (setSizeNat n S) = levelWt ; typed as psq = lvl (def-eq pc).
        let lep_symm = self.symm(lvl.clone(), psq.clone(), lep);
        // chain : w_pow = psq = lvl.
        self.trans(w_pow, psq, lvl, pmb_symm, lep_symm)
    }

    /// Per-S leaf `aa_eq : A·A = 4^n·(Ahat·Ahat)`  (`Ahat := A·inv(2^n)`).
    /// Built as the symm of `4^n·(Ahat·Ahat) = A·A`.
    fn aa_eq(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let a = self.a_coeff(parent, n, g, s);
        let inv2 = self.inv(self.pownat_lit(2, n));
        let p4 = self.pownat_lit(4, n);
        let ahat = self.mul(a.clone(), inv2.clone()); // A·inv2
        let aa = self.mul(a.clone(), a.clone()); // A·A
        let inv2_inv2 = self.mul(inv2.clone(), inv2.clone()); // inv2·inv2
        let ahat_ahat = self.mul(ahat.clone(), ahat.clone()); // Ahat·Ahat
        let aa_inv2inv2 = self.mul(aa.clone(), inv2_inv2.clone()); // (A·A)·(inv2·inv2)

        // t0 = 4^n·(Ahat·Ahat).
        let t0 = self.mul(p4.clone(), ahat_ahat.clone());
        // mmmc : (A·inv2)·(A·inv2) = (A·A)·(inv2·inv2).
        let mmmc = self.mmmc_at(a.clone(), inv2.clone(), a.clone(), inv2.clone());
        // s01 : 4^n·(Ahat·Ahat) = 4^n·((A·A)·(inv2·inv2))   congr (4^n·_) mmmc.
        let t1 = self.mul(p4.clone(), aa_inv2inv2.clone());
        let mot4 = self.mul_left_motive(parent, &p4);
        let s01 = self.congr_rat(ahat_ahat.clone(), aa_inv2inv2.clone(), mot4, mmmc);
        // s12 : 4^n·((A·A)·(inv2·inv2)) = (A·A)·(4^n·(inv2·inv2))   reassoc c·(b·d)=b·(c·d).
        //   c := 4^n, b := A·A, d := inv2·inv2.
        let t2 = self.mul(aa.clone(), self.mul(p4.clone(), inv2_inv2.clone()));
        let s12 = self.reassoc_cbd_bcd(parent, &p4, &aa, &inv2_inv2);
        // s23 : (A·A)·(4^n·(inv2·inv2)) = (A·A)·1   congr ((A·A)·_) four_inv_two_sq_cancel.
        let p4_inv = self.mul(p4.clone(), inv2_inv2.clone());
        let fitc = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.four_inv_two_sq_cancel"),
                vec![],
            ),
            [n.clone()],
        ); // 4^n·(inv2·inv2) = 1
        let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let t3 = self.mul(aa.clone(), one.clone());
        let mot_aa = self.mul_left_motive(parent, &aa);
        let s23 = self.congr_rat(p4_inv.clone(), one.clone(), mot_aa, fitc);
        // s34 : (A·A)·1 = A·A   mul_one (A·A).
        let s34 = self.mul_one_at(aa.clone());
        // chain forward : 4^n·(Ahat·Ahat) = A·A.
        let c01 = self.trans(t0.clone(), t1.clone(), t2.clone(), s01, s12);
        let c012 = self.trans(t0.clone(), t2.clone(), t3.clone(), c01, s23);
        let fwd = self.trans(t0.clone(), t3.clone(), aa.clone(), c012, s34); // 4^n·Ahat² = A·A
                                                                             // @Eq.symm Rat t0 aa fwd : aa = t0  (fwd : t0 = aa ⟹ A·A = 4^n·Ahat²).
        self.symm(t0, aa, fwd)
    }

    /// `c·(b·d) = b·(c·d)` — move the outer factor `c` inward past `b`.
    ///   `c·(b·d) →[symm assoc c b d] (c·b)·d →[congr (_·d) comm c b] (b·c)·d
    ///          →[assoc b c d] b·(c·d)`.
    fn reassoc_cbd_bcd(&self, parent: &EnvDeclBuilder, cc: &Expr, b: &Expr, d: &Expr) -> Expr {
        let cbd = self.mul(cc.clone(), self.mul(b.clone(), d.clone())); // c·(b·d)
        let cb_d = self.mul(self.mul(cc.clone(), b.clone()), d.clone()); // (c·b)·d
        let bc_d = self.mul(self.mul(b.clone(), cc.clone()), d.clone()); // (b·c)·d
        let bcd = self.mul(b.clone(), self.mul(cc.clone(), d.clone())); // b·(c·d)
                                                                        // s1 : c·(b·d) = (c·b)·d   symm (assoc c b d).
        let s1 = self.symm(
            cb_d.clone(),
            cbd.clone(),
            self.mul_assoc(cc.clone(), b.clone(), d.clone()),
        );
        // s2 : (c·b)·d = (b·c)·d   congr (_·d) (comm c b).
        let mot = self.mul_right_motive(parent, d);
        let s2 = self.congr_rat(
            self.mul(cc.clone(), b.clone()),
            self.mul(b.clone(), cc.clone()),
            mot,
            self.mul_comm(cc.clone(), b.clone()),
        );
        // s3 : (b·c)·d = b·(c·d)   assoc b c d.
        let s3 = self.mul_assoc(b.clone(), cc.clone(), d.clone());
        let t = self.trans(cbd.clone(), cb_d.clone(), bc_d.clone(), s1, s2);
        self.trans(cbd, bc_d, bcd, t, s3)
    }

    /// P-integrand `fun S => 4^n·(w_pow S·(Ahat·Ahat))` — the middle integrand of
    /// step 4 leg A (`Σ_S w_pow·(A·A) → Σ_S 4^n·(w_pow·(Ahat·Ahat))`).
    fn p_mid_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pc = self.popcount_inline(&sb, n, &s);
        let w_third = self.pow(&self.third(), &pc);
        let w_pow = self.mul(w_third.clone(), w_third);
        let ahat = self.ahat(&sb, n, g, &s);
        let ahat_ahat = self.mul(ahat.clone(), ahat);
        let body = self.mul(self.pownat_lit(4, n), self.mul(w_pow, ahat_ahat));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// Inner P-integrand `fun S => w_pow S·(Ahat·Ahat)` (after `4^n` pulled out).
    fn p_inner_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pc = self.popcount_inline(&sb, n, &s);
        let w_third = self.pow(&self.third(), &pc);
        let w_pow = self.mul(w_third.clone(), w_third);
        let ahat = self.ahat(&sb, n, g, &s);
        let body = self.mul(w_pow, self.mul(ahat.clone(), ahat));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// Q-integrand `fun S => levelWt (1/3) n S·(Ahat·Ahat)` — the TARGET RHS.
    fn q_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let lvl = self.levelwt(n, &s);
        let ahat = self.ahat(&sb, n, g, &s);
        let body = self.mul(lvl, self.mul(ahat.clone(), ahat));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

/// `∀ (n : Nat) (g : HCPoint n → Rat),
///    (Σ_y (T g y)·(T g y))·inv(8^n) = Σ_S levelWt (1/3) n S·(Ahat·Ahat)`.
fn two_norm_spectral_norm_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);

    let lhs_fn = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let tgy = c.op_apply(&c.third(), &n, &g, &y);
        let body = c.mul(tgy.clone(), tgy);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs_un = c.ssum(&n, lhs_fn);
    let inv8 = c.inv(c.pownat_lit(8, &n));
    let w_norm = c.mul(lhs_un, inv8);
    let q = c.ssum(&n, c.q_fn(&b, &n, &g));
    let concl = c.eq_rat(w_norm, q);

    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `λ n g => <W_norm = (cube·P)·inv8 = ((cube·4^n)·Q)·inv8 = 1·Q = Q>`.
fn two_norm_spectral_norm_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);

    // ── named quantities ──
    let lhs_fn = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let tgy = c.op_apply(&c.third(), &n, &g, &y);
        let body = c.mul(tgy.clone(), tgy);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs_un = c.ssum(&n, lhs_fn); // Σ_y (T g y)²
    let inv8 = c.inv(c.pownat_lit(8, &n));
    let cube = c.cube(&n); // mk(ofNat(Nat.pow 2 n)) 1
    let p2 = c.pownat_lit(2, &n);
    let p4 = c.pownat_lit(4, &n);

    let p = c.ssum(&n, c.spectral_s_fn(&b, &n, &g)); // P = Σ_S w_pow·(A·A)
    let p_mid = c.ssum(&n, c.p_mid_fn(&b, &n, &g)); // Σ_S 4^n·(w_pow·Ahat²)
    let p_inner = c.ssum(&n, c.p_inner_fn(&b, &n, &g)); // Σ_S w_pow·Ahat²
    let q = c.ssum(&n, c.q_fn(&b, &n, &g)); // Q = Σ_S levelWt·Ahat²

    // ── step 4: P = 4^n·Q ──
    // legA : P = Σ_S 4^n·(w_pow·Ahat²)   ss_congr over per-S (aa + reassoc).
    let leg_a_hyp = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        // per-S: w_pow·(A·A) = 4^n·(w_pow·(Ahat·Ahat)).
        let pc = c.popcount_inline(&sb, &n, &s);
        let w_third = c.pow(&c.third(), &pc);
        let w_pow = c.mul(w_third.clone(), w_third);
        let a = c.a_coeff(&sb, &n, &g, &s);
        let aa = c.mul(a.clone(), a.clone());
        let inv2 = c.inv(c.pownat_lit(2, &n));
        let ahat = c.mul(a.clone(), inv2);
        let ahat_ahat = c.mul(ahat.clone(), ahat);
        // s1 : w_pow·(A·A) = w_pow·(4^n·(Ahat·Ahat))   congr (w_pow·_) (aa_eq).
        let aa_eq = c.aa_eq(&sb, &n, &g, &s); // A·A = 4^n·(Ahat·Ahat)
        let rhs_in = c.mul(p4.clone(), ahat_ahat.clone());
        let mot_w = c.mul_left_motive(&sb, &w_pow);
        let s1 = c.congr_rat(aa.clone(), rhs_in.clone(), mot_w, aa_eq);
        let lhs_s = c.mul(w_pow.clone(), aa.clone());
        let mid_s = c.mul(w_pow.clone(), rhs_in.clone());
        // s2 : w_pow·(4^n·(Ahat·Ahat)) = 4^n·(w_pow·(Ahat·Ahat))   reassoc a·(c·b)=c·(a·b).
        //   here a := w_pow, c := 4^n, b := Ahat·Ahat.
        let s2 = c.reassoc_acb_cab(&sb, &w_pow, &p4, &ahat_ahat);
        let tgt_s = c.mul(p4.clone(), c.mul(w_pow.clone(), ahat_ahat.clone()));
        let body = c.trans(lhs_s, mid_s, tgt_s, s1, s2);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg_a = c.ss_congr(
        &n,
        &c.spectral_s_fn(&b, &n, &g),
        &c.p_mid_fn(&b, &n, &g),
        leg_a_hyp,
    );
    // legB : Σ_S 4^n·(w_pow·Ahat²) = 4^n·Σ_S w_pow·Ahat²   ss_smul.
    let leg_b = c.ss_smul(&n, &p4, &c.p_inner_fn(&b, &n, &g));
    let p4_pinner = c.mul(p4.clone(), p_inner.clone());
    // legC : Σ_S w_pow·Ahat² = Σ_S levelWt·Ahat² = Q   ss_congr over per-S (wl).
    let leg_c_hyp = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let ahat = c.ahat(&sb, &n, &g, &s);
        let ahat_ahat = c.mul(ahat.clone(), ahat);
        let pc = c.popcount_inline(&sb, &n, &s);
        let w_third = c.pow(&c.third(), &pc);
        let w_pow = c.mul(w_third.clone(), w_third);
        let lvl = c.levelwt(&n, &s);
        // wl : w_pow = levelWt ; congr (_·(Ahat·Ahat)).
        let wl = c.wl_eq(&sb, &n, &s);
        let mot = c.mul_right_motive(&sb, &ahat_ahat);
        let body = c.congr_rat(w_pow, lvl, mot, wl);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg_c = c.ss_congr(
        &n,
        &c.p_inner_fn(&b, &n, &g),
        &c.q_fn(&b, &n, &g),
        leg_c_hyp,
    );
    // 4^n·Σ_S w_pow·Ahat² = 4^n·Q   congr (4^n·_) legC.
    let mot_p4 = c.mul_left_motive(&b, &p4);
    let p4_q = c.mul(p4.clone(), q.clone());
    let leg_c_scaled = c.congr_rat(p_inner.clone(), q.clone(), mot_p4, leg_c);
    // P = Σmid = 4^n·Σinner = 4^n·Q.
    let p_eq_a = c.trans(p.clone(), p_mid.clone(), p4_pinner.clone(), leg_a, leg_b);
    let p_eq_4q = c.trans(
        p.clone(),
        p4_pinner.clone(),
        p4_q.clone(),
        p_eq_a,
        leg_c_scaled,
    ); // P = 4^n·Q

    // ── step 5: W_norm = Q ──
    // r1 : LHS_un = cube·P   (rung1).
    let r1 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.noise_two_norm_spectral_third"),
            vec![],
        ),
        [n.clone(), g.clone()],
    );
    let cube_p = c.mul(cube.clone(), p.clone());
    // w0 : W_norm = (cube·P)·inv8   congr (_·inv8) r1.
    let mot_inv8 = c.mul_right_motive(&b, &inv8);
    let w_norm = c.mul(lhs_un.clone(), inv8.clone());
    let w0 = c.congr_rat(lhs_un.clone(), cube_p.clone(), mot_inv8, r1);
    // w1 : (cube·P)·inv8 = (cube·(4^n·Q))·inv8   congr (_·inv8) (congr (cube·_) (P=4^n·Q)).
    let cube_4q = c.mul(cube.clone(), p4_q.clone());
    let mot_cube = c.mul_left_motive(&b, &cube);
    let inner_w1 = c.congr_rat(p.clone(), p4_q.clone(), mot_cube, p_eq_4q);
    let mot_inv8b = c.mul_right_motive(&b, &inv8);
    let w1 = c.congr_rat(cube_p.clone(), cube_4q.clone(), mot_inv8b, inner_w1);
    // w2 : (cube·(4^n·Q))·inv8 = ((cube·4^n)·Q)·inv8   congr (_·inv8) (symm assoc cube 4^n Q).
    let cube4 = c.mul(cube.clone(), p4.clone());
    let cube4_q = c.mul(cube4.clone(), q.clone()); // (cube·4^n)·Q
    let assoc_cube = c.mul_assoc(cube.clone(), p4.clone(), q.clone()); // (cube·4^n)·Q = cube·(4^n·Q)
    let assoc_cube_symm = c.symm(cube4_q.clone(), cube_4q.clone(), assoc_cube);
    let mot_inv8c = c.mul_right_motive(&b, &inv8);
    let w2 = c.congr_rat(cube_4q.clone(), cube4_q.clone(), mot_inv8c, assoc_cube_symm);
    // w3 : ((cube·4^n)·Q)·inv8 = ((cube·4^n)·inv8)·Q   reassoc (a·b)·c = (a·c)·b.
    //   a := cube·4^n, b := Q, c := inv8.
    let cube4_inv8 = c.mul(cube4.clone(), inv8.clone());
    let cube4inv8_q = c.mul(cube4_inv8.clone(), q.clone());
    let w3 = c.reassoc_ab_c_ac_b(&b, &cube4, &q, &inv8);
    // w4 : ((cube·4^n)·inv8)·Q = ((2^n·4^n)·inv8)·Q   congr (_·Q) (congr (_·inv8) (cube=2^n)).
    //   cube = 2^n : symm (powNat_two_eq_natCast n).
    let p2p4 = c.mul(p2.clone(), p4.clone());
    let p2p4_inv8 = c.mul(p2p4.clone(), inv8.clone());
    let p2p4inv8_q = c.mul(p2p4_inv8.clone(), q.clone());
    let pte = Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_two_eq_natCast"), vec![]),
        [n.clone()],
    ); // pte : 2^n = mk(ofNat(Nat.pow 2 n)) 1 = cube
       // symm(l=cube, r=p2, h=pte : p2=cube) : cube = p2  (convention: symm l r (h:r=l) gives l=r).
    let cube_eq_p2 = c.symm(p2.clone(), cube.clone(), pte); // cube = 2^n
                                                            // congr (_·4^n) (cube=2^n) : cube·4^n = 2^n·4^n.
    let mot_p4r = c.mul_right_motive(&b, &p4);
    let cube4_eq = c.congr_rat(cube.clone(), p2.clone(), mot_p4r, cube_eq_p2);
    // congr (_·inv8) : (cube·4^n)·inv8 = (2^n·4^n)·inv8.
    let mot_inv8d = c.mul_right_motive(&b, &inv8);
    let inner_w4 = c.congr_rat(cube4.clone(), p2p4.clone(), mot_inv8d, cube4_eq);
    // congr (_·Q).
    let mot_qr = c.mul_right_motive(&b, &q);
    let w4 = c.congr_rat(cube4_inv8.clone(), p2p4_inv8.clone(), mot_qr, inner_w4);
    // w5 : ((2^n·4^n)·inv8)·Q = 1·Q   congr (_·Q) (step1 : (2^n·4^n)·inv8 = 1).
    let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let one_q = c.mul(one.clone(), q.clone());
    let step1 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.powNat_two_four_inv_eight_cancel"),
            vec![],
        ),
        [n.clone()],
    ); // (2^n·4^n)·inv8 = 1
    let mot_qr2 = c.mul_right_motive(&b, &q);
    let w5 = c.congr_rat(p2p4_inv8.clone(), one.clone(), mot_qr2, step1);
    // w6 : 1·Q = Q   one_mul.
    let w6 = c.one_mul_at(q.clone());

    // ── assemble : W_norm = (cube·P)·inv8 = … = 1·Q = Q ──
    // The intermediate endpoints, in order:
    //   A0 = W_norm
    //   A1 = (cube·P)·inv8
    //   A2 = (cube·(4^n·Q))·inv8
    //   A3 = ((cube·4^n)·Q)·inv8
    //   A4 = ((cube·4^n)·inv8)·Q
    //   A5 = ((2^n·4^n)·inv8)·Q
    //   A6 = 1·Q
    //   A7 = Q
    let a0 = w_norm.clone();
    let a1 = c.mul(cube_p.clone(), inv8.clone());
    let a2 = c.mul(cube_4q.clone(), inv8.clone());
    let a3 = c.mul(cube4_q.clone(), inv8.clone());
    let a4 = cube4inv8_q.clone();
    let a5 = p2p4inv8_q.clone();
    let a6 = one_q.clone();
    let a7 = q.clone();
    let s_a0_a1 = w0; // W_norm = (cube·P)·inv8
    let s_a1_a2 = w1; // (cube·P)·inv8 = (cube·(4^n·Q))·inv8
    let s_a2_a3 = w2; // = ((cube·4^n)·Q)·inv8
    let s_a3_a4 = w3; // = ((cube·4^n)·inv8)·Q
    let s_a4_a5 = w4; // = ((2^n·4^n)·inv8)·Q
    let s_a5_a6 = w5; // = 1·Q
    let s_a6_a7 = w6; // = Q

    let ch = c.trans(a0.clone(), a1.clone(), a2.clone(), s_a0_a1, s_a1_a2);
    let ch = c.trans(a0.clone(), a2.clone(), a3.clone(), ch, s_a2_a3);
    let ch = c.trans(a0.clone(), a3.clone(), a4.clone(), ch, s_a3_a4);
    let ch = c.trans(a0.clone(), a4.clone(), a5.clone(), ch, s_a4_a5);
    let ch = c.trans(a0.clone(), a5.clone(), a6.clone(), ch, s_a5_a6);
    let proof = c.trans(a0, a6, a7, ch, s_a6_a7);

    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl ComposeConsts {
    /// `a·(c·b) = c·(a·b)` — move the inner factor `c` outward (the
    /// `rung1_leg3_leaf` pattern, reused here for `p_mid` leg A s2).
    fn reassoc_acb_cab(&self, parent: &EnvDeclBuilder, a: &Expr, cc: &Expr, b: &Expr) -> Expr {
        let acb = self.mul(a.clone(), self.mul(cc.clone(), b.clone())); // a·(c·b)
        let ac_b = self.mul(self.mul(a.clone(), cc.clone()), b.clone()); // (a·c)·b
        let ca_b = self.mul(self.mul(cc.clone(), a.clone()), b.clone()); // (c·a)·b
        let c_ab = self.mul(cc.clone(), self.mul(a.clone(), b.clone())); // c·(a·b)
        let s1 = self.symm(
            ac_b.clone(),
            acb.clone(),
            self.mul_assoc(a.clone(), cc.clone(), b.clone()),
        );
        let mot = self.mul_right_motive(parent, b);
        let s2 = self.congr_rat(
            self.mul(a.clone(), cc.clone()),
            self.mul(cc.clone(), a.clone()),
            mot,
            self.mul_comm(a.clone(), cc.clone()),
        );
        let s3 = self.mul_assoc(cc.clone(), a.clone(), b.clone());
        let t = self.trans(acb.clone(), ac_b.clone(), ca_b.clone(), s1, s2);
        self.trans(acb, ca_b, c_ab, t, s3)
    }

    /// `(a·b)·c = (a·c)·b` — swap the second/third factors of a left-nested product.
    ///   `(a·b)·c →[assoc a b c] a·(b·c) →[congr (a·_) comm b c] a·(c·b)
    ///          →[symm assoc a c b] (a·c)·b`.
    fn reassoc_ab_c_ac_b(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        let ab_c = self.mul(self.mul(a.clone(), b.clone()), cc.clone()); // (a·b)·c
        let a_bc = self.mul(a.clone(), self.mul(b.clone(), cc.clone())); // a·(b·c)
        let a_cb = self.mul(a.clone(), self.mul(cc.clone(), b.clone())); // a·(c·b)
        let ac_b = self.mul(self.mul(a.clone(), cc.clone()), b.clone()); // (a·c)·b
        let s1 = self.mul_assoc(a.clone(), b.clone(), cc.clone()); // (a·b)·c = a·(b·c)
        let mot = self.mul_left_motive(parent, a);
        let s2 = self.congr_rat(
            self.mul(b.clone(), cc.clone()),
            self.mul(cc.clone(), b.clone()),
            mot,
            self.mul_comm(b.clone(), cc.clone()),
        ); // a·(b·c) = a·(c·b)
        let s3 = self.symm(
            ac_b.clone(),
            a_cb.clone(),
            self.mul_assoc(a.clone(), cc.clone(), b.clone()),
        ); // a·(c·b) = (a·c)·b
        let t = self.trans(ab_c.clone(), a_bc.clone(), a_cb.clone(), s1, s2);
        self.trans(ab_c, a_cb, ac_b, t, s3)
    }
}
