// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.chi_offdiag_pair_cancel` — the
//! per-index pair cancellation that drives the off-diagonal average
//! `E[χ_U] = 0` for a subset `U` whose top coordinate is present.
//!
//! ```text
//! chi_offdiag_pair_cancel : ∀ (n : Nat) (U : HCPoint (n+1)),
//!   @Eq Bool (U (Fin.last n)) Bool.true →
//!   ∀ (i : Fin (2^n)),
//!     @Eq Rat
//!       (Rat.add
//!          (chi (n+1) U (hcDecode (n+1) (castP (Fin.castAdd (2^n) (2^n) i))))
//!          (chi (n+1) U (hcDecode (n+1) (castP (Fin.addNat  (2^n) (2^n) i)))))
//!       Rat.zero
//! ```
//!
//! For the off-diagonal cube split, index `i` pairs a LOW point (top bit `0`)
//! with a HIGH point (top bit `1`). `chi_succ` factors each character into the
//! same lower-`n` character `P i := chi n (U∘castSucc) (hcDecode n i)` (the two
//! points agree on coordinates `< n` — the `hcDecode_restrict_*` keystones)
//! times the top factor `factor (U (last n)) (bit n)`. With the top coordinate
//! present (`U (last n) = true`) the top factor is the bare sign `pm (bit n)`,
//! and the two top bits are `false` (LOW, `testBit_lt_pow`) and `true` (HIGH,
//! `testBit_add_two_pow_self`). So the pair is
//! `P i · pm false + P i · pm true = P i · (pm false + pm true) = P i · 0 = 0`
//! by `Rat.left_distrib`, the landed `pm_false_add_pm_true_eq_zero`, and
//! `Rat.mul_zero`. Summing this over `i` (`Fin.sum_add` + `Fin.sum_zero_fn`)
//! collapses the whole `2^(n+1)` numerator to `0`, i.e. `E[χ_U] = 0`.
//!
//! Kernel-checked, `ProofQuality::Constructive`: the closure routes through
//! `chi_succ`, the `hcDecode_restrict_*` correspondences, `chi`, `pm`,
//! `Nat.testBit_lt_pow`, `Nat.testBit_add_two_pow_self`, `Fin.isLt`,
//! `Rat.left_distrib`, `Rat.mul_zero`, `pm_false_add_pm_true_eq_zero`, and
//! `congrArg` / `Eq.*` built-ins — all axiom-free or foundational.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct OffDiagConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_: Expr,
    btrue: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    pm: Expr,
    chi: Expr,
    hc_decode: Expr,
    cast_add: Expr,
    add_nat: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    two: Expr,
    // index transport pieces (castP).
    nat_add: Expr,
    pow_two_succ: Expr,
    eq_symm: Expr,
    eq_ndrec_fin: Expr,
    // proof glue.
    eq1: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    congr_arg: Expr,
    chi_succ: Expr,
    restrict_lo: Expr,
    restrict_hi: Expr,
    decode_lo_bit: Expr,
    decode_hi_bit: Expr,
    testbit_lt_pow: Expr,
    testbit_add_self: Expr,
    left_distrib: Expr,
    mul_zero: Expr,
    pm_cancel: Expr,
}

impl OffDiagConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            two,
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            chi_succ: Expr::const_(Name::from_string("BoolAnalysis.chi_succ"), vec![]),
            restrict_lo: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_restrict_castAdd"),
                vec![],
            ),
            restrict_hi: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_restrict_addNat"),
                vec![],
            ),
            decode_lo_bit: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_castP_castAdd"),
                vec![],
            ),
            decode_hi_bit: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_castP_addNat"),
                vec![],
            ),
            testbit_lt_pow: Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
            testbit_add_self: Expr::const_(
                Name::from_string("Nat.testBit_add_two_pow_self"),
                vec![],
            ),
            left_distrib: Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            mul_zero: Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            pm_cancel: Expr::const_(
                Name::from_string("BoolAnalysis.pm_false_add_pm_true_eq_zero"),
                vec![],
            ),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n, s, x])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), x])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }

    /// `fun (i : Fin n) => p (Fin.castSucc n i)` — restrict a `HCPoint (n+1)`
    /// to its first `n` coordinates (matches `chi_succ`'s `restrict`).
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cs = Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i]);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, Expr::app(p.clone(), cs)))
    }

    /// `castP n (idx_map (2^n) (2^n) i) : Fin (2^(n+1))`.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, i: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm.clone(),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), self.fin_of(&m)))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat.clone(), sum_pow, motive, mapped, p2sn, e],
        )
    }

    /// `hcDecode (n+1) (castP n (idx_map .. i)) : HCPoint (n+1)`.
    fn decoded(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, i: &Expr) -> Expr {
        let cp = self.cast_p(parent, n, idx_map, i);
        Expr::apps(self.hc_decode.clone(), [self.succ(n), cp])
    }
}

/// Build the per-index pair-cancellation theorem.
fn build_type(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());

    // hU : U (Fin.last n) = Bool.true
    let u_last = Expr::app(u.clone(), c.last(&n));
    let hu_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), u_last, c.btrue.clone()],
    );
    let (hu_id, _hu) = b.fresh_local(hu_ty.clone());

    let p2n = c.pow2(&n);
    let (i_id, i) = b.fresh_local(c.fin_of(&p2n));

    let xlo = c.decoded(&b, &n, &c.cast_add, &i);
    let xhi = c.decoded(&b, &n, &c.add_nat, &i);
    let lhs = c.radd(
        c.chi(sn.clone(), u.clone(), xlo),
        c.chi(sn.clone(), u.clone(), xhi),
    );
    let concl = c.eq_rat(lhs, c.rat_zero.clone());

    let ty = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&p2n), concl);
    let ty = b.mk_pi(hu_id, BinderInfo::Default, hu_ty, ty);
    let ty = b.mk_pi(u_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let hu_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), u_last.clone(), c.btrue.clone()],
    );
    let (hu_id, hu) = b.fresh_local(hu_ty.clone());
    let p2n = c.pow2(&n);
    let (i_id, i) = b.fresh_local(c.fin_of(&p2n));

    // P := chi n (restrict U) (hcDecode n i) — the common lower-n character.
    let restrict_u = c.restrict(&b, &n, &u);
    let dec_n_i = Expr::apps(c.hc_decode.clone(), [n.clone(), i.clone()]);
    let p = c.chi(n.clone(), restrict_u.clone(), dec_n_i.clone());

    // val i and its bound witness h_i : val i < 2^n  (= @Fin.isLt (2^n) i).
    let val_i = c.val(&p2n, &i);
    let h_i = Expr::apps(c.fin_islt.clone(), [p2n.clone(), i.clone()]);

    let xlo = c.decoded(&b, &n, &c.cast_add, &i);
    let xhi = c.decoded(&b, &n, &c.add_nat, &i);
    let chi_lo = c.chi(sn.clone(), u.clone(), xlo.clone());
    let chi_hi = c.chi(sn.clone(), u.clone(), xhi.clone());

    // ── chi_lo = P · pm false ────────────────────────────────────────────
    // chi_succ n U xlo : chi (n+1) U xlo
    //   = chi n (restrict U) (restrict xlo) · factor (U (last n)) (xlo (last n))
    // restrict xlo ≡ hcDecode n i? NOT defeq (it is hcDecode_restrict_castAdd).
    // So we rewrite the WHOLE RHS in three congruent moves bundled by trans.
    //
    // Strategy: build the target `P · pm false` and prove `chi_lo = P·pm false`
    // by a single `Eq.trans` chain:
    //   leg_a : chi_lo = chi n (restrict U)(restrict xlo) · factor (U last)(xlo last)   [chi_succ]
    //   leg_b : (that) = P · pm false                                                   [congr on both factors]
    //
    // leg_b is itself a `congr` on a 2-ary `Rat.mul`. We assemble it from:
    //   - hL : chi n (restrict U)(restrict xlo) = P
    //          = congrArg (chi n (restrict U)) (restrict_lo n i)
    //   - hR : factor (U last)(xlo last) = pm false
    //          via hU (U last = true) and the bit value (xlo last = false).
    //
    // Because `factor true b ≡ pm b` definitionally, and `xlo last ≡ ... = false`
    // after the bit lemma, we route hR through pm.

    // hL : chi n (restrict U) (restrict xlo) = P
    let restrict_xlo = c.restrict(&b, &n, &xlo);
    let chi_pre_lo = c.chi(n.clone(), restrict_u.clone(), restrict_xlo.clone());
    let restrict_lo_eq = Expr::apps(c.restrict_lo.clone(), [n.clone(), i.clone()]);
    // congrArg (fun y => chi n (restrict U) y) restrict_lo_eq : chi_pre_lo = P
    let chi_fixed_lo = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(c.hcpoint_of(&n));
        let body = c.chi(n.clone(), restrict_u.clone(), y);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.hcpoint_of(&n), body))
    };
    let h_l_lo = Expr::apps(
        c.congr_arg.clone(),
        [
            c.hcpoint_of(&n),
            c.rat.clone(),
            restrict_xlo.clone(),
            dec_n_i.clone(),
            chi_fixed_lo.clone(),
            restrict_lo_eq,
        ],
    );

    // bit_lo : xlo (last n) = false  via hcDecode_castP_castAdd n i (last n) then
    // testBit_lt_pow n (val i) h_i.  xlo (last n) ≡ hcDecode (n+1)(castP..)(last n).
    // hcDecode_castP_castAdd n i (last n) : xlo (last n) = testBit (val i) (val (n+1)(last n))
    //   and val (n+1)(last n) ≡ n defeq, so RHS ≡ testBit (val i) n.
    let xlo_last = Expr::app(xlo.clone(), c.last(&n));
    let bit_lo_corr = Expr::apps(c.decode_lo_bit.clone(), [n.clone(), i.clone(), c.last(&n)]);
    // testbit_lt_pow n (val i) h_i : testBit (val i) n = false
    let bit_lt = Expr::apps(
        c.testbit_lt_pow.clone(),
        [n.clone(), val_i.clone(), h_i.clone()],
    );
    // bit_lo : xlo last = false  (Eq.trans over Bool; mid = testBit (val i) n)
    let testbit_vi_n = Expr::apps(
        Expr::const_(Name::from_string("Nat.testBit"), vec![]),
        [val_i.clone(), c.val(&sn, &c.last(&n))],
    );
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let bit_lo = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            c.bool_.clone(),
            xlo_last.clone(),
            testbit_vi_n,
            bfalse.clone(),
            bit_lo_corr,
            bit_lt,
        ],
    );

    // hR_lo : factor (U last)(xlo last) = pm false.
    // factor sb xb := Bool.rec one (1-2⟦xb⟧) sb.  With hU (U last = true) and
    // bit_lo (xlo last = false):
    //   congr over the 2-ary `factor` along hU and bit_lo lands on factor true false
    //   ≡ pm false (defeq). Build motive `fun (sb xb) => factor sb xb` and use a
    //   double congrArg. We fold both rewrites into one `Eq.trans`:
    //     factor (U last)(xlo last) = factor true (xlo last)   [congr along hU]
    //     factor true (xlo last)    = factor true false        [congr along bit_lo]
    //   then factor true false ≡ pm false defeq, so the RHS is stated as `pm false`.
    let factor = |c: &OffDiagConsts, parent: &EnvDeclBuilder, sb: Expr, xb: Expr| -> Expr {
        // factor sb xb = Bool.rec (fun _=>Rat) one (1 - 2·(Bool.rec 0 1 xb)) sb
        let l1 = Level::succ(Level::zero());
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1]);
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, _t) = mb.fresh_local(c.bool_.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.bool_.clone(), c.rat.clone()))
        };
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_zero = c.rat_zero.clone();
        let rat_two = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    c.two.clone(),
                ),
                Expr::app(
                    c.nat_succ.clone(),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                ),
            ],
        );
        let embed = Expr::apps(
            bool_rec.clone(),
            [motive.clone(), rat_zero, rat_one.clone(), xb],
        );
        let signed = Expr::apps(
            Expr::const_(Name::from_string("Rat.sub"), vec![]),
            [rat_one.clone(), c.rmul(rat_two, embed)],
        );
        Expr::apps(bool_rec, [motive, rat_one, signed, sb])
    };

    // factor (U last) (xlo last)
    let fac_u_lo = factor(c, &b, u_last.clone(), xlo_last.clone());
    // factor true (xlo last)
    let fac_true_lo = factor(c, &b, c.btrue.clone(), xlo_last.clone());
    // factor true false  (≡ pm false defeq)
    let fac_true_false = factor(c, &b, c.btrue.clone(), bfalse.clone());

    // congr along hU: factor (U last)(xlo last) = factor true (xlo last)
    let fac_motive_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.bool_.clone());
        let body = factor(c, &d, s, xlo_last.clone());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let h_fac_s_lo = Expr::apps(
        c.congr_arg.clone(),
        [
            c.bool_.clone(),
            c.rat.clone(),
            u_last.clone(),
            c.btrue.clone(),
            fac_motive_s,
            hu.clone(),
        ],
    );
    // congr along bit_lo: factor true (xlo last) = factor true false
    let fac_motive_x_lo = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(c.bool_.clone());
        let body = factor(c, &d, c.btrue.clone(), x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let h_fac_x_lo = Expr::apps(
        c.congr_arg.clone(),
        [
            c.bool_.clone(),
            c.rat.clone(),
            xlo_last.clone(),
            bfalse.clone(),
            fac_motive_x_lo,
            bit_lo,
        ],
    );
    // hR_lo : factor (U last)(xlo last) = pm false  (fac_true_false ≡ pm false)
    let pm_false = c.pm(bfalse.clone());
    let h_r_lo = c.trans_rat(
        fac_u_lo.clone(),
        fac_true_lo.clone(),
        pm_false.clone(),
        h_fac_s_lo,
        {
            // h_fac_x_lo : fac_true_lo = fac_true_false ; restated RHS pm false (defeq).
            h_fac_x_lo
        },
    );
    let _ = fac_true_false;

    // leg_lo : chi_lo = P · pm false
    //   chi_succ n U xlo : chi_lo = chi_pre_lo · fac_u_lo
    let chi_succ_lo = Expr::apps(c.chi_succ.clone(), [n.clone(), u.clone(), xlo.clone()]);
    let chi_pre_times_fac_lo = c.rmul(chi_pre_lo.clone(), fac_u_lo.clone());
    let p_times_pmfalse = c.rmul(p.clone(), pm_false.clone());
    // congr on Rat.mul: chi_pre_lo·fac_u_lo = P·pm false
    let leg_lo_congr = bin_congr(
        c,
        &b,
        &c.rat_mul,
        chi_pre_lo.clone(),
        p.clone(),
        fac_u_lo.clone(),
        pm_false.clone(),
        h_l_lo,
        h_r_lo,
    );
    let chi_lo_eq = c.trans_rat(
        chi_lo.clone(),
        chi_pre_times_fac_lo,
        p_times_pmfalse.clone(),
        chi_succ_lo,
        leg_lo_congr,
    );

    // ── chi_hi = P · pm true  (mirror, with addNat / testBit_add_self) ────
    let restrict_xhi = c.restrict(&b, &n, &xhi);
    let chi_pre_hi = c.chi(n.clone(), restrict_u.clone(), restrict_xhi.clone());
    let restrict_hi_eq = Expr::apps(c.restrict_hi.clone(), [n.clone(), i.clone()]);
    let h_l_hi = Expr::apps(
        c.congr_arg.clone(),
        [
            c.hcpoint_of(&n),
            c.rat.clone(),
            restrict_xhi.clone(),
            dec_n_i.clone(),
            chi_fixed_lo,
            restrict_hi_eq,
        ],
    );

    let xhi_last = Expr::app(xhi.clone(), c.last(&n));
    let bit_hi_corr = Expr::apps(c.decode_hi_bit.clone(), [n.clone(), i.clone(), c.last(&n)]);
    // testbit_add_self n (val i) h_i : testBit (2^n + val i) n = true
    let bit_self = Expr::apps(
        c.testbit_add_self.clone(),
        [n.clone(), val_i.clone(), h_i.clone()],
    );
    let testbit_add_vi_n = Expr::apps(
        Expr::const_(Name::from_string("Nat.testBit"), vec![]),
        [c.nadd(p2n.clone(), val_i.clone()), c.val(&sn, &c.last(&n))],
    );
    let bit_hi = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            c.bool_.clone(),
            xhi_last.clone(),
            testbit_add_vi_n,
            c.btrue.clone(),
            bit_hi_corr,
            bit_self,
        ],
    );

    let fac_u_hi = factor(c, &b, u_last.clone(), xhi_last.clone());
    let fac_true_hi = factor(c, &b, c.btrue.clone(), xhi_last.clone());
    let fac_motive_s_hi = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.bool_.clone());
        let body = factor(c, &d, s, xhi_last.clone());
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let h_fac_s_hi = Expr::apps(
        c.congr_arg.clone(),
        [
            c.bool_.clone(),
            c.rat.clone(),
            u_last.clone(),
            c.btrue.clone(),
            fac_motive_s_hi,
            hu.clone(),
        ],
    );
    let fac_motive_x_hi = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(c.bool_.clone());
        let body = factor(c, &d, c.btrue.clone(), x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let h_fac_x_hi = Expr::apps(
        c.congr_arg.clone(),
        [
            c.bool_.clone(),
            c.rat.clone(),
            xhi_last.clone(),
            c.btrue.clone(),
            fac_motive_x_hi,
            bit_hi,
        ],
    );
    let pm_true = c.pm(c.btrue.clone());
    let h_r_hi = c.trans_rat(
        fac_u_hi.clone(),
        fac_true_hi.clone(),
        pm_true.clone(),
        h_fac_s_hi,
        h_fac_x_hi,
    );

    let chi_succ_hi = Expr::apps(c.chi_succ.clone(), [n.clone(), u.clone(), xhi.clone()]);
    let chi_pre_times_fac_hi = c.rmul(chi_pre_hi.clone(), fac_u_hi.clone());
    let p_times_pmtrue = c.rmul(p.clone(), pm_true.clone());
    let leg_hi_congr = bin_congr(
        c,
        &b,
        &c.rat_mul,
        chi_pre_hi.clone(),
        p.clone(),
        fac_u_hi.clone(),
        pm_true.clone(),
        h_l_hi,
        h_r_hi,
    );
    let chi_hi_eq = c.trans_rat(
        chi_hi.clone(),
        chi_pre_times_fac_hi,
        p_times_pmtrue.clone(),
        chi_succ_hi,
        leg_hi_congr,
    );

    // ── combine: chi_lo + chi_hi = P·pm false + P·pm true = P·0 = 0 ───────
    // sum_eq : chi_lo + chi_hi = P·pm false + P·pm true   (congr on Rat.add)
    let sum_eq = bin_congr(
        c,
        &b,
        &c.rat_add,
        chi_lo.clone(),
        p_times_pmfalse.clone(),
        chi_hi.clone(),
        p_times_pmtrue.clone(),
        chi_lo_eq,
        chi_hi_eq,
    );
    // distrib : P·pm false + P·pm true = P·(pm false + pm true)
    //   = Eq.symm (Rat.left_distrib P (pm false) (pm true))
    let pm_sum = c.radd(pm_false.clone(), pm_true.clone());
    let p_times_pmsum = c.rmul(p.clone(), pm_sum.clone());
    let distrib_fwd = Expr::apps(
        c.left_distrib.clone(),
        [p.clone(), pm_false.clone(), pm_true.clone()],
    );
    // left_distrib : P·(a+b) = P·a + P·b. We need the reverse, so Eq.symm.
    let distrib = Expr::apps(
        c.eq_symm.clone(),
        [
            c.rat.clone(),
            p_times_pmsum.clone(),
            c.radd(p_times_pmfalse.clone(), p_times_pmtrue.clone()),
            distrib_fwd,
        ],
    );
    // pm_cancel : pm false + pm true = 0  ⇒ congr: P·(pm false+pm true) = P·0
    let p_times_zero = c.rmul(p.clone(), c.rat_zero.clone());
    let cancel_congr = {
        let m = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.rmul(p.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        Expr::apps(
            c.congr_arg.clone(),
            [
                c.rat.clone(),
                c.rat.clone(),
                pm_sum.clone(),
                c.rat_zero.clone(),
                m,
                c.pm_cancel.clone(),
            ],
        )
    };
    // mul_zero : P·0 = 0
    let mulz = Expr::app(c.mul_zero.clone(), p.clone());

    // Chain: (chi_lo+chi_hi) = P·pmf+P·pmt = P·(pmf+pmt) = P·0 = 0.
    let step1 = c.trans_rat(
        c.radd(chi_lo.clone(), chi_hi.clone()),
        c.radd(p_times_pmfalse.clone(), p_times_pmtrue.clone()),
        p_times_pmsum.clone(),
        sum_eq,
        distrib,
    );
    let step2 = c.trans_rat(
        c.radd(chi_lo.clone(), chi_hi.clone()),
        p_times_pmsum.clone(),
        p_times_zero.clone(),
        step1,
        cancel_congr,
    );
    let proof = c.trans_rat(
        c.radd(chi_lo, chi_hi),
        p_times_zero,
        c.rat_zero.clone(),
        step2,
        mulz,
    );

    let val = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), proof);
    let val = b.mk_lam(hu_id, BinderInfo::Default, hu_ty, val);
    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

/// `congr` on a binary `Rat` operator `op` (`Rat.add` or `Rat.mul`): from
/// `al = ar` and `bl = br` derive `op al bl = op ar br`, as two chained
/// `congrArg`s glued by `Eq.trans`. The motive lambdas are built with
/// `child_of(parent)` so any free variables captured from the outer
/// declaration scope (`n`, `i`, `U`, …) stay bound.
#[allow(clippy::too_many_arguments)]
fn bin_congr(
    c: &OffDiagConsts,
    parent: &EnvDeclBuilder,
    op: &Expr,
    al: Expr,
    ar: Expr,
    bl: Expr,
    br: Expr,
    hl: Expr,
    hr: Expr,
) -> Expr {
    let app2 = |op: &Expr, a: Expr, b: Expr| -> Expr { Expr::apps(op.clone(), [a, b]) };
    // m1 := fun z => op z bl
    let m1 = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = app2(op, z, bl.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1 = Expr::apps(
        c.congr_arg.clone(),
        [c.rat.clone(), c.rat.clone(), al.clone(), ar.clone(), m1, hl],
    );
    // m2 := fun z => op ar z
    let m2 = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = app2(op, ar.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s2 = Expr::apps(
        c.congr_arg.clone(),
        [c.rat.clone(), c.rat.clone(), bl.clone(), br.clone(), m2, hr],
    );
    c.trans_rat(
        app2(op, al, bl.clone()),
        app2(op, ar.clone(), bl),
        app2(op, ar, br),
        s1,
        s2,
    )
}

// ===========================================================================
// chi_offdiag_numerator_zero — the full off-diagonal numerator vanishes.
// ===========================================================================

impl OffDiagConsts {
    /// `Fin.sum n f`.
    fn fsum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Fin.sum"), vec![]), [n, f])
    }
    /// `fun (k : Fin (2^(n+1))) => chi (n+1) U (hcDecode (n+1) k)` — the
    /// numerator integrand (= `Expect`'s numerator summand for `g = χ_U`).
    fn numerator_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let sn = self.succ(n);
        let p2sn = self.pow2(&sn);
        let (k_id, k) = b.fresh_local(self.fin_of(&p2sn));
        let dec = Expr::apps(self.hc_decode.clone(), [sn.clone(), k]);
        let body = self.chi(sn, u.clone(), dec);
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, self.fin_of(&p2sn), body))
    }
    /// `fun (x : HCPoint (n+1)) => chi (n+1) U x` — the character as a function,
    /// the `g` fed to `hcSumSplit`.
    fn chi_u_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let sn = self.succ(n);
        let hcp = self.hcpoint_of(&sn);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.chi(sn, u.clone(), x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (i : Fin (2^n)) => chi (n+1) U (hcDecode (n+1) (castP (idx_map .. i)))`
    /// — one cube-split half-sum integrand.
    fn half_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr, idx_map: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = b.fresh_local(self.fin_of(&p2n));
        let dec = self.decoded(&b, n, idx_map, &i);
        let body = self.chi(self.succ(n), u.clone(), dec);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (_ : Fin (2^n)) => Rat.zero`.
    fn zero_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, _i) = b.fresh_local(self.fin_of(&p2n));
        b.finish_child(b.mk_lam(
            i_id,
            BinderInfo::Default,
            self.fin_of(&p2n),
            self.rat_zero.clone(),
        ))
    }
}

fn build_numerator_type(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let hu_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), u_last, c.btrue.clone()],
    );
    let (hu_id, _hu) = b.fresh_local(hu_ty.clone());

    let p2sn = c.pow2(&sn);
    let lhs = c.fsum(p2sn, c.numerator_fn(&b, &n, &u));
    let concl = c.eq_rat(lhs, c.rat_zero.clone());

    let ty = b.mk_pi(hu_id, BinderInfo::Default, hu_ty, concl);
    let ty = b.mk_pi(u_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_numerator_value(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let hu_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), u_last, c.btrue.clone()],
    );
    let (hu_id, hu) = b.fresh_local(hu_ty.clone());

    let p2n = c.pow2(&n);
    let p2sn = c.pow2(&sn);

    let numer = c.numerator_fn(&b, &n, &u);
    let chi_u = c.chi_u_fn(&b, &n, &u);
    let lo_fn = c.half_fn(&b, &n, &u, &c.cast_add);
    let hi_fn = c.half_fn(&b, &n, &u, &c.add_nat);
    let zero_fn = c.zero_fn(&b, &n);

    let numer_sum = c.fsum(p2sn.clone(), numer);
    let sum_lo = c.fsum(p2n.clone(), lo_fn.clone());
    let sum_hi = c.fsum(p2n.clone(), hi_fn.clone());
    let split_rhs = c.radd(sum_lo.clone(), sum_hi.clone());

    // step1 : numerator = Σlow + Σhigh   (hcSumSplit n (χ_U fn))
    //   hcSumSplit's LHS `Fin.sum (2^(n+1)) (fun k => (χ_U fn) (hcDecode (n+1) k))`
    //   is β-equal to our `numer_sum`; its RHS halves β-reduce to lo_fn / hi_fn.
    let step1 = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.hcSumSplit"), vec![]),
        [n.clone(), chi_u],
    );

    // pair_fn : fun i => lo_fn i + hi_fn i
    let pair_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(c.fin_of(&p2n));
        let lo_i = Expr::app(lo_fn.clone(), i.clone());
        let hi_i = Expr::app(hi_fn.clone(), i.clone());
        let body = c.radd(lo_i, hi_i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    let sum_pair = c.fsum(p2n.clone(), pair_fn.clone());

    // step2 : Σlow + Σhigh = Σ (fun i => lo i + hi i)
    //   Eq.symm (Fin.sum_add (2^n) lo_fn hi_fn)
    let sum_add_fwd = Expr::apps(
        Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
        [p2n.clone(), lo_fn.clone(), hi_fn.clone()],
    );
    let step2 = Expr::apps(
        c.eq_symm.clone(),
        [
            c.rat.clone(),
            sum_pair.clone(),
            split_rhs.clone(),
            sum_add_fwd,
        ],
    );

    // step3 : Σ (fun i => lo i + hi i) = Σ (fun _ => 0)
    //   Fin.sum_congr (2^n) pair_fn zero_fn (fun i => chi_offdiag_pair_cancel n U hU i)
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(c.fin_of(&p2n));
        let body = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.chi_offdiag_pair_cancel"),
                vec![],
            ),
            [n.clone(), u.clone(), hu.clone(), i],
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    let sum_zero = c.fsum(p2n.clone(), zero_fn.clone());
    let step3 = Expr::apps(
        Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
        [p2n.clone(), pair_fn, zero_fn, pointwise],
    );

    // step4 : Σ (fun _ => 0) = 0   (Fin.sum_zero_fn (2^n))
    let step4 = Expr::app(
        Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]),
        p2n.clone(),
    );

    // Chain everything with Eq.trans:
    //   numer = Σlow+Σhigh = Σpair = Σzero = 0.
    let t1 = c.trans_rat(
        numer_sum.clone(),
        split_rhs.clone(),
        sum_pair.clone(),
        step1,
        step2,
    );
    let t2 = c.trans_rat(numer_sum.clone(), sum_pair, sum_zero.clone(), t1, step3);
    let proof = c.trans_rat(numer_sum, sum_zero, c.rat_zero.clone(), t2, step4);

    let val = b.mk_lam(hu_id, BinderInfo::Default, hu_ty, proof);
    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ===========================================================================
// chi_inner_offdiag_zero — E[χ_S·χ_T] = 0 when S, T differ at the top coord.
// ===========================================================================

impl OffDiagConsts {
    /// `fun (i : Fin (n+1)) => Bool.xor (S i) (T i)` — the symmetric difference
    /// `S Δ T`, the witness `U` fed to `chi_expect_zero`.
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, sn: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_sn = self.fin_of(sn);
        let (i_id, i) = b.fresh_local(fin_sn.clone());
        let body = Expr::apps(
            Expr::const_(Name::from_string("Bool.xor"), vec![]),
            [Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i)],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_sn, body))
    }
    /// `BoolAnalysis.Expect (n+1) (fun x => Rat.mul (chi (n+1) S x) (chi (n+1) T x))`.
    fn expect_inner(&self, parent: &EnvDeclBuilder, sn: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(sn);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.rmul(
            self.chi(sn.clone(), s.clone(), x.clone()),
            self.chi(sn.clone(), t.clone(), x),
        );
        let integrand = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            [sn.clone(), integrand],
        )
    }
}

fn build_inner_offdiag_type(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    // h : Bool.xor (S (last n)) (T (last n)) = true   (S, T differ at the top).
    let sd = c.symm_diff_fn(&b, &sn, &s, &t);
    let sd_last = Expr::app(sd.clone(), c.last(&n));
    let h_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), sd_last, c.btrue.clone()],
    );
    let (h_id, _h) = b.fresh_local(h_ty.clone());

    let lhs = c.expect_inner(&b, &sn, &s, &t);
    let concl = c.eq_rat(lhs, c.rat_zero.clone());
    let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_inner_offdiag_value(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let sd = c.symm_diff_fn(&b, &sn, &s, &t);
    let sd_last = Expr::app(sd.clone(), c.last(&n));
    let h_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), sd_last, c.btrue.clone()],
    );
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let expect_inner = c.expect_inner(&b, &sn, &s, &t);
    let expect_symmdiff = c.expect_chi_u(&b, &n, &sd);

    // leg1 : E[χ_S·χ_T] = E[χ_{SΔT}]   (chi_inner_eq_expect_symmDiff (n+1) S T)
    let leg1 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.chi_inner_eq_expect_symmDiff"),
            vec![],
        ),
        [sn.clone(), s.clone(), t.clone()],
    );
    // leg2 : E[χ_{SΔT}] = 0   (chi_expect_zero n (SΔT) h)
    let leg2 = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.chi_expect_zero"), vec![]),
        [n.clone(), sd.clone(), h.clone()],
    );
    let proof = c.trans_rat(
        expect_inner,
        expect_symmdiff,
        c.rat_zero.clone(),
        leg1,
        leg2,
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_inner_offdiag_zero`: the off-diagonal
    /// character inner product vanishes, `E[χ_S·χ_T] = 0`, whenever `S` and `T`
    /// differ at the top coordinate (`Bool.xor (S (last n)) (T (last n)) = true`).
    /// `Eq.trans` of the inner-product reduction `chi_inner_eq_expect_symmDiff`
    /// (`E[χ_S·χ_T] = E[χ_{SΔT}]`) and the off-diagonal average `chi_expect_zero`
    /// (`E[χ_{SΔT}] = 0`). Together with the diagonal `chi_self_inner_eq_one`
    /// this is character orthonormality. Idempotent.
    pub(crate) fn register_chi_inner_offdiag_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_inner_offdiag_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_chi_inner_symm_diff_theorem()?;
        self.register_chi_expect_zero_theorem()?;

        let c = OffDiagConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_inner_offdiag_type(&c),
            value: build_inner_offdiag_value(&c),
        })
    }
}

// ===========================================================================
// chi_expect_zero — E[χ_U] = 0 (the off-diagonal average) via numerator/2^n.
// ===========================================================================

impl OffDiagConsts {
    /// The Expect denominator `D := Rat.mk (Int.ofNat (2^(n+1))) 1`.
    fn expect_denom(&self, sn: &Expr) -> Expr {
        let p2sn = self.pow2(sn);
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), p2sn),
                Expr::app(
                    self.nat_succ.clone(),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                ),
            ],
        )
    }
    fn rdiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.div"), vec![]), [a, b])
    }
    fn rinv(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.inv"), vec![]), a)
    }
    /// `BoolAnalysis.Expect (n+1) (fun x => chi (n+1) U x)`.
    fn expect_chi_u(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let sn = self.succ(n);
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            [sn, self.chi_u_fn(parent, n, u)],
        )
    }
}

fn build_expect_zero_type(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let hu_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), u_last, c.btrue.clone()],
    );
    let (hu_id, _hu) = b.fresh_local(hu_ty.clone());

    let lhs = c.expect_chi_u(&b, &n, &u);
    let concl = c.eq_rat(lhs, c.rat_zero.clone());
    let ty = b.mk_pi(hu_id, BinderInfo::Default, hu_ty, concl);
    let ty = b.mk_pi(u_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_expect_zero_value(c: &OffDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let hu_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.bool_.clone(), u_last, c.btrue.clone()],
    );
    let (hu_id, hu) = b.fresh_local(hu_ty.clone());

    let p2sn = c.pow2(&sn);
    let denom = c.expect_denom(&sn);
    let numer_sum = c.fsum(p2sn, c.numerator_fn(&b, &n, &u));

    // expect_lhs := Expect (n+1) (χ_U fn)  ≡ Rat.div numer_sum denom  (δβ).
    let expect_lhs = c.expect_chi_u(&b, &n, &u);
    let div_numer = c.rdiv(numer_sum.clone(), denom.clone());
    let div_zero = c.rdiv(c.rat_zero.clone(), denom.clone());

    // numerator_zero n U hU : numer_sum = 0
    let numer_zero = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.chi_offdiag_numerator_zero"),
            vec![],
        ),
        [n.clone(), u.clone(), hu.clone()],
    );
    // leg1 : Rat.div numer_sum D = Rat.div 0 D
    //   congrArg (fun z => Rat.div z D) numer_zero
    let div_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.rdiv(z, denom.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg1 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            numer_sum.clone(),
            c.rat_zero.clone(),
            div_motive,
            numer_zero,
        ],
    );
    // leg2 : Rat.div 0 D = 0
    //   Rat.div 0 D ≡ Rat.mul 0 (Rat.inv D), and Rat.zero_mul (inv D) : that = 0.
    let leg2 = Expr::app(
        Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
        c.rinv(denom.clone()),
    );

    // proof : Expect (n+1) (χ_U) = 0
    //   Eq.trans leg1 leg2 (expect_lhs ≡ div_numer ≡ leg1.lhs defeq; div_zero ≡ leg2.lhs defeq).
    let proof = c.trans_rat(expect_lhs, div_zero, c.rat_zero.clone(), leg1, leg2);
    // (div_numer documents the defeq target between expect_lhs and leg1.lhs.)
    let _ = div_numer;

    let val = b.mk_lam(hu_id, BinderInfo::Default, hu_ty, proof);
    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_expect_zero`: the off-diagonal character
    /// average vanishes, `E[χ_U] = 0`, for `U` with top coordinate present.
    /// The numerator (`chi_offdiag_numerator_zero`) is `0`, and `0 / 2^(n+1) = 0`
    /// (`Rat.div 0 D ≡ Rat.mul 0 (inv D)` then `Rat.zero_mul`). Idempotent.
    pub(crate) fn register_chi_expect_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_expect_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_chi_offdiag_numerator_zero_theorem()?;
        // Rat.zero_mul is a constructive Rat-quotient theorem.
        self.init_rat()?;

        let c = OffDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_expect_zero_type(&c),
            value: build_expect_zero_value(&c),
        })
    }

    /// Register `BoolAnalysis.chi_offdiag_numerator_zero`: the full
    /// `2^(n+1)`-cube character numerator vanishes when the top coordinate of
    /// `U` is present. Idempotent.
    pub(crate) fn register_chi_offdiag_numerator_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_offdiag_numerator_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_chi_offdiag_pair_cancel_theorem()?;
        self.register_hc_sum_split_theorem()?; // hcSumSplit
                                               // The Fin.sum overlay installs the constructive Fin.sum_add / Fin.sum_congr
                                               // / Fin.sum_zero_fn theorems this assembly consumes.
        self.init_fin_sum()?;

        let c = OffDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_numerator_type(&c),
            value: build_numerator_value(&c),
        })
    }
}

impl Environment {
    /// Register `BoolAnalysis.chi_offdiag_pair_cancel` as a kernel-checked,
    /// constructive theorem. Idempotent.
    pub(crate) fn register_chi_offdiag_pair_cancel_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_offdiag_pair_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_chi_succ_theorem()?;
        self.register_hc_decode_split_theorems()?; // restrict_* + decode_* + isLt + testbit lemmas
        self.register_pm_coordinate_vanishing_theorem()?; // pm_false_add_pm_true_eq_zero
                                                          // Rat.left_distrib / Rat.mul_zero are constructive Rat-quotient theorems.
        self.init_rat_field_inst()?;

        let c = OffDiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_offdiag_pair_cancel_theorem()
            .expect("register_chi_offdiag_pair_cancel_theorem");
        env
    }

    #[test]
    fn test_chi_offdiag_pair_cancel_is_constructive_theorem() {
        let env = make_env();
        let name = Name::from_string("BoolAnalysis.chi_offdiag_pair_cancel");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_offdiag_pair_cancel proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_offdiag_pair_cancel must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_offdiag_pair_cancel's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_chi_inner_offdiag_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_inner_offdiag_zero_theorem()
            .expect("register_chi_inner_offdiag_zero_theorem");
        let name = Name::from_string("BoolAnalysis.chi_inner_offdiag_zero");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_inner_offdiag_zero proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_inner_offdiag_zero must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_inner_offdiag_zero's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_chi_expect_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_expect_zero_theorem()
            .expect("register_chi_expect_zero_theorem");
        let name = Name::from_string("BoolAnalysis.chi_expect_zero");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_expect_zero proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_expect_zero must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_expect_zero's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_chi_offdiag_numerator_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_offdiag_numerator_zero_theorem()
            .expect("register_chi_offdiag_numerator_zero_theorem");
        let name = Name::from_string("BoolAnalysis.chi_offdiag_numerator_zero");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_offdiag_numerator_zero proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_offdiag_numerator_zero must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_offdiag_numerator_zero's transitive axiom closure must be empty"
        );
    }
}
