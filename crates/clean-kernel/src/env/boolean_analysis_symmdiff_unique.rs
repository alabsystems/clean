// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Symmetric-difference index uniqueness — the general-pivot generalization of
//! `setSizeNat_hcDecode_imp_val_zero` that the noise-semigroup delta-extraction
//! turns on.
//!
//! `emptyset_mass_isolation` extracts the ∅-term of a `subsetSum` because the
//! ONLY `Fin (2^n)` index whose decoded point has popcount zero is the index `0`
//! (`setSizeNat_hcDecode_imp_val_zero`). The noise semigroup needs the SAME
//! collapse at a GENERAL pivot `jS : Fin (2^n)`: the only `jT` for which
//! `S Δ T = ∅` (i.e. `setSizeNat n (S Δ T) = 0`, with `S = hcDecode n jS`,
//! `T = hcDecode n jT`) is `jT = jS`. That is the content of
//!
//! ```text
//! BoolAnalysis.setSizeNat_symmDiff_hcDecode_imp_val_eq :
//!   ∀ (n : Nat) (jS jT : Fin (Nat.pow 2 n)),
//!     Eq Nat (setSizeNat n (fun i => Bool.xor (hcDecode n jS i) (hcDecode n jT i)))
//!            Nat.zero
//!       → Eq Nat (Fin.val (Nat.pow 2 n) jS) (Fin.val (Nat.pow 2 n) jT)
//! ```
//!
//! ## Route (mirrors `setSizeNat_hcDecode_imp_val_zero`, pairwise)
//!
//! `setSizeNat n (S Δ T) ≡ Fin.sumNat n (fun i => indNat ((S Δ T) i))` (reducible),
//! so `Fin.sumNat_eq_zero` gives `∀ i : Fin n, indNat ((S Δ T) i) = 0`. For each
//! bit position `j : Nat`, `Nat.le_or_lt n j`:
//!   • `n ≤ j` (high): `Fin.val jS, Fin.val jT < 2^n ≤ 2^j`, so `Nat.testBit_lt_pow`
//!     makes both `testBit … j` false — equal by `Eq.trans`/`Eq.symm`.
//!   • `j < n` (low): the popcount fact at `⟨j,hlt⟩ : Fin n` gives
//!     `indNat ((S Δ T) ⟨j⟩) = 0`, so `(S Δ T) ⟨j⟩ = false` (`indNat_eq_zero`),
//!     i.e. `Bool.xor (testBit (val jS) j) (testBit (val jT) j) = false`
//!     (`(hcDecode n k) ⟨j,hlt⟩ ≡ testBit (val k) j`, def-eq). The Bool helper
//!     `Bool.eq_of_xor_eq_false` turns that into the bit equality.
//! `Nat.eq_of_testBit_eq (val jS) (val jT) allBits` then forces `val jS = val jT`.
//!
//! The Bool helper `Bool.eq_of_xor_eq_false : ∀ a b, Bool.xor a b = false → a = b`
//! is proved by `Bool.casesOn` on both arguments (the two diagonal cases are
//! `Eq.refl`; the two off-diagonal cases give `true = false` / `false = true`
//! hypotheses refuted by `Bool.noConfusion`).
//!
//! Every cited brick is constructive with an empty admitted-axiom closure, so
//! both decls are `ProofQuality::Constructive`, empty closure. No axiom added or
//! removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `Bool.eq_of_xor_eq_false : ∀ (a b : Bool), Eq Bool (Bool.xor a b) Bool.false
    ///   → Eq Bool a b`. Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub(crate) fn register_bool_eq_of_xor_eq_false(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Bool.eq_of_xor_eq_false");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?; // Bool, Bool.xor, Bool.casesOn, Bool.noConfusion
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
        let bool_cases = Expr::const_(Name::from_string("Bool.casesOn"), vec![l0.clone()]);
        let bool_no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![l0.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let xor = |a: Expr, b: Expr| Expr::apps(bool_xor.clone(), [a, b]);
        let eq_b = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [bool_.clone(), l, r],
            )
        };

        // ── type: ∀ a b, xor a b = false → a = b ──
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_.clone());
            let (bb_id, bb) = b.fresh_local(bool_.clone());
            let hyp = eq_b(xor(a.clone(), bb.clone()), bool_false.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = eq_b(a.clone(), bb.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, bool_.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, bool_.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_.clone());
            let (bb_id, bb) = b.fresh_local(bool_.clone());
            let hyp = eq_b(xor(a.clone(), bb.clone()), bool_false.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());

            // outer motive on `a`: fun av => (xor av bb = false) → (av = bb)
            let outer_motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (av_id, av) = m.fresh_local(bool_.clone());
                let prem = eq_b(xor(av.clone(), bb.clone()), bool_false.clone());
                let concl = eq_b(av.clone(), bb.clone());
                let body = Expr::pi(BinderInfo::Default, prem, concl);
                m.finish_child(m.mk_lam(av_id, BinderInfo::Default, bool_.clone(), body))
            };

            // For a fixed `av`, an inner `Bool.casesOn` on `bb`. We need, per `av`:
            //   fun (hp : xor av bb = false) => Bool.casesOn over bb …
            // Build the two `av` minors (av = false, av = true), each casing on bb.
            // inner motive on `bb` (for a concrete av-value `av0`):
            //   fun bv => (xor av0 bv = false) → (av0 = bv)
            let inner_motive = |av0: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut m = EnvDeclBuilder::child_of(parent);
                let (bv_id, bv) = m.fresh_local(bool_.clone());
                let prem = eq_b(xor(av0.clone(), bv.clone()), bool_false.clone());
                let concl = eq_b(av0.clone(), bv.clone());
                let body = Expr::pi(BinderInfo::Default, prem, concl);
                m.finish_child(m.mk_lam(bv_id, BinderInfo::Default, bool_.clone(), body))
            };

            // refl minor: when av0 = bv0, goal `av0 = bv0` by Eq.refl (hp unused).
            let refl_minor = |av0: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut m = EnvDeclBuilder::child_of(parent);
                let prem = eq_b(xor(av0.clone(), av0.clone()), bool_false.clone());
                let (hp_id, _hp) = m.fresh_local(prem.clone());
                let refl = Expr::apps(eq_refl.clone(), [bool_.clone(), av0.clone()]);
                m.finish_child(m.mk_lam(hp_id, BinderInfo::Default, prem, refl))
            };

            // conflict minor: when av0 ≠ bv0, `xor av0 bv0 ≡ true`, so hp : true = false,
            //   refuted by Bool.noConfusion. Goal target is `av0 = bv0`.
            let conflict_minor = |av0: &Expr, bv0: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut m = EnvDeclBuilder::child_of(parent);
                let prem = eq_b(xor(av0.clone(), bv0.clone()), bool_false.clone());
                let (hp_id, hp) = m.fresh_local(prem.clone());
                let target = eq_b(av0.clone(), bv0.clone());
                // @Bool.noConfusion.{0} target true false hp  (xor av0 bv0 ≡ true)
                let body = Expr::apps(
                    bool_no_conf.clone(),
                    [target, bool_true.clone(), bool_false.clone(), hp],
                );
                m.finish_child(m.mk_lam(hp_id, BinderInfo::Default, prem, body))
            };

            // av = false branch: @Bool.casesOn (inner_motive false) bb
            //   (bv=false → refl) (bv=true → conflict false true)
            let false_branch = {
                let im = inner_motive(&bool_false, &b);
                let bv_false_minor = refl_minor(&bool_false, &b);
                let bv_true_minor = conflict_minor(&bool_false, &bool_true, &b);
                Expr::apps(
                    bool_cases.clone(),
                    [im, bb.clone(), bv_false_minor, bv_true_minor],
                )
            };
            // av = true branch: @Bool.casesOn (inner_motive true) bb
            //   (bv=false → conflict true false) (bv=true → refl)
            let true_branch = {
                let im = inner_motive(&bool_true, &b);
                let bv_false_minor = conflict_minor(&bool_true, &bool_false, &b);
                let bv_true_minor = refl_minor(&bool_true, &b);
                Expr::apps(
                    bool_cases.clone(),
                    [im, bb.clone(), bv_false_minor, bv_true_minor],
                )
            };

            // @Bool.casesOn outer_motive a false_branch true_branch : motive a
            //   = (xor a bb = false → a = bb); apply to h.
            let cases = Expr::apps(
                bool_cases.clone(),
                [outer_motive, a.clone(), false_branch, true_branch],
            );
            let body = Expr::app(cases, h);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(bb_id, BinderInfo::Default, bool_.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.setSizeNat_symmDiff_hcDecode_imp_val_eq :
    ///   ∀ (n : Nat) (jS jT : Fin (Nat.pow 2 n)),
    ///     Eq Nat (setSizeNat n (fun i => Bool.xor (hcDecode n jS i) (hcDecode n jT i)))
    ///            Nat.zero
    ///       → Eq Nat (Fin.val (Nat.pow 2 n) jS) (Fin.val (Nat.pow 2 n) jT)`.
    ///
    /// The general-pivot index uniqueness — see module docs. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub(crate) fn register_setsizenat_symmdiff_hcdecode_imp_val_eq(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSizeNat_symmDiff_hcDecode_imp_val_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // hcDecode, Fin.sumNat, HCPoint
        self.init_bool()?; // Bool.xor
        self.register_set_size_nat()?; // setSizeNat
        self.register_fin_sum_nat_eq_zero()?;
        self.register_indnat_eq_zero()?;
        self.register_bool_eq_of_xor_eq_false()?;
        // Number-theory bricks (idempotent registrars from their own modules).
        self.init_nat()?;
        self.init_le()?;
        self.init_nat_succ_base()?; // Nat.zero_le, Nat.succ_le_succ
        self.init_nat_trans_lt_le_lt()?; // Nat.lt_of_lt_of_le
        self.register_nat_mul_left_cancel_succ_proof()?; // Nat.le_or_lt
        self.register_nat_testbit_lt_pow_proof()?; // Nat.testBit_lt_pow
        self.register_nat_eq_of_testbit_proof()?; // Nat.eq_of_testBit_eq
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let (ty, value) = build_symmdiff_imp_val_eq();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build (type, value) of `setSizeNat_symmDiff_hcDecode_imp_val_eq`.
fn build_symmdiff_imp_val_eq() -> (Expr, Expr) {
    let l0 = Level::zero();
    let l1 = Level::succ(l0.clone());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
    let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
    let fin_sum_nat = Expr::const_(Name::from_string("Fin.sumNat"), vec![]);
    let fin_sum_nat_eq_zero = Expr::const_(Name::from_string("Fin.sumNat_eq_zero"), vec![]);
    let indnat_eq_zero = Expr::const_(Name::from_string("BoolAnalysis.indNat_eq_zero"), vec![]);
    let eq_of_xor = Expr::const_(Name::from_string("Bool.eq_of_xor_eq_false"), vec![]);
    let testbit = Expr::const_(Name::from_string("Nat.testBit"), vec![]);
    let testbit_lt_pow = Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]);
    let eq_of_testbit = Expr::const_(Name::from_string("Nat.eq_of_testBit_eq"), vec![]);
    let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
    let le_or_lt = Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]);
    let lt_of_lt_of_le = Expr::const_(Name::from_string("Nat.lt_of_lt_of_le"), vec![]);
    let or_cases = Expr::const_(Name::from_string("Or.casesOn"), vec![]);
    let bool_rec_nat = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
    let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);

    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
    let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
    let val = |n: &Expr, k: &Expr| Expr::apps(fin_val.clone(), [n.clone(), k.clone()]);
    let testbit_of = |a: Expr, b: Expr| Expr::apps(testbit.clone(), [a, b]);
    let le = |a: Expr, b: Expr| Expr::apps(nat_le.clone(), [a, b]);
    let lt = |a: Expr, b: Expr| Expr::apps(nat_lt.clone(), [a, b]);
    let xor = |a: Expr, b: Expr| Expr::apps(bool_xor.clone(), [a, b]);
    let eq_n = |l: Expr, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [nat.clone(), l, r],
        )
    };
    let eq_b = |l: Expr, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [bool_.clone(), l, r],
        )
    };
    let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
    // indNat b = @Bool.rec (fun _ => Nat) 0 1 b (the setSizeNat summand)
    let nat_motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
    let ind_nat = |b: Expr| {
        Expr::apps(
            bool_rec_nat.clone(),
            [nat_motive.clone(), nat_zero.clone(), one_nat.clone(), b],
        )
    };
    // (hcDecode n k) i
    let decode_at = |n: &Expr, k: &Expr, i: Expr| {
        Expr::app(Expr::apps(hc_decode.clone(), [n.clone(), k.clone()]), i)
    };
    // S Δ T as an HCPoint: fun i => Bool.xor ((hcDecode n jS) i) ((hcDecode n jT) i)
    let sd_fn = |parent: &EnvDeclBuilder, n: &Expr, js: &Expr, jt: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = d.fresh_local(fin_of(n));
        let body = xor(decode_at(n, js, i.clone()), decode_at(n, jt, i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(n), body))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (js_id, js) = b.fresh_local(fin_of(&pow2(&n)));
        let (jt_id, jt) = b.fresh_local(fin_of(&pow2(&n)));
        let sd = sd_fn(&b, &n, &js, &jt);
        let ss = Expr::apps(set_size_nat.clone(), [n.clone(), sd]);
        let hyp = eq_n(ss, nat_zero.clone());
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let concl = eq_n(val(&pow2(&n), &js), val(&pow2(&n), &jt));
        let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let e = b.mk_pi(jt_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_pi(js_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (js_id, js) = b.fresh_local(fin_of(&pow2(&n)));
        let (jt_id, jt) = b.fresh_local(fin_of(&pow2(&n)));
        let sd = sd_fn(&b, &n, &js, &jt);
        let ss = Expr::apps(set_size_nat.clone(), [n.clone(), sd]);
        let hyp = eq_n(ss, nat_zero.clone());
        let (h_id, h) = b.fresh_local(hyp.clone());

        // summand : fun (i : Fin n) => indNat ((S Δ T) i)
        let summand = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(fin_of(&n));
            let sd_i = xor(decode_at(&n, &js, i.clone()), decode_at(&n, &jt, i.clone()));
            let body = ind_nat(sd_i);
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_of(&n), body))
        };

        // allZero : ∀ i : Fin n, indNat ((S Δ T) i) = 0  := Fin.sumNat_eq_zero n summand h
        //   (h : setSizeNat n (S Δ T) = 0 ≡ Fin.sumNat n summand = 0, reducible)
        let all_zero = Expr::apps(
            fin_sum_nat_eq_zero.clone(),
            [n.clone(), summand.clone(), h.clone()],
        );

        let vs = val(&pow2(&n), &js);
        let vt = val(&pow2(&n), &jt);

        // allBits : ∀ (j : Nat), testBit (val jS) j = testBit (val jT) j
        let all_bits = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(nat.clone());
            let bit_s = testbit_of(vs.clone(), j.clone());
            let bit_t = testbit_of(vt.clone(), j.clone());
            let target = eq_b(bit_s.clone(), bit_t.clone());

            let or_a = le(n.clone(), j.clone());
            let or_b = lt(j.clone(), n.clone());
            let or_motive = {
                let mut m = EnvDeclBuilder::child_of(&d);
                let or_ty = Expr::apps(
                    Expr::const_(Name::from_string("Or"), vec![]),
                    [or_a.clone(), or_b.clone()],
                );
                let (z_id, _z) = m.fresh_local(or_ty.clone());
                m.finish_child(m.mk_lam(z_id, BinderInfo::Default, or_ty, target.clone()))
            };

            // high_minor : n ≤ j → testBit (val jS) j = testBit (val jT) j
            //   Both testBits are false: testBit_lt_pow on each (val k < 2^n ≤ 2^j),
            //   then bit_s = false = bit_t via Eq.trans (·) (Eq.symm ·).
            let high_minor = {
                let mut m = EnvDeclBuilder::child_of(&d);
                let (hle_id, hle) = m.fresh_local(or_a.clone());
                let zero_le_one = Expr::apps(
                    Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                    [one_nat.clone()],
                );
                let one_le_two = Expr::apps(
                    Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
                    [nat_zero.clone(), one_nat.clone(), zero_le_one],
                );
                let pow_le = Expr::apps(
                    pow_le_pow_right.clone(),
                    [two_nat.clone(), n.clone(), j.clone(), one_le_two, hle],
                );
                // false-bit for a given index k with value vk: testBit_lt_pow j vk lt_vk
                let false_bit = |vk: &Expr, k: &Expr, m: &EnvDeclBuilder| -> Expr {
                    let islt = Expr::apps(fin_islt.clone(), [pow2(&n), k.clone()]);
                    let lt_vk = Expr::apps(
                        lt_of_lt_of_le.clone(),
                        [vk.clone(), pow2(&n), pow2(&j), islt, pow_le.clone()],
                    );
                    Expr::apps(testbit_lt_pow.clone(), [j.clone(), vk.clone(), lt_vk])
                };
                // hs : bit_s = false ; ht : bit_t = false
                let hs = false_bit(&vs, &js, &m);
                let ht = false_bit(&vt, &jt, &m);
                // ht_sym : false = bit_t
                let ht_sym = Expr::apps(
                    eq_symm.clone(),
                    [bool_.clone(), bit_t.clone(), bool_false.clone(), ht],
                );
                // bit_s = false = bit_t
                let body = Expr::apps(
                    eq_trans.clone(),
                    [
                        bool_.clone(),
                        bit_s.clone(),
                        bool_false.clone(),
                        bit_t.clone(),
                        hs,
                        ht_sym,
                    ],
                );
                m.finish_child(m.mk_lam(hle_id, BinderInfo::Default, or_a.clone(), body))
            };

            // low_minor : j < n → testBit (val jS) j = testBit (val jT) j
            //   ⟨j,hlt⟩ : Fin n; (hcDecode n k) ⟨j,hlt⟩ ≡ testBit (val k) j (def-eq).
            //   allZero ⟨j⟩ : indNat ((S Δ T) ⟨j⟩) = 0
            //   indNat_eq_zero (…) (allZero ⟨j⟩) : (S Δ T) ⟨j⟩ = false
            //     ≡ Bool.xor (testBit (val jS) j) (testBit (val jT) j) = false (def-eq)
            //   Bool.eq_of_xor_eq_false bit_s bit_t (that) : bit_s = bit_t.
            let low_minor = {
                let mut m = EnvDeclBuilder::child_of(&d);
                let (hlt_id, hlt) = m.fresh_local(or_b.clone());
                let fin_j = Expr::apps(fin_mk.clone(), [n.clone(), j.clone(), hlt.clone()]);
                let sd_at = xor(
                    decode_at(&n, &js, fin_j.clone()),
                    decode_at(&n, &jt, fin_j.clone()),
                );
                let az = Expr::app(all_zero.clone(), fin_j);
                // hxor : (S Δ T) ⟨j⟩ = false
                let hxor = Expr::apps(indnat_eq_zero.clone(), [sd_at, az]);
                // Bool.eq_of_xor_eq_false bit_s bit_t hxor : bit_s = bit_t
                let body = Expr::apps(eq_of_xor.clone(), [bit_s.clone(), bit_t.clone(), hxor]);
                m.finish_child(m.mk_lam(hlt_id, BinderInfo::Default, or_b.clone(), body))
            };

            let lor = Expr::apps(le_or_lt.clone(), [n.clone(), j.clone()]);
            let body = Expr::apps(
                or_cases.clone(),
                [or_a, or_b, or_motive, lor, high_minor, low_minor],
            );
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, nat.clone(), body))
        };

        // Nat.eq_of_testBit_eq (val jS) (val jT) allBits : val jS = val jT
        let final_pf = Expr::apps(eq_of_testbit.clone(), [vs.clone(), vt.clone(), all_bits]);

        let e = b.mk_lam(h_id, BinderInfo::Default, hyp, final_pf);
        let e = b.mk_lam(jt_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_lam(js_id, BinderInfo::Default, fin_of(&pow2(&n)), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn assert_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_bool_eq_of_xor_eq_false_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_bool_eq_of_xor_eq_false()
            .expect("register_bool_eq_of_xor_eq_false");
        env.register_bool_eq_of_xor_eq_false().expect("idempotent");
        assert_constructive(&env, "Bool.eq_of_xor_eq_false");
    }

    #[test]
    fn test_setsizenat_symmdiff_imp_val_eq_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_setsizenat_symmdiff_hcdecode_imp_val_eq()
            .expect("register_setsizenat_symmdiff_hcdecode_imp_val_eq");
        env.register_setsizenat_symmdiff_hcdecode_imp_val_eq()
            .expect("idempotent");
        assert_constructive(&env, "BoolAnalysis.setSizeNat_symmDiff_hcDecode_imp_val_eq");
    }
}
