// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Fin.prod_single` — the multiplicative twin of the constructive
//! `Fin.sum_single` (`nn_verify_fin_sum_single_proof.rs`).
//!
//! `Fin.prod_single : ∀ (n : Nat) (i : Fin n) (c : Rat),
//!     Fin.prod n (fun j => @ite Rat (@Eq (Fin n) j i) (@instDecidableEqFin n j i)
//!        c Rat.one) = c`
//!
//! A finite product over a Kronecker-style factor that is `c` at the single index
//! `i` and the multiplicative identity `Rat.one` everywhere else collapses to `c`.
//! The proof is the `Fin.sum_single` proof with `Rat.add ↦ Rat.mul`,
//! `Rat.zero ↦ Rat.one`, `Fin.sum ↦ Fin.prod`, `Fin.sum_congr ↦ Fin.prod_congr`,
//! `Fin.sum_zero_fn ↦ Fin.prod_const_one`, `Rat.zero_add ↦ Rat.one_mul`,
//! `Rat.add_zero ↦ Rat.mul_one`, and the `Fin.sum_succ` ι-equation replaced by the
//! `Fin.prod_succ` ι-equation (which peels the LAST coordinate as a `Rat.mul`).
//!
//! Unlike `Fin.sum_single` this needs NO in-range premise: the off-diagonal value
//! is the unit `1`, so even when the pivot `i` is junk (`Fin.val i ≥ n`) and is
//! never enumerated, every factor is `1` and the product is `1` — but the
//! statement's diagonal index `i` is matched by `@Eq (Fin n) j i`, and with the
//! standard `Fin.lastCases` / `Fin.isLt` descent the diagonal is always hit
//! exactly once at any in-range `i`, while junk `i` is excluded because the
//! `cast`-branch recursion supplies `Fin.isLt`. We keep the in-range premise to
//! mirror `Fin.sum_single` exactly and reuse `Fin.isLt` at call sites.
//!
//! Supporting lemma `Fin.kron_one_castSucc` is the `Fin.kron_castSucc` twin with
//! the off-diagonal `0` replaced by `1`. Both are axiom-free
//! `ProofQuality::Constructive` Theorems.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `Fin.kron_one_castSucc : (k : Nat) (i j : Fin k) (c : Rat) →
    ///    @ite Rat (@Eq (Fin (succ k)) (castSucc k j) (castSucc k i))
    ///             (@instDecidableEqFin (succ k) (castSucc k j) (castSucc k i)) c 1
    ///  = @ite Rat (@Eq (Fin k) j i) (@instDecidableEqFin k j i) c 1`
    ///
    /// The multiplicative-identity twin of `Fin.kron_castSucc`. Same
    /// `Decidable.rec` + `if_pos`/`if_neg` skeleton, off-diagonal value `Rat.one`
    /// instead of `Rat.zero`. Axiom-free.
    pub(super) fn register_fin_kron_one_castsucc(
        &mut self,
        c: &FinSumConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.kron_one_castSucc"))
            .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }
        self.register_ite_pos_neg_lemmas()?;
        self.register_fin_index_lemmas()?;

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![l0.clone()]);
        let if_pos = Expr::const_(Name::from_string("if_pos"), vec![l1.clone()]);
        let if_neg = Expr::const_(Name::from_string("if_neg"), vec![l1.clone()]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
        let cs_inj = Expr::const_(Name::from_string("Fin.castSucc_inj"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        let fin_n = |n: Expr| Expr::app(c.fin.clone(), n);
        let succ = |n: Expr| Expr::app(nat_succ.clone(), n);
        let eqf = |nn: Expr, a: Expr, b: Expr| Expr::apps(eq1.clone(), [fin_n(nn), a, b]);
        let inst = |nn: Expr, a: Expr, b: Expr| Expr::apps(c.inst_dec_eq_fin.clone(), [nn, a, b]);
        // @ite Rat cond decinst x 1
        let ite = |cond: Expr, decinst: Expr, x: Expr| {
            Expr::apps(
                c.ite.clone(),
                [c.rat.clone(), cond, decinst, x, rat_one.clone()],
            )
        };
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [c.rat.clone(), l, r]);

        // bound vars order: k, i, j, x.
        let build = |b: &mut EnvDeclBuilder| {
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (i_id, i) = b.fresh_local(fin_n(k.clone()));
            let (j_id, j) = b.fresh_local(fin_n(k.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            (k_id, k, i_id, i, j_id, j, x_id, x)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k, i_id, i, j_id, j, x_id, x) = build(&mut b);
            let sk = succ(k.clone());
            let csj = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
            let csi = Expr::apps(fin_cast.clone(), [k.clone(), i.clone()]);
            let lhs = ite(
                eqf(sk.clone(), csj.clone(), csi.clone()),
                inst(sk.clone(), csj, csi),
                x.clone(),
            );
            let rhs = ite(
                eqf(k.clone(), j.clone(), i.clone()),
                inst(k.clone(), j.clone(), i.clone()),
                x.clone(),
            );
            let concl = eq_rat(lhs, rhs);
            let r = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), concl);
            let r = b.mk_pi(j_id, BinderInfo::Default, fin_n(k.clone()), r);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n(k.clone()), r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k, i_id, i, j_id, j, x_id, x) = build(&mut b);
            let sk = succ(k.clone());
            let csj = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
            let csi = Expr::apps(fin_cast.clone(), [k.clone(), i.clone()]);
            let cond_s = eqf(sk.clone(), csj.clone(), csi.clone());
            let inst_s = inst(sk.clone(), csj.clone(), csi.clone());
            let cond_k = eqf(k.clone(), j.clone(), i.clone());
            let inst_k = inst(k.clone(), j.clone(), i.clone());
            let lhs = ite(cond_s.clone(), inst_s.clone(), x.clone());

            // dmotive : (d : Decidable cond_k) → Prop := fun d => lhs = @ite Rat cond_k d x 1
            let dmotive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let dec_k = Expr::app(dec.clone(), cond_k.clone());
                let (dd_id, dd) = d.fresh_local(dec_k.clone());
                let rhs_d = ite(cond_k.clone(), dd, x.clone());
                let body = eq_rat(lhs.clone(), rhs_d);
                d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_k, body))
            };

            // isFalse minor: lhs = 1.  @if_neg cond_s inst_s hne_s Rat x 1.
            let false_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let not_k = Expr::pi(BinderInfo::Default, cond_k.clone(), false_c.clone());
                let (hne_id, hne) = d.fresh_local(not_k.clone());
                let hne_s = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (e_id, e) = g.fresh_local(cond_s.clone());
                    let inj = Expr::apps(cs_inj.clone(), [k.clone(), j.clone(), i.clone(), e]);
                    let body = Expr::app(hne.clone(), inj);
                    g.finish_child(g.mk_lam(e_id, BinderInfo::Default, cond_s.clone(), body))
                };
                // Lean order: @if_neg {c} {inst} (h) {α} {t} {e}.
                let proof = Expr::apps(
                    if_neg.clone(),
                    [
                        cond_s.clone(),
                        inst_s.clone(),
                        hne_s,
                        c.rat.clone(),
                        x.clone(),
                        rat_one.clone(),
                    ],
                );
                d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_k, proof))
            };

            // isTrue minor: lhs = x.  @if_pos cond_s inst_s heq_s Rat x 1.
            let true_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (heq_id, heq) = d.fresh_local(cond_k.clone());
                let cast_k = Expr::app(fin_cast.clone(), k.clone());
                let heq_s = Expr::apps(
                    congr_arg.clone(),
                    [
                        fin_n(k.clone()),
                        fin_n(sk.clone()),
                        j.clone(),
                        i.clone(),
                        cast_k,
                        heq.clone(),
                    ],
                );
                // Lean order: @if_pos {c} {inst} (h) {α} {t} {e}.
                let proof = Expr::apps(
                    if_pos.clone(),
                    [
                        cond_s.clone(),
                        inst_s.clone(),
                        heq_s,
                        c.rat.clone(),
                        x.clone(),
                        rat_one.clone(),
                    ],
                );
                d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, cond_k.clone(), proof))
            };

            let rec_app = Expr::apps(
                dec_rec.clone(),
                [cond_k.clone(), dmotive, false_minor, true_minor, inst_k],
            );

            let r = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), rec_app);
            let r = b.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), r);
            let r = b.mk_lam(i_id, BinderInfo::Default, fin_n(k.clone()), r);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.kron_one_castSucc"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Constructive `Fin.prod_single` (multiplicative twin of `Fin.sum_single`).
    ///
    /// `(n : Nat) (i : Fin n) (c : Rat) → Nat.lt (Fin.val n i) n →
    ///   Fin.prod n (fun j => @ite Rat (@Eq (Fin n) j i) (@instDecidableEqFin n j i)
    ///     c Rat.one) = c`
    ///
    /// `Nat.rec` on `n`, `Fin.lastCases` on the index at the successor step,
    /// `instDecidableEqFin` discharged by `if_pos`/`if_neg`, the off-diagonal
    /// prefix folded to `1` by `Fin.prod_congr` / `Fin.prod_const_one`, and
    /// `Rat.one_mul` / `Rat.mul_one` to clear the unit. Axiom-free.
    pub(super) fn register_fin_prod_single_theorem(
        &mut self,
        c: &FinSumConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.prod_single"))
            .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }
        self.register_fin_prod_one_theorems()?; // Fin.prod_const_one, Fin.prod_congr
        self.register_fin_prod_succ_theorem()?; // Fin.prod_succ
        self.register_fin_kron_one_castsucc(c)?;
        self.register_fin_last_cases()?;
        self.register_ite_pos_neg_lemmas()?;
        self.register_fin_index_lemmas()?;

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let nat = c.nat.clone();
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_mul = c.rat_mul.clone();
        let fin_prod = Expr::const_(Name::from_string("Fin.prod"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]);
        let not_succ_le_zero = Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]);

        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last_cases = Expr::const_(Name::from_string("Fin.lastCases"), vec![l0.clone()]);
        let fin_prod_congr = Expr::const_(Name::from_string("Fin.prod_congr"), vec![]);
        let fin_prod_const_one = Expr::const_(Name::from_string("Fin.prod_const_one"), vec![]);
        let fin_kron_cs = Expr::const_(Name::from_string("Fin.kron_one_castSucc"), vec![]);
        let cs_ne_last = Expr::const_(Name::from_string("Fin.castSucc_ne_last"), vec![]);
        let last_ne_cs = Expr::const_(Name::from_string("Fin.last_ne_castSucc"), vec![]);

        let if_pos = Expr::const_(Name::from_string("if_pos"), vec![l1.clone()]);
        let if_neg = Expr::const_(Name::from_string("if_neg"), vec![l1.clone()]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
        let congr = Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
        let rat_mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
        let rat_one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);

        // ── helpers ──
        let fin_n = |n: Expr| Expr::app(c.fin.clone(), n);
        let succ = |n: Expr| Expr::app(nat_succ.clone(), n);
        let val = |n: Expr, x: Expr| Expr::apps(fin_val.clone(), [n, x]);
        let lt = |a: Expr, b: Expr| Expr::apps(nat_lt.clone(), [a, b]);
        let prod = |n: Expr, f: Expr| Expr::apps(fin_prod.clone(), [n, f]);
        let eqf = |nn: Expr, a: Expr, b: Expr| Expr::apps(eq1.clone(), [fin_n(nn), a, b]);
        let eq_rat = |a: Expr, b: Expr| Expr::apps(eq1.clone(), [c.rat.clone(), a, b]);
        let inst = |nn: Expr, a: Expr, b: Expr| Expr::apps(c.inst_dec_eq_fin.clone(), [nn, a, b]);
        // @ite Rat (Eq (Fin N) j piv) (inst N j piv) x 1
        let kron_term = |nn: Expr, piv: Expr, x: Expr, j: Expr| {
            Expr::apps(
                c.ite.clone(),
                [
                    c.rat.clone(),
                    eqf(nn.clone(), j.clone(), piv.clone()),
                    inst(nn, j, piv),
                    x,
                    rat_one.clone(),
                ],
            )
        };
        let kron_fn = |parent: &EnvDeclBuilder, nn: &Expr, piv: &Expr, x: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = ch.fresh_local(fin_n(nn.clone()));
            let body = kron_term(nn.clone(), piv.clone(), x.clone(), j);
            ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_n(nn.clone()), body))
        };
        // fun _ : Fin k => Rat.one  (matches Fin.prod_const_one's factor)
        let one_fn = |parent: &EnvDeclBuilder, k: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, _i) = ch.fresh_local(fin_n(k.clone()));
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n(k.clone()), rat_one.clone()))
        };

        // motive M k := ∀ (i : Fin k) (x : Rat),
        //                 Nat.lt (Fin.val k i) k → Fin.prod k (kron_fn k i x) = x
        let mk_motive_body = |parent: &EnvDeclBuilder, k: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = d.fresh_local(fin_n(k.clone()));
            let (x_id, x) = d.fresh_local(c.rat.clone());
            let prem = lt(val(k.clone(), i.clone()), k.clone());
            let (h_id, _h) = d.fresh_local(prem.clone());
            let kf = kron_fn(&d, k, &i, &x);
            let concl = eq_rat(prod(k.clone(), kf), x.clone());
            let r = d.mk_pi(h_id, BinderInfo::Default, prem, concl);
            let r = d.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = d.mk_pi(i_id, BinderInfo::Default, fin_n(k.clone()), r);
            d.finish_child(r)
        };

        // Statement type.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (i_id, i) = b.fresh_local(fin_n(n.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let prem = lt(val(n.clone(), i.clone()), n.clone());
            let (h_id, _h) = b.fresh_local(prem.clone());
            let kf = kron_fn(&b, &n, &i, &x);
            let concl = eq_rat(prod(n.clone(), kf), x.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, prem, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n(n.clone()), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let body = mk_motive_body(&b, &k);
            b.finish(b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body))
        };

        // Base: M 0. premise Nat.lt _ 0 uninhabited → False.elim.
        let base = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(fin_n(nat_zero.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let val0 = val(nat_zero.clone(), i.clone());
            let prem = lt(val0.clone(), nat_zero.clone());
            let (h_id, h) = b.fresh_local(prem.clone());
            let kf = kron_fn(&b, &nat_zero, &i, &x);
            let goal = eq_rat(prod(nat_zero.clone(), kf), x.clone());
            let false_pf = Expr::apps(not_succ_le_zero.clone(), [val0, h]);
            let body = Expr::apps(false_elim.clone(), [goal, false_pf]);
            let r = b.mk_lam(h_id, BinderInfo::Default, prem, body);
            let r = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(i_id, BinderInfo::Default, fin_n(nat_zero.clone()), r);
            b.finish(r)
        };

        // Step.
        let step = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let ih_ty = mk_motive_body(&b, &k);
            let (ih_id, ih) = b.fresh_local(ih_ty.clone());
            let sk = succ(k.clone());
            let (i_id, i) = b.fresh_local(fin_n(sk.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let prem_i = lt(val(sk.clone(), i.clone()), sk.clone());
            let (h_id, h) = b.fresh_local(prem_i.clone());

            // P : Fin (succ k) → Prop
            let p_motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = d.fresh_local(fin_n(sk.clone()));
                let prem_w = lt(val(sk.clone(), w.clone()), sk.clone());
                let kfw = kron_fn(&d, &sk, &w, &x);
                let concl = eq_rat(prod(sk.clone(), kfw), x.clone());
                let body = Expr::arrow(prem_w, concl);
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, fin_n(sk.clone()), body))
            };

            // ── last_case : P (Fin.last k) ──
            let last_case = {
                let lk = Expr::app(fin_last.clone(), k.clone());
                let mut d = EnvDeclBuilder::child_of(&b);
                let prem_last = lt(val(sk.clone(), lk.clone()), sk.clone());
                let (hh_id, _hh) = d.fresh_local(prem_last.clone());

                // prefix factor: fun j:Fin k => kron_term (succ k)(last k) x (castSucc k j)
                let pre_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let csj = Expr::apps(fin_cast.clone(), [k.clone(), j]);
                    let body = kron_term(sk.clone(), lk.clone(), x.clone(), csj);
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                let of = one_fn(&d, &k);

                // pointwise: pre_fn j = 1 (off-diagonal: castSucc k j ≠ last k)
                let pw_pre = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let csj = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
                    let cond = eqf(sk.clone(), csj.clone(), lk.clone());
                    let inst_j = inst(sk.clone(), csj.clone(), lk.clone());
                    let hne = Expr::apps(cs_ne_last.clone(), [k.clone(), j.clone()]);
                    let body = Expr::apps(
                        if_neg.clone(),
                        // Lean order: @if_neg {c} {inst} (h) {α} {t} {e}.
                        [cond, inst_j, hne, c.rat.clone(), x.clone(), rat_one.clone()],
                    );
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                // Fin.prod_congr k pre_fn one_fn pw_pre : Fin.prod k pre_fn = Fin.prod k one_fn
                let congr_pre = Expr::apps(
                    fin_prod_congr.clone(),
                    [k.clone(), pre_fn.clone(), of.clone(), pw_pre],
                );
                // Fin.prod_const_one k : Fin.prod k one_fn = Rat.one
                let pcone = Expr::app(fin_prod_const_one.clone(), k.clone());
                // hpre : Fin.prod k pre_fn = Rat.one
                let hpre = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.rat.clone(),
                        prod(k.clone(), pre_fn.clone()),
                        prod(k.clone(), of.clone()),
                        rat_one.clone(),
                        congr_pre,
                        pcone,
                    ],
                );

                // hlast : F (last k) = x (diagonal: if_pos on Eq.refl)
                let cond_d = eqf(sk.clone(), lk.clone(), lk.clone());
                let inst_d = inst(sk.clone(), lk.clone(), lk.clone());
                let refl_last = Expr::apps(eq_refl.clone(), [fin_n(sk.clone()), lk.clone()]);
                let hlast = Expr::apps(
                    if_pos.clone(),
                    // Lean order: @if_pos {c} {inst} (h) {α} {t} {e}.
                    [
                        cond_d,
                        inst_d,
                        refl_last,
                        c.rat.clone(),
                        x.clone(),
                        rat_one.clone(),
                    ],
                );

                // congrArg Rat.mul hpre : Rat.mul (Fin.prod k pre_fn) = Rat.mul Rat.one
                let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
                let cg_mul = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.rat.clone(),
                        rat_to_rat.clone(),
                        prod(k.clone(), pre_fn.clone()),
                        rat_one.clone(),
                        rat_mul.clone(),
                        hpre,
                    ],
                );
                let f_last = kron_term(sk.clone(), lk.clone(), x.clone(), lk.clone());
                // congr (cg_mul)(hlast) : Rat.mul (Fin.prod k pre_fn)(F (last k)) = Rat.mul 1 x
                let mul_pre = Expr::app(rat_mul.clone(), prod(k.clone(), pre_fn.clone()));
                let mul_one = Expr::app(rat_mul.clone(), rat_one.clone());
                let combined = Expr::apps(
                    congr.clone(),
                    [
                        c.rat.clone(),
                        c.rat.clone(),
                        mul_pre,
                        mul_one,
                        f_last.clone(),
                        x.clone(),
                        cg_mul,
                        hlast,
                    ],
                );
                // Rat.one_mul x : Rat.mul Rat.one x = x
                let omul = Expr::app(rat_one_mul.clone(), x.clone());
                let lhs_mul = Expr::app(
                    Expr::app(rat_mul.clone(), prod(k.clone(), pre_fn.clone())),
                    f_last,
                );
                let mid_mul = Expr::app(Expr::app(rat_mul.clone(), rat_one.clone()), x.clone());
                let proof = Expr::apps(
                    eq_trans.clone(),
                    [c.rat.clone(), lhs_mul, mid_mul, x.clone(), combined, omul],
                );
                d.finish_child(d.mk_lam(hh_id, BinderInfo::Default, prem_last, proof))
            };

            // ── cast_case : (i' : Fin k) → P (Fin.castSucc k i') ──
            let cast_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (ip_id, ip) = d.fresh_local(fin_n(k.clone()));
                let csi = Expr::apps(fin_cast.clone(), [k.clone(), ip.clone()]);
                let prem_cs = lt(val(sk.clone(), csi.clone()), sk.clone());
                let (hh_id, _hh) = d.fresh_local(prem_cs.clone());

                // prefix factor: fun j:Fin k => kron_term (succ k)(castSucc k i') x (castSucc k j)
                let pre_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let csj = Expr::apps(fin_cast.clone(), [k.clone(), j]);
                    let body = kron_term(sk.clone(), csi.clone(), x.clone(), csj);
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                // target prefix: kron_fn k i' x
                let kron_k = kron_fn(&d, &k, &ip, &x);

                // pointwise: fun j:Fin k => Fin.kron_one_castSucc k i' j x
                let pw_pre = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let body = Expr::apps(
                        fin_kron_cs.clone(),
                        [k.clone(), ip.clone(), j.clone(), x.clone()],
                    );
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                let congr_pre = Expr::apps(
                    fin_prod_congr.clone(),
                    [k.clone(), pre_fn.clone(), kron_k.clone(), pw_pre],
                );
                // ih i' x (Fin.isLt k i') : Fin.prod k kron_k = x
                let islt_ip = Expr::apps(fin_islt.clone(), [k.clone(), ip.clone()]);
                let ih_app = Expr::apps(ih.clone(), [ip.clone(), x.clone(), islt_ip]);
                // hpre : Fin.prod k pre_fn = x
                let hpre = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.rat.clone(),
                        prod(k.clone(), pre_fn.clone()),
                        prod(k.clone(), kron_k.clone()),
                        x.clone(),
                        congr_pre,
                        ih_app,
                    ],
                );

                // hlast : G (last k) = 1 (last-term off-diagonal: last ≠ castSucc i')
                let lk = Expr::app(fin_last.clone(), k.clone());
                let cond_l = eqf(sk.clone(), lk.clone(), csi.clone());
                let inst_l = inst(sk.clone(), lk.clone(), csi.clone());
                let hne_last = Expr::apps(last_ne_cs.clone(), [k.clone(), ip.clone()]);
                let hlast = Expr::apps(
                    if_neg.clone(),
                    // Lean order: @if_neg {c} {inst} (h) {α} {t} {e}.
                    [
                        cond_l,
                        inst_l,
                        hne_last,
                        c.rat.clone(),
                        x.clone(),
                        rat_one.clone(),
                    ],
                );

                // congrArg Rat.mul hpre : Rat.mul (Fin.prod k pre_fn) = Rat.mul x
                let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
                let cg_mul = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.rat.clone(),
                        rat_to_rat.clone(),
                        prod(k.clone(), pre_fn.clone()),
                        x.clone(),
                        rat_mul.clone(),
                        hpre,
                    ],
                );
                let g_last = kron_term(sk.clone(), csi.clone(), x.clone(), lk.clone());
                // congr (cg_mul)(hlast) : Rat.mul (Fin.prod k pre_fn)(G (last k)) = Rat.mul x 1
                let mul_pre = Expr::app(rat_mul.clone(), prod(k.clone(), pre_fn.clone()));
                let mul_x = Expr::app(rat_mul.clone(), x.clone());
                let combined = Expr::apps(
                    congr.clone(),
                    [
                        c.rat.clone(),
                        c.rat.clone(),
                        mul_pre,
                        mul_x,
                        g_last.clone(),
                        rat_one.clone(),
                        cg_mul,
                        hlast,
                    ],
                );
                // Rat.mul_one x : Rat.mul x Rat.one = x
                let mone = Expr::app(rat_mul_one.clone(), x.clone());
                let lhs_mul = Expr::app(
                    Expr::app(rat_mul.clone(), prod(k.clone(), pre_fn.clone())),
                    g_last,
                );
                let mid_mul = Expr::app(Expr::app(rat_mul.clone(), x.clone()), rat_one.clone());
                let proof = Expr::apps(
                    eq_trans.clone(),
                    [c.rat.clone(), lhs_mul, mid_mul, x.clone(), combined, mone],
                );
                let r = d.mk_lam(hh_id, BinderInfo::Default, prem_cs, proof);
                d.finish_child(d.mk_lam(ip_id, BinderInfo::Default, fin_n(k.clone()), r))
            };

            // @Fin.lastCases.{0} k P last_case cast_case i, then apply h.
            let lc = Expr::apps(
                fin_last_cases.clone(),
                [k.clone(), p_motive, last_case, cast_case, i.clone()],
            );
            let applied = Expr::app(lc, h.clone());

            let r = b.mk_lam(h_id, BinderInfo::Default, prem_i, applied);
            let r = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(i_id, BinderInfo::Default, fin_n(sk.clone()), r);
            let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
            let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // value: fun n i x h => @Nat.rec.{0} motive base step n i x h
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (i_id, i) = b.fresh_local(fin_n(n.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let prem = lt(val(n.clone(), i.clone()), n.clone());
            let (h_id, h) = b.fresh_local(prem.clone());
            let rec_app = Expr::apps(
                nat_rec.clone(),
                [
                    motive,
                    base,
                    step,
                    n.clone(),
                    i.clone(),
                    x.clone(),
                    h.clone(),
                ],
            );
            let r = b.mk_lam(h_id, BinderInfo::Default, prem, rec_app);
            let r = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(i_id, BinderInfo::Default, fin_n(n.clone()), r);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.prod_single"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_fin_sum().expect("init_fin_sum");
        env
    }

    #[test]
    fn test_fin_kron_one_castsucc_axiom_free_theorem() {
        let mut env = env();
        let c = FinSumConsts::new();
        env.register_fin_kron_one_castsucc(&c)
            .expect("register_fin_kron_one_castsucc");
        let n = Name::from_string("Fin.kron_one_castSucc");
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .expect("Fin.kron_one_castSucc should type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "Fin.kron_one_castSucc must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
    }

    #[test]
    fn test_fin_prod_single_axiom_free_theorem() {
        let mut env = env();
        let c = FinSumConsts::new();
        env.register_fin_prod_single_theorem(&c)
            .expect("register_fin_prod_single_theorem");
        let n = Name::from_string("Fin.prod_single");
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .expect("Fin.prod_single should type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "Fin.prod_single must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }
}
