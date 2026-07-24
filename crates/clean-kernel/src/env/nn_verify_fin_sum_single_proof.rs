// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.sum_single` (the last TCB `Fin` axiom) plus its
//! supporting congruence lemma `Fin.sum_congr`. Real kernel-checked terms (NO
//! `sorry`, NO axiom), built on the FAITHFUL `Fin` carrier.
//!
//! - `Fin.sum_congr : (n : Nat) (f g : Fin n → Rat) → (∀ i, f i = g i)
//!     → Fin.sum n f = Fin.sum n g` — pointwise-equal summands give equal sums.
//!     Proved by `Nat.rec` on `n` using the `Fin.sum` carrier's ι-equations
//!     (`Fin.sum 0 _ ≡ 0`, `Fin.sum (succ k) f ≡ Rat.add (Fin.sum k (f∘castSucc))
//!     (f (last k))`) + `congr`/`congrArg`.
//!
//! - `Fin.sum_single : (n : Nat) (i : Fin n) (x : Rat) → Nat.lt (Fin.val i) n
//!     → Fin.sum n (fun j => @ite Rat (Eq (Fin n) j i) (instDecidableEqFin j i)
//!        x 0) = x` — Kronecker-delta collapse. Proved by `Nat.rec` on `n`,
//!     `Fin.lastCases` on the index at the successor step, the now-computable
//!     `instDecidableEqFin` discharged by `if_pos`/`if_neg`, and
//!     `Fin.sum_congr` to fold the off-diagonal prefix sum to zero.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `Fin.sum_congr : (n : Nat) (f g : Fin n → Rat)
    ///     → (∀ i : Fin n, f i = g i) → Fin.sum n f = Fin.sum n g`.
    ///
    /// Constructive `Nat.rec` induction; axiom-free.
    pub(super) fn register_fin_sum_congr(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.sum_congr"))
            .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }

        let l1 = Level::succ(Level::zero());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let congr = Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

        // helpers
        let fin_n = |n: Expr| Expr::app(c.fin.clone(), n);
        let sum = |n: Expr, f: Expr| Expr::apps(c.fin_sum.clone(), [n, f]);
        let app1 = |f: Expr, a: Expr| Expr::app(f, a);
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [c.rat.clone(), l, r]);
        // f ∘ castSucc k := fun i : Fin k => f (Fin.castSucc k i)
        let comp_cast = |parent: &EnvDeclBuilder, k: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = ch.fresh_local(fin_n(k.clone()));
            let cast_i = Expr::apps(fin_cast.clone(), [k.clone(), i]);
            let body = Expr::app(f.clone(), cast_i);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n(k.clone()), body))
        };

        // pointwise hypothesis type: ∀ i : Fin n, f i = g i
        let hyp_ty = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = ch.fresh_local(fin_n(n.clone()));
            let body = eq_rat(app1(f.clone(), i.clone()), app1(g.clone(), i));
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n(n.clone()), body))
        };

        // Statement type.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ft = c.fin_to_rat(n.clone());
            let (f_id, f) = b.fresh_local(ft.clone());
            let (g_id, g) = b.fresh_local(ft.clone());
            let h = hyp_ty(&b, &n, &f, &g);
            let (h_id, _h) = b.fresh_local(h.clone());
            let concl = eq_rat(sum(n.clone(), f.clone()), sum(n.clone(), g.clone()));
            let r = b.mk_pi(h_id, BinderInfo::Default, h, concl);
            let r = b.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
            let r = b.mk_pi(f_id, BinderInfo::Default, ft, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // motive: fun (k : Nat) => ∀ (f g : Fin k → Rat), (∀ i, f i = g i)
        //                                  → Fin.sum k f = Fin.sum k g
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let inner = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let ft = c.fin_to_rat(k.clone());
                let (f_id, f) = d.fresh_local(ft.clone());
                let (g_id, g) = d.fresh_local(ft.clone());
                let h = hyp_ty(&d, &k, &f, &g);
                let (h_id, _h) = d.fresh_local(h.clone());
                let concl = eq_rat(sum(k.clone(), f.clone()), sum(k.clone(), g.clone()));
                let r = d.mk_pi(h_id, BinderInfo::Default, h, concl);
                let r = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
                let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
                d.finish_child(r)
            };
            b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
        };

        // Base: fun (f g : Fin 0 → Rat) (h) => @Eq.refl Rat Rat.zero
        //   (Fin.sum 0 f ≡ 0 ≡ Fin.sum 0 g, so refl on Rat.zero fits)
        let base = {
            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let mut b = EnvDeclBuilder::new();
            let ft = c.fin_to_rat(nat_zero.clone());
            let (f_id, f) = b.fresh_local(ft.clone());
            let (g_id, g) = b.fresh_local(ft.clone());
            let h = hyp_ty(&b, &nat_zero, &f, &g);
            let (h_id, _h) = b.fresh_local(h.clone());
            let refl = Expr::apps(eq_refl.clone(), [c.rat.clone(), c.rat_zero.clone()]);
            let r = b.mk_lam(h_id, BinderInfo::Default, h, refl);
            let r = b.mk_lam(g_id, BinderInfo::Default, ft.clone(), r);
            let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
            b.finish(r)
        };

        // Step: fun (k) (ih : motive k) (f g : Fin (succ k) → Rat) (h) =>
        //   congr (congrArg Rat.add (ih (f∘cs) (g∘cs) (fun i => h (castSucc k i))))
        //         (h (last k))
        let step = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            // ih : motive k = ∀ f g, (∀ i, f i = g i) → Fin.sum k f = Fin.sum k g
            let ih_ty = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let ft = c.fin_to_rat(k.clone());
                let (f_id, f) = d.fresh_local(ft.clone());
                let (g_id, g) = d.fresh_local(ft.clone());
                let h = hyp_ty(&d, &k, &f, &g);
                let (h_id, _h) = d.fresh_local(h.clone());
                let concl = eq_rat(sum(k.clone(), f.clone()), sum(k.clone(), g.clone()));
                let r = d.mk_pi(h_id, BinderInfo::Default, h, concl);
                let r = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
                let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
                d.finish_child(r)
            };
            let (ih_id, ih) = b.fresh_local(ih_ty.clone());

            let succ_k = Expr::app(nat_succ.clone(), k.clone());
            let ft_sk = c.fin_to_rat(succ_k.clone());
            let (f_id, f) = b.fresh_local(ft_sk.clone());
            let (g_id, g) = b.fresh_local(ft_sk.clone());
            let h_outer = hyp_ty(&b, &succ_k, &f, &g);
            let (h_id, h) = b.fresh_local(h_outer.clone());

            let f_cs = comp_cast(&b, &k, &f);
            let g_cs = comp_cast(&b, &k, &g);

            // hyp for ih: fun (i : Fin k) => h (Fin.castSucc k i)
            //   : (f∘cs) i = (g∘cs) i  (both sides β-reduce to f/g (castSucc k i))
            let h_cs = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = d.fresh_local(fin_n(k.clone()));
                let cast_i = Expr::apps(fin_cast.clone(), [k.clone(), i]);
                let body = Expr::app(h.clone(), cast_i);
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n(k.clone()), body))
            };

            // ih_app : Fin.sum k (f∘cs) = Fin.sum k (g∘cs)
            let ih_app = Expr::apps(ih.clone(), [f_cs.clone(), g_cs.clone(), h_cs]);

            // h_last : f (last k) = g (last k)
            let last_k = Expr::app(fin_last.clone(), k.clone());
            let h_last = Expr::app(h.clone(), last_k.clone());

            // congrArg Rat.add ih_app : Rat.add (Fin.sum k (f∘cs)) = Rat.add (Fin.sum k (g∘cs))
            //   @congrArg.{1,1} Rat (Rat → Rat) (Fin.sum k (f∘cs)) (Fin.sum k (g∘cs)) Rat.add ih_app
            let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
            let sum_f = sum(k.clone(), f_cs.clone());
            let sum_g = sum(k.clone(), g_cs.clone());
            let congr_add = Expr::apps(
                congr_arg.clone(),
                [
                    c.rat.clone(),
                    rat_to_rat.clone(),
                    sum_f.clone(),
                    sum_g.clone(),
                    c.rat_add.clone(),
                    ih_app,
                ],
            );

            // congr (congr_add) (h_last)
            //   : Rat.add (Fin.sum k (f∘cs)) (f (last k))
            //   = Rat.add (Fin.sum k (g∘cs)) (g (last k))
            //   @congr.{1,1} Rat Rat (Rat.add sum_f) (Rat.add sum_g) (f (last k)) (g (last k))
            //                congr_add h_last
            let add_sum_f = Expr::app(c.rat_add.clone(), sum_f);
            let add_sum_g = Expr::app(c.rat_add.clone(), sum_g);
            let f_last = Expr::app(f.clone(), last_k.clone());
            let g_last = Expr::app(g.clone(), last_k);
            let result = Expr::apps(
                congr.clone(),
                [
                    c.rat.clone(),
                    c.rat.clone(),
                    add_sum_f,
                    add_sum_g,
                    f_last,
                    g_last,
                    congr_add,
                    h_last,
                ],
            );

            let r = b.mk_lam(h_id, BinderInfo::Default, h_outer, result);
            let r = b.mk_lam(g_id, BinderInfo::Default, ft_sk.clone(), r);
            let r = b.mk_lam(f_id, BinderInfo::Default, ft_sk, r);
            let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // value: fun n f g h => @Nat.rec.{0} motive base step n f g h
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ft = c.fin_to_rat(n.clone());
            let (f_id, f) = b.fresh_local(ft.clone());
            let (g_id, g) = b.fresh_local(ft.clone());
            let h = hyp_ty(&b, &n, &f, &g);
            let (h_id, hh) = b.fresh_local(h.clone());
            let rec_app = Expr::apps(
                nat_rec.clone(),
                [motive, base, step, n.clone(), f.clone(), g.clone(), hh],
            );
            let r = b.mk_lam(h_id, BinderInfo::Default, h, rec_app);
            let r = b.mk_lam(g_id, BinderInfo::Default, ft.clone(), r);
            let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sum_congr"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Fin.kron_castSucc : (k : Nat) (i j : Fin k) (x : Rat) →
    ///    @ite Rat (@Eq (Fin (succ k)) (castSucc k j) (castSucc k i))
    ///             (@instDecidableEqFin (succ k) (castSucc k j) (castSucc k i)) x 0
    ///  = @ite Rat (@Eq (Fin k) j i) (@instDecidableEqFin k j i) x 0`
    ///
    /// The Kronecker summand is invariant under simultaneously embedding both
    /// the running index and the pivot via `Fin.castSucc` — the heart of the
    /// `cast`-branch IH bridge. Proved by `Decidable.rec` on
    /// `instDecidableEqFin k j i`, discharging each branch with `if_pos`/`if_neg`
    /// (the `castSucc`-side condition is transported via `congrArg`/
    /// `Fin.castSucc_inj`). Axiom-free.
    pub(super) fn register_fin_kron_castsucc(&mut self, c: &FinSumConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.kron_castSucc"))
            .is_some_and(|d| d.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }
        self.register_ite_pos_neg_lemmas()?;
        self.register_fin_index_lemmas()?;

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
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
        // @Eq (Fin N) a b
        let eqf = |nn: Expr, a: Expr, b: Expr| Expr::apps(eq1.clone(), [fin_n(nn), a, b]);
        // @instDecidableEqFin N a b
        let inst = |nn: Expr, a: Expr, b: Expr| Expr::apps(c.inst_dec_eq_fin.clone(), [nn, a, b]);
        // @ite Rat cond decinst x 0
        let ite = |cond: Expr, decinst: Expr, x: Expr| {
            Expr::apps(
                c.ite.clone(),
                [c.rat.clone(), cond, decinst, x, c.rat_zero.clone()],
            )
        };
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [c.rat.clone(), l, r]);

        // Build the two ite terms (LHS over Fin (succ k), RHS over Fin k).
        // bound vars order in type/value: k, i, j, x.
        let build = |b: &mut EnvDeclBuilder| {
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (i_id, i) = b.fresh_local(fin_n(k.clone()));
            let (j_id, j) = b.fresh_local(fin_n(k.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            (k_id, k, i_id, i, j_id, j, x_id, x)
        };

        // Type.
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

        // Value.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k, i_id, i, j_id, j, x_id, x) = build(&mut b);
            let sk = succ(k.clone());
            let csj = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
            let csi = Expr::apps(fin_cast.clone(), [k.clone(), i.clone()]);
            // Condition / instance on each side.
            let cond_s = eqf(sk.clone(), csj.clone(), csi.clone());
            let inst_s = inst(sk.clone(), csj.clone(), csi.clone());
            let cond_k = eqf(k.clone(), j.clone(), i.clone());
            let inst_k = inst(k.clone(), j.clone(), i.clone());
            let lhs = ite(cond_s.clone(), inst_s.clone(), x.clone());

            // dmotive : (d : Decidable cond_k) → Prop
            //   := fun d => @Eq Rat lhs (@ite Rat cond_k d x 0)
            let dmotive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let dec_k = Expr::app(dec.clone(), cond_k.clone());
                let (dd_id, dd) = d.fresh_local(dec_k.clone());
                let rhs_d = ite(cond_k.clone(), dd, x.clone());
                let body = eq_rat(lhs.clone(), rhs_d);
                d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_k, body))
            };

            // isFalse minor: fun (hne : cond_k → False) =>
            //   goal: lhs = @ite Rat cond_k (isFalse hne) x 0 ≡ lhs = 0.
            //   if_neg on lhs:  @if_neg cond_s inst_s hne_s Rat x 0 : lhs = 0,
            //   where hne_s : cond_s → False := fun e => hne (castSucc_inj k j i e).
            let false_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let not_k = Expr::pi(BinderInfo::Default, cond_k.clone(), false_c.clone());
                let (hne_id, hne) = d.fresh_local(not_k.clone());
                // hne_s : cond_s → False
                let hne_s = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (e_id, e) = g.fresh_local(cond_s.clone());
                    // castSucc_inj k j i e : @Eq (Fin k) j i = cond_k
                    let inj = Expr::apps(cs_inj.clone(), [k.clone(), j.clone(), i.clone(), e]);
                    let body = Expr::app(hne.clone(), inj);
                    g.finish_child(g.mk_lam(e_id, BinderInfo::Default, cond_s.clone(), body))
                };
                // @if_neg {cond_s} {inst_s} hne_s {Rat} {x} {0} : lhs = 0  (Lean order)
                let proof = Expr::apps(
                    if_neg.clone(),
                    [
                        cond_s.clone(),
                        inst_s.clone(),
                        hne_s,
                        c.rat.clone(),
                        x.clone(),
                        c.rat_zero.clone(),
                    ],
                );
                d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_k, proof))
            };

            // isTrue minor: fun (heq : cond_k) =>
            //   goal: lhs = @ite Rat cond_k (isTrue heq) x 0 ≡ lhs = x.
            //   if_pos on lhs: @if_pos cond_s inst_s heq_s Rat x 0 : lhs = x,
            //   where heq_s : cond_s := congrArg (Fin.castSucc k) heq.
            let true_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (heq_id, heq) = d.fresh_local(cond_k.clone());
                // congrArg (Fin k) (Fin (succ k)) j i (Fin.castSucc k) heq : cond_s
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
                // @if_pos {cond_s} {inst_s} heq_s {Rat} {x} {0} : lhs = x  (Lean order)
                let proof = Expr::apps(
                    if_pos.clone(),
                    [
                        cond_s.clone(),
                        inst_s.clone(),
                        heq_s,
                        c.rat.clone(),
                        x.clone(),
                        c.rat_zero.clone(),
                    ],
                );
                d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, cond_k.clone(), proof))
            };

            // @Decidable.rec.{0} cond_k dmotive false_minor true_minor inst_k
            //   : dmotive inst_k = (lhs = @ite Rat cond_k inst_k x 0) = (lhs = rhs)
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
            name: Name::from_string("Fin.kron_castSucc"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Constructive `Fin.sum_single` — eliminates the last TCB `Fin` axiom.
    ///
    /// `(n : Nat) (i : Fin n) (x : Rat) → Nat.lt (Fin.val n i) n →
    ///   Fin.sum n (fun j => @ite Rat (@Eq (Fin n) j i) (@instDecidableEqFin n j i)
    ///     x Rat.zero) = x`
    ///
    /// `Nat.rec` induction on `n`. Base (`n = 0`) is vacuous: the premise
    /// `Nat.lt _ 0` is uninhabited (`Nat.not_succ_le_zero`), `False.elim`. Step
    /// (`n = succ k`): `Fin.lastCases` on `i` —
    ///
    /// - `i = Fin.last k`: the diagonal `last`-term collapses to `x` (`if_pos`
    ///   on `Eq.refl`); the `castSucc`-prefix is all-zero
    ///   (`Fin.castSucc_ne_last` + `if_neg`, folded by `Fin.sum_congr` /
    ///   `Fin.sum_zero_fn`); `Rat.zero_add` finishes `0 + x = x`.
    /// - `i = Fin.castSucc k i'`: the `last`-term is zero
    ///   (`Fin.last_ne_castSucc` + `if_neg`); the prefix equals the `Fin k`
    ///   Kronecker sum (`Fin.kron_castSucc` + `Fin.sum_congr`) which the IH
    ///   collapses to `x` (using `Fin.isLt i' : Fin.val i' < k`);
    ///   `Rat.add_zero` finishes `x + 0 = x`.
    ///
    /// Axiom-free: every reference is a generated recursor, reducible
    /// definition, or one of the axiom-free Theorems above.
    pub(super) fn register_fin_sum_single_theorem(
        &mut self,
        c: &FinSumConsts,
    ) -> Result<(), EnvError> {
        // Prerequisite lemmas (all axiom-free). `Fin.sum_zero_fn` is registered
        // earlier in `init_fin_sum`; we only depend on it (no re-register, since
        // `register_fin_sum_zero_fn` is not idempotent).
        self.register_fin_sum_congr(c)?;
        self.register_fin_kron_castsucc(c)?;
        self.register_fin_last_cases()?;
        self.register_ite_pos_neg_lemmas()?;
        self.register_fin_index_lemmas()?;

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let nat = c.nat.clone();
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
        let fin_sum_congr = Expr::const_(Name::from_string("Fin.sum_congr"), vec![]);
        let fin_sum_zero_fn = Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]);
        let fin_kron_cs = Expr::const_(Name::from_string("Fin.kron_castSucc"), vec![]);
        let cs_ne_last = Expr::const_(Name::from_string("Fin.castSucc_ne_last"), vec![]);
        let last_ne_cs = Expr::const_(Name::from_string("Fin.last_ne_castSucc"), vec![]);

        let if_pos = Expr::const_(Name::from_string("if_pos"), vec![l1.clone()]);
        let if_neg = Expr::const_(Name::from_string("if_neg"), vec![l1.clone()]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
        let congr = Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
        let rat_add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
        let rat_zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);

        // ── helpers ──
        let fin_n = |n: Expr| Expr::app(c.fin.clone(), n);
        let succ = |n: Expr| Expr::app(nat_succ.clone(), n);
        let val = |n: Expr, x: Expr| Expr::apps(fin_val.clone(), [n, x]);
        let lt = |a: Expr, b: Expr| Expr::apps(nat_lt.clone(), [a, b]);
        let sum = |n: Expr, f: Expr| Expr::apps(c.fin_sum.clone(), [n, f]);
        let eqf = |nn: Expr, a: Expr, b: Expr| Expr::apps(eq1.clone(), [fin_n(nn), a, b]);
        let eq_rat = |a: Expr, b: Expr| Expr::apps(eq1.clone(), [c.rat.clone(), a, b]);
        let inst = |nn: Expr, a: Expr, b: Expr| Expr::apps(c.inst_dec_eq_fin.clone(), [nn, a, b]);
        // single Kronecker term @ite Rat (Eq (Fin N) j piv) (inst N j piv) x 0
        let kron_term = |nn: Expr, piv: Expr, x: Expr, j: Expr| {
            Expr::apps(
                c.ite.clone(),
                [
                    c.rat.clone(),
                    eqf(nn.clone(), j.clone(), piv.clone()),
                    inst(nn, j, piv),
                    x,
                    c.rat_zero.clone(),
                ],
            )
        };
        // kron function: fun j : Fin N => kron_term N piv x j
        let kron_fn = |parent: &EnvDeclBuilder, nn: &Expr, piv: &Expr, x: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = ch.fresh_local(fin_n(nn.clone()));
            let body = kron_term(nn.clone(), piv.clone(), x.clone(), j);
            ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_n(nn.clone()), body))
        };
        // fun _ : Fin k => Rat.zero  (matches Fin.sum_zero_fn's summand)
        let zero_fn = |parent: &EnvDeclBuilder, k: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (i_id, _i) = ch.fresh_local(fin_n(k.clone()));
            ch.finish_child(ch.mk_lam(
                i_id,
                BinderInfo::Default,
                fin_n(k.clone()),
                c.rat_zero.clone(),
            ))
        };

        // motive M k := ∀ (i : Fin k) (x : Rat),
        //                 Nat.lt (Fin.val k i) k → Fin.sum k (kron_fn k i x) = x
        let mk_motive_body = |parent: &EnvDeclBuilder, k: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (i_id, i) = d.fresh_local(fin_n(k.clone()));
            let (x_id, x) = d.fresh_local(c.rat.clone());
            let prem = lt(val(k.clone(), i.clone()), k.clone());
            let (h_id, _h) = d.fresh_local(prem.clone());
            let kf = kron_fn(&d, k, &i, &x);
            let concl = eq_rat(sum(k.clone(), kf), x.clone());
            let r = d.mk_pi(h_id, BinderInfo::Default, prem, concl);
            let r = d.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = d.mk_pi(i_id, BinderInfo::Default, fin_n(k.clone()), r);
            d.finish_child(r)
        };

        // Statement type: ∀ (n)(i : Fin n)(x)(h : Nat.lt (Fin.val n i) n),
        //                   Fin.sum n (kron_fn n i x) = x
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (i_id, i) = b.fresh_local(fin_n(n.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let prem = lt(val(n.clone(), i.clone()), n.clone());
            let (h_id, _h) = b.fresh_local(prem.clone());
            let kf = kron_fn(&b, &n, &i, &x);
            let concl = eq_rat(sum(n.clone(), kf), x.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, prem, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n(n.clone()), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // motive (for Nat.rec): fun (k : Nat) => M k
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let body = mk_motive_body(&b, &k);
            b.finish(b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body))
        };

        // Base: M 0 = ∀ (i : Fin 0)(x)(h : Nat.lt (Fin.val 0 i) 0), … = x.
        //   h : Nat.lt (Fin.val 0 i) 0 ≡ Nat.le (succ (Fin.val 0 i)) 0.
        //   @False.elim.{0} (goal) (Nat.not_succ_le_zero (Fin.val 0 i) h)
        let base = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(fin_n(nat_zero.clone()));
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let val0 = val(nat_zero.clone(), i.clone());
            let prem = lt(val0.clone(), nat_zero.clone());
            let (h_id, h) = b.fresh_local(prem.clone());
            let kf = kron_fn(&b, &nat_zero, &i, &x);
            let goal = eq_rat(sum(nat_zero.clone(), kf), x.clone());
            // Nat.not_succ_le_zero (Fin.val 0 i) h : False
            let false_pf = Expr::apps(not_succ_le_zero.clone(), [val0, h]);
            let body = Expr::apps(false_elim.clone(), [goal, false_pf]);
            let r = b.mk_lam(h_id, BinderInfo::Default, prem, body);
            let r = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(i_id, BinderInfo::Default, fin_n(nat_zero.clone()), r);
            b.finish(r)
        };

        // Step: fun (k)(ih : M k)(i : Fin (succ k))(x)(h) => <goal>.
        //   lastCases motive P i := Nat.lt (Fin.val (succ k) i) (succ k)
        //                               → Fin.sum (succ k) (kron_fn (succ k) i x) = x
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
            //   := fun (w : Fin (succ k)) =>
            //        Nat.lt (Fin.val (succ k) w) (succ k)
            //          → Fin.sum (succ k) (kron_fn (succ k) w x) = x
            let p_motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = d.fresh_local(fin_n(sk.clone()));
                let prem_w = lt(val(sk.clone(), w.clone()), sk.clone());
                let kfw = kron_fn(&d, &sk, &w, &x);
                let concl = eq_rat(sum(sk.clone(), kfw), x.clone());
                // Non-dependent premise → conclusion (the premise binder is unused
                // in `concl`, so a plain arrow is correct).
                let body = Expr::arrow(prem_w, concl);
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, fin_n(sk.clone()), body))
            };

            // ── last_case : P (Fin.last k) ──
            // fun (_h : Nat.lt (Fin.val (succ k)(last k)) (succ k)) =>
            //   Eq.trans (congr (congrArg Rat.add hpre) hlast) (Rat.zero_add x)
            let last_case = {
                let lk = Expr::app(fin_last.clone(), k.clone());
                let mut d = EnvDeclBuilder::child_of(&b);
                let prem_last = lt(val(sk.clone(), lk.clone()), sk.clone());
                let (hh_id, _hh) = d.fresh_local(prem_last.clone());

                // F := kron_fn (succ k) (last k) x
                // prefix summand: fun j:Fin k => F (castSucc k j)
                //   = kron_term (succ k) (last k) x (castSucc k j)
                let pre_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let csj = Expr::apps(fin_cast.clone(), [k.clone(), j]);
                    let body = kron_term(sk.clone(), lk.clone(), x.clone(), csj);
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                let zf = zero_fn(&d, &k);

                // pointwise: fun j:Fin k => @if_neg cond (castSucc k j) Rat inst hne x 0
                //   : (pre_fn j) = 0, where
                //   cond = Eq (Fin (succ k)) (castSucc k j) (last k),
                //   hne  = Fin.castSucc_ne_last k j.
                let pw_pre = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let csj = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
                    let cond = eqf(sk.clone(), csj.clone(), lk.clone());
                    let inst_j = inst(sk.clone(), csj.clone(), lk.clone());
                    let hne = Expr::apps(cs_ne_last.clone(), [k.clone(), j.clone()]);
                    // Lean order: @if_neg {c} {inst} (h) {α} {t} {e}.
                    let body = Expr::apps(
                        if_neg.clone(),
                        [
                            cond,
                            inst_j,
                            hne,
                            c.rat.clone(),
                            x.clone(),
                            c.rat_zero.clone(),
                        ],
                    );
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                // Fin.sum_congr k pre_fn zf pw_pre : Fin.sum k pre_fn = Fin.sum k zf
                let congr_pre = Expr::apps(
                    fin_sum_congr.clone(),
                    [k.clone(), pre_fn.clone(), zf.clone(), pw_pre],
                );
                // Fin.sum_zero_fn k : Fin.sum k zf = Rat.zero
                let szf = Expr::app(fin_sum_zero_fn.clone(), k.clone());
                // hpre : Fin.sum k pre_fn = Rat.zero
                let hpre = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.rat.clone(),
                        sum(k.clone(), pre_fn.clone()),
                        sum(k.clone(), zf.clone()),
                        c.rat_zero.clone(),
                        congr_pre,
                        szf,
                    ],
                );

                // hlast : F (last k) = x
                //   F (last k) = kron_term (succ k)(last k) x (last k)
                //     = @ite Rat (Eq (Fin (succ k))(last k)(last k)) inst x 0
                //   @if_pos cond inst (Eq.refl (Fin (succ k))(last k)) x 0 : … = x
                let cond_d = eqf(sk.clone(), lk.clone(), lk.clone());
                let inst_d = inst(sk.clone(), lk.clone(), lk.clone());
                let refl_last = Expr::apps(eq_refl.clone(), [fin_n(sk.clone()), lk.clone()]);
                // Lean order: @if_pos {c} {inst} (h) {α} {t} {e}.
                let hlast = Expr::apps(
                    if_pos.clone(),
                    [
                        cond_d,
                        inst_d,
                        refl_last,
                        c.rat.clone(),
                        x.clone(),
                        c.rat_zero.clone(),
                    ],
                );

                // congrArg Rat.add hpre : Rat.add (Fin.sum k pre_fn) = Rat.add Rat.zero
                let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
                let cg_add = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.rat.clone(),
                        rat_to_rat.clone(),
                        sum(k.clone(), pre_fn.clone()),
                        c.rat_zero.clone(),
                        c.rat_add.clone(),
                        hpre,
                    ],
                );
                // F (last k) value (the second add operand), for congr's a/b.
                let f_last = kron_term(sk.clone(), lk.clone(), x.clone(), lk.clone());
                // congr (cg_add) (hlast)
                //   : Rat.add (Fin.sum k pre_fn) (F (last k))
                //   = Rat.add Rat.zero x
                let add_pre = Expr::app(c.rat_add.clone(), sum(k.clone(), pre_fn.clone()));
                let add_zero = Expr::app(c.rat_add.clone(), c.rat_zero.clone());
                let combined = Expr::apps(
                    congr.clone(),
                    [
                        c.rat.clone(),
                        c.rat.clone(),
                        add_pre,
                        add_zero,
                        f_last.clone(),
                        x.clone(),
                        cg_add,
                        hlast,
                    ],
                );
                // Rat.zero_add x : Rat.add Rat.zero x = x
                let zadd = Expr::app(rat_zero_add.clone(), x.clone());
                // Eq.trans combined zadd : Rat.add (Fin.sum k pre_fn)(F (last k)) = x
                //   ≡ goal Fin.sum (succ k) F = x  (LHS reduces via sum_succ ι)
                let lhs_add = Expr::app(
                    Expr::app(c.rat_add.clone(), sum(k.clone(), pre_fn.clone())),
                    f_last,
                );
                let mid_add =
                    Expr::app(Expr::app(c.rat_add.clone(), c.rat_zero.clone()), x.clone());
                let proof = Expr::apps(
                    eq_trans.clone(),
                    [c.rat.clone(), lhs_add, mid_add, x.clone(), combined, zadd],
                );
                d.finish_child(d.mk_lam(hh_id, BinderInfo::Default, prem_last, proof))
            };

            // ── cast_case : (i' : Fin k) → P (Fin.castSucc k i') ──
            // fun (i' : Fin k)(_h) =>
            //   Eq.trans (congr (congrArg Rat.add hpre) hlast) (Rat.add_zero x)
            let cast_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (ip_id, ip) = d.fresh_local(fin_n(k.clone()));
                let csi = Expr::apps(fin_cast.clone(), [k.clone(), ip.clone()]);
                let prem_cs = lt(val(sk.clone(), csi.clone()), sk.clone());
                let (hh_id, _hh) = d.fresh_local(prem_cs.clone());

                // G := kron_fn (succ k) (castSucc k i') x
                // prefix summand: fun j:Fin k => G (castSucc k j)
                //   = kron_term (succ k) (castSucc k i') x (castSucc k j)
                let pre_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let csj = Expr::apps(fin_cast.clone(), [k.clone(), j]);
                    let body = kron_term(sk.clone(), csi.clone(), x.clone(), csj);
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                // target prefix: kron_fn k i' x (the Fin k Kronecker)
                let kron_k = kron_fn(&d, &k, &ip, &x);

                // pointwise: fun j:Fin k => Fin.kron_castSucc k i' j x
                //   : (pre_fn j) = (kron_k j)
                let pw_pre = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (j_id, j) = g.fresh_local(fin_n(k.clone()));
                    let body = Expr::apps(
                        fin_kron_cs.clone(),
                        [k.clone(), ip.clone(), j.clone(), x.clone()],
                    );
                    g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), body))
                };
                // Fin.sum_congr k pre_fn kron_k pw_pre : Fin.sum k pre_fn = Fin.sum k kron_k
                let congr_pre = Expr::apps(
                    fin_sum_congr.clone(),
                    [k.clone(), pre_fn.clone(), kron_k.clone(), pw_pre],
                );
                // ih i' x (Fin.isLt k i') : Fin.sum k kron_k = x
                let islt_ip = Expr::apps(fin_islt.clone(), [k.clone(), ip.clone()]);
                let ih_app = Expr::apps(ih.clone(), [ip.clone(), x.clone(), islt_ip]);
                // hpre : Fin.sum k pre_fn = x
                let hpre = Expr::apps(
                    eq_trans.clone(),
                    [
                        c.rat.clone(),
                        sum(k.clone(), pre_fn.clone()),
                        sum(k.clone(), kron_k.clone()),
                        x.clone(),
                        congr_pre,
                        ih_app,
                    ],
                );

                // hlast : G (last k) = 0
                //   G (last k) = kron_term (succ k)(castSucc k i') x (last k)
                //     = @ite Rat (Eq (Fin (succ k))(last k)(castSucc k i')) inst x 0
                //   @if_neg cond inst (Fin.last_ne_castSucc k i') x 0 : … = 0
                let lk = Expr::app(fin_last.clone(), k.clone());
                let cond_l = eqf(sk.clone(), lk.clone(), csi.clone());
                let inst_l = inst(sk.clone(), lk.clone(), csi.clone());
                let hne_last = Expr::apps(last_ne_cs.clone(), [k.clone(), ip.clone()]);
                // Lean order: @if_neg {c} {inst} (h) {α} {t} {e}.
                let hlast = Expr::apps(
                    if_neg.clone(),
                    [
                        cond_l,
                        inst_l,
                        hne_last,
                        c.rat.clone(),
                        x.clone(),
                        c.rat_zero.clone(),
                    ],
                );

                // congrArg Rat.add hpre : Rat.add (Fin.sum k pre_fn) = Rat.add x
                let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
                let cg_add = Expr::apps(
                    congr_arg.clone(),
                    [
                        c.rat.clone(),
                        rat_to_rat.clone(),
                        sum(k.clone(), pre_fn.clone()),
                        x.clone(),
                        c.rat_add.clone(),
                        hpre,
                    ],
                );
                // G (last k) value (second add operand)
                let g_last = kron_term(sk.clone(), csi.clone(), x.clone(), lk.clone());
                // congr (cg_add) (hlast)
                //   : Rat.add (Fin.sum k pre_fn)(G (last k)) = Rat.add x Rat.zero
                let add_pre = Expr::app(c.rat_add.clone(), sum(k.clone(), pre_fn.clone()));
                let add_x = Expr::app(c.rat_add.clone(), x.clone());
                let combined = Expr::apps(
                    congr.clone(),
                    [
                        c.rat.clone(),
                        c.rat.clone(),
                        add_pre,
                        add_x,
                        g_last.clone(),
                        c.rat_zero.clone(),
                        cg_add,
                        hlast,
                    ],
                );
                // Rat.add_zero x : Rat.add x Rat.zero = x
                let azero = Expr::app(rat_add_zero.clone(), x.clone());
                let lhs_add = Expr::app(
                    Expr::app(c.rat_add.clone(), sum(k.clone(), pre_fn.clone())),
                    g_last,
                );
                let mid_add =
                    Expr::app(Expr::app(c.rat_add.clone(), x.clone()), c.rat_zero.clone());
                let proof = Expr::apps(
                    eq_trans.clone(),
                    [c.rat.clone(), lhs_add, mid_add, x.clone(), combined, azero],
                );
                let r = d.mk_lam(hh_id, BinderInfo::Default, prem_cs, proof);
                d.finish_child(d.mk_lam(ip_id, BinderInfo::Default, fin_n(k.clone()), r))
            };

            // @Fin.lastCases.{0} k P last_case cast_case i  : P i
            //   then apply premise h : Nat.lt (Fin.val (succ k) i) (succ k).
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
            name: Name::from_string("Fin.sum_single"),
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
        let c = FinSumConsts::new();
        env.register_fin_sum_congr(&c).expect("sum_congr");
        env.register_fin_kron_castsucc(&c).expect("kron_castSucc");
        env
    }

    #[test]
    fn test_fin_sum_single_is_constructive_theorem() {
        // `init_fin_sum` now registers the kernel-checked Theorem (overwriting
        // the legacy admitted Axiom).
        let env = {
            let mut env = Environment::with_prelude();
            env.init_fin_sum().expect("init_fin_sum");
            env
        };
        let n = Name::from_string("Fin.sum_single");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .expect("Fin.sum_single should type-check");

        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem,
            "Fin.sum_single must be a kernel-checked Theorem, not an Axiom"
        );

        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            names.is_empty(),
            "Fin.sum_single must be axiom-free, got {names:?}"
        );
        assert!(
            matches!(env.proof_quality(&n), Some(ProofQuality::Constructive)),
            "Fin.sum_single must be Constructive, got {:?}",
            env.proof_quality(&n)
        );
    }

    #[test]
    fn test_fin_kron_castsucc_type_checks_and_axiom_free() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Fin.kron_castSucc"),
                vec![],
            ))
            .expect("Fin.kron_castSucc should type-check");
        let n = Name::from_string("Fin.kron_castSucc");
        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            names.is_empty(),
            "Fin.kron_castSucc must be axiom-free, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_fin_sum_congr_type_checks_and_axiom_free() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Fin.sum_congr"), vec![]))
            .expect("Fin.sum_congr should type-check");
        let n = Name::from_string("Fin.sum_congr");
        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            names.is_empty(),
            "Fin.sum_congr must be axiom-free, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }
}
