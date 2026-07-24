// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `instDecidableEqFin : {n : Nat} → (a b : Fin n) →
//! Decidable (Eq a b)` — a real kernel term (NO `sorry`, NO axiom), eliminating
//! the former foundational `instDecidableEqFin` axiom over the FAITHFUL `Fin`
//! carrier (`Fin.mk : {n} → (val : Nat) → (isLt : Nat.lt val n) → Fin n`).
//!
//! Decision: dispatch on `Nat.decEq (Fin.val a) (Fin.val b)`.
//! - `isTrue (h : Fin.val a = Fin.val b)` lifts to `a = b` via
//!   [`Fin.eq_of_val_eq`] — `a` and `b` are structure values whose only data
//!   field is `val`, so equal `val`s force `a = b` (the `isLt` field is a
//!   proof, irrelevant under the kernel's proof-irrelevance).
//! - `isFalse (hne : Fin.val a = Fin.val b → False)` refutes `a = b` via
//!   `fun (h : a = b) => hne (congrArg Fin.val h)`.
//!
//! # `Fin.eq_of_val_eq`
//!
//! `{n} → (a b : Fin n) → @Eq Nat (Fin.val a) (Fin.val b) → @Eq (Fin n) a b`.
//!
//! Built by a double `Fin.rec` destructuring `a ≡ ⟨va, pa⟩`, `b ≡ ⟨vb, pb⟩`
//! (where `Fin.val ⟨v, p⟩ ≡ v` by ι), reducing the hypothesis to `va = vb`, then
//! `Eq.ndrec`-transporting along it with motive
//! `fun (w : Nat) => (pw : Nat.lt w n) → @Eq (Fin n) ⟨va, pa⟩ ⟨w, pw⟩`. The base
//! case `C va` is discharged by `@Eq.refl (Fin n) ⟨va, pa⟩` — well-typed at
//! `⟨va, pa⟩ = ⟨va, pw⟩` because the kernel's PROOF-IRRELEVANCE makes the two
//! `Fin.mk`s (differing only in the irrelevant `isLt` proof) definitionally
//! equal. Applying the transported `C vb` to `pb` yields `⟨va, pa⟩ = ⟨vb, pb⟩`.
//!
//! # Axiom closure
//!
//! Mentions only `Eq`/`Eq.refl`/`Eq.ndrec`, `Fin`/`Fin.mk`/`Fin.rec`/`Fin.val`,
//! `Nat`/`Nat.lt`/`Nat.decEq`, `Decidable`(`.rec`/`.isTrue`/`.isFalse`),
//! `congrArg`, `False` — all generated recursors / reducible definitions / the
//! axiom-free `Nat.decEq`. So `env.axiom_deps("instDecidableEqFin")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Fin.eq_of_val_eq` and the kernel-checked computable
    /// `instDecidableEqFin` definition. Idempotent; axiom-free.
    ///
    /// REQUIRES: `Fin` (faithful carrier), `Fin.mk`, `Fin.rec`, `Fin.val`,
    ///           `Nat`, `Nat.lt`, `Nat.decEq`, `Eq`(+`Eq.refl`/`Eq.ndrec`),
    ///           `congrArg`, `Decidable`(+ctors/rec), `False`.
    pub(crate) fn register_fin_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("instDecidableEqFin"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Definition)
        {
            return Ok(());
        }

        // Dependencies.
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin()?; // faithful carrier + Fin.val + Fin.isLt
        self.init_lt()?; // Nat.lt
        self.init_true_false()?;
        self.init_decidable()?;
        self.register_nat_dec_eq_proof()?;

        // ----- shared constants -----
        let type0 = Level::zero();
        let type1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        // `Fin.rec` eliminating into `Sort 1` (Type 0) for `eq_of_val_eq`'s
        // motive `(b : Fin n) → … → @Eq (Fin n) a b : Prop`, but the OUTER
        // recursion's motive lands in `Prop` (Sort 0). The constructor's data is
        // in `Type`, so large elimination into `Prop` is allowed (single ctor).
        let fin_rec_prop = Expr::const_(Name::from_string("Fin.rec"), vec![type0.clone()]);
        let nat_dec_eq = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
        let eq_ty1 = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl1 = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        // Eq.ndrec.{v,u}; here we transport along `va = vb : Eq Nat`, so u = 1
        // (Nat : Type 0 = Sort 1) and v = 0 (motive lands in Prop).
        let eq_ndrec = Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![type0.clone(), type1.clone()],
        );
        let eq_nat = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        // helpers
        let fin_n = |n: Expr| Expr::app(fin_c.clone(), n);
        let lt = |a: Expr, b: Expr| Expr::app(Expr::app(nat_lt.clone(), a), b);
        let mk = |n: Expr, v: Expr, p: Expr| Expr::apps(fin_mk.clone(), [n, v, p]);
        let val = |n: Expr, x: Expr| Expr::apps(fin_val.clone(), [n, x]);
        let eq_fin = |n: Expr, l: Expr, r: Expr| Expr::apps(eq_ty1.clone(), [fin_n(n), l, r]);
        let eq_n = |l: Expr, r: Expr| Expr::apps(eq_nat.clone(), [nat.clone(), l, r]);

        // ─────────────────────── Fin.eq_of_val_eq ───────────────────────
        if self
            .get_const(&Name::from_string("Fin.eq_of_val_eq"))
            .is_none()
        {
            // Type: {n} → (a b : Fin n) → @Eq Nat (Fin.val a) (Fin.val b)
            //                            → @Eq (Fin n) a b
            let eqv_type = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                let (a_id, a) = b.fresh_local(fin_n(n.clone()));
                let (bv_id, bv) = b.fresh_local(fin_n(n.clone()));
                let hyp = eq_n(val(n.clone(), a.clone()), val(n.clone(), bv.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let concl = eq_fin(n.clone(), a.clone(), bv.clone());
                let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
                let r = b.mk_pi(bv_id, BinderInfo::Default, fin_n(n.clone()), r);
                let r = b.mk_pi(a_id, BinderInfo::Default, fin_n(n.clone()), r);
                let r = b.mk_pi(n_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };

            // Value: fun {n} (a b : Fin n) (h) =>
            //   @Fin.rec n (outer_motive) outer_mk a b h
            // outer_motive a := (b : Fin n) → Fin.val a = Fin.val b → a = b
            // outer_mk va pa := fun (b : Fin n) (h) =>
            //   @Fin.rec n (inner_motive) inner_mk b h
            //   inner_motive b := Fin.val ⟨va,pa⟩ = Fin.val b → ⟨va,pa⟩ = b
            //   inner_mk vb pb := fun (h : va = vb) =>
            //     @Eq.ndrec Nat va (transport_motive) (Eq.refl ⟨va,pa⟩) vb h pb
            //   transport_motive w := (pw : Nat.lt w n) → ⟨va,pa⟩ = ⟨w,pw⟩
            let eqv_value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());

                // outer_motive: fun (a : Fin n) =>
                //   (b : Fin n) → Fin.val a = Fin.val b → @Eq (Fin n) a b
                let outer_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (am_id, am) = c.fresh_local(fin_n(n.clone()));
                    let body = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (bb_id, bb) = d.fresh_local(fin_n(n.clone()));
                        let hyp = eq_n(val(n.clone(), am.clone()), val(n.clone(), bb.clone()));
                        let (h_id, _h) = d.fresh_local(hyp.clone());
                        let concl = eq_fin(n.clone(), am.clone(), bb.clone());
                        let r = d.mk_pi(h_id, BinderInfo::Default, hyp, concl);
                        let r = d.mk_pi(bb_id, BinderInfo::Default, fin_n(n.clone()), r);
                        d.finish_child(r)
                    };
                    c.finish_child(c.mk_lam(am_id, BinderInfo::Default, fin_n(n.clone()), body))
                };

                // outer_mk: fun (va : Nat) (pa : Nat.lt va n) =>
                //   fun (b : Fin n) (h : Fin.val ⟨va,pa⟩ = Fin.val b) =>
                //     @Fin.rec n (inner_motive) (inner_mk) b h
                let outer_mk = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (va_id, va) = c.fresh_local(nat.clone());
                    let pa_ty = lt(va.clone(), n.clone());
                    let (pa_id, pa) = c.fresh_local(pa_ty.clone());
                    let a_val = mk(n.clone(), va.clone(), pa.clone()); // ⟨va,pa⟩ : Fin n

                    let lam_body = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (bb_id, bb) = d.fresh_local(fin_n(n.clone()));
                        let h_ty = eq_n(val(n.clone(), a_val.clone()), val(n.clone(), bb.clone()));
                        let (h_id, h) = d.fresh_local(h_ty.clone());

                        // inner_motive: fun (b : Fin n) =>
                        //   Fin.val ⟨va,pa⟩ = Fin.val b → @Eq (Fin n) ⟨va,pa⟩ b
                        let inner_motive = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (bm_id, bm) = e.fresh_local(fin_n(n.clone()));
                            let body = {
                                let mut g = EnvDeclBuilder::child_of(&e);
                                let hh_ty =
                                    eq_n(val(n.clone(), a_val.clone()), val(n.clone(), bm.clone()));
                                let (hh_id, _hh) = g.fresh_local(hh_ty.clone());
                                let concl = eq_fin(n.clone(), a_val.clone(), bm.clone());
                                let r = g.mk_pi(hh_id, BinderInfo::Default, hh_ty, concl);
                                g.finish_child(r)
                            };
                            e.finish_child(e.mk_lam(
                                bm_id,
                                BinderInfo::Default,
                                fin_n(n.clone()),
                                body,
                            ))
                        };

                        // inner_mk: fun (vb : Nat) (pb : Nat.lt vb n) =>
                        //   fun (h : Fin.val ⟨va,pa⟩ = Fin.val ⟨vb,pb⟩)  -- ≡ va = vb
                        //   => @Eq.ndrec Nat va transport_motive
                        //        (@Eq.refl (Fin n) ⟨va,pa⟩) vb h pb
                        let inner_mk = {
                            let mut e = EnvDeclBuilder::child_of(&d);
                            let (vb_id, vb) = e.fresh_local(nat.clone());
                            let pb_ty = lt(vb.clone(), n.clone());
                            let (pb_id, pb) = e.fresh_local(pb_ty.clone());
                            let b_val = mk(n.clone(), vb.clone(), pb.clone());
                            let hin_ty =
                                eq_n(val(n.clone(), a_val.clone()), val(n.clone(), b_val.clone()));
                            let (hin_id, hin) = e.fresh_local(hin_ty.clone());

                            // transport_motive: fun (w : Nat) =>
                            //   (pw : Nat.lt w n) → @Eq (Fin n) ⟨va,pa⟩ ⟨w,pw⟩
                            let transport_motive = {
                                let mut g = EnvDeclBuilder::child_of(&e);
                                let (w_id, w) = g.fresh_local(nat.clone());
                                let inner = {
                                    let mut k = EnvDeclBuilder::child_of(&g);
                                    let pw_ty = lt(w.clone(), n.clone());
                                    let (pw_id, pw) = k.fresh_local(pw_ty.clone());
                                    let rhs = mk(n.clone(), w.clone(), pw.clone());
                                    let concl = eq_fin(n.clone(), a_val.clone(), rhs);
                                    let r = k.mk_pi(pw_id, BinderInfo::Default, pw_ty, concl);
                                    k.finish_child(r)
                                };
                                g.finish_child(g.mk_lam(
                                    w_id,
                                    BinderInfo::Default,
                                    nat.clone(),
                                    inner,
                                ))
                            };

                            // base case `transport_motive va`:
                            //   fun (pw : Nat.lt va n) => @Eq.refl (Fin n) ⟨va,pa⟩
                            // typed at ⟨va,pa⟩ = ⟨va,pw⟩ via proof-irrelevance of pa/pw.
                            let base = {
                                let mut g = EnvDeclBuilder::child_of(&e);
                                let pw_ty = lt(va.clone(), n.clone());
                                let (pw_id, _pw) = g.fresh_local(pw_ty.clone());
                                let refl =
                                    Expr::apps(eq_refl1.clone(), [fin_n(n.clone()), a_val.clone()]);
                                g.finish_child(g.mk_lam(pw_id, BinderInfo::Default, pw_ty, refl))
                            };

                            // @Eq.ndrec Nat va transport_motive base vb hin
                            //   : transport_motive vb
                            //   = (pw : Nat.lt vb n) → ⟨va,pa⟩ = ⟨vb,pw⟩
                            let transported = Expr::apps(
                                eq_ndrec.clone(),
                                [
                                    nat.clone(),
                                    va.clone(),
                                    transport_motive,
                                    base,
                                    vb.clone(),
                                    hin.clone(),
                                ],
                            );
                            // apply to pb : ⟨va,pa⟩ = ⟨vb,pb⟩
                            let applied = Expr::app(transported, pb.clone());
                            let r = e.mk_lam(hin_id, BinderInfo::Default, hin_ty, applied);
                            let r = e.mk_lam(pb_id, BinderInfo::Default, pb_ty, r);
                            let r = e.mk_lam(vb_id, BinderInfo::Default, nat.clone(), r);
                            e.finish_child(r)
                        };

                        // @Fin.rec.{0} n inner_motive inner_mk b h
                        let inner_rec = Expr::apps(
                            fin_rec_prop.clone(),
                            [n.clone(), inner_motive, inner_mk, bb.clone()],
                        );
                        let applied = Expr::app(inner_rec, h.clone());
                        let r = d.mk_lam(h_id, BinderInfo::Default, h_ty, applied);
                        let r = d.mk_lam(bb_id, BinderInfo::Default, fin_n(n.clone()), r);
                        d.finish_child(r)
                    };

                    let r = c.mk_lam(pa_id, BinderInfo::Default, pa_ty, lam_body);
                    let r = c.mk_lam(va_id, BinderInfo::Default, nat.clone(), r);
                    c.finish_child(r)
                };

                // body: fun (a b : Fin n) (h) =>
                //   @Fin.rec.{0} n outer_motive outer_mk a b h
                let (a_id, a) = b.fresh_local(fin_n(n.clone()));
                let (bv_id, bv) = b.fresh_local(fin_n(n.clone()));
                let hyp = eq_n(val(n.clone(), a.clone()), val(n.clone(), bv.clone()));
                let (h_id, h) = b.fresh_local(hyp.clone());
                let outer_rec = Expr::apps(
                    fin_rec_prop.clone(),
                    [n.clone(), outer_motive, outer_mk, a.clone()],
                );
                let applied = Expr::apps(outer_rec, [bv.clone(), h.clone()]);
                let r = b.mk_lam(h_id, BinderInfo::Default, hyp, applied);
                let r = b.mk_lam(bv_id, BinderInfo::Default, fin_n(n.clone()), r);
                let r = b.mk_lam(a_id, BinderInfo::Default, fin_n(n.clone()), r);
                let r = b.mk_lam(n_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Fin.eq_of_val_eq"),
                level_params: vec![],
                type_: eqv_type,
                value: eqv_value,
                is_reducible: true,
            })?;
        }

        let eq_of_val_eq = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);

        // ─────────────────────── instDecidableEqFin ───────────────────────
        // Type: {n : Nat} → (a b : Fin n) → Decidable (@Eq (Fin n) a b)
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(fin_n(n.clone()));
            let (bv_id, bv) = b.fresh_local(fin_n(n.clone()));
            let concl = Expr::app(dec.clone(), eq_fin(n.clone(), a.clone(), bv.clone()));
            let r = b.mk_pi(bv_id, BinderInfo::Default, fin_n(n.clone()), concl);
            let r = b.mk_pi(a_id, BinderInfo::Default, fin_n(n.clone()), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun {n} (a b : Fin n) =>
        //   @Decidable.rec (Eq Nat (Fin.val a)(Fin.val b)) dmotive
        //     isFalse_min isTrue_min (Nat.decEq (Fin.val a)(Fin.val b))
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(fin_n(n.clone()));
            let (bv_id, bv) = b.fresh_local(fin_n(n.clone()));

            let va = val(n.clone(), a.clone());
            let vb = val(n.clone(), bv.clone());
            let p_nat = eq_n(va.clone(), vb.clone()); // Eq Nat (Fin.val a)(Fin.val b)
            let goal = eq_fin(n.clone(), a.clone(), bv.clone()); // Eq (Fin n) a b
            let dec_goal = Expr::app(dec.clone(), goal.clone());

            // dmotive: fun (_ : Decidable p_nat) => Decidable (Eq (Fin n) a b)
            let dmotive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let dec_pnat = Expr::app(dec.clone(), p_nat.clone());
                let (d_id, _d) = c.fresh_local(dec_pnat.clone());
                c.finish_child(c.mk_lam(d_id, BinderInfo::Default, dec_pnat, dec_goal.clone()))
            };

            // isFalse_min: fun (hne : p_nat → False) =>
            //   @Decidable.isFalse goal
            //     (fun (h : Eq (Fin n) a b) =>
            //        hne (@congrArg (Fin n) Nat a b Fin.val h))
            let is_false_min = {
                let not_p = Expr::pi(BinderInfo::Default, p_nat.clone(), false_c.clone());
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hne_id, hne) = c.fresh_local(not_p.clone());
                let disproof = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h_id, h) = d.fresh_local(goal.clone());
                    // congrArg : {α β} (a b : α) (f : α → β) → a = b → f a = f b
                    // @congrArg (Fin n) Nat a b (Fin.val n) h : Fin.val a = Fin.val b
                    let fin_val_n = Expr::app(fin_val.clone(), n.clone());
                    let cong = Expr::apps(
                        congr_arg.clone(),
                        [
                            fin_n(n.clone()),
                            nat.clone(),
                            a.clone(),
                            bv.clone(),
                            fin_val_n,
                            h.clone(),
                        ],
                    );
                    let body = Expr::app(hne.clone(), cong);
                    d.finish_child(d.mk_lam(h_id, BinderInfo::Default, goal.clone(), body))
                };
                let body = Expr::apps(is_false.clone(), [goal.clone(), disproof]);
                c.finish_child(c.mk_lam(hne_id, BinderInfo::Default, not_p, body))
            };

            // isTrue_min: fun (heq : p_nat) =>
            //   @Decidable.isTrue goal (@Fin.eq_of_val_eq n a b heq)
            let is_true_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (heq_id, heq) = c.fresh_local(p_nat.clone());
                let lifted = Expr::apps(
                    eq_of_val_eq.clone(),
                    [n.clone(), a.clone(), bv.clone(), heq.clone()],
                );
                let body = Expr::apps(is_true.clone(), [goal.clone(), lifted]);
                c.finish_child(c.mk_lam(heq_id, BinderInfo::Default, p_nat.clone(), body))
            };

            let discriminant = Expr::apps(nat_dec_eq.clone(), [va.clone(), vb.clone()]);
            let rec_app = Expr::apps(
                dec_rec.clone(),
                [p_nat, dmotive, is_false_min, is_true_min, discriminant],
            );
            let r = b.mk_lam(bv_id, BinderInfo::Default, fin_n(n.clone()), rec_app);
            let r = b.mk_lam(a_id, BinderInfo::Default, fin_n(n.clone()), r);
            let r = b.mk_lam(n_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableEqFin"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_dec_eq_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_dec_eq_proof().expect("register");
        env.register_fin_dec_eq_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]))
            .expect("Fin.eq_of_val_eq should type-check");
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("instDecidableEqFin"),
                vec![],
            ))
            .expect("instDecidableEqFin should type-check");

        let kind = env
            .get_const(&Name::from_string("instDecidableEqFin"))
            .expect("registered")
            .kind;
        assert_eq!(
            kind,
            super::super::types::ConstantKind::Definition,
            "instDecidableEqFin must be a computable Definition, not an Axiom"
        );

        for name in ["instDecidableEqFin", "Fin.eq_of_val_eq"] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .expect("registered");
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        }
    }
}
