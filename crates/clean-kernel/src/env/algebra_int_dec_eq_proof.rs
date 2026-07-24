// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Int.decEq : (a b : Int) → Decidable (Eq a b)` — a real kernel
//! term (NO `sorry`, NO axiom), backing `instDecidableEqInt` so `decide`/`if`
//! over `Int` equalities resolve an instance instead of the elaborator's
//! synthetic `Decidable`-sorry fallback (`infer/elab_app.rs`).
//!
//! `Int` is the 2-constructor inductive `Int.ofNat : Nat → Int` /
//! `Int.negSucc : Nat → Int` (see `init_int`). Equality is decided by a 2×2
//! `Int.rec`/`Int.rec` case split:
//!
//! - **same constructor** (`ofNat na`/`ofNat nb`, or `negSucc na`/`negSucc nb`):
//!   dispatch on `Nat.decEq na nb`. `isTrue` lifts `na = nb` to the goal via
//!   `congrArg <ctor>`; `isFalse` refutes `<ctor> na = <ctor> nb` by mapping it
//!   through the carrier projection `Int.natCarrier` (`ofNat n ↦ n`,
//!   `negSucc n ↦ n`, built here via `Int.rec`) — `congrArg Int.natCarrier h`
//!   reduces (ι) to `na = nb`, contradicting the `Nat.decEq` `isFalse` witness.
//! - **different constructors** (`ofNat`/`negSucc` either way): `isFalse` with
//!   `fun h => Int.noConfusion h` — distinct constructors make
//!   `Int.noConfusionType False _ _` δ-reduce to `False`.
//!
//! # Axiom closure
//!
//! The term mentions only `Eq`, `Int`, `Int.ofNat`, `Int.negSucc`, `Int.rec`,
//! `Int.noConfusion`, `Int.natCarrier` (a local `Int.rec` def), `Nat`,
//! `Nat.decEq`, `Decidable`(`.rec`/`.isTrue`/`.isFalse`), `congrArg`, `False` —
//! all constructive (generated recursors / reducible definitions / the
//! axiom-free `Nat.decEq`). So `env.axiom_deps("Int.decEq")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Int.natCarrier : Int → Nat` (`ofNat n ↦ n`, `negSucc n ↦ n`)
    /// and the kernel-checked `Int.decEq` definition. Idempotent; axiom-free.
    ///
    /// REQUIRES: `Int`, `Int.ofNat`, `Int.negSucc`, `Int.rec`,
    ///           `Int.noConfusion`, `Nat`, `Nat.decEq`, `Eq`, `congrArg`,
    ///           `Decidable`(+ctors/rec), `False` are registered.
    pub(crate) fn register_int_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("Int.decEq")).is_some() {
            return Ok(());
        }

        // Dependencies. `init_true_false` before `init_decidable` so
        // `Decidable.isFalse` carries the real `(p → False)` negation type.
        self.init_eq()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_true_false()?;
        self.init_decidable()?;
        self.register_nat_dec_eq_proof()?;
        if self
            .get_const(&Name::from_string("Int.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        // ----- shared constants -----
        let type1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let int_c = Expr::const_(Name::from_string("Int"), vec![]);
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let int_rec = Expr::const_(Name::from_string("Int.rec"), vec![type1.clone()]);
        let no_conf = Expr::const_(Name::from_string("Int.noConfusion"), vec![Level::zero()]);
        let nat_dec_eq = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
        let eq_ty = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let carrier_c = Expr::const_(Name::from_string("Int.natCarrier"), vec![]);

        // helper closures
        let eq_i = |l: Expr, r: Expr| Expr::apps(eq_ty.clone(), [int_c.clone(), l, r]);
        let dec_eq_i = |l: Expr, r: Expr| Expr::app(dec.clone(), eq_i(l, r));
        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
                [nat.clone(), l, r],
            )
        };

        // ----- Int.natCarrier : Int → Nat := fun i => Int.rec (fun n => n)
        //       (fun n => n) i  (carrier of either constructor) -----
        if self
            .get_const(&Name::from_string("Int.natCarrier"))
            .is_none()
        {
            let carrier_type = Expr::pi(BinderInfo::Default, int_c.clone(), nat.clone());
            let carrier_value = {
                let mut b = EnvDeclBuilder::new();
                let (i_id, i) = b.fresh_local(int_c.clone());
                // motive: fun (_ : Int) => Nat
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (mi_id, _mi) = c.fresh_local(int_c.clone());
                    c.finish_child(c.mk_lam(mi_id, BinderInfo::Default, int_c.clone(), nat.clone()))
                };
                let ofnat_min = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (n_id, n) = c.fresh_local(nat.clone());
                    c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat.clone(), n))
                };
                let negsucc_min = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (n_id, n) = c.fresh_local(nat.clone());
                    c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat.clone(), n))
                };
                let rec_app =
                    Expr::apps(int_rec.clone(), [motive, ofnat_min, negsucc_min, i.clone()]);
                let e = b.mk_lam(i_id, BinderInfo::Default, int_c.clone(), rec_app);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.natCarrier"),
                level_params: vec![],
                type_: carrier_type,
                value: carrier_value,
                is_reducible: true,
            })?;
        }

        // ----- Type: (a b : Int) → Decidable (Eq a b) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_c.clone());
            let (bv_id, bv) = b.fresh_local(int_c.clone());
            let concl = dec_eq_i(a.clone(), bv.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, int_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_c.clone(), e);
            b.finish(e)
        };

        // Build the same-constructor decision: dispatch on `Nat.decEq na nb`,
        // lifting through constructor `ctor` (`Int.ofNat` or `Int.negSucc`).
        // `parent` is the builder whose scope `na` lives in (the a-minor),
        // `na` is the already-bound outer carrier.
        let same_ctor_b_minor = |ctor: &Expr, na: &Expr, d_parent: &EnvDeclBuilder| -> Expr {
            let mut d = EnvDeclBuilder::child_of(d_parent);
            let (nb_id, nb) = d.fresh_local(nat.clone());
            let ctor_na = Expr::app(ctor.clone(), na.clone());
            let ctor_nb = Expr::app(ctor.clone(), nb.clone());
            let p_nat = eq_n(na.clone(), nb.clone());
            let concl = dec_eq_i(ctor_na.clone(), ctor_nb.clone());

            // Decidable.rec motive: fun (_ : Decidable (Eq Nat na nb)) => concl
            let dmotive = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (dsc_id, _dsc) = e.fresh_local(Expr::app(dec.clone(), p_nat.clone()));
                e.finish_child(e.mk_lam(
                    dsc_id,
                    BinderInfo::Default,
                    Expr::app(dec.clone(), p_nat.clone()),
                    concl.clone(),
                ))
            };

            // isFalse minor: fun (hne : Eq Nat na nb → False) =>
            //   @Decidable.isFalse concl
            //     (fun (h : Eq Int (ctor na) (ctor nb)) =>
            //        hne (@congrArg Int Nat (ctor na) (ctor nb) Int.natCarrier h))
            let is_false_min = {
                let not_p = Expr::pi(BinderInfo::Default, p_nat.clone(), false_c.clone());
                let mut e = EnvDeclBuilder::child_of(&d);
                let (hne_id, hne) = e.fresh_local(not_p.clone());
                let eq_ctor = eq_i(ctor_na.clone(), ctor_nb.clone());
                let disproof = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (h_id, h) = g.fresh_local(eq_ctor.clone());
                    // congrArg Int.natCarrier h
                    //   : Eq Nat (natCarrier (ctor na)) (natCarrier (ctor nb))
                    //   ≡ Eq Nat na nb   (ι on Int.natCarrier (ctor _))
                    let cong = Expr::apps(
                        congr_arg.clone(),
                        [
                            int_c.clone(),
                            nat.clone(),
                            ctor_na.clone(),
                            ctor_nb.clone(),
                            carrier_c.clone(),
                            h,
                        ],
                    );
                    let body = Expr::app(hne.clone(), cong);
                    g.finish_child(g.mk_lam(h_id, BinderInfo::Default, eq_ctor.clone(), body))
                };
                let body = Expr::apps(is_false.clone(), [eq_ctor, disproof]);
                e.finish_child(e.mk_lam(hne_id, BinderInfo::Default, not_p, body))
            };

            // isTrue minor: fun (heq : Eq Nat na nb) =>
            //   @Decidable.isTrue concl (@congrArg Nat Int na nb ctor heq)
            let is_true_min = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (heq_id, heq) = e.fresh_local(p_nat.clone());
                let lifted = Expr::apps(
                    congr_arg.clone(),
                    [
                        nat.clone(),
                        int_c.clone(),
                        na.clone(),
                        nb.clone(),
                        ctor.clone(),
                        heq,
                    ],
                );
                // `Decidable.isTrue : {p : Prop} → p → Decidable p` takes the
                // PROPOSITION `p` (= `Eq Int (ctor na) (ctor nb)`), not the
                // `Decidable p` goal type.
                let eq_ctor = eq_i(ctor_na.clone(), ctor_nb.clone());
                let body = Expr::apps(is_true.clone(), [eq_ctor, lifted]);
                e.finish_child(e.mk_lam(heq_id, BinderInfo::Default, p_nat.clone(), body))
            };

            let discriminant = Expr::apps(nat_dec_eq.clone(), [na.clone(), nb.clone()]);
            let rec_app = Expr::apps(
                dec_rec.clone(),
                [p_nat, dmotive, is_false_min, is_true_min, discriminant],
            );
            d.finish_child(d.mk_lam(nb_id, BinderInfo::Default, nat.clone(), rec_app))
        };

        // Build the different-constructor decision (b-minor): the goal
        // `Decidable (Eq Int (ctor_a na) (ctor_b nb))` with distinct
        // constructors — `isFalse (fun h => Int.noConfusion h)`.
        let diff_ctor_b_minor =
            |ctor_a_na: &Expr, ctor_b: &Expr, d_parent: &EnvDeclBuilder| -> Expr {
                let mut d = EnvDeclBuilder::child_of(d_parent);
                let (nb_id, nb) = d.fresh_local(nat.clone());
                let ctor_nb = Expr::app(ctor_b.clone(), nb.clone());
                let eq_mix = eq_i(ctor_a_na.clone(), ctor_nb.clone());
                // fun (h : Eq Int (ctor_a na) (ctor_b nb)) =>
                //   @Int.noConfusion.{0} False (ctor_a na) (ctor_b nb) h
                let disproof = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (h_id, h) = g.fresh_local(eq_mix.clone());
                    let body = Expr::apps(
                        no_conf.clone(),
                        [false_c.clone(), ctor_a_na.clone(), ctor_nb.clone(), h],
                    );
                    g.finish_child(g.mk_lam(h_id, BinderInfo::Default, eq_mix.clone(), body))
                };
                let body = Expr::apps(is_false.clone(), [eq_mix, disproof]);
                d.finish_child(d.mk_lam(nb_id, BinderInfo::Default, nat.clone(), body))
            };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_c.clone());
            let (bv_id, bv) = b.fresh_local(int_c.clone());

            // outer motive: fun (_a : Int) => Decidable (Eq Int _a b)
            let motive_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ap_id, ap) = c.fresh_local(int_c.clone());
                c.finish_child(c.mk_lam(
                    ap_id,
                    BinderInfo::Default,
                    int_c.clone(),
                    dec_eq_i(ap, bv.clone()),
                ))
            };

            // a is `Int.ofNat na`: inner Int.rec on b.
            let a_ofnat_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (na_id, na) = c.fresh_local(nat.clone());
                let ofnat_na = Expr::app(of_nat.clone(), na.clone());
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (bp_id, bp) = d.fresh_local(int_c.clone());
                    d.finish_child(d.mk_lam(
                        bp_id,
                        BinderInfo::Default,
                        int_c.clone(),
                        dec_eq_i(ofnat_na.clone(), bp),
                    ))
                };
                // b = ofNat nb : same ctor; b = negSucc nb : different.
                let b_ofnat = same_ctor_b_minor(&of_nat, &na, &c);
                let b_negsucc = diff_ctor_b_minor(&ofnat_na, &neg_succ, &c);
                let inner_rec =
                    Expr::apps(int_rec.clone(), [motive_b, b_ofnat, b_negsucc, bv.clone()]);
                c.finish_child(c.mk_lam(na_id, BinderInfo::Default, nat.clone(), inner_rec))
            };

            // a is `Int.negSucc na`: inner Int.rec on b.
            let a_negsucc_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (na_id, na) = c.fresh_local(nat.clone());
                let negsucc_na = Expr::app(neg_succ.clone(), na.clone());
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (bp_id, bp) = d.fresh_local(int_c.clone());
                    d.finish_child(d.mk_lam(
                        bp_id,
                        BinderInfo::Default,
                        int_c.clone(),
                        dec_eq_i(negsucc_na.clone(), bp),
                    ))
                };
                // b = ofNat nb : different; b = negSucc nb : same ctor.
                let b_ofnat = diff_ctor_b_minor(&negsucc_na, &of_nat, &c);
                let b_negsucc = same_ctor_b_minor(&neg_succ, &na, &c);
                let inner_rec =
                    Expr::apps(int_rec.clone(), [motive_b, b_ofnat, b_negsucc, bv.clone()]);
                c.finish_child(c.mk_lam(na_id, BinderInfo::Default, nat.clone(), inner_rec))
            };

            let outer_rec = Expr::apps(
                int_rec.clone(),
                [motive_a, a_ofnat_min, a_negsucc_min, a.clone()],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, int_c.clone(), outer_rec);
            let e = b.mk_lam(a_id, BinderInfo::Default, int_c.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.decEq"),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    #[test]
    fn test_int_dec_eq_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_int_dec_eq_proof().expect("register");
        env.register_int_dec_eq_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Int.decEq"), vec![]))
            .expect("Int.decEq should type-check");
        let deps = env
            .axiom_deps(&Name::from_string("Int.decEq"))
            .expect("registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "Int.decEq must be axiom-free, got {names:?}"
        );
    }
}
