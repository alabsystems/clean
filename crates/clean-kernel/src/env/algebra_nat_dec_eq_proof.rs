// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Nat.decEq : (a b : Nat) → Decidable (Eq a b)` — the sound
//! decision procedure for natural-number equality, built as a real kernel term
//! (NO `sorry`, NO axiom).
//!
//! This is the leaf that makes `if (1 = 1) then … else …` and `decide`
//! over `Nat` equalities elaborate without a synthetic `sorry`. It is
//! registered as a `Decidable`-class instance (see `init_decidable_eq`) whose
//! resolved type, after stripping the two explicit `Nat` binders, is
//! `Decidable (@Eq Nat ?a ?b)` — exactly the shape the elaborator's
//! `resolve_decidable` asks for.
//!
//! # Proof sketch
//!
//! Double structural recursion. With `C n := (m : Nat) → Decidable (Eq n m)`:
//!
//! ```text
//! Nat.decEq : (n m : Nat) → Decidable (Eq n m) :=
//!   fun n m => (@Nat.rec.{1} C zCase sCase n) m
//!   zCase : C 0           -- fun m => Nat.rec … m
//!     | 0      => isTrue  (Eq.refl 0)
//!     | succ k => isFalse (fun h => Nat.noConfusion h)        -- 0 ≠ succ k
//!   sCase : (n) → C n → C (succ n)  -- fun n ih_n m => Nat.rec … m
//!     | 0      => isFalse (fun h => Nat.noConfusion h)        -- succ n ≠ 0
//!     | succ k => match ih_n k with                           -- decide n = k
//!         | isTrue  h   => isTrue  (congrArg Nat.succ h)      -- succ n = succ k
//!         | isFalse hne => isFalse (fun heq => hne (Nat.succ_inj n k heq))
//! ```
//!
//! Every `isFalse` branch carries a genuine `¬(a = b)` term: for distinct
//! constructors `@Nat.noConfusionType False 0 (succ k)` δι-reduces to `False`
//! (so `@Nat.noConfusion.{0} False 0 (succ k) h : False` directly, no
//! continuation); for the `succ/succ` diagonal we discharge via the
//! constructive `Nat.succ_inj` (constructor injectivity, itself a
//! `Nat.noConfusion` term — see `algebra_nat_succ_inj_proof.rs`).
//!
//! # Axiom closure
//!
//! The term mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.rec`, `Nat.noConfusion`, `Nat.succ_inj`, `congrArg`, `Decidable`,
//! `Decidable.isTrue`, `Decidable.isFalse`, `Decidable.rec`, and `False` — all
//! constructive (generated recursors / reducible definitions / constructive
//! theorems). So `env.axiom_deps("Nat.decEq")` is empty and
//! `env.proof_quality("Nat.decEq") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.decEq` as a kernel-checked `Declaration::Definition`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Nat.noConfusion`,
    ///           `Eq`, `Eq.refl`, `congrArg`, `Decidable` (+ ctors/rec) are
    ///           registered (auto-initialized here).
    /// ENSURES: On success, `Nat.decEq` is a `Definition` whose value
    ///          type-checks at `(a b : Nat) → Decidable (Eq a b)` and whose
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.decEq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // IMPORT MODE (`suppress_lossy_structure_stubs`): WITHHOLD Clean's
        // hand-rolled `Nat.decEq`. Two reasons, both tied to the gated
        // `Nat.succ_inj` overlay (see `register_nat_succ_inj_proof`):
        //
        //  1. Clean's `Nat.decEq` VALUE is a double-`Nat.rec` decision procedure
        //     whose succ/succ diagonal disproof references the divergent
        //     `Nat.succ_inj` overlay. With that overlay gated out in import mode,
        //     this term would reference an absent constant and fail `add_decl`,
        //     which would in turn abort the whole import prelude (this helper is
        //     reached from `init_decidable_eq`). Withholding it keeps prelude
        //     construction sound.
        //
        //  2. Genuine Lean 4 v4.8.0 `Nat.decEq` (a `@[reducible]` `Nat.beq`-based
        //     `match` definition, axiom-free) lives in `Init` and is already part
        //     of every Mathlib import closure, so the import lane loses nothing —
        //     the real `Nat.decEq` (and the genuine `instDecidableEqNat`) serve
        //     the `decide`/`if a=b` path through the trusted/checked import path.
        //
        // SOUNDNESS: identical to the `Nat.succ_inj` and Nat-arith overlay gates
        // — suppression only ever lets the genuine kernel-checked Mathlib/Init
        // constant import in the overlay's place; nothing here touches
        // `is_def_eq`/`check_type`/`whnf`. The NON-import lane (`clean check`,
        // the `decide` path, and every Clean-native consumer — Fin/Int/UInt/
        // Char/String decEq, `boolean_analysis_*`, the nn-verify Fin lanes)
        // keeps Clean's `Nat.decEq` UNCHANGED.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        self.init_eq()?;
        self.init_nat()?;
        // `False` must exist before the term references it, AND must be
        // registered before `init_decidable` so `Decidable.isFalse` carries the
        // real `(p → False)` negation type (not the impredicative `∀ q, q`
        // fallback used pre-`init_true_false`).
        self.init_true_false()?;
        self.init_decidable()?;
        if self
            .get_const(&Name::from_string("Nat.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }
        // The succ/succ diagonal's disproof needs constructor injectivity.
        self.register_nat_succ_inj_proof()?;
        // `Nat.beq_refl` / `Nat.ne_of_beq_false` back the SOUND `isFalse` witness
        // the `Nat.decEq` native-decide reducer emits (replacing `sorryAx`).
        // Co-registered here so `Nat.decEq` existing ⟹ the lemmas exist.
        self.register_nat_beq_lemmas()?;

        // ----- shared constants -----
        let type1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ_c = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![type1.clone()]);
        let no_conf = Expr::const_(Name::from_string("Nat.noConfusion"), vec![Level::zero()]);
        let succ_inj = Expr::const_(Name::from_string("Nat.succ_inj"), vec![]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        // helper closures over the shared constants
        let succ = |x: Expr| Expr::app(succ_c.clone(), x);
        let eqn = |l: Expr, r: Expr| Expr::apps(eq_c.clone(), [nat.clone(), l, r]);
        let dec_eq = |l: Expr, r: Expr| Expr::app(dec.clone(), eqn(l, r));
        let mk_true = |prop: Expr, pf: Expr| Expr::apps(is_true.clone(), [prop, pf]);
        let mk_false = |prop: Expr, neg: Expr| Expr::apps(is_false.clone(), [prop, neg]);
        // `@Nat.noConfusion.{0} False lhs rhs h : False` for distinct ctors.
        let noconf_false = |lhs: Expr, rhs: Expr, h: Expr| {
            Expr::apps(no_conf.clone(), [false_c.clone(), lhs, rhs, h])
        };

        // ----- Type: (n m : Nat) → Decidable (Eq n m) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (m_id, m) = b.fresh_local(nat.clone());
            let concl = dec_eq(n.clone(), m.clone());
            let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // ----- outer motive: fun (_n : Nat) => (m : Nat) → Decidable (Eq _n m)
        let outer_c = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = c.fresh_local(nat.clone());
                let body = dec_eq(n.clone(), m);
                c.finish_child(c.mk_pi(m_id, BinderInfo::Default, nat.clone(), body))
            };
            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), inner))
        };

        // ----- zCase : C 0 = fun (m : Nat) => Nat.rec zC zZ zS m -----
        // zinnerC : fun (_m : Nat) => Decidable (Eq 0 _m)
        let z_inner_c = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let body = dec_eq(zero.clone(), m);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
        };
        // zinnerZ : Decidable (Eq 0 0) = isTrue (Eq.refl 0)
        let z_inner_z = mk_true(
            eqn(zero.clone(), zero.clone()),
            Expr::apps(eq_refl.clone(), [nat.clone(), zero.clone()]),
        );
        // zinnerS : fun (k : Nat) (_ih : Decidable (Eq 0 k)) =>
        //             isFalse (fun (h : Eq 0 (succ k)) => Nat.noConfusion h)
        let z_inner_s = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let (ih_id, _ih) = b.fresh_local(dec_eq(zero.clone(), k.clone()));
            let prop = eqn(zero.clone(), succ(k.clone()));
            let neg = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(prop.clone());
                let body = noconf_false(zero.clone(), succ(k.clone()), h);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, prop.clone(), body))
            };
            let body = mk_false(prop, neg);
            let e = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                dec_eq(zero.clone(), k.clone()),
                body,
            );
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };
        let z_case = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let body = Expr::apps(
                nat_rec.clone(),
                [z_inner_c.clone(), z_inner_z.clone(), z_inner_s.clone(), m],
            );
            b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
        };

        // ----- sCase : (n) → C n → C (succ n)
        //   = fun (n : Nat) (ih_n : C n) (m : Nat) => Nat.rec sIC sIZ sIS m
        let s_case = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            // ih_n : (m : Nat) → Decidable (Eq n m)
            let ih_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = c.fresh_local(nat.clone());
                let body = dec_eq(n.clone(), m);
                c.finish_child(c.mk_pi(m_id, BinderInfo::Default, nat.clone(), body))
            };
            let (ih_id, ih_n) = b.fresh_local(ih_ty.clone());
            let (m_id, m) = b.fresh_local(nat.clone());

            // sIC : fun (_m : Nat) => Decidable (Eq (succ n) _m)
            let s_inner_c = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mc_id, mc) = c.fresh_local(nat.clone());
                let body = dec_eq(succ(n.clone()), mc);
                c.finish_child(c.mk_lam(mc_id, BinderInfo::Default, nat.clone(), body))
            };
            // sIZ : Decidable (Eq (succ n) 0) = isFalse (fun h => Nat.noConfusion h)
            let s_inner_z = {
                let prop = eqn(succ(n.clone()), zero.clone());
                let neg = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(prop.clone());
                    let body = noconf_false(succ(n.clone()), zero.clone(), h);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, prop.clone(), body))
                };
                mk_false(prop, neg)
            };
            // sIS : fun (k : Nat) (_ih_m : Decidable (Eq (succ n) k)) =>
            //         @Decidable.rec.{1} (Eq n k) motive isFalseMin isTrueMin (ih_n k)
            let s_inner_s = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = c.fresh_local(nat.clone());
                let (ihm_id, _ihm) = c.fresh_local(dec_eq(succ(n.clone()), k.clone()));

                let p_nk = eqn(n.clone(), k.clone()); // Eq n k
                let concl = dec_eq(succ(n.clone()), succ(k.clone())); // Decidable (Eq (succ n)(succ k))

                // motive : fun (_ : Decidable (Eq n k)) => Decidable (Eq (succ n)(succ k))
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (dsc_id, _dsc) = d.fresh_local(Expr::app(dec.clone(), p_nk.clone()));
                    d.finish_child(d.mk_lam(
                        dsc_id,
                        BinderInfo::Default,
                        Expr::app(dec.clone(), p_nk.clone()),
                        concl.clone(),
                    ))
                };

                // isFalseMin : fun (hne : Eq n k → False) =>
                //   isFalse (fun (heq : Eq (succ n)(succ k)) =>
                //              hne (Nat.succ_inj n k heq))
                let is_false_min = {
                    let not_p = Expr::pi(BinderInfo::Default, p_nk.clone(), false_c.clone());
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hne_id, hne) = d.fresh_local(not_p.clone());
                    let succ_eq = eqn(succ(n.clone()), succ(k.clone()));
                    let neg = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (heq_id, heq) = e.fresh_local(succ_eq.clone());
                        let inj = Expr::apps(succ_inj.clone(), [n.clone(), k.clone(), heq]);
                        let body = Expr::app(hne.clone(), inj);
                        e.finish_child(e.mk_lam(heq_id, BinderInfo::Default, succ_eq.clone(), body))
                    };
                    let body = mk_false(succ_eq, neg);
                    d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p, body))
                };

                // isTrueMin : fun (heq : Eq n k) =>
                //   isTrue (congrArg Nat Nat n k Nat.succ heq)
                let is_true_min = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (heq_id, heq) = d.fresh_local(p_nk.clone());
                    let lifted = Expr::apps(
                        congr_arg.clone(),
                        [
                            nat.clone(),
                            nat.clone(),
                            n.clone(),
                            k.clone(),
                            succ_c.clone(),
                            heq,
                        ],
                    );
                    let body = mk_true(eqn(succ(n.clone()), succ(k.clone())), lifted);
                    d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, p_nk.clone(), body))
                };

                let discriminant = Expr::app(ih_n.clone(), k.clone());
                let rec_app = Expr::apps(
                    dec_rec.clone(),
                    [
                        p_nk.clone(),
                        motive,
                        is_false_min,
                        is_true_min,
                        discriminant,
                    ],
                );
                let e = c.mk_lam(
                    ihm_id,
                    BinderInfo::Default,
                    dec_eq(succ(n.clone()), k.clone()),
                    rec_app,
                );
                let e = c.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
                c.finish_child(e)
            };

            let rec_body = Expr::apps(nat_rec.clone(), [s_inner_c, s_inner_z, s_inner_s, m]);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), rec_body);
            let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // ----- value: fun (n m : Nat) => (Nat.rec outer_c zCase sCase n) m -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (m_id, m) = b.fresh_local(nat.clone());
            let rec_n = Expr::apps(
                nat_rec.clone(),
                [outer_c.clone(), z_case.clone(), s_case.clone(), n],
            );
            let body = Expr::app(rec_n, m);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
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
    use crate::env::types::ConstantKind;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// The kernel accepts the `Nat.decEq` decision-procedure term and registers
    /// it as a `Definition` (not an `Axiom`), idempotently.
    #[test]
    fn test_nat_dec_eq_registered_and_type_checks() {
        let mut env = Environment::new();
        env.register_nat_dec_eq_proof().expect("first registration");
        env.register_nat_dec_eq_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Nat.decEq"))
            .expect("Nat.decEq should be registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        assert!(info.value.is_some(), "Definition must retain its value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.decEq"), vec![]))
            .expect("Nat.decEq should type-check");
    }

    /// Axiom closure is empty — every branch is a real constructive term
    /// (recursors, `Nat.noConfusion`, `Nat.succ_inj`, `congrArg`); NO `sorry`,
    /// NO declared axiom. (`Nat.decEq` is a `Definition`/data, not a `Theorem`,
    /// so `proof_quality` does not classify it; the empty axiom closure is the
    /// soundness guarantee — `sorryAx`, were it present, would appear here.)
    #[test]
    fn test_nat_dec_eq_axiom_closure_empty() {
        let mut env = Environment::new();
        env.register_nat_dec_eq_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.decEq"))
            .expect("Nat.decEq is registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "Nat.decEq must have empty axiom closure, got {names:?}"
        );
    }

    /// The decision-procedure body genuinely dispatches via `Decidable.rec` and
    /// discharges disequality via `Nat.noConfusion` — guards against a
    /// degenerate / `sorry`-laden masquerade.
    #[test]
    fn test_nat_dec_eq_uses_decidable_rec_and_no_confusion() {
        let mut env = Environment::new();
        env.register_nat_dec_eq_proof().unwrap();
        let info = env.get_const(&Name::from_string("Nat.decEq")).unwrap();
        let value = info.value.as_ref().expect("Definition has value");

        fn mentions(e: &Expr, target: &str) -> bool {
            let mut hit = false;
            fn go(e: &Expr, target: &str, hit: &mut bool) {
                if *hit {
                    return;
                }
                match e.kind() {
                    ExprKind::Const(n, _) if n.to_string() == target => {
                        *hit = true;
                    }
                    ExprKind::App(f, a) => {
                        go(f, target, hit);
                        go(a, target, hit);
                    }
                    ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                        go(t, target, hit);
                        go(b, target, hit);
                    }
                    ExprKind::Let(_, t, v, b, _) => {
                        go(t, target, hit);
                        go(v, target, hit);
                        go(b, target, hit);
                    }
                    _ => {}
                }
            }
            go(e, target, &mut hit);
            hit
        }

        assert!(
            mentions(value, "Decidable.rec"),
            "must dispatch via Decidable.rec"
        );
        assert!(
            mentions(value, "Nat.noConfusion"),
            "must use Nat.noConfusion"
        );
        assert!(mentions(value, "Nat.succ_inj"), "must use Nat.succ_inj");
        assert!(mentions(value, "Nat.rec"), "must recurse via Nat.rec");
        assert!(!mentions(value, "sorryAx"), "must not contain sorryAx");
    }

    /// End-to-end: after `init_decidable_eq`, `Decidable` is a resolvable class
    /// and `Nat.decEq` is registered as one of its instances.
    #[test]
    fn test_decidable_class_and_nat_instance_registered() {
        let mut env = Environment::new();
        env.init_decidable_eq().expect("init_decidable_eq");
        assert!(
            env.classes()
                .any(|c| c.name == Name::from_string("Decidable")),
            "Decidable must be a registered class"
        );
        let insts = env.get_class_instances(&Name::from_string("Decidable"));
        assert!(
            insts
                .iter()
                .any(|i| i.name == Name::from_string("Nat.decEq")),
            "Nat.decEq must be registered as a Decidable instance"
        );
    }
}
