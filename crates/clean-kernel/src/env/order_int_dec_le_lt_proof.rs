// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Int.decLe : (a b : Int) → Decidable (Int.le a b)` and
//! `Int.decLt : (a b : Int) → Decidable (Int.lt a b)` — real kernel terms
//! (NO `sorry`, NO axiom). These are the leaves that let `if (a ≤ b)` /
//! `if (a < b)` / `decide` over `Int` orderings elaborate without a synthetic
//! `sorry`, demoting the legacy `Declaration::Axiom`s `instDecidableIntLe` /
//! `instDecidableIntLt` (`order_int.rs::init_int_decidable_ord`) to
//! `Declaration::Definition`s carrying these real values.
//!
//! This mirrors the wave-1/wave-7 `Nat` work (`algebra_nat_dec_le_proof.rs`),
//! but the discriminator is structural rather than `ble`-based: `Int.le`/`Int.lt`
//! are both `Int.NonNeg`-of-a-difference, and `Int.NonNeg x` is decidable by a
//! single `@Int.rec` case-split on the sign of `x`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)               -- reducible Definition
//! Int.lt a b := Int.le (Int.add a 1) b
//!             ≡ Int.NonNeg (Int.sub b (Int.add a 1))     -- (1 := ofNat (succ 0))
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! # Proof shape
//!
//! ## `Int.not_nonneg_negSucc : (n : Nat) → Int.NonNeg (Int.negSucc n) → False`
//!
//! A `@Int.NonNeg.rec.{0}` recursion against the discriminator predicate
//! `disc i := @Int.rec.{1} (fun _ => Prop) (fun _ => True) (fun _ => False) i`
//! (`True` on `Int.ofNat`, `False` on `Int.negSucc`). The single `ofNat` minor
//! is closed with `True.intro`; instantiated at the major `Int.negSucc n` the
//! recursor yields `disc (Int.negSucc n) ≡ False`. Generalizes the `negSucc 0`
//! discharge of `algebra_int_lt_irrefl_proof.rs` to an arbitrary index `n`.
//!
//! ## `Int.decNonNeg : (x : Int) → Decidable (Int.NonNeg x)`
//!
//! A single `@Int.rec.{1}` case-split on `x` with motive
//! `fun (x : Int) => Decidable (Int.NonNeg x)`:
//!
//! - `ofNat n` minor → `@Decidable.isTrue (Int.NonNeg (Int.ofNat n)) (@Int.NonNeg.mk n)`
//! - `negSucc n` minor → `@Decidable.isFalse (Int.NonNeg (Int.negSucc n))
//!                          (Int.not_nonneg_negSucc n)`
//!
//! ## `Int.decLe` / `Int.decLt`
//!
//! Thin reducible wrappers:
//!
//! ```text
//! Int.decLe a b := Int.decNonNeg (Int.sub b a)
//! Int.decLt a b := Int.decNonNeg (Int.sub b (Int.add a 1))
//! ```
//!
//! `Decidable (Int.NonNeg (Int.sub b a))` is def-eq to `Decidable (Int.le a b)`
//! (δ-unfold `Int.le`); likewise `Decidable (Int.NonNeg (Int.sub b (a+1)))` is
//! def-eq to `Decidable (Int.lt a b)` (δ-unfold `Int.lt` then `Int.le`). So the
//! declared types `(a b : Int) → Decidable (Int.le a b)` / `… (Int.lt a b)`
//! kernel-check against these values.
//!
//! # Axiom closure
//!
//! The terms mention only `Int`, `Int.ofNat`, `Int.negSucc`, `Int.sub`,
//! `Int.add`, `Int.le`, `Int.lt`, `Int.NonNeg`(`.mk`/`.rec`), `Int.rec`,
//! `Nat`(`.zero`/`.succ`), `Bool`-free logical primitives `True`/`True.intro`/
//! `False`, `Decidable`(`.isTrue`/`.isFalse`) — all constructive (generated
//! recursors / reducible definitions / inductive constructors). So
//! `env.axiom_deps("Int.not_nonneg_negSucc")`, `…("Int.decNonNeg")`,
//! `…("Int.decLe")`, `…("Int.decLt")` are all empty, and the demoted
//! `instDecidableIntLe` / `instDecidableIntLt` Definitions inherit empty
//! closures.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the four declarations.
struct IntDecConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub: Expr,
    int_add: Expr,
    int_le: Expr,
    int_lt: Expr,
    nonneg: Expr,
    nonneg_mk: Expr,
    /// `Int.NonNeg.rec.{0}` — Prop-valued (result `False`/`Prop` : Sort 0).
    nonneg_rec: Expr,
    /// `Int.rec.{1}` — value into `Decidable _ : Type` / `Prop : Sort 1`.
    int_rec_type1: Expr,
    decidable: Expr,
    is_true: Expr,
    is_false: Expr,
    true_const: Expr,
    true_intro: Expr,
    false_const: Expr,
    not_nonneg_negsucc: Expr,
    dec_nonneg: Expr,
}

impl IntDecConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            int_rec_type1: Expr::const_(Name::from_string("Int.rec"), vec![type1.clone()]),
            decidable: Expr::const_(Name::from_string("Decidable"), vec![]),
            is_true: Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
            is_false: Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            not_nonneg_negsucc: Expr::const_(Name::from_string("Int.not_nonneg_negSucc"), vec![]),
            dec_nonneg: Expr::const_(Name::from_string("Int.decNonNeg"), vec![]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    fn dec_of(&self, p: Expr) -> Expr {
        Expr::app(self.decidable.clone(), p)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [x, y])
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [x, y])
    }

    /// `Int.ofNat (Nat.succ Nat.zero)`  (the literal `1 : Int`).
    fn one(&self) -> Expr {
        self.of_nat(Expr::app(self.nat_succ.clone(), self.nat_zero.clone()))
    }

    /// `disc = @Int.rec.{1} (fun _ : Int => Prop) (fun _ : Nat => True)
    ///                      (fun _ : Nat => False)`.
    ///
    /// `disc (Int.ofNat n)` reduces to `True`, `disc (Int.negSucc n)` to
    /// `False`. Built as a closed (no free fvar) term.
    fn discriminator(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        // motive: fun _ : Int => Prop
        let prop_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (i_id, _i) = mb.fresh_local(self.int_type.clone());
            let lam = mb.mk_lam(
                i_id,
                BinderInfo::Default,
                self.int_type.clone(),
                Expr::prop(),
            );
            mb.finish_child(lam)
        };
        // ofNat minor: fun _ : Nat => True
        let of_nat_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat_type.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat_type.clone(),
                self.true_const.clone(),
            );
            mb.finish_child(lam)
        };
        // negSucc minor: fun _ : Nat => False
        let neg_succ_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat_type.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat_type.clone(),
                self.false_const.clone(),
            );
            mb.finish_child(lam)
        };
        // disc = fun i : Int => @Int.rec.{1} prop_motive of_nat_minor neg_succ_minor i
        let (i_id, i) = b.fresh_local(self.int_type.clone());
        let rec_app = Expr::apps(
            self.int_rec_type1.clone(),
            [prop_motive, of_nat_minor, neg_succ_minor, i.clone()],
        );
        let lam = b.mk_lam(i_id, BinderInfo::Default, self.int_type.clone(), rec_app);
        b.finish_child(lam)
    }
}

// ===========================================================================
// Int.not_nonneg_negSucc : (n : Nat) → Int.NonNeg (Int.negSucc n) → False
// ===========================================================================

fn build_not_nonneg_negsucc_type(c: &IntDecConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let hyp = c.nonneg_of(c.neg_succ(n.clone()));
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, hyp, c.false_const.clone());
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), r);
    b.finish(r)
}

fn build_not_nonneg_negsucc_value(c: &IntDecConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let neg_succ_n = c.neg_succ(n.clone());
    let hyp = c.nonneg_of(neg_succ_n.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());

    let disc = c.discriminator(&b);

    // NonNeg.rec motive: fun (i : Int) (_ : NonNeg i) => disc i
    let rec_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let hi_type = c.nonneg_of(i.clone());
        let (hi_id, _hi) = mb.fresh_local(hi_type.clone());
        let body = Expr::app(disc.clone(), i.clone());
        let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_type, body);
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
        mb.finish_child(lam)
    };

    // NonNeg.rec minor: fun (m : Nat) => True.intro   (goal `disc (ofNat m) ≡ True`)
    let rec_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = mb.fresh_local(c.nat_type.clone());
        let lam = mb.mk_lam(
            m_id,
            BinderInfo::Default,
            c.nat_type.clone(),
            c.true_intro.clone(),
        );
        mb.finish_child(lam)
    };

    // @Int.NonNeg.rec.{0} rec_motive rec_minor (Int.negSucc n) h
    //   : disc (Int.negSucc n) ≡ False
    let false_proof = Expr::apps(c.nonneg_rec.clone(), [rec_motive, rec_minor, neg_succ_n, h]);

    // λ (n : Nat) (h : NonNeg (negSucc n)) => false_proof
    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, false_proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val);
    b.finish(val)
}

// ===========================================================================
// Int.decNonNeg : (x : Int) → Decidable (Int.NonNeg x)
// ===========================================================================

fn build_dec_nonneg_type(c: &IntDecConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.int_type.clone());
    let concl = c.dec_of(c.nonneg_of(x.clone()));
    let r = b.mk_pi(x_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(r)
}

fn build_dec_nonneg_value(c: &IntDecConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.int_type.clone());

    // motive: fun (x : Int) => Decidable (Int.NonNeg x)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let body = c.dec_of(c.nonneg_of(i.clone()));
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // ofNat minor: fun (n : Nat) =>
    //   @Decidable.isTrue (Int.NonNeg (Int.ofNat n)) (@Int.NonNeg.mk n)
    let of_nat_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = mb.fresh_local(c.nat_type.clone());
        let prop = c.nonneg_of(c.of_nat(n.clone()));
        let witness = Expr::app(c.nonneg_mk.clone(), n.clone());
        let body = Expr::apps(c.is_true.clone(), [prop, witness]);
        let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // negSucc minor: fun (n : Nat) =>
    //   @Decidable.isFalse (Int.NonNeg (Int.negSucc n)) (Int.not_nonneg_negSucc n)
    let neg_succ_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = mb.fresh_local(c.nat_type.clone());
        let prop = c.nonneg_of(c.neg_succ(n.clone()));
        let disproof = Expr::app(c.not_nonneg_negsucc.clone(), n.clone());
        let body = Expr::apps(c.is_false.clone(), [prop, disproof]);
        let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // @Int.rec.{1} motive of_nat_minor neg_succ_minor x : Decidable (NonNeg x)
    let rec_app = Expr::apps(
        c.int_rec_type1.clone(),
        [motive, of_nat_minor, neg_succ_minor, x.clone()],
    );
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    b.finish(lam)
}

// ===========================================================================
// Int.decLe / Int.decLt
// ===========================================================================

/// `(a b : Int) → Decidable (rel a b)` for a chosen `rel` constant.
fn build_dec_rel_type(c: &IntDecConsts, rel: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.dec_of(Expr::apps(rel.clone(), [a.clone(), bv.clone()]));
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// `Int.decLe := λ a b => Int.decNonNeg (Int.sub b a)`.
fn build_dec_le_value(c: &IntDecConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let body = Expr::app(c.dec_nonneg.clone(), c.sub(bv.clone(), a.clone()));
    let r = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    let r = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// `Int.decLt := λ a b => Int.decNonNeg (Int.sub b (Int.add a 1))`.
fn build_dec_lt_value(c: &IntDecConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let a_plus_one = c.add(a.clone(), c.one());
    let body = Expr::app(c.dec_nonneg.clone(), c.sub(bv.clone(), a_plus_one));
    let r = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    let r = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

impl Environment {
    /// Register the constructive `Int.not_nonneg_negSucc`, `Int.decNonNeg`,
    /// `Int.decLe`, `Int.decLt` kernel terms (idempotent, axiom-free).
    ///
    /// # Contract
    ///
    /// REQUIRES: `Int`, `Int.ofNat`, `Int.negSucc`, `Int.sub`, `Int.add`,
    ///           `Int.le`, `Int.lt`, `Int.NonNeg`(+`.mk`/`.rec`), `Int.rec`,
    ///           `Nat`(+`.zero`/`.succ`), `True`/`True.intro`/`False`,
    ///           `Decidable`(+ctors) are registered (auto-initialized here).
    /// ENSURES: On success, all four constants are kernel-checked
    ///          `Declaration::Definition` / `Declaration::Theorem` values whose
    ///          axiom closures are empty.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_dec_le_lt_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let have_le = self.get_const(&Name::from_string("Int.decLe")).is_some();
        let have_lt = self.get_const(&Name::from_string("Int.decLt")).is_some();
        if have_le && have_lt {
            return Ok(());
        }

        // Dependencies. `init_true_false` before `init_decidable` so
        // `Decidable.isFalse` carries the real `(p → False)` negation type.
        self.init_int_ord()?; // Int.le, Int.lt, Int.NonNeg(+mk/rec), Int.sub, Int.add
        self.init_true_false()?; // True, True.intro, False
        self.init_decidable()?; // Decidable, isTrue, isFalse

        let c = IntDecConsts::new();

        // ── Int.not_nonneg_negSucc ──
        let name_nnns = Name::from_string("Int.not_nonneg_negSucc");
        if self.get_const(&name_nnns).is_none() {
            let type_ = build_not_nonneg_negsucc_type(&c);
            let value = build_not_nonneg_negsucc_value(&c);
            self.add_decl(Declaration::Theorem {
                name: name_nnns,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Int.decNonNeg ──
        let name_dnn = Name::from_string("Int.decNonNeg");
        if self.get_const(&name_dnn).is_none() {
            let type_ = build_dec_nonneg_type(&c);
            let value = build_dec_nonneg_value(&c);
            self.add_decl(Declaration::Definition {
                name: name_dnn,
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // ── Int.decLe ──
        if !have_le {
            let type_ = build_dec_rel_type(&c, &c.int_le);
            let value = build_dec_le_value(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.decLe"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // ── Int.decLt ──
        if !have_lt {
            let type_ = build_dec_rel_type(&c, &c.int_lt);
            let value = build_dec_lt_value(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.decLt"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_int_dec_le_lt_registered_and_type_check() {
        let mut env = Environment::new();
        env.register_int_dec_le_lt_proof()
            .expect("first registration");
        env.register_int_dec_le_lt_proof()
            .expect("idempotent re-registration");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for (name, kind) in [
            ("Int.not_nonneg_negSucc", ConstantKind::Theorem),
            ("Int.decNonNeg", ConstantKind::Definition),
            ("Int.decLe", ConstantKind::Definition),
            ("Int.decLt", ConstantKind::Definition),
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(info.kind, kind, "{name} declaration kind");
            assert!(info.value.is_some(), "{name} must retain its value");
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    #[test]
    fn test_int_dec_le_lt_axiom_closures_empty() {
        let mut env = Environment::new();
        env.register_int_dec_le_lt_proof().unwrap();
        for name in [
            "Int.not_nonneg_negSucc",
            "Int.decNonNeg",
            "Int.decLe",
            "Int.decLt",
        ] {
            let n = Name::from_string(name);
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(
                !names.iter().any(|s| s == "sorry" || s == "sorryAx"),
                "{name} must not depend on sorry/sorryAx; closure = {names:?}"
            );
            assert!(
                names.is_empty(),
                "{name} must have empty axiom closure, got {names:?}"
            );
        }
    }
}
