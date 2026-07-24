// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 4** (`rung4-reflect`): the NNReal→Rat ORDER-REFLECTION.
//!
//! `algebra_nnreal_le.rs` lands the FORWARD `ofRat` order bridge
//! `NNReal.ofRat_le_ofRat : Rat.le a b → NNReal.le (ofRat a)(ofRat b)` and names
//! its missing twin: the order-REFLECTION
//! `NNReal.le (ofRat a)(ofRat b) → Rat.le a b`. THIS module lands that twin,
//! routed through a genuine Rat Archimedean reverse step.
//!
//! ## What this registers (constructive, EMPTY admitted-axiom closure)
//!
//! 1. `Rat.le_of_forall_pos_lt_add :
//!      ∀ (a b : Rat), (∀ (e : Rat), Rat.lt Rat.zero e → Rat.lt a (Rat.add b e))
//!        → Rat.le a b`
//!    — the Rat Archimedean reverse. Proof (`Classical.em (a ≤ b)`):
//!    - YES (`a ≤ b`): returned directly.
//!    - NO (`hnab : ¬(a ≤ b)`): `Rat.le_total a b` refutes its left disjunct by
//!      `hnab`, so `b ≤ a`; with `hnab`, `lt_iff.mpr ⟨b≤a, hnab⟩ : b < a`. Then
//!      `Rat.sub_pos_of_lt b a : 0 < a − b`; instantiate the hypothesis at
//!      `e := a − b` giving `a < b + (a − b)`. `Rat.sub_add_cancel b a :
//!      (a−b)+b = a` and `Rat.add_comm b (a−b) : b+(a−b) = (a−b)+b` chain to
//!      `b+(a−b) = a`; `Eq.subst` transports `a < b+(a−b)` to `a < a`, whose
//!      `lt_iff.mp` `.right` applied to `.left` is `False`; `False.elim` closes
//!      `a ≤ b`.
//!
//! 2. `NNReal.ofRat_le_ofRat_rev :
//!      ∀ (a b : Rat) (ha : Rat.le Rat.zero a)(hb : Rat.le Rat.zero b),
//!        NNReal.le (NNReal.ofRat a ha)(NNReal.ofRat b hb) → Rat.le a b`
//!    — the order-reflection. Proof: `NNReal.ofRat a ha` ι-reduces to
//!    `Quot.mk Equiv (CauSeq.const (NNRat.ofRat a ha))`, so the hypothesis
//!    `H : NNReal.le (ofRat a)(ofRat b)` is def-eq to
//!    `CauSeq.le (const a)(const b)`, i.e. `∀ e>0, ∃ N, ∀ n≥N,
//!    NNRat.val (seq (const a) n) < NNRat.val (seq (const b) n) + e`, and each
//!    `NNRat.val (seq (const ·) n)` ι-reduces to the underlying rational. For a
//!    fixed `e>0`, `Exists.elim (H e he)` yields `N` and `hN`; `hN N (Nat.le_refl N)`
//!    is (def-eq) `a < b + e`. So `∀ e>0, a < b+e`; feed to (1) to conclude
//!    `a ≤ b`.
//!
//! Each is a `Declaration::Theorem`, `ProofQuality::Constructive`, with an empty
//! admitted-axiom closure (foundational only — `Classical.em` is the kernel-
//! checked Diaconescu theorem whose closure is foundational). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the reflection rung. Carrier spellings (`NNReal.ofRat`,
/// `NNReal.le`, `Rat.add`, `Rat.sub`) byte-match the consumed Definitions/lemmas.
struct ReflectConsts {
    prop: Expr,
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nnreal: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    u1: Level,
}

impl ReflectConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::sort(Level::zero()),
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_sub: k("Rat.sub"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nnreal: k("NNReal"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nonneg(&self, x: Expr) -> Expr {
        self.le(self.rat_zero.clone(), x)
    }
    fn nn_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    fn of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x, h])
    }

    // ── Prop plumbing ────────────────────────────────────────────────────────
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
    }
    /// `P → False` as a raw `Pi` (the un-δ-unfolded `Not`, matching `Iff.mpr`).
    fn not_pi(&self, parent: &EnvDeclBuilder, p: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let false_ = Expr::const_(Name::from_string("False"), vec![]);
        let (x_id, _) = ch.fresh_local(p.clone());
        ch.finish_child(ch.mk_pi(x_id, BinderInfo::Default, p, false_))
    }
    fn and_(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [p, q, hp, hq],
        )
    }
    fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [p, q, h],
        )
    }
    fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("And.right"), vec![]),
            [p, q, h],
        )
    }
    fn iff_mp(&self, lhs: Expr, rhs: Expr, hiff: Expr, hl: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Iff.mp"), vec![]),
            [lhs, rhs, hiff, hl],
        )
    }
    fn iff_mpr(&self, lhs: Expr, rhs: Expr, hiff: Expr, hr: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Iff.mpr"), vec![]),
            [lhs, rhs, hiff, hr],
        )
    }
    fn lt_iff(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
            [a, b],
        )
    }
    fn false_elim(&self, goal: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [goal, h],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn eq_subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Eq.trans Rat a b c h1 h2 : Eq Rat a c`.
    fn eq_trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// Or.rec case-split into a non-dependent `goal`.
    fn or_elim(
        &self,
        parent: &EnvDeclBuilder,
        p: Expr,
        q: Expr,
        goal: Expr,
        h_or: Expr,
        h_left: Expr,
        h_right: Expr,
    ) -> Expr {
        let or_c = Expr::const_(Name::from_string("Or"), vec![]);
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let or_ty = Expr::apps(or_c, [p.clone(), q.clone()]);
            let (h_id, _) = m.fresh_local(or_ty.clone());
            m.finish_child(m.mk_lam(h_id, BinderInfo::Default, or_ty, goal))
        };
        Expr::apps(or_rec, [p, q, motive, h_left, h_right, h_or])
    }
}

// ─────────────── Rat.le_of_forall_pos_lt_add ────────────────────────────────

// Proof-term + type builders live in a sibling include to keep this file
// under the 500-line convention.
include!("boolean_analysis_kkl_rung4_reflect_build.rs");

impl Environment {
    /// Register `Rat.le_of_forall_pos_lt_add` and `NNReal.ofRat_le_ofRat_rev`
    /// — **RUNG 4** of the KKL finish: the NNReal→Rat order-reflection. See
    /// module docs. Both kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent; no axiom added/removed.
    pub fn register_kkl_nnreal_to_rat_reflection(&mut self) -> Result<(), EnvError> {
        // Rat Archimedean reverse deps.
        self.init_eq()?;
        self.init_rat()?; // Rat.add, Rat.sub, Rat.lt, Rat.le
        self.init_classical()?; // Classical.em + Or + Or.rec
        self.init_and()?; // And / And.intro / And.left / And.right
        self.init_iff()?; // Iff.mp / Iff.mpr
        self.init_true_false()?; // False / False.elim
        self.register_rat_order_proofs()?; // Rat.le_total, Rat.lt_iff_le_not_le
        self.init_rat_field_inst()?; // Rat.add_comm (live quotient proof)
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.sub_pos_of_lt, Rat.sub_add_cancel

        let c = ReflectConsts::new();
        let arch_name = Name::from_string("Rat.le_of_forall_pos_lt_add");
        if self.get_const(&arch_name).is_none() {
            self.add_decl(Declaration::Theorem {
                name: arch_name,
                level_params: vec![],
                type_: forall_pos_lt_add_type(&c),
                value: forall_pos_lt_add_value(&c),
            })?;
        }

        // Reflection deps (NNReal.le carrier + ofRat).
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.ofRat, CauSeq.const, NNRat.*
        self.init_exists()?; // Exists.elim

        let reflect_name = Name::from_string("NNReal.ofRat_le_ofRat_rev");
        if self.get_const(&reflect_name).is_none() {
            self.add_decl(Declaration::Theorem {
                name: reflect_name,
                level_params: vec![],
                type_: reflect_type(&c),
                value: reflect_value(&c),
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["Rat.le_of_forall_pos_lt_add", "NNReal.ofRat_le_ofRat_rev"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_kkl_nnreal_to_rat_reflection()
            .expect("register_kkl_nnreal_to_rat_reflection");
        env
    }

    #[test]
    fn test_reflection_theorems_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} proof must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_reflection_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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
    }

    #[test]
    fn test_reflection_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_nnreal_to_rat_reflection().expect("first");
        env.register_kkl_nnreal_to_rat_reflection()
            .expect("idempotent");
    }
}
