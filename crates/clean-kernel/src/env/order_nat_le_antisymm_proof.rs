// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.le_antisymm` from `Nat.le.rec`.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Nat.le_antisymm`
//! (see `order.rs::init_nat_le_antisymm` / `init_nat_partial_order`) with a
//! `Declaration::Theorem` whose body is a genuine kernel-checked proof term
//! built by induction on the first hypothesis `h1 : a ≤ b` via `Nat.le.rec`.
//!
//! # Proof sketch
//!
//! ```text
//! theorem Nat.le_antisymm (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
//!   @Nat.le.rec a
//!     (fun (x : Nat) (_ : Nat.le a x) => Nat.le x a → Eq a x)   -- motive
//!     (fun (_ : Nat.le a a) => Eq.refl a)                       -- refl case
//!     (fun {m : Nat} (hm : Nat.le a m)
//!          (_ih : Nat.le m a → Eq a m) (hsa : Nat.le (succ m) a) =>
//!        False.elim (Eq a (succ m))
//!          (Nat.lt_irrefl m (Nat.le_trans (succ m) a m hsa hm)))  -- step case
//!     b h1 h2
//! ```
//!
//! The recursor runs on the major premise `h1 : a ≤ b` with the
//! implication-valued motive `P x := (x ≤ a → a = x)`.
//!
//! - **refl case** (`x := a`): the goal `a ≤ a → a = a` is discharged by the
//!   constant function returning `Eq.refl a`.
//! - **step case** (`x := succ m`, with `hm : a ≤ m` and an unused induction
//!   hypothesis): given `hsa : succ m ≤ a`, transitivity with `hm : a ≤ m`
//!   yields `succ m ≤ m`, i.e. `Nat.lt m m`. `Nat.lt_irrefl m` turns that into
//!   `False`, and `False.elim` produces the (vacuous) goal `a = succ m`.
//!
//! The stated type uses `LE.le Nat instLENat` (typeclass form), while
//! `Nat.le.rec`'s motive operates on the bare `Nat.le` inductive. The two are
//! definitionally equal because `instLENat` is a reducible definition of
//! `LE.mk Nat Nat.le`; this is the same defeq relied on throughout `order.rs`
//! (see the `nat_le_tc` helper) and by `order_nat_le_trans_proof.rs`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.le`, `Nat.le.rec`, `Nat.succ`,
//! `LE.le`, `instLENat`, `Eq`, `Eq.refl`, `False`, `False.elim`,
//! `Nat.le_trans`, and `Nat.lt_irrefl`. None of these are `Declaration::Axiom`:
//! `Nat.le.rec` is auto-generated kernel machinery, `instLENat` / `LE.le` are
//! reducible definitions, and `Nat.le_trans` / `Nat.lt_irrefl` are themselves
//! constructive theorems (see `order_nat_le_trans_proof.rs` and
//! `nat_lt_irrefl_proof.rs`). Therefore `env.axiom_deps("Nat.le_antisymm")` is
//! empty and `env.proof_quality("Nat.le_antisymm") == ProofQuality::Constructive`.
//!
//! Tracks #3599 (Nat-order axiom demotion).

use super::decl_builder::EnvDeclBuilder;
use super::order::nat_le_tc;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatLeAntisymmConsts {
    nat_type: Expr,
    nat_succ: Expr,
    nat_le_raw: Expr,
    nat_le_rec: Expr,
    nat_le_trans: Expr,
    nat_lt_irrefl: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    false_const: Expr,
    false_elim: Expr,
}

impl NatLeAntisymmConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_le_raw: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            nat_le_trans: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            nat_lt_irrefl: Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
            #[cfg(test)]
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            // False.elim.{0} — the eliminated goal `Eq a (succ m)` lives in Prop.
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        }
    }

    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }

    fn le_raw(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.nat_le_raw.clone(), [lhs, rhs])
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }
}

/// Build `∀ a b : Nat, LE.le a b → LE.le b a → Eq a b` (typeclass form).
fn build_type(c: &NatLeAntisymmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let h1_type = nat_le_tc(a.clone(), bv.clone());
    let (h1_id, _h1) = b.fresh_local(h1_type.clone());
    let h2_type = nat_le_tc(bv.clone(), a.clone());
    let (h2_id, _h2) = b.fresh_local(h2_type.clone());
    let concl = c.eq_nat(a.clone(), bv.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

/// Motive: `fun (x : Nat) (_ : Nat.le a x) => Nat.le x a → Eq a x`.
fn build_motive(c: &NatLeAntisymmConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.nat_type.clone());
    let le_a_x = c.le_raw(va.clone(), x.clone());
    let (hx_id, _hx) = mb.fresh_local(le_a_x.clone());
    let le_x_a = c.le_raw(x.clone(), va.clone());
    let imp = {
        let (h_id, _h) = mb.fresh_local(le_x_a.clone());
        mb.mk_pi(
            h_id,
            BinderInfo::Default,
            le_x_a,
            c.eq_nat(va.clone(), x.clone()),
        )
    };
    let lam_h = mb.mk_lam(hx_id, BinderInfo::Default, le_a_x, imp);
    let lam_x = mb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), lam_h);
    mb.finish_child(lam_x)
}

/// Refl case: `fun (_ : Nat.le a a) => Eq.refl a`.
///
/// `motive a (Nat.le.refl a)` reduces to `Nat.le a a → Eq a a`, so the
/// constant function returning the reflexivity proof inhabits it.
fn build_refl_case(c: &NatLeAntisymmConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut rb = EnvDeclBuilder::child_of(parent);
    let le_a_a = c.le_raw(va.clone(), va.clone());
    let (h_id, _h) = rb.fresh_local(le_a_a.clone());
    let refl = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), va.clone()]);
    let lam = rb.mk_lam(h_id, BinderInfo::Default, le_a_a, refl);
    rb.finish_child(lam)
}

/// Step case:
/// `fun {m : Nat} (hm : Nat.le a m) (_ih : Nat.le m a → Eq a m)
///      (hsa : Nat.le (succ m) a) =>
///    False.elim (Eq a (succ m))
///      (Nat.lt_irrefl m (Nat.le_trans (succ m) a m hsa hm))`.
fn build_step_case(c: &NatLeAntisymmConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = sb.fresh_local(c.nat_type.clone());

    // hm : Nat.le a m — the recursor's index hypothesis at `m`.
    let le_a_m = c.le_raw(va.clone(), m.clone());
    let (hm_id, hm) = sb.fresh_local(le_a_m.clone());

    // ih : Nat.le m a → Eq a m — induction hypothesis (unused; the step is
    // discharged by contradiction rather than recursion).
    let le_m_a = c.le_raw(m.clone(), va.clone());
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&sb);
        let (h_id, _h) = ib.fresh_local(le_m_a.clone());
        let imp = ib.mk_pi(
            h_id,
            BinderInfo::Default,
            le_m_a.clone(),
            c.eq_nat(va.clone(), m.clone()),
        );
        ib.finish_child(imp)
    };
    let (ih_id, _ih) = sb.fresh_local(ih_type.clone());

    // hsa : Nat.le (succ m) a — the hypothesis of the goal `motive (succ m)`.
    let succ_m = c.succ(m.clone());
    let le_sm_a = c.le_raw(succ_m.clone(), va.clone());
    let (hsa_id, hsa) = sb.fresh_local(le_sm_a.clone());

    // Nat.le_trans (succ m) a m hsa hm : succ m ≤ m  (≡ Nat.lt m m).
    let trans_app = Expr::apps(
        c.nat_le_trans.clone(),
        [succ_m.clone(), va.clone(), m.clone(), hsa, hm],
    );
    // Nat.lt_irrefl m (...) : False.
    let absurd = Expr::apps(c.nat_lt_irrefl.clone(), [m.clone(), trans_app]);
    // False.elim (Eq a (succ m)) absurd : Eq a (succ m).
    let goal = c.eq_nat(va.clone(), succ_m);
    let body = Expr::apps(c.false_elim.clone(), [goal, absurd]);

    let lam_hsa = sb.mk_lam(hsa_id, BinderInfo::Default, le_sm_a, body);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_hsa);
    let lam_hm = sb.mk_lam(hm_id, BinderInfo::Default, le_a_m, lam_ih);
    let lam_m = sb.mk_lam(m_id, BinderInfo::Implicit, c.nat_type.clone(), lam_hm);
    sb.finish_child(lam_m)
}

/// Body: `λ (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) =>
///          @Nat.le.rec a motive refl_case step_case b h1 h2`.
fn build_value(c: &NatLeAntisymmConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = vb.fresh_local(c.nat_type.clone());
    let h1_type = nat_le_tc(a.clone(), bv.clone());
    let (h1_id, h1) = vb.fresh_local(h1_type.clone());
    let h2_type = nat_le_tc(bv.clone(), a.clone());
    let (h2_id, h2) = vb.fresh_local(h2_type.clone());

    let motive = build_motive(c, &vb, &a);
    let refl_case = build_refl_case(c, &vb, &a);
    let step_case = build_step_case(c, &vb, &a);

    // @Nat.le.rec a motive refl_case step_case b h1 : (b ≤ a → a = b)
    let rec_app = Expr::apps(
        c.nat_le_rec.clone(),
        [a.clone(), motive, refl_case, step_case, bv.clone(), h1],
    );
    // (...) h2 : a = b
    let body = Expr::app(rec_app, h2);

    let val = vb.mk_lam(h2_id, BinderInfo::Default, h2_type, body);
    let val = vb.mk_lam(h1_id, BinderInfo::Default, h1_type, val);
    let val = vb.mk_lam(bv_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Nat.le_antisymm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body recurses on the first hypothesis `h1 : a ≤ b` via
    /// `Nat.le.rec` with the implication-valued motive `fun x _ => x ≤ a → a = x`.
    /// The refl case returns `Eq.refl a`; the step case derives `succ m ≤ m`
    /// from transitivity and discharges the (impossible) goal via
    /// `Nat.lt_irrefl` + `False.elim`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_le()`, `self.init_lt()`, `self.init_eq()`,
    ///           `self.init_true_false()` provide the supporting symbols.
    /// ENSURES: On success, `self` contains a `Declaration::Theorem` named
    ///          `Nat.le_antisymm` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.le_antisymm` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_le_antisymm_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_antisymm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Supporting symbols and constructive lemmas.
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_true_false()?;
        self.register_nat_le_trans_proof()?;
        self.register_nat_lt_irrefl_theorem()?;

        let c = NatLeAntisymmConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3599). Induction on the
        // first hypothesis `h1 : a ≤ b` via `Nat.le.rec` with motive
        // `fun x _ => x ≤ a → a = x`. Refl case returns `Eq.refl a`; step case
        // at `succ m` transports `succ m ≤ a` and `a ≤ m` through `Nat.le_trans`
        // to `succ m ≤ m ≡ Nat.lt m m`, contradicted by `Nat.lt_irrefl m`, and
        // `False.elim` discharges the goal. No `sorry`, no self-reference, no
        // domain-axiom dependency (`Nat.le_trans`, `Nat.lt_irrefl` are
        // constructive; `Nat.le.rec` is generated kernel machinery). Replaces
        // the prior `Declaration::Axiom` registered in `order.rs`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// Kernel accepts the `Nat.le.rec` proof term; registered as a Theorem (not
    /// Axiom), idempotently.
    #[test]
    fn test_nat_le_antisymm_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_le_antisymm_proof()
            .expect("first registration");
        env.register_nat_le_antisymm_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.le_antisymm"))
            .expect("Nat.le_antisymm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.le_antisymm"), vec![]))
            .expect("Nat.le_antisymm should type-check");
    }

    /// After peeling four λ binders (a, b, h1, h2), the proof root is
    /// `@Nat.le.rec` — guards against an `Eq.refl` / axiom-reference masquerade
    /// (antisymmetry is an implication that cannot reduce without induction).
    #[test]
    fn test_nat_le_antisymm_proof_uses_le_rec() {
        let mut env = Environment::new();
        env.register_nat_le_antisymm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.le_antisymm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..4 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.le.rec",
                "Nat.le_antisymm proof root must be Nat.le.rec"
            ),
            k => panic!("expected Const(Nat.le.rec, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive). `Nat.le_trans` and `Nat.lt_irrefl`
    /// are themselves constructive theorems, so antisymmetry inherits empty
    /// domain-axiom deps.
    #[test]
    fn test_nat_le_antisymm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_le_antisymm_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.le_antisymm"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.le_antisymm must have empty axiom closure, got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.le_antisymm"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
