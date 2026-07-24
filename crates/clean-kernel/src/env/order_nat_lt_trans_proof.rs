// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.lt_trans` from `Nat.le.rec`.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Nat.lt_trans`
//! (see `order.rs::init_nat_lt_trans`) with a `Declaration::Theorem` whose
//! body is a genuine kernel-checked proof term built by induction on the
//! second hypothesis via `Nat.le.rec`.
//!
//! # Proof sketch
//!
//! `Nat.lt` is a reducible `Definition` `fun n m => Nat.le (Nat.succ n) m`,
//! and `instLTNat` / `instLENat` are reducible. Hence, up to definitional
//! equality:
//!
//! - `hab : a < b   ≡  Nat.le (Nat.succ a) b`
//! - `hbc : b < c   ≡  Nat.le (Nat.succ b) c`
//! - goal `a < c    ≡  Nat.le (Nat.succ a) c`
//!
//! ```text
//! theorem Nat.lt_trans (a b c : Nat) (hab : a < b) (hbc : b < c) : a < c :=
//!   @Nat.le.rec (Nat.succ b) (fun k _ => Nat.le (Nat.succ a) k)
//!     (Nat.le.step hab)                       -- refl minor
//!     (fun {m} _ ih => Nat.le.step ih)         -- step minor
//!     c hbc
//! ```
//!
//! Recursion runs on `hbc` at `Nat.le` parameter `Nat.succ b`:
//! - **refl minor** proves the motive at index `Nat.succ b`, i.e.
//!   `Nat.le (Nat.succ a) (Nat.succ b)`. From `hab : Nat.le (Nat.succ a) b`,
//!   `@Nat.le.step (Nat.succ a) b hab` has exactly that type.
//! - **step minor** at index `Nat.succ m`, given `ih : Nat.le (Nat.succ a) m`,
//!   produces `@Nat.le.step (Nat.succ a) m ih : Nat.le (Nat.succ a) (Nat.succ m)`.
//!
//! The result `Nat.le (Nat.succ a) c` is definitionally equal to the stated
//! typeclass goal `LT.lt @Nat instLTNat a c` (same defeq used throughout
//! `order.rs` and by `nat_top_level_ordering_proof.rs`).
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.succ`, `Nat.le`, `Nat.le.rec`,
//! `Nat.le.step`, `LT.lt`, `instLTNat`, `LE.le`, `instLENat`. None are
//! `Declaration::Axiom` — `Nat.le.rec` is auto-generated kernel machinery and
//! the `inst*` / projection consts are reducible Definitions. Therefore
//! `env.axiom_deps("Nat.lt_trans")` is empty and
//! `env.proof_quality("Nat.lt_trans") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (kernel-order-soundness). Sibling: `order_nat_le_trans_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::order::nat_lt_tc;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// FVar handles for the five outer binders of `Nat.lt_trans`.
struct OuterBinders {
    a_id: crate::expr::FVarId,
    bv_id: crate::expr::FVarId,
    c_id: crate::expr::FVarId,
    hab_id: crate::expr::FVarId,
    hbc_id: crate::expr::FVarId,
    a: Expr,
    bv: Expr,
    c: Expr,
    hab: Expr,
    hbc: Expr,
    hab_type: Expr,
    hbc_type: Expr,
}

fn fresh_outer_binders(b: &mut EnvDeclBuilder, nat_const: &Expr) -> OuterBinders {
    let (a_id, a) = b.fresh_local(nat_const.clone());
    let (bv_id, bv) = b.fresh_local(nat_const.clone());
    let (c_id, c) = b.fresh_local(nat_const.clone());
    let hab_type = nat_lt_tc(a.clone(), bv.clone());
    let (hab_id, hab) = b.fresh_local(hab_type.clone());
    let hbc_type = nat_lt_tc(bv.clone(), c.clone());
    let (hbc_id, hbc) = b.fresh_local(hbc_type.clone());
    OuterBinders {
        a_id,
        bv_id,
        c_id,
        hab_id,
        hbc_id,
        a,
        bv,
        c,
        hab,
        hbc,
        hab_type,
        hbc_type,
    }
}

/// Build the theorem type:
///   `∀ a b c : Nat, a < b → b < c → a < c` (typeclass `LT.lt` form).
fn build_trans_type(b: &mut EnvDeclBuilder, nat_const: &Expr, ob: &OuterBinders) -> Expr {
    let ty_body = nat_lt_tc(ob.a.clone(), ob.c.clone());
    let e = b.mk_pi(ob.hbc_id, BinderInfo::Default, ob.hbc_type.clone(), ty_body);
    let e = b.mk_pi(ob.hab_id, BinderInfo::Default, ob.hab_type.clone(), e);
    let e = b.mk_pi(ob.c_id, BinderInfo::Default, nat_const.clone(), e);
    let e = b.mk_pi(ob.bv_id, BinderInfo::Default, nat_const.clone(), e);
    b.mk_pi(ob.a_id, BinderInfo::Default, nat_const.clone(), e)
}

/// Build the motive: `fun (k : Nat) (_ : Nat.le (Nat.succ b) k) => Nat.le (Nat.succ a) k`.
///
/// Both the major's parameter and the conclusion are in the bare `Nat.le`
/// form (which `Nat.lt` reduces to); the kernel matches them against the
/// typeclass goal up to definitional equality.
fn build_motive(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_succ: &Expr,
    nat_le_raw: &Expr,
    ob: &OuterBinders,
) -> Expr {
    let succ_a = Expr::app(nat_succ.clone(), ob.a.clone());
    let succ_b = Expr::app(nat_succ.clone(), ob.bv.clone());
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = mb.fresh_local(nat_const.clone());
    let nat_le_sb_k = Expr::apps(nat_le_raw.clone(), [succ_b, k.clone()]);
    let (h_id, _h) = mb.fresh_local(nat_le_sb_k.clone());
    let body = Expr::apps(nat_le_raw.clone(), [succ_a, k.clone()]);
    let lam1 = mb.mk_lam(h_id, BinderInfo::Default, nat_le_sb_k, body);
    let lam2 = mb.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), lam1);
    mb.finish_child(lam2)
}

/// Build the refl minor: `@Nat.le.step (Nat.succ a) b hab`.
///
/// The motive at index `Nat.succ b` (the `Nat.le.refl` index) is
/// `Nat.le (Nat.succ a) (Nat.succ b)`. `Nat.le.step` lifts
/// `hab : Nat.le (Nat.succ a) b` to exactly that.
fn build_minor_refl(nat_succ: &Expr, nat_le_step: &Expr, ob: &OuterBinders) -> Expr {
    let succ_a = Expr::app(nat_succ.clone(), ob.a.clone());
    Expr::apps(nat_le_step.clone(), [succ_a, ob.bv.clone(), ob.hab.clone()])
}

/// Build the step minor:
///   `fun {m : Nat} (_ : Nat.le (Nat.succ b) m) (ih : Nat.le (Nat.succ a) m)
///        => @Nat.le.step (Nat.succ a) m ih`.
fn build_minor_step(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_succ: &Expr,
    nat_le_raw: &Expr,
    nat_le_step: &Expr,
    ob: &OuterBinders,
) -> Expr {
    let succ_a = Expr::app(nat_succ.clone(), ob.a.clone());
    let succ_b = Expr::app(nat_succ.clone(), ob.bv.clone());
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = sb.fresh_local(nat_const.clone());
    let nat_le_sb_m = Expr::apps(nat_le_raw.clone(), [succ_b, m.clone()]);
    let (h_id, _h) = sb.fresh_local(nat_le_sb_m.clone());
    let ih_type = Expr::apps(nat_le_raw.clone(), [succ_a.clone(), m.clone()]);
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let step_app = Expr::apps(nat_le_step.clone(), [succ_a, m.clone(), ih]);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
    let lam_h = sb.mk_lam(h_id, BinderInfo::Default, nat_le_sb_m, lam_ih);
    let lam_m = sb.mk_lam(m_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
    sb.finish_child(lam_m)
}

/// Close `body` with the five outer lambdas `λ a b c hab hbc => body`.
fn close_outer_lambdas(
    b: &mut EnvDeclBuilder,
    nat_const: &Expr,
    ob: &OuterBinders,
    body: Expr,
) -> Expr {
    let e = b.mk_lam(ob.hbc_id, BinderInfo::Default, ob.hbc_type.clone(), body);
    let e = b.mk_lam(ob.hab_id, BinderInfo::Default, ob.hab_type.clone(), e);
    let e = b.mk_lam(ob.c_id, BinderInfo::Default, nat_const.clone(), e);
    let e = b.mk_lam(ob.bv_id, BinderInfo::Default, nat_const.clone(), e);
    b.mk_lam(ob.a_id, BinderInfo::Default, nat_const.clone(), e)
}

impl Environment {
    /// Register `Nat.lt_trans` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body recurses on the second hypothesis `hbc : b < c` via
    /// `Nat.le.rec` at parameter `Nat.succ b`, with motive
    /// `fun k _ => Nat.le (Nat.succ a) k`. The refl case lifts `hab : a < b`
    /// (i.e. `Nat.le (Nat.succ a) b`) by `Nat.le.step`; the step case applies
    /// `Nat.le.step` to the inductive hypothesis.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_le()` / `self.init_lt()` register `Nat.le`, its
    ///           recursor, and the reducible `Nat.lt` / `instLTNat` /
    ///           `instLENat`.
    /// ENSURES: On success, `self` contains a `Declaration::Theorem` named
    ///          `Nat.lt_trans` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.lt_trans` is already registered with any
    ///          declaration kind, this call returns `Ok(())` unchanged.
    pub(crate) fn register_nat_lt_trans_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Ensure Nat.le / Nat.lt and the recursor are present.
        self.init_le()?;
        self.init_lt()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_raw = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let ob = fresh_outer_binders(&mut b, &nat_const);

        let type_raw = build_trans_type(&mut b, &nat_const, &ob);
        let type_ = b.finish(type_raw);

        let motive = build_motive(&b, &nat_const, &nat_succ, &nat_le_raw, &ob);
        let minor_refl = build_minor_refl(&nat_succ, &nat_le_step, &ob);
        let minor_step =
            build_minor_step(&b, &nat_const, &nat_succ, &nat_le_raw, &nat_le_step, &ob);

        // @Nat.le.rec (Nat.succ b) motive minor_refl minor_step c hbc
        let succ_b = Expr::app(nat_succ.clone(), ob.bv.clone());
        let rec_app = Expr::apps(
            nat_le_rec,
            [
                succ_b,         // param n = Nat.succ b
                motive,         // motive
                minor_refl,     // refl minor = Nat.le.step hab
                minor_step,     // step minor
                ob.c.clone(),   // index m = c
                ob.hbc.clone(), // major (hbc : Nat.le (Nat.succ b) c by reducibility)
            ],
        );

        // SOUNDNESS (#3604 kernel-order-soundness): Real kernel-checked proof
        // term. Induction on the second hypothesis via `Nat.le.rec` at
        // parameter `Nat.succ b` with motive `fun k _ => Nat.le (Nat.succ a) k`.
        // Refl minor `@Nat.le.step (Nat.succ a) b hab` proves
        // `Nat.le (Nat.succ a) (Nat.succ b)`; step minor applies `Nat.le.step`
        // to the IH. The bare `Nat.le (Nat.succ a) c` result is defeq to the
        // typeclass goal `LT.lt @Nat instLTNat a c` via reducibility of
        // `Nat.lt` / `instLTNat` / `instLENat`. No `sorry`, no self-reference,
        // no domain-axiom dependency (`Nat.le.rec` is kernel machinery).
        // Replaces the prior `Declaration::Axiom` in `order.rs::init_nat_lt_trans`.
        let value_raw = close_outer_lambdas(&mut b, &nat_const, &ob, rec_app);
        let value = b.finish(value_raw);

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

    /// Kernel accepts the `Nat.le.rec` proof term; registered as a Theorem
    /// (not Axiom), idempotently.
    #[test]
    fn test_nat_lt_trans_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_lt_trans_proof()
            .expect("first registration");
        env.register_nat_lt_trans_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.lt_trans"))
            .expect("Nat.lt_trans should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.lt_trans"), vec![]))
            .expect("Nat.lt_trans should type-check");
    }

    /// After peeling five λ binders (a, b, c, hab, hbc), the proof root is
    /// `@Nat.le.rec` — guards against an axiom-reference masquerade (the law
    /// is an implication that cannot reduce without induction).
    #[test]
    fn test_nat_lt_trans_proof_uses_nat_le_rec() {
        let mut env = Environment::new();
        env.register_nat_lt_trans_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.lt_trans"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..5 {
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
                "Nat.lt_trans proof root must be Nat.le.rec"
            ),
            k => panic!("expected Const(Nat.le.rec, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive).
    #[test]
    fn test_nat_lt_trans_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_lt_trans_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.lt_trans"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.lt_trans must have empty axiom closure, got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.lt_trans"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
