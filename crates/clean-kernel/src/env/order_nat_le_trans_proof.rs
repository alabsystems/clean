// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.le_trans` from `Nat.le.rec`.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Nat.le_trans`
//! (see `order.rs::init_nat_preorder` / `init_nat_le_trans`) with a
//! `Declaration::Theorem` whose body is a genuine kernel-checked proof term
//! built by induction on the second hypothesis via `Nat.le.rec`.
//!
//! # Proof sketch
//!
//! ```text
//! theorem Nat.le_trans (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
//!   @Nat.le.rec b (fun k _ => a ≤ k) hab
//!     (fun {m} _ ih => Nat.le.step ih) c hbc
//! ```
//!
//! The theorem's stated type uses `LE.le Nat instLENat` (typeclass form),
//! while `Nat.le.rec`'s motive operates on the bare `Nat.le` inductive.
//! The two are definitionally equal because `instLENat` is a reducible
//! Definition of `LE.mk Nat Nat.le`, so the kernel accepts `Nat.le a c`
//! where `LE.le Nat instLENat a c` is expected (and vice versa for the
//! incoming hypotheses). This is the same defeq relied on by the rest of
//! `order.rs` (see the `nat_le_tc` helper).
//!
//! # Axiom closure
//!
//! The proof term mentions only: `Nat`, `Nat.le`, `Nat.le.rec`, `Nat.le.step`,
//! `LE.le`, `instLENat`. None of these are `Declaration::Axiom` — `Nat.le.rec`
//! is auto-generated kernel machinery and `instLENat` / `LE.le` are reducible
//! Definitions. Therefore `env.axiom_deps("Nat.le_trans")` is empty and
//! `env.proof_quality("Nat.le_trans") == ProofQuality::Constructive`.
//!
//! Tracks issue #3552.

use super::decl_builder::EnvDeclBuilder;
use super::order::nat_le_tc;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// FVar handles for the five outer binders of `Nat.le_trans`.
///
/// Carries both the `FVarId` (needed by `mk_pi` / `mk_lam` when closing a
/// binder) and the `Expr` reference (needed when building subterms).
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
    let hab_type = nat_le_tc(a.clone(), bv.clone());
    let (hab_id, hab) = b.fresh_local(hab_type.clone());
    let hbc_type = nat_le_tc(bv.clone(), c.clone());
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
///   `∀ a b c : Nat, LE.le Nat instLENat a b → LE.le Nat instLENat b c → LE.le Nat instLENat a c`
fn build_trans_type(b: &mut EnvDeclBuilder, nat_const: &Expr, ob: &OuterBinders) -> Expr {
    let ty_body = nat_le_tc(ob.a.clone(), ob.c.clone());
    let e = b.mk_pi(ob.hbc_id, BinderInfo::Default, ob.hbc_type.clone(), ty_body);
    let e = b.mk_pi(ob.hab_id, BinderInfo::Default, ob.hab_type.clone(), e);
    let e = b.mk_pi(ob.c_id, BinderInfo::Implicit, nat_const.clone(), e);
    let e = b.mk_pi(ob.bv_id, BinderInfo::Implicit, nat_const.clone(), e);
    b.mk_pi(ob.a_id, BinderInfo::Implicit, nat_const.clone(), e)
}

/// Build the motive: `fun (k : Nat) (_ : Nat.le b k) => LE.le Nat instLENat a k`.
///
/// `a` and `b` are outer fvars captured from the parent builder. Using a
/// child builder keeps FVar ID ranges disjoint (#1544).
fn build_motive(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_le_raw: &Expr,
    ob: &OuterBinders,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = mb.fresh_local(nat_const.clone());
    let nat_le_b_k = Expr::app(Expr::app(nat_le_raw.clone(), ob.bv.clone()), k.clone());
    let (h_id, _h) = mb.fresh_local(nat_le_b_k.clone());
    let body = nat_le_tc(ob.a.clone(), k.clone());
    let lam1 = mb.mk_lam(h_id, BinderInfo::Default, nat_le_b_k, body);
    let lam2 = mb.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), lam1);
    mb.finish_child(lam2)
}

/// Build the step case:
///   `fun {m : Nat} (_ : Nat.le b m) (ih : LE.le Nat instLENat a m) => @Nat.le.step a m ih`.
///
/// `Nat.le.step`'s implicit `{n}` is the Nat.le parameter (= `a` here); its
/// implicit `{m}` is the index. We apply explicitly via `@`-form to avoid
/// implicit-argument elaboration concerns in the kernel.
fn build_minor_step(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_le_raw: &Expr,
    nat_le_step: &Expr,
    ob: &OuterBinders,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = sb.fresh_local(nat_const.clone());
    let nat_le_b_m = Expr::app(Expr::app(nat_le_raw.clone(), ob.bv.clone()), m.clone());
    let (h_id, _h) = sb.fresh_local(nat_le_b_m.clone());
    let ih_type = nat_le_tc(ob.a.clone(), m.clone());
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let step_app = Expr::apps(nat_le_step.clone(), [ob.a.clone(), m.clone(), ih]);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
    let lam_h = sb.mk_lam(h_id, BinderInfo::Default, nat_le_b_m, lam_ih);
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
    /// Register `Nat.le_trans` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body recurses on the second hypothesis `hbc : b ≤ c` via
    /// `Nat.le.rec`, with motive `fun k _ => a ≤ k`. The refl case returns
    /// `hab : a ≤ b`; the step case applies `Nat.le.step` to the inductive
    /// hypothesis.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_le()` has been (or will be) called before this.
    /// ENSURES: On success, `self` contains a `Declaration::Theorem` named
    ///          `Nat.le_trans` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.le_trans` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_le_trans_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Ensure Nat.le and its recursor are present.
        self.init_le()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_le_raw = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let ob = fresh_outer_binders(&mut b, &nat_const);

        let type_raw = build_trans_type(&mut b, &nat_const, &ob);
        let type_ = b.finish(type_raw);

        let motive = build_motive(&b, &nat_const, &nat_le_raw, &ob);
        let minor_step = build_minor_step(&b, &nat_const, &nat_le_raw, &nat_le_step, &ob);

        // @Nat.le.rec b motive hab minor_step c hbc
        let rec_app = Expr::apps(
            nat_le_rec,
            [
                ob.bv.clone(),  // param n
                motive,         // motive
                ob.hab.clone(), // minor_refl = hab
                minor_step,     // minor_step
                ob.c.clone(),   // index m
                ob.hbc.clone(), // major
            ],
        );

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
