// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.add_right_cancel : ∀ n m k : Nat, Eq (Nat.add n m) (Nat.add k m) → Eq n k`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof term is
//! built by induction on the cancelled (second) argument `m` via `Nat.rec.{0}`,
//! using constructor injectivity `Nat.succ_inj` in the step case.
//!
//! # Proof sketch
//!
//! `Nat.add` recurses on its SECOND argument:
//! `Nat.add x Nat.zero ≡ x` and `Nat.add x (Nat.succ j) ≡ Nat.succ (Nat.add x j)`.
//!
//! Fix `n k : Nat` and induct on `m` with the implication-valued motive
//! ```text
//! motive t := Eq (Nat.add n t) (Nat.add k t) → Eq n k
//! ```
//!
//! **Base case** `motive Nat.zero`. By iota, `Nat.add n Nat.zero ≡ n` and
//! `Nat.add k Nat.zero ≡ k`, so `motive Nat.zero` defn-equals
//! `Eq n k → Eq n k`. The base witness is therefore the identity
//! `λ (h : Eq n k) => h`.
//!
//! **Step case** at `Nat.succ j`, given
//! `ih : Eq (Nat.add n j) (Nat.add k j) → Eq n k`. The hypothesis
//! `h : Eq (Nat.add n (Nat.succ j)) (Nat.add k (Nat.succ j))` is, by iota,
//! defn-equal to `Eq (Nat.succ (Nat.add n j)) (Nat.succ (Nat.add k j))`.
//! Applying `Nat.succ_inj (Nat.add n j) (Nat.add k j) h` yields
//! `Eq (Nat.add n j) (Nat.add k j)`, which `ih` consumes to produce `Eq n k`.
//!
//! ```text
//! theorem Nat.add_right_cancel (n m k : Nat) :
//!     Eq (Nat.add n m) (Nat.add k m) → Eq n k :=
//!   @Nat.rec.{0}
//!     (fun t => Eq (Nat.add n t) (Nat.add k t) → Eq n k)        -- motive
//!     (fun h => h)                                              -- base
//!     (fun (j : Nat) (ih : ...) (h : ...) =>
//!        ih (Nat.succ_inj (Nat.add n j) (Nat.add k j) h))       -- step
//!     m
//! ```
//!
//! Note the registered signature orders binders `n m k`, with the cancelled
//! variable `m` in the middle; the recursion runs on `m`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Nat`, `Nat.add`, `Nat.succ`, `Nat.rec`, and
//! `Nat.succ_inj`. `Nat.succ_inj` is itself a constructive
//! `Declaration::Theorem` (built from `Nat.noConfusion`), so
//! `env.axiom_deps("Nat.add_right_cancel")` is empty and
//! `env.proof_quality("Nat.add_right_cancel") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (cancellation-law demotion). Sibling helper:
//! `algebra_nat_succ_inj_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatAddRightCancelConsts {
    nat_type: Expr,
    nat_add: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    succ_inj: Expr,
}

impl NatAddRightCancelConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive (implication of equalities).
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1]),
            succ_inj: Expr::const_(Name::from_string("Nat.succ_inj"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }
}

/// Build `∀ n m k : Nat, Eq (Nat.add n m) (Nat.add k m) → Eq n k`.
fn build_type(c: &NatAddRightCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let hyp = c.eq_nat(c.add(n.clone(), m.clone()), c.add(k.clone(), m.clone()));
    let concl = c.eq_nat(n.clone(), k.clone());
    let body = {
        let (h_id, _h) = b.fresh_local(hyp.clone());
        b.mk_pi(h_id, BinderInfo::Default, hyp, concl)
    };
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

/// Motive: `λ (t : Nat) => Eq (Nat.add n t) (Nat.add k t) → Eq n k`.
fn build_motive(
    c: &NatAddRightCancelConsts,
    parent: &EnvDeclBuilder,
    vn: &Expr,
    vk: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let hyp = c.eq_nat(c.add(vn.clone(), t.clone()), c.add(vk.clone(), t.clone()));
    let concl = c.eq_nat(vn.clone(), vk.clone());
    let imp = {
        let (h_id, _h) = mb.fresh_local(hyp.clone());
        mb.mk_pi(h_id, BinderInfo::Default, hyp, concl)
    };
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), imp);
    mb.finish_child(lam)
}

/// Base case: `λ (h : Eq n k) => h`.
///
/// `motive Nat.zero` reduces to `Eq n k → Eq n k` (iota: `Nat.add x zero ≡ x`),
/// so the identity inhabits it.
fn build_base(c: &NatAddRightCancelConsts, parent: &EnvDeclBuilder, vn: &Expr, vk: &Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let eq_nk = c.eq_nat(vn.clone(), vk.clone());
    let (h_id, h) = bb.fresh_local(eq_nk.clone());
    let lam = bb.mk_lam(h_id, BinderInfo::Default, eq_nk, h);
    bb.finish_child(lam)
}

/// Step case:
/// `λ (j : Nat) (ih : motive j) (h : motive-hyp (succ j)) =>
///     ih (Nat.succ_inj (Nat.add n j) (Nat.add k j) h)`.
///
/// `h`'s declared type uses `Nat.succ j`, which by iota is defn-equal to
/// `Eq (Nat.succ (Nat.add n j)) (Nat.succ (Nat.add k j))`. `Nat.succ_inj`
/// peels both `succ`s; `ih` discharges the remaining implication.
fn build_step(c: &NatAddRightCancelConsts, parent: &EnvDeclBuilder, vn: &Expr, vk: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = sb.fresh_local(c.nat_type.clone());

    // ih : Eq (Nat.add n j) (Nat.add k j) → Eq n k
    let nj = c.add(vn.clone(), j.clone());
    let kj = c.add(vk.clone(), j.clone());
    let ih_hyp = c.eq_nat(nj.clone(), kj.clone());
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&sb);
        let (hh_id, _hh) = ib.fresh_local(ih_hyp.clone());
        let imp = ib.mk_pi(
            hh_id,
            BinderInfo::Default,
            ih_hyp.clone(),
            c.eq_nat(vn.clone(), vk.clone()),
        );
        ib.finish_child(imp)
    };
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());

    // h : Eq (Nat.add n (Nat.succ j)) (Nat.add k (Nat.succ j))
    let succ_j = Expr::app(c.nat_succ.clone(), j.clone());
    let h_type = c.eq_nat(c.add(vn.clone(), succ_j.clone()), c.add(vk.clone(), succ_j));
    let (h_id, h) = sb.fresh_local(h_type.clone());

    // Nat.succ_inj (Nat.add n j) (Nat.add k j) h
    //   : Eq (Nat.add n j) (Nat.add k j)
    // (h's declared type iota-reduces to Eq (succ (add n j)) (succ (add k j)),
    //  which is exactly the input Nat.succ_inj expects.)
    let inner = Expr::apps(c.succ_inj.clone(), [nj, kj, h]);
    let body = Expr::app(ih, inner);

    let lam_h = sb.mk_lam(h_id, BinderInfo::Default, h_type, body);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_h);
    let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_j)
}

/// Body: `λ (n m k : Nat) => @Nat.rec.{0} motive base step m`.
fn build_value(c: &NatAddRightCancelConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());
    let (m_id, m) = vb.fresh_local(c.nat_type.clone());
    let (k_id, k) = vb.fresh_local(c.nat_type.clone());
    let motive = build_motive(c, &vb, &n, &k);
    let base = build_base(c, &vb, &n, &k);
    let step = build_step(c, &vb, &n, &k);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, m]);
    let val = vb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val = vb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Nat.add_right_cancel` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`.
    /// REQUIRES: `Nat.succ_inj` is registered as a constructive
    ///           `Declaration::Theorem` (see `register_nat_succ_inj_proof`).
    /// ENSURES: On success, `Nat.add_right_cancel` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.add_right_cancel` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_add_right_cancel_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_right_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_succ_inj_proof()?;

        let c = NatAddRightCancelConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on the
        // cancelled (second) argument `m` via `Nat.rec.{0}` with an
        // implication-valued motive. Base case is the identity `λ h => h`
        // (motive at Nat.zero iota-reduces to `Eq n k → Eq n k`). Step case at
        // `Nat.succ j` applies `Nat.succ_inj (Nat.add n j) (Nat.add k j) h`
        // (the hypothesis iota-reduces to an equality of `succ`s) and feeds the
        // result to the induction hypothesis. No `sorry`, no self-reference, no
        // domain-axiom dependency (`Nat.succ_inj` is itself constructive,
        // built from `Nat.noConfusion`). Replaces the prior `Declaration::Axiom`
        // in `data_types_nat_lemmas.rs::init_nat_arith_lemmas`.
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

    /// Kernel accepts the `Nat.rec` + `Nat.succ_inj` proof term; registered as a
    /// Theorem (not Axiom), idempotently.
    #[test]
    fn test_nat_add_right_cancel_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_add_right_cancel_proof()
            .expect("first registration");
        env.register_nat_add_right_cancel_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.add_right_cancel"))
            .expect("Nat.add_right_cancel should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Nat.add_right_cancel"),
                vec![],
            ))
            .expect("Nat.add_right_cancel should type-check");
    }

    /// After peeling three λ binders (n, m, k), the proof root is `@Nat.rec.{0}`
    /// — guards against an `Eq.refl` / axiom-reference masquerade (the law is
    /// an implication that cannot reduce without induction on `m`).
    #[test]
    fn test_nat_add_right_cancel_proof_uses_nat_rec() {
        let mut env = Environment::new();
        env.register_nat_add_right_cancel_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_right_cancel"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..3 {
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
                "Nat.rec",
                "Nat.add_right_cancel proof root must be Nat.rec"
            ),
            k => panic!("expected Const(Nat.rec, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive). `Nat.succ_inj` is constructive
    /// (built from `Nat.noConfusion`), so the cancellation law inherits empty
    /// domain-axiom deps.
    #[test]
    fn test_nat_add_right_cancel_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_add_right_cancel_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.add_right_cancel"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.add_right_cancel must have empty axiom closure, got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.add_right_cancel"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
