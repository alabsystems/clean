// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.le_total` by double induction.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Nat.le_total`
//! (see `order.rs::init_nat_linear_order`, whose comment previously read
//! "the actual proof would require a decidability argument or case analysis
//! on Nat") with a `Declaration::Theorem` whose body is a genuine
//! kernel-checked proof term built by induction on the first argument `a`
//! via `Nat.rec`, with a case split on the second argument `b` via
//! `Nat.casesOn` and an `Or.rec` on the induction hypothesis in the
//! successor/successor case.
//!
//! # Proof sketch
//!
//! ```text
//! theorem Nat.le_total (a b : Nat) : Or (Nat.le a b) (Nat.le b a) :=
//!   @Nat.rec (fun s => ∀ y, Or (Nat.le s y) (Nat.le y s))
//!     -- base (a = 0): 0 ≤ y, so the left disjunct holds for every y.
//!     (fun y => Or.inl _ _ (Nat.zero_le y))
//!     -- step (a = succ s): case on y.
//!     (fun s ih y =>
//!       Nat.casesOn (motive := fun w => Or (Nat.le (succ s) w) (Nat.le w (succ s))) y
//!         -- y = 0: 0 ≤ succ s, so the right disjunct holds.
//!         (Or.inr _ _ (Nat.zero_le (succ s)))
//!         -- y = succ j: lift `ih j : Or (s ≤ j) (j ≤ s)` through Nat.succ_le_succ.
//!         (fun j =>
//!           Or.rec
//!             (fun h => Or.inl _ _ (Nat.succ_le_succ s j h))
//!             (fun h => Or.inr _ _ (Nat.succ_le_succ j s h))
//!             (ih j)))
//!     a b
//! ```
//!
//! The theorem's stated type uses the typeclass form `LE.le Nat instLENat`
//! (matching the prior axiom signature so the `LinearOrder Nat` instance and
//! every downstream consumer keep type-checking), while the proof body works
//! on the bare `Nat.le` inductive. The two are definitionally equal because
//! `instLENat` is a reducible `Definition` of `LE.mk Nat Nat.le`; this is the
//! same defeq relied on throughout `order.rs` (see the `nat_le_tc` helper) and
//! by `order_nat_le_trans_proof.rs` / `order_nat_le_antisymm_proof.rs`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.rec`, `Nat.casesOn`, `Nat.succ`,
//! `Nat.le`, `Or`, `Or.inl`, `Or.inr`, `Or.rec`, `Nat.zero_le`, and
//! `Nat.succ_le_succ`. None of these is a `Declaration::Axiom`: `Nat.rec`,
//! `Nat.casesOn`, and `Or.rec` are auto-generated kernel machinery, and
//! `Nat.zero_le` / `Nat.succ_le_succ` are themselves constructive theorems
//! (see `algebra_nat_mul_cancel_proof.rs::register_nat_zero_le` and
//! `nat_top_level_ordering_proof.rs::register_nat_succ_le_succ_theorem`).
//! Therefore `env.axiom_deps("Nat.le_total")` is empty and
//! `env.proof_quality("Nat.le_total") == ProofQuality::Constructive`.
//!
//! Tracks #3599 (Nat-order axiom demotion); unblocks `Int.le_total`.

use super::decl_builder::EnvDeclBuilder;
use super::order::nat_le_tc;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatLeTotalConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    nat_rec: Expr,
    nat_cases_on: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    le_step_ctor: Expr,
    or_const: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    zero_le: Expr,
    succ_le_succ: Expr,
}

impl NatLeTotalConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // `Nat.rec.{0}` / `Nat.casesOn.{0}` — Prop motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_cases_on: Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            le_step_ctor: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            // `Or.rec` eliminating into Prop carries no explicit motive level here.
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            zero_le: Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
            succ_le_succ: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
        }
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    /// `@Nat.le.step n m h : Nat.le n (Nat.succ m)`.
    fn le_step_app(&self, n: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_step_ctor.clone(), [n, m, h])
    }

    /// `Nat.le x y` (raw inductive form).
    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    /// `Or (Nat.le x y) (Nat.le y x)`.
    fn or_disj(&self, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.or_const.clone(),
            [
                self.le_of(x.clone(), y.clone()),
                self.le_of(y.clone(), x.clone()),
            ],
        )
    }

    /// `Nat.zero_le n : Nat.le Nat.zero n`.
    fn zero_le_app(&self, n: Expr) -> Expr {
        Expr::app(self.zero_le.clone(), n)
    }

    /// `Nat.succ_le_succ n m h : Nat.le (succ n) (succ m)`.
    fn succ_le_succ_app(&self, n: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.succ_le_succ.clone(), [n, m, h])
    }
}

/// Build the stated theorem type (typeclass form, matching the prior axiom):
///   `∀ a b : Nat, Or (LE.le Nat instLENat a b) (LE.le Nat instLENat b a)`.
fn build_type(c: &NatLeTotalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bb_id, bb) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(
        c.or_const.clone(),
        [
            nat_le_tc(a.clone(), bb.clone()),
            nat_le_tc(bb.clone(), a.clone()),
        ],
    );
    let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Outer induction motive:
///   `fun (s : Nat) => ∀ (y : Nat), Or (Nat.le s y) (Nat.le y s)`.
fn build_motive(c: &NatLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (s_id, s) = mb.fresh_local(c.nat.clone());
    let inner = {
        let mut yb = EnvDeclBuilder::child_of(&mb);
        let (y_id, y) = yb.fresh_local(c.nat.clone());
        let body = c.or_disj(&s, &y);
        let pi = yb.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), body);
        yb.finish_child(pi)
    };
    let lam = mb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), inner);
    mb.finish_child(lam)
}

/// Base case (`a = 0`):
///   `fun (y : Nat) => Or.inl (Nat.le 0 y) (Nat.le y 0) (Nat.zero_le y)`.
fn build_base(c: &NatLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut zb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = zb.fresh_local(c.nat.clone());
    let le_zero_y = c.le_of(c.zero.clone(), y.clone());
    let le_y_zero = c.le_of(y.clone(), c.zero.clone());
    let body = Expr::apps(
        c.or_inl.clone(),
        [le_zero_y, le_y_zero, c.zero_le_app(y.clone())],
    );
    let lam = zb.mk_lam(y_id, BinderInfo::Default, c.nat.clone(), body);
    zb.finish_child(lam)
}

/// `Nat.casesOn` motive for the inner split on `y`:
///   `fun (w : Nat) => Or (Nat.le (succ s) w) (Nat.le w (succ s))`.
fn build_cases_motive(c: &NatLeTotalConsts, parent: &EnvDeclBuilder, succ_s: &Expr) -> Expr {
    let mut cm = EnvDeclBuilder::child_of(parent);
    let (w_id, w) = cm.fresh_local(c.nat.clone());
    let body = c.or_disj(succ_s, &w);
    let lam = cm.mk_lam(w_id, BinderInfo::Default, c.nat.clone(), body);
    cm.finish_child(lam)
}

/// Inner zero case (`y = 0`): `Or.inr` witnessed by `Nat.zero_le (succ s)`,
/// proving `Or (Nat.le (succ s) 0) (Nat.le 0 (succ s))`.
fn build_inner_zero_case(c: &NatLeTotalConsts, succ_s: &Expr) -> Expr {
    let left = c.le_of(succ_s.clone(), c.zero.clone());
    let right = c.le_of(c.zero.clone(), succ_s.clone());
    Expr::apps(
        c.or_inr.clone(),
        [left, right, c.zero_le_app(succ_s.clone())],
    )
}

/// Inner successor case (`y = succ j`): `fun (j : Nat) => Or.rec ... (ih j)`,
/// lifting `ih j : Or (Nat.le s j) (Nat.le j s)` through `Nat.succ_le_succ`
/// into `Or (Nat.le (succ s) (succ j)) (Nat.le (succ j) (succ s))`.
fn build_inner_succ_case(
    c: &NatLeTotalConsts,
    parent: &EnvDeclBuilder,
    s: &Expr,
    succ_s: &Expr,
    ih: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = cb.fresh_local(c.nat.clone());
    let succ_j = c.succ_of(j.clone());

    let a_prop = c.le_of(s.clone(), j.clone()); // s ≤ j
    let b_prop = c.le_of(j.clone(), s.clone()); // j ≤ s

    let goal_left = c.le_of(succ_s.clone(), succ_j.clone()); // succ s ≤ succ j
    let goal_right = c.le_of(succ_j.clone(), succ_s.clone()); // succ j ≤ succ s
    let goal = Expr::apps(c.or_const.clone(), [goal_left.clone(), goal_right.clone()]);

    // const motive for Or.rec: `fun (_ : Or a_prop b_prop) => goal`.
    let or_motive = {
        let mut om = EnvDeclBuilder::child_of(&cb);
        let or_ab = Expr::apps(c.or_const.clone(), [a_prop.clone(), b_prop.clone()]);
        let (hh_id, _hh) = om.fresh_local(or_ab.clone());
        let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
        om.finish_child(lam)
    };

    // inl case: `fun (h : s ≤ j) => Or.inl _ _ (Nat.succ_le_succ s j h)`.
    let case_inl = {
        let mut ic = EnvDeclBuilder::child_of(&cb);
        let (h_id, h) = ic.fresh_local(a_prop.clone());
        let lifted = c.succ_le_succ_app(s.clone(), j.clone(), h);
        let body = Expr::apps(
            c.or_inl.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = ic.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), body);
        ic.finish_child(lam)
    };

    // inr case: `fun (h : j ≤ s) => Or.inr _ _ (Nat.succ_le_succ j s h)`.
    let case_inr = {
        let mut rc = EnvDeclBuilder::child_of(&cb);
        let (h_id, h) = rc.fresh_local(b_prop.clone());
        let lifted = c.succ_le_succ_app(j.clone(), s.clone(), h);
        let body = Expr::apps(
            c.or_inr.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = rc.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), body);
        rc.finish_child(lam)
    };

    let ih_j = Expr::app(ih.clone(), j.clone());
    let or_rec_app = Expr::apps(
        c.or_rec.clone(),
        [a_prop, b_prop, or_motive, case_inl, case_inr, ih_j],
    );
    let lam_j = cb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), or_rec_app);
    cb.finish_child(lam_j)
}

/// Step case (`a = succ s`):
///   `fun (s : Nat) (ih : ∀ y, Or (s ≤ y) (y ≤ s)) (y : Nat) =>
///      Nat.casesOn (motive := ...) y zero_case succ_case`.
fn build_step(c: &NatLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (s_id, s) = sb.fresh_local(c.nat.clone());

    // ih : ∀ y, Or (Nat.le s y) (Nat.le y s)
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&sb);
        let (y_id, y) = ib.fresh_local(c.nat.clone());
        let body = c.or_disj(&s, &y);
        let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), body);
        ib.finish_child(pi)
    };
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let (y_id, y) = sb.fresh_local(c.nat.clone());
    let succ_s = c.succ_of(s.clone());

    let cases_motive = build_cases_motive(c, &sb, &succ_s);
    let zero_case = build_inner_zero_case(c, &succ_s);
    let succ_case = build_inner_succ_case(c, &sb, &s, &succ_s, &ih);

    // Lean-faithful casesOn order: motive, major, then minors.
    let cases = Expr::apps(
        c.nat_cases_on.clone(),
        [cases_motive, y.clone(), zero_case, succ_case],
    );
    let lam_y = sb.mk_lam(y_id, BinderInfo::Default, c.nat.clone(), cases);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_y);
    let lam_s = sb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), lam_ih);
    sb.finish_child(lam_s)
}

/// Body:
///   `fun (a b : Nat) => @Nat.rec motive base step a b`.
fn build_value(c: &NatLeTotalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bb_id, bb) = b.fresh_local(c.nat.clone());

    let motive = build_motive(c, &b);
    let base = build_base(c, &b);
    let step = build_step(c, &b);

    // @Nat.rec.{0} motive base step a : (∀ y, Or (a ≤ y) (y ≤ a)); apply to b.
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, a.clone()]);
    let applied = Expr::app(rec_app, bb.clone());

    let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Nat.zero_le : ∀ n : Nat, Nat.le Nat.zero n` as a constructive
    /// `Declaration::Theorem`, if not already present.
    ///
    /// Induction on `n` via `Nat.rec.{0}` with motive `fun t => Nat.le 0 t`.
    /// Base: `Nat.le.refl 0`. Step: `fun k ih => Nat.le.step 0 k ih`. This
    /// mirrors `algebra_nat_mul_cancel_proof.rs::register_nat_zero_le` but is
    /// kept local so `Nat.le_total` does not pull in the mul-cancel bundle.
    fn register_nat_zero_le_lemma(&mut self, c: &NatLeTotalConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.zero_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());

        let type_ = {
            let body = c.le_of(c.zero.clone(), n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le 0 t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(c.zero.clone(), t);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base: Nat.le.refl 0 : Nat.le 0 0
        let base = c.le_refl_app(c.zero.clone());
        // step: fun (k : Nat) (ih : Nat.le 0 k) => Nat.le.step 0 k ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_type = c.le_of(c.zero.clone(), k.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = c.le_step_app(c.zero.clone(), k, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term, no axiom/self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `Nat.le_total` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body inducts on the first argument `a` via `Nat.rec`, splits
    /// on the second argument `b` via `Nat.casesOn`, and threads the induction
    /// hypothesis through `Or.rec` + `Nat.succ_le_succ` in the
    /// successor/successor case. The base case uses `Nat.zero_le`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()`, `self.init_le()`, `self.init_or()` provide
    ///           the supporting symbols. `Nat.zero_le` / `Nat.succ_le_succ` are
    ///           registered as constructive theorems by the dependency calls
    ///           below.
    /// ENSURES: On success, `self` contains a `Declaration::Theorem` named
    ///          `Nat.le_total` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.le_total` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_le_total_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_total");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Supporting symbols and constructive helper lemmas.
        self.init_nat()?;
        self.init_le()?;
        self.init_or()?;
        // `Nat.succ_le_succ` (constructive theorem, via the top-level ordering
        // bundle). `init_nat_top_level_ordering` also wires `init_nat` /
        // `init_le` / `init_lt`.
        self.init_nat_top_level_ordering()?;

        let c = NatLeTotalConsts::new();

        // `Nat.zero_le` — registered locally as a small constructive `Nat.rec`
        // term (idempotent on `get_const`), keeping this module independent of
        // the heavyweight `Nat.mul_left_cancel_succ` proof bundle.
        self.register_nat_zero_le_lemma(&c)?;

        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3599). Double induction —
        // `Nat.rec` on `a`, `Nat.casesOn` on `b`, `Or.rec` on the induction
        // hypothesis in the succ/succ case. Base case uses `Nat.zero_le`; the
        // succ/succ case lifts both disjuncts through `Nat.succ_le_succ`. No
        // `sorry`, no self-reference, no domain-axiom dependency (`Nat.zero_le`
        // and `Nat.succ_le_succ` are constructive theorems; `Nat.rec`,
        // `Nat.casesOn`, `Or.rec` are generated kernel machinery). Replaces the
        // prior `Declaration::Axiom` registered in `order.rs`.
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

    /// Kernel accepts the double-induction proof term; registered as a Theorem
    /// (not Axiom), idempotently.
    #[test]
    fn test_nat_le_total_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_le_total_proof()
            .expect("first registration");
        env.register_nat_le_total_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.le_total"))
            .expect("Nat.le_total should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.le_total"), vec![]))
            .expect("Nat.le_total should type-check");
    }

    /// `init_nat_linear_order` registers `Nat.le_total` as the constructive
    /// Theorem (not the legacy Axiom), and the whole hierarchy still builds.
    #[test]
    fn test_init_nat_linear_order_registers_le_total_theorem() {
        let mut env = Environment::new();
        env.init_nat_linear_order().expect("linear order init");
        let info = env
            .get_const(&Name::from_string("Nat.le_total"))
            .expect("Nat.le_total should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Nat.le_total must be a Theorem after init_nat_linear_order"
        );
    }

    /// After peeling two λ binders (a, b), the proof root is `@Nat.rec` —
    /// guards against an axiom-reference masquerade.
    #[test]
    fn test_nat_le_total_proof_uses_nat_rec() {
        let mut env = Environment::new();
        env.register_nat_le_total_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.le_total"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..2 {
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
                "Nat.le_total proof root must be Nat.rec"
            ),
            k => panic!("expected Const(Nat.rec, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive). `Nat.zero_le` and
    /// `Nat.succ_le_succ` are themselves constructive theorems, so totality
    /// inherits an empty domain-axiom closure.
    #[test]
    fn test_nat_le_total_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_le_total_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.le_total"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.le_total must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    /// Proof quality is `Constructive`.
    #[test]
    fn test_nat_le_total_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_nat_le_total_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Nat.le_total"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Nat.le_total must be Constructive, got {:?}",
            quality
        );
    }
}
