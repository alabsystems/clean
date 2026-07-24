// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.lt_iff_le_not_le : ∀ a b : Int,
//!    Iff (Int.lt a b) (And (Int.le a b) (Not (Int.le b a)))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_linear_order` with a kernel-checked
//! `Declaration::Theorem` whose transitive axiom closure is empty. This is the
//! residual admitted Int order axiom that `Rat.lt_iff_le_not_le` (see
//! `algebra_rat_order_proofs.rs`) delegates to; eliminating it discharges that
//! delegation's `AxiomDependent` classification at the root.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)                 -- reducible Definition
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b       -- reducible Definition
//! Not P      := P → False                                -- reducible Definition
//! ```
//!
//! So `Int.lt a b` is definitionally `Int.le (Int.add a 1) b`, and in
//! particular `Int.le (Int.add a 1) a` is definitionally `Int.lt a a`.
//!
//! # Proof strategy
//!
//! The biconditional is built with `Iff.intro` of two functions.
//!
//! ## Forward (`mp : Int.lt a b → And (Int.le a b) (Not (Int.le b a))`)
//!
//! `λ (h : Int.lt a b) =>`
//! `  And.intro (Int.le a b) (Not (Int.le b a))`
//! `    (Int.le_of_lt a b h)`
//! `    (λ (hba : Int.le b a) =>`
//! `       Int.lt_irrefl a (Int.le_trans (Int.add a 1) b a h hba))`
//!
//! The first component is the constructive `Int.le_of_lt`. For the second, `h`
//! is definitionally `Int.le (a+1) b`, so chaining it with `hba : Int.le b a`
//! through the constructive `Int.le_trans` yields `Int.le (a+1) a`, which is
//! definitionally `Int.lt a a`; the constructive `Int.lt_irrefl a` rejects it,
//! producing `False`. The whole `λ hba => …` inhabits
//! `Int.le b a → False ≡ Not (Int.le b a)`.
//!
//! ## Reverse (`mpr : And (Int.le a b) (Not (Int.le b a)) → Int.lt a b`)
//!
//! `λ (hand) =>` with `hab := And.left … hand`, `hnba := And.right … hand`,
//! case-split on the constructive `Int.lt_trichotomy a b :
//! Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))` via `@Or.rec`:
//!
//! - `Int.lt a b`: the goal directly.
//! - `Eq a b`: transport `Int.le_refl a : Int.le a a` along `heq : Eq a b`
//!   (`@Eq.subst` with motive `λ x => Int.le x a`) to `Int.le b a`, feed to
//!   `hnba` for `False`, discharge the goal with `@False.elim`.
//! - `Int.lt b a`: `Int.le_of_lt b a` gives `Int.le b a`, feed to `hnba` for
//!   `False`, discharge with `@False.elim`.
//!
//! `hab` is unused in the reverse term (the disjunction already pins the
//! sign); it is still extracted to mirror the standard statement.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.lt`, `Int.le`, `Int.add`,
//! `Int.ofNat`, `Iff.intro`, `And`, `And.intro`, `And.left`, `And.right`,
//! `Not`, `Or`, `Or.rec`, `False`, `False.elim`, `Eq`, `Eq.subst`, and the
//! constructive empty-closure Int order theorems `Int.le_of_lt`,
//! `Int.le_trans`, `Int.lt_irrefl`, `Int.le_refl`, `Int.lt_trichotomy` — none
//! of which is a `Declaration::Axiom`. Therefore
//! `env.axiom_deps("Int.lt_iff_le_not_le")` is empty and
//! `env.proof_quality("Int.lt_iff_le_not_le") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtIffConsts {
    int_type: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    not_const: Expr,
    and_const: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    iff_const: Expr,
    iff_intro: Expr,
    or_const: Expr,
    or_rec: Expr,
    eq_const: Expr,
    eq_subst: Expr,
    false_elim: Expr,
    le_of_lt: Expr,
    le_trans: Expr,
    lt_irrefl: Expr,
    le_refl: Expr,
    lt_trichotomy: Expr,
}

impl IntLtIffConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            not_const: Expr::const_(Name::from_string("Not"), vec![]),
            and_const: Expr::const_(Name::from_string("And"), vec![]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            iff_const: Expr::const_(Name::from_string("Iff"), vec![]),
            iff_intro: Expr::const_(Name::from_string("Iff.intro"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            // Or.rec eliminating into the `Prop`-valued goal `Int.lt a b`.
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            // Eq lives in Type 1 here (Int : Type 0), so Eq.subst.{1}.
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
            // The goal closed by False.elim is `Int.lt a b : Prop` (Sort 0).
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            le_of_lt: Expr::const_(Name::from_string("Int.le_of_lt"), vec![]),
            le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            lt_irrefl: Expr::const_(Name::from_string("Int.lt_irrefl"), vec![]),
            le_refl: Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            lt_trichotomy: Expr::const_(Name::from_string("Int.lt_trichotomy"), vec![]),
        }
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_lt.clone(), [x, y])
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [x, y])
    }

    /// `1 := Int.ofNat (Nat.succ Nat.zero)` — the canonical `Int.lt` unit.
    fn one(&self) -> Expr {
        Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }

    fn not_of(&self, p: Expr) -> Expr {
        Expr::app(self.not_const.clone(), p)
    }

    fn and_of(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_const.clone(), [p, q])
    }

    fn or_of(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [p, q])
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// The RHS proposition `And (Int.le a b) (Not (Int.le b a))`.
    fn rhs_prop(&self, a: &Expr, bb: &Expr) -> Expr {
        let le_ab = self.le(a.clone(), bb.clone());
        let not_le_ba = self.not_of(self.le(bb.clone(), a.clone()));
        self.and_of(le_ab, not_le_ba)
    }
}

/// Build `∀ a b : Int, Iff (Int.lt a b) (And (Int.le a b) (Not (Int.le b a)))`.
fn build_type(c: &IntLtIffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bb_id, bb) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bb.clone());
    let rhs = c.rhs_prop(&a, &bb);
    let iff = Expr::apps(c.iff_const.clone(), [lt_ab, rhs]);
    let r = b.mk_pi(bb_id, BinderInfo::Default, c.int_type.clone(), iff);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Forward `mp : Int.lt a b → And (Int.le a b) (Not (Int.le b a))`.
fn build_mp(c: &IntLtIffConsts, parent: &EnvDeclBuilder, a: &Expr, bb: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let lt_ab = c.lt(a.clone(), bb.clone());
    let (h_id, h) = b.fresh_local(lt_ab.clone());

    let le_ab = c.le(a.clone(), bb.clone());
    let le_ba = c.le(bb.clone(), a.clone());
    let not_le_ba = c.not_of(le_ba.clone());

    // First component: Int.le_of_lt a b h : Int.le a b.
    let left = Expr::apps(c.le_of_lt.clone(), [a.clone(), bb.clone(), h.clone()]);

    // Second component: λ (hba : Int.le b a) =>
    //   Int.lt_irrefl a (Int.le_trans (a+1) b a h hba)   : Int.lt a a → False
    // (h : Int.lt a b ≡ Int.le (a+1) b; le_trans gives Int.le (a+1) a ≡ Int.lt a a.)
    let right = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (hba_id, hba) = rb.fresh_local(le_ba.clone());
        let a_plus_one = c.add(a.clone(), c.one());
        // Int.le_trans (a+1) b a h hba : Int.le (a+1) a
        let chained = Expr::apps(
            c.le_trans.clone(),
            [a_plus_one, bb.clone(), a.clone(), h.clone(), hba.clone()],
        );
        // Int.lt_irrefl a : Not (Int.lt a a) ≡ Int.lt a a → False; apply to chained.
        let irrefl = Expr::app(c.lt_irrefl.clone(), a.clone());
        let false_proof = Expr::app(irrefl, chained);
        let lam = rb.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), false_proof);
        rb.finish_child(lam)
    };

    // And.intro (Int.le a b) (Not (Int.le b a)) left right.
    let body = Expr::apps(c.and_intro.clone(), [le_ab, not_le_ba, left, right]);
    let lam = b.mk_lam(h_id, BinderInfo::Default, lt_ab, body);
    b.finish_child(lam)
}

/// Reverse `mpr : And (Int.le a b) (Not (Int.le b a)) → Int.lt a b`.
fn build_mpr(c: &IntLtIffConsts, parent: &EnvDeclBuilder, a: &Expr, bb: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let rhs = c.rhs_prop(a, bb);
    let (hand_id, hand) = b.fresh_local(rhs.clone());

    let lt_ab = c.lt(a.clone(), bb.clone());
    let lt_ba = c.lt(bb.clone(), a.clone());
    let le_ab = c.le(a.clone(), bb.clone());
    let le_ba = c.le(bb.clone(), a.clone());
    let not_le_ba = c.not_of(le_ba.clone());
    let eq_ab = c.eq_int(a.clone(), bb.clone());
    let inner_or = c.or_of(eq_ab.clone(), lt_ba.clone()); // Or (Eq a b) (lt b a)

    // hnba := And.right (Int.le a b) (Not (Int.le b a)) hand : Not (Int.le b a).
    let hnba = Expr::apps(
        c.and_right.clone(),
        [le_ab.clone(), not_le_ba.clone(), hand.clone()],
    );
    // hab := And.left … hand : Int.le a b  (mirrors the statement; unused below).
    let _hab = Expr::apps(
        c.and_left.clone(),
        [le_ab.clone(), not_le_ba.clone(), hand.clone()],
    );

    // ----- inner Or.rec: case-split Or (Eq a b) (lt b a) into the goal lt a b -----
    // const motive: fun (_ : Or (Eq a b) (lt b a)) => Int.lt a b
    let inner_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, _x) = mb.fresh_local(inner_or.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, inner_or.clone(), lt_ab.clone());
        mb.finish_child(lam)
    };

    // case Eq a b: λ (heq : Eq a b) =>
    //   False.elim (lt a b) (hnba (Eq.subst Int (λ x => le x a) a b heq (le_refl a)))
    let case_eq = {
        let mut eb = EnvDeclBuilder::child_of(&b);
        let (heq_id, heq) = eb.fresh_local(eq_ab.clone());
        // subst motive: fun (x : Int) => Int.le x a
        let subst_motive = {
            let mut sm = EnvDeclBuilder::child_of(&eb);
            let (x_id, x) = sm.fresh_local(c.int_type.clone());
            let body = c.le(x, a.clone());
            let lam = sm.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
            sm.finish_child(lam)
        };
        // Int.le_refl a : Int.le a a ≡ motive a.
        let refl_le = Expr::app(c.le_refl.clone(), a.clone());
        // Eq.subst Int motive a b heq refl_le : motive b = Int.le b a.
        let le_ba_proof = Expr::apps(
            c.eq_subst.clone(),
            [
                c.int_type.clone(),
                subst_motive,
                a.clone(),
                bb.clone(),
                heq.clone(),
                refl_le,
            ],
        );
        // hnba le_ba_proof : False.
        let false_proof = Expr::app(hnba.clone(), le_ba_proof);
        // False.elim (Int.lt a b) false_proof : Int.lt a b.
        let body = Expr::apps(c.false_elim.clone(), [lt_ab.clone(), false_proof]);
        let lam = eb.mk_lam(heq_id, BinderInfo::Default, eq_ab.clone(), body);
        eb.finish_child(lam)
    };

    // case lt b a: λ (hltba : Int.lt b a) =>
    //   False.elim (lt a b) (hnba (Int.le_of_lt b a hltba))
    let case_lt_ba = {
        let mut lb = EnvDeclBuilder::child_of(&b);
        let (hltba_id, hltba) = lb.fresh_local(lt_ba.clone());
        // Int.le_of_lt b a hltba : Int.le b a.
        let le_ba_proof = Expr::apps(c.le_of_lt.clone(), [bb.clone(), a.clone(), hltba.clone()]);
        let false_proof = Expr::app(hnba.clone(), le_ba_proof);
        let body = Expr::apps(c.false_elim.clone(), [lt_ab.clone(), false_proof]);
        let lam = lb.mk_lam(hltba_id, BinderInfo::Default, lt_ba.clone(), body);
        lb.finish_child(lam)
    };

    // @Or.rec (Eq a b) (lt b a) inner_motive case_eq case_lt_ba (· : Or …)
    let inner_or_rec = |scrut: Expr| {
        Expr::apps(
            c.or_rec.clone(),
            [
                eq_ab.clone(),
                lt_ba.clone(),
                inner_motive.clone(),
                case_eq.clone(),
                case_lt_ba.clone(),
                scrut,
            ],
        )
    };

    // ----- outer Or.rec: case-split lt_trichotomy a b into the goal lt a b -----
    // const motive: fun (_ : Or (lt a b) (Or (Eq a b) (lt b a))) => Int.lt a b
    let outer_or = c.or_of(lt_ab.clone(), inner_or.clone());
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, _x) = mb.fresh_local(outer_or.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, outer_or.clone(), lt_ab.clone());
        mb.finish_child(lam)
    };

    // case lt a b: λ (h : Int.lt a b) => h
    let case_lt_ab = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = cb.fresh_local(lt_ab.clone());
        let lam = cb.mk_lam(h_id, BinderInfo::Default, lt_ab.clone(), h);
        cb.finish_child(lam)
    };

    // case Or (Eq a b) (lt b a): λ (ho : Or (Eq a b) (lt b a)) => inner_or_rec ho
    let case_inner = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (ho_id, ho) = cb.fresh_local(inner_or.clone());
        let body = inner_or_rec(ho);
        let lam = cb.mk_lam(ho_id, BinderInfo::Default, inner_or.clone(), body);
        cb.finish_child(lam)
    };

    // Int.lt_trichotomy a b : Or (lt a b) (Or (Eq a b) (lt b a)).
    let tri = Expr::apps(c.lt_trichotomy.clone(), [a.clone(), bb.clone()]);
    // @Or.rec (lt a b) (Or (Eq a b) (lt b a)) outer_motive case_lt_ab case_inner tri
    let body = Expr::apps(
        c.or_rec.clone(),
        [
            lt_ab.clone(),
            inner_or.clone(),
            outer_motive,
            case_lt_ab,
            case_inner,
            tri,
        ],
    );

    let lam = b.mk_lam(hand_id, BinderInfo::Default, rhs, body);
    b.finish_child(lam)
}

/// Build the closed proof value:
/// `λ (a b : Int) => Iff.intro (Int.lt a b) (And …) mp mpr`.
fn build_value(c: &IntLtIffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bb_id, bb) = b.fresh_local(c.int_type.clone());

    let lt_ab = c.lt(a.clone(), bb.clone());
    let rhs = c.rhs_prop(&a, &bb);

    let mp = build_mp(c, &b, &a, &bb);
    let mpr = build_mpr(c, &b, &a, &bb);

    // Iff.intro (Int.lt a b) (And …) mp mpr.
    let iff = Expr::apps(c.iff_intro.clone(), [lt_ab, rhs, mp, mpr]);

    let lam = b.mk_lam(bb_id, BinderInfo::Default, c.int_type.clone(), iff);
    let lam = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), lam);
    b.finish(lam)
}

impl Environment {
    /// Register `Int.lt_iff_le_not_le` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.add`, `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.subst`.
    /// REQUIRES: `self.init_and()` has registered `And` / `And.intro` /
    ///           `And.left` / `And.right`.
    /// REQUIRES: `self.init_iff()` has registered `Iff` / `Iff.intro`.
    /// REQUIRES: `self.init_or()` has registered `Or` / `Or.rec`.
    /// REQUIRES: `self.init_true_false()` has registered `Not` / `False` /
    ///           `False.elim`.
    /// ENSURES: On success, `Int.lt_iff_le_not_le` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_iff_le_not_le` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_iff_le_not_le_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_iff_le_not_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_or()?;
        self.init_true_false()?;

        // Constructive empty-closure order dependencies.
        self.register_int_le_of_lt_proof()?;
        self.register_int_le_trans_proof()?;
        self.register_int_lt_irrefl_proof()?;
        self.register_int_le_refl_proof()?;
        self.register_int_lt_trichotomy_proof()?;

        let c = IntLtIffConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `Iff.intro` packages a
        // forward and a reverse function. Forward: `Int.le_of_lt` for the `≤`
        // component, and `Int.lt_irrefl a (Int.le_trans (a+1) b a h hba)` for
        // `¬(b ≤ a)` (using `h : Int.lt a b ≡ Int.le (a+1) b` definitionally, so
        // the chain lands in `Int.le (a+1) a ≡ Int.lt a a`). Reverse: an
        // `@Or.rec` case-split on the constructive `Int.lt_trichotomy a b` —
        // the `a < b` disjunct is the goal; the `a = b` disjunct transports
        // `Int.le_refl a` along `Eq.subst` to `Int.le b a` and the `b < a`
        // disjunct sends `Int.le_of_lt b a` to `Int.le b a`, both feeding the
        // `¬(b ≤ a)` hypothesis to `False` and discharging the goal via
        // `@False.elim`. No `sorry`, no self-reference, no domain-axiom
        // dependency. Replaces the prior `Declaration::Axiom` in
        // `order_int.rs::init_int_linear_order` — the residual admitted Int
        // order axiom that `Rat.lt_iff_le_not_le` delegates to.
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
    use crate::env::{ConstantKind, ProofQuality};

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_lt_iff_le_not_le_proof()
            .expect("register_int_lt_iff_le_not_le_proof should succeed");
        env
    }

    #[test]
    fn test_int_lt_iff_le_not_le_registered_as_theorem() {
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Int.lt_iff_le_not_le"))
            .expect("Int.lt_iff_le_not_le should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Int.lt_iff_le_not_le must be a kernel-checked Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Int.lt_iff_le_not_le Theorem must retain its proof value"
        );
    }

    #[test]
    fn test_int_lt_iff_le_not_le_constructive() {
        let env = registered_env();
        let q = env
            .proof_quality(&Name::from_string("Int.lt_iff_le_not_le"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Int.lt_iff_le_not_le must be Constructive, got {q:?}"
        );
    }

    #[test]
    fn test_int_lt_iff_le_not_le_axiom_deps_empty() {
        let env = registered_env();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_iff_le_not_le"))
            .expect("Int.lt_iff_le_not_le is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_iff_le_not_le must have empty domain-axiom closure, got {domain_deps:?}"
        );
    }

    #[test]
    fn test_int_lt_iff_le_not_le_type_checks() {
        use crate::tc::TypeChecker;
        let env = registered_env();
        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Int.lt_iff_le_not_le"),
                vec![],
            ))
            .expect("Int.lt_iff_le_not_le should kernel-type-check");
    }

    #[test]
    fn test_int_lt_iff_le_not_le_proof_root_is_iff_intro() {
        use crate::expr::ExprKind;
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Int.lt_iff_le_not_le"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the two outer λ binders (a, b), then the head must be Iff.intro.
        let mut body: Expr = value.clone();
        for _ in 0..2 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {k:?}"),
            };
        }
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Iff.intro",
                "Int.lt_iff_le_not_le proof root must be Iff.intro"
            ),
            k => panic!("expected Const(Iff.intro), got {k:?}"),
        }
    }

    #[test]
    fn test_int_lt_iff_le_not_le_idempotent() {
        let mut env = Environment::new();
        env.register_int_lt_iff_le_not_le_proof()
            .expect("first registration");
        env.register_int_lt_iff_le_not_le_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_iff_le_not_le"))
            .expect("Int.lt_iff_le_not_le should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
