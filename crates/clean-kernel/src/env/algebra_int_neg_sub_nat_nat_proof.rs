// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.neg_subNatNat : forall m n : Nat,
//!     Eq Int (Int.neg (Int.subNatNat m n)) (Int.subNatNat n m)`.
//!
//! Negating `Int.subNatNat m n` (morally `m - n` as an `Int`) swaps the two
//! arguments: `-(m - n) = n - m`. This is the key normalization lemma behind
//! `Int.neg_add` (the mixed-sign `add` branches reduce
//! `Int.neg (Int.add a b)` to `Int.neg (Int.subNatNat _ _)`).
//!
//! # Proof sketch
//!
//! `Int.subNatNat` is a reducible Definition by recursion on its SECOND
//! argument:
//!
//! ```text
//! Int.subNatNat m Nat.zero          = Int.ofNat m
//! Int.subNatNat Nat.zero (succ n)   = Int.negSucc n
//! Int.subNatNat (succ m) (succ n)   = Int.subNatNat m n
//! ```
//!
//! and `Int.neg` is a reducible Definition:
//!
//! ```text
//! Int.neg (ofNat 0)        = ofNat 0
//! Int.neg (ofNat (succ k)) = negSucc k
//! Int.neg (negSucc k)      = ofNat (succ k)
//! ```
//!
//! We prove by nested `@Nat.rec.{0}`: outer on `m` (capturing the induction
//! hypothesis `ih_m : forall n, neg (subNatNat m n) = subNatNat n m`), inner
//! on `n`. The four constructor corners close as: three refl corners (pure
//! `@Eq.refl.{1}` via iota + delta), and the (succ, succ) corner via the
//! outer hypothesis `ih_m` applied to the inner index `k`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.neg`, `Int.subNatNat`,
//! `Int.ofNat`, `Int.negSucc`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`,
//! `Eq`, `Eq.refl`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.neg_subNatNat")` is empty and the proof quality is
//! `ProofQuality::Constructive`.
//!
//! Tracks #3604. Consumer: `algebra_int_neg_add_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntNegSubNatNatConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    int_neg: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    /// `Int.subNatNat_zero_succ n : Eq Int (subNatNat 0 (succ n)) (negSucc n)`.
    snn_zero_succ: Expr,
    /// `Int.subNatNat_succ_succ m n : Eq Int (subNatNat (succ m) (succ n)) (subNatNat m n)`.
    snn_succ_succ: Expr,
}

impl IntNegSubNatNatConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            snn_zero_succ: Expr::const_(Name::from_string("Int.subNatNat_zero_succ"), vec![]),
            snn_succ_succ: Expr::const_(Name::from_string("Int.subNatNat_succ_succ"), vec![]),
        }
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    /// `@Eq.symm.{1} Int a b h : Eq Int b a` given `h : Eq Int a b`.
    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    /// `@Eq.trans.{1} Int a b c hab hbc : Eq Int a c`.
    fn trans_int(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), a, b, c, hab, hbc],
        )
    }

    /// `@congrArg.{1,1} Int Int a b Int.neg h : Eq Int (neg a) (neg b)`
    /// given `h : Eq Int a b`.
    fn congr_neg(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.int_type.clone(),
                self.int_type.clone(),
                a,
                b,
                self.int_neg.clone(),
                h,
            ],
        )
    }

    /// `Int.subNatNat_zero_succ n : Eq Int (subNatNat 0 (succ n)) (negSucc n)`.
    fn snn_zero_succ_at(&self, n: Expr) -> Expr {
        Expr::app(self.snn_zero_succ.clone(), n)
    }

    /// `Int.subNatNat_succ_succ m n :
    ///   Eq Int (subNatNat (succ m) (succ n)) (subNatNat m n)`.
    fn snn_succ_succ_at(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.snn_succ_succ.clone(), m), n)
    }
}

/// Build `forall m n : Nat, Eq Int (Int.neg (Int.subNatNat m n)) (Int.subNatNat n m)`.
fn build_type(c: &IntNegSubNatNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(
        c.neg(c.sub_nat_nat(m.clone(), n.clone())),
        c.sub_nat_nat(n, m),
    );
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Outer motive: `lambda (m : Nat) =>
///   forall n : Nat, Eq Int (Int.neg (Int.subNatNat m n)) (Int.subNatNat n m)`.
fn build_outer_motive(c: &IntNegSubNatNatConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = mb.fresh_local(c.nat_type.clone());
    let (n_id, n) = mb.fresh_local(c.nat_type.clone());
    let body = c.eq_int(
        c.neg(c.sub_nat_nat(m.clone(), n.clone())),
        c.sub_nat_nat(n, m),
    );
    let pi = mb.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), body);
    let lam = mb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), pi);
    mb.finish_child(lam)
}

/// Inner `Nat.rec` over `n` for a fixed `m_lit : Nat`.
///
/// `outer_opt` carries the OUTER recursion data when `m_lit = succ j`:
/// `(j, ih_m)` where `j` is the outer predecessor (`m_lit = Nat.succ j`) and
/// `ih_m : forall n, neg (subNatNat j n) = subNatNat n j` is the outer
/// induction hypothesis. It is `None` in the `m = 0` branch.
///
/// Under the SOUND kernel `Int.subNatNat` only iota-reduces on its second
/// argument, so the mixed-sign corners are NOT closeable by `refl`; they are
/// discharged with `Int.subNatNat_zero_succ` / `Int.subNatNat_succ_succ` and
/// the outer hypothesis (#3604).
fn build_inner_rec(
    c: &IntNegSubNatNatConsts,
    parent: &EnvDeclBuilder,
    m_lit: &Expr,
    outer_opt: Option<(&Expr, &Expr)>,
) -> Expr {
    let mut rb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = rb.fresh_local(c.nat_type.clone());

    let inner_motive = {
        let mut ib = EnvDeclBuilder::child_of(&rb);
        let (t_id, t) = ib.fresh_local(c.nat_type.clone());
        let body = c.eq_int(
            c.neg(c.sub_nat_nat(m_lit.clone(), t.clone())),
            c.sub_nat_nat(t, m_lit.clone()),
        );
        let lam = ib.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(lam)
    };

    // n = 0 corner: goal `Eq Int (neg (subNatNat m_lit 0)) (subNatNat 0 m_lit)`.
    let zero_case = match outer_opt {
        // m_lit = 0: both sides reduce to `ofNat 0`; pure refl.
        None => c.refl_int(c.sub_nat_nat(c.nat_zero.clone(), m_lit.clone())),
        // m_lit = succ j: LHS `neg (subNatNat (succ j) 0)` reduces (iota on the
        // second arg, then `Int.neg` iota) to `negSucc j`, but RHS
        // `subNatNat 0 (succ j)` is stuck. Bridge with the symmetric
        // `subNatNat_zero_succ j : Eq Int (subNatNat 0 (succ j)) (negSucc j)`;
        // its endpoints are `negSucc j` (defeq the goal LHS) and
        // `subNatNat 0 (succ j)` (the goal RHS).
        Some((j, _ih_m)) => {
            let snn_zero_succ_j = c.snn_zero_succ_at(j.clone());
            c.symm_int(
                c.sub_nat_nat(c.nat_zero.clone(), c.succ(j.clone())),
                c.neg_succ(j.clone()),
                snn_zero_succ_j,
            )
        }
    };

    // n = succ k corner: goal
    //   `Eq Int (neg (subNatNat m_lit (succ k))) (subNatNat (succ k) m_lit)`.
    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&rb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_inner_ty = c.eq_int(
            c.neg(c.sub_nat_nat(m_lit.clone(), k.clone())),
            c.sub_nat_nat(k.clone(), m_lit.clone()),
        );
        let (ih_inner_id, _ih_inner) = sb.fresh_local(ih_inner_ty.clone());

        let proof = match outer_opt {
            // m_lit = succ j: goal
            //   `Eq Int (neg (subNatNat (succ j) (succ k))) (subNatNat (succ k) (succ j))`.
            // Chain three steps:
            //   (1) congrArg Int.neg (subNatNat_succ_succ j k)
            //         : neg (subNatNat (succ j)(succ k)) = neg (subNatNat j k)
            //   (2) ih_m k
            //         : neg (subNatNat j k) = subNatNat k j
            //   (3) Eq.symm (subNatNat_succ_succ k j)
            //         : subNatNat k j = subNatNat (succ k)(succ j)
            Some((j, ih_m)) => {
                let neg_snn_succ = c.neg(c.sub_nat_nat(c.succ(j.clone()), c.succ(k.clone())));
                let neg_snn_jk = c.neg(c.sub_nat_nat(j.clone(), k.clone()));
                let snn_kj = c.sub_nat_nat(k.clone(), j.clone());
                let snn_succ_kj = c.sub_nat_nat(c.succ(k.clone()), c.succ(j.clone()));

                let step1 = c.congr_neg(
                    c.sub_nat_nat(c.succ(j.clone()), c.succ(k.clone())),
                    c.sub_nat_nat(j.clone(), k.clone()),
                    c.snn_succ_succ_at(j.clone(), k.clone()),
                );
                let step2 = Expr::app(ih_m.clone(), k.clone());
                let step3 = c.symm_int(
                    snn_succ_kj.clone(),
                    snn_kj.clone(),
                    c.snn_succ_succ_at(k.clone(), j.clone()),
                );

                let step12 = c.trans_int(
                    neg_snn_succ.clone(),
                    neg_snn_jk,
                    snn_kj.clone(),
                    step1,
                    step2,
                );
                c.trans_int(neg_snn_succ, snn_kj, snn_succ_kj, step12, step3)
            }
            // m_lit = 0: goal
            //   `Eq Int (neg (subNatNat 0 (succ k))) (subNatNat (succ k) 0)`.
            // RHS reduces (iota) to `ofNat (succ k)`. `subNatNat 0 (succ k)` is
            // stuck, so map `subNatNat_zero_succ k` through `Int.neg`:
            //   congrArg Int.neg (subNatNat_zero_succ k)
            //     : neg (subNatNat 0 (succ k)) = neg (negSucc k)
            // and `neg (negSucc k)` reduces (iota) to `ofNat (succ k)`,
            // definitionally equal to the goal RHS `subNatNat (succ k) 0`.
            None => c.congr_neg(
                c.sub_nat_nat(c.nat_zero.clone(), c.succ(k.clone())),
                c.neg_succ(k.clone()),
                c.snn_zero_succ_at(k.clone()),
            ),
        };

        let lam_ih = sb.mk_lam(ih_inner_id, BinderInfo::Default, ih_inner_ty, proof);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [inner_motive, zero_case, succ_case, n]);
    let lam_n = rb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    rb.finish_child(lam_n)
}

/// Body: `lambda (m : Nat) => @Nat.rec.{0} outer_motive zero_case succ_case m`.
fn build_value(c: &IntNegSubNatNatConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (m_id, m) = vb.fresh_local(c.nat_type.clone());

    let outer_motive = build_outer_motive(c, &vb);

    let zero_case = build_inner_rec(c, &vb, &c.nat_zero.clone(), None);

    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (j_id, j) = sb.fresh_local(c.nat_type.clone());
        let ih_m_ty = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let (n_id, n) = ib.fresh_local(c.nat_type.clone());
            let body = c.eq_int(
                c.neg(c.sub_nat_nat(j.clone(), n.clone())),
                c.sub_nat_nat(n, j.clone()),
            );
            let pi = ib.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), body);
            ib.finish_child(pi)
        };
        let (ih_m_id, ih_m) = sb.fresh_local(ih_m_ty.clone());

        let succ_j = c.succ(j.clone());
        let inner = build_inner_rec(c, &sb, &succ_j, Some((&j, &ih_m)));

        let lam_ih = sb.mk_lam(ih_m_id, BinderInfo::Default, ih_m_ty, inner);
        let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_j)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [outer_motive, zero_case, succ_case, m]);
    let val_raw = vb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.neg_subNatNat` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.neg`, `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.neg_subNatNat` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_neg_sub_nat_nat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.neg_subNatNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        // Provides the mixed-sign normalization lemmas the constructive proof
        // needs because `Int.subNatNat` only iota-reduces on its second
        // argument, so the mixed-sign corners are NOT closeable by `refl`.
        // Register them directly (not via `init_int_arith_lemmas`, which itself
        // calls back into this proof and would recurse): both are constructive
        // and do NOT depend on `Int.neg_subNatNat`, so there is no cycle.
        self.register_int_sub_nat_nat_zero_succ_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        let c = IntNegSubNatNatConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Nat.rec.{0}` (outer on `m`, inner on `n`). Three constructor
        // corners close by pure `@Eq.refl.{1}`; the (succ, succ) corner closes
        // with the outer induction hypothesis applied to the inner index. No
        // `sorry`, no self-reference, no domain-axiom dependency.
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
    use crate::env::ConstantKind;

    #[test]
    fn test_int_neg_sub_nat_nat_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_neg_sub_nat_nat_proof()
            .expect("first registration");
        env.register_int_neg_sub_nat_nat_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.neg_subNatNat"))
            .expect("Int.neg_subNatNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_neg_sub_nat_nat_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_neg_sub_nat_nat_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.neg_subNatNat"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body.clone(),
            k => panic!("expected outer lambda, got {:?}", k),
        };
        let mut head = outer_body;
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Int.neg_subNatNat proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_neg_sub_nat_nat_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_neg_sub_nat_nat_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.neg_subNatNat"))
            .expect("Int.neg_subNatNat is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.neg_subNatNat must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
