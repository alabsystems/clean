// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K2a layer: the spectral double-count identity.
//!
//! Defines the reducible set-size carrier and the Fubini double-count that is
//! the spectral bookkeeping spine of KKL:
//!
//! ```text
//! BoolAnalysis.setSize (n : Nat) (S : HCPoint n) : Rat :=
//!   Fin.sum n (fun i => ind (S i))
//!
//! BoolAnalysis.subsetSum_double_count : ∀ (n : Nat) (w : HCPoint n → Rat),
//!   Fin.sum n (fun i => subsetSum n (fun S => ind (S i) · w S))
//!     = subsetSum n (fun S => setSize n S · w S)
//! ```
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! Unfolding `subsetSum n G = Fin.sum (2^n) (fun j => G (hcDecode n j))`, the LHS
//! is `Σ_i Σ_j F i j` with `F i j := ind ((hcDecode n j) i) · w (hcDecode n j)`.
//!
//! 1. `Fin.sum_swap n (2^n) F` (the finite Fubini engine) transposes to
//!    `Σ_j Σ_i F i j`.
//! 2. Per fixed `j` (fixed subset `S := hcDecode n j`):
//!    `Fin.sum_mul n (fun i => ind (S i)) (w S) :
//!       Σ_i (ind (S i) · w S) = (Σ_i ind (S i)) · w S`.
//!    The RHS `(Σ_i ind (S i)) · w S` is DEFINITIONALLY `setSize n S · w S`
//!    (reducible `setSize`). `Fin.sum_congr` lifts this pointwise rewrite over
//!    `j` to turn `Σ_j Σ_i F i j` into `Σ_j (setSize n (hcDecode n j) · w (…))`.
//! 3. That last sum is DEFINITIONALLY `subsetSum n (fun S => setSize n S · w S)`
//!    (reducible `subsetSum`), closing the goal.
//!
//! Every dependency (`Fin.sum_swap`, `Fin.sum_mul`, `Fin.sum_congr`,
//! `subsetSum`, `setSize`, `ind`, `hcDecode`) is `Constructive` with empty
//! closure, so the double-count is too.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `BoolAnalysis.setSize (n : Nat) (S : HCPoint n) : Rat`
    /// `:= Fin.sum n (fun i => ind (S i))`.
    ///
    /// The `Rat`-valued cardinality of the subset `S ⊆ [n]` (sum of indicators).
    /// Reducible `Declaration::Definition`; closure bottoms out in reducible
    /// `Fin.sum` / `ind`, so theorems over it stay `Constructive`. Idempotent.
    pub(crate) fn register_set_size(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSize");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        self.init_boolean_analysis_foundations()?; // HCPoint, ind
        self.init_fin_sum()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);

        let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());

        // Type: (n : Nat) -> HCPoint n -> Rat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let s_type = hcpoint_of(&n);
            let (s_id, _s) = b.fresh_local(s_type.clone());
            let r = b.mk_pi(s_id, BinderInfo::Default, s_type, rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n : Nat) (S : HCPoint n) =>
        //   Fin.sum n (fun (i : Fin n) => ind (S i))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let s_type = hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(s_type.clone());

            let summand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let body = Expr::app(ind.clone(), Expr::app(s.clone(), i));
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            let body = Expr::apps(fin_sum.clone(), [n.clone(), summand]);
            let r = b.mk_lam(s_id, BinderInfo::Default, s_type, body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.subsetSum_double_count :
    ///   ∀ (n : Nat) (w : HCPoint n → Rat),
    ///     Fin.sum n (fun i => subsetSum n (fun S => ind (S i) · w S))
    ///       = subsetSum n (fun S => setSize n S · w S)`.
    ///
    /// The Fubini double-count. Kernel-checked, constructive, empty closure.
    /// Idempotent.
    pub fn register_subset_sum_double_count(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_double_count");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_fin_sum_swap_theorem()?;
        self.register_fin_sum_mul_theorem()?;
        self.init_fin_sum()?; // Fin.sum_congr

        let c = DcConsts::new();
        let ty = build_double_count_type(&c);
        let value = build_double_count_proof(&c);

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Shared atoms for the double-count construction.
struct DcConsts {
    nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_swap: Expr,
    fin_sum_mul: Expr,
    fin_sum_congr: Expr,
    subset_sum: Expr,
    set_size: Expr,
    ind: Expr,
    hc_decode: Expr,
    hcpoint: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    eq1: Expr,
}

impl DcConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_swap: Expr::const_(Name::from_string("Fin.sum_swap"), vec![]),
            fin_sum_mul: Expr::const_(Name::from_string("Fin.sum_mul"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![u1]),
        }
    }

    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    fn ind_app(&self, s_i: Expr) -> Expr {
        Expr::app(self.ind.clone(), s_i)
    }
    fn fin_sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }

    /// `fun (S : HCPoint n) => ind (S i) · w S` — the per-coordinate integrand.
    fn coord_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr, i: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let body = self.mul(self.ind_app(s_i), Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (S : HCPoint n) => setSize n S · w S` — the RHS integrand.
    fn size_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let size = Expr::apps(self.set_size.clone(), [n.clone(), s.clone()]);
        let body = self.mul(size, Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `F : Fin n → Fin (2^n) → Rat`,
    /// `F i j := ind ((hcDecode n j) i) · w (hcDecode n j)`.
    fn swap_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let mut ci = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ci.fresh_local(fin_n.clone());
        let inner = {
            let mut cj = EnvDeclBuilder::child_of(&ci);
            let fin_pow = self.fin_of(&self.pow2(n));
            let (j_id, j) = cj.fresh_local(fin_pow.clone());
            let s = self.decode(n, &j);
            let s_i = Expr::app(s.clone(), i.clone());
            let body = self.mul(self.ind_app(s_i), Expr::app(w.clone(), s));
            cj.finish_child(cj.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
        };
        ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, inner))
    }
}

/// Type:
/// `∀ (n) (w : HCPoint n → Rat),
///    Fin.sum n (fun i => subsetSum n (fun S => ind (S i) · w S))
///      = subsetSum n (fun S => setSize n S · w S)`.
fn build_double_count_type(c: &DcConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let w_ty = c.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());

    // LHS: Fin.sum n (fun i => subsetSum n (coord_fn i))
    let lhs_summand = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let g = c.coord_fn(&ch, &n, &w, &i);
        let body = Expr::apps(c.subset_sum.clone(), [n.clone(), g]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let lhs = c.fin_sum(n.clone(), lhs_summand);

    // RHS: subsetSum n (size_fn)
    let rhs = Expr::apps(c.subset_sum.clone(), [n.clone(), c.size_fn(&b, &n, &w)]);

    let body = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(w_id, BinderInfo::Default, w_ty, body);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Proof:
/// `Eq.trans (Fin.sum_swap n (2^n) F) (Fin.sum_congr (2^n) … per_j)`.
fn build_double_count_proof(c: &DcConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let w_ty = c.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());

    let p2n = c.pow2(&n);
    let big_f = c.swap_fn(&b, &n, &w);

    // step1 : Σ_i Σ_j F i j = Σ_j Σ_i F i j   [Fin.sum_swap n (2^n) F]
    let step1 = Expr::apps(
        c.fin_sum_swap.clone(),
        [n.clone(), p2n.clone(), big_f.clone()],
    );

    // mid := Σ_j (Σ_i F i j)  — RHS of sum_swap.
    //   inner_swapped j := fun j => Fin.sum n (fun i => F i j)
    let inner_swapped = {
        let mut cj = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&p2n);
        let (j_id, j) = cj.fresh_local(fin_pow.clone());
        let row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            // F i j = ind ((hcDecode n j) i) · w (hcDecode n j)
            let s = c.decode(&n, &j);
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(c.ind_app(s_i), Expr::app(w.clone(), s));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let body = c.fin_sum(n.clone(), row);
        cj.finish_child(cj.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
    };

    // target_j := fun j => setSize n (hcDecode n j) · w (hcDecode n j)
    let target_j = {
        let mut cj = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&p2n);
        let (j_id, j) = cj.fresh_local(fin_pow.clone());
        let s = c.decode(&n, &j);
        let size = Expr::apps(c.set_size.clone(), [n.clone(), s.clone()]);
        let body = c.mul(size, Expr::app(w.clone(), s));
        cj.finish_child(cj.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
    };

    // per_j : fun (j : Fin (2^n)) =>
    //   Fin.sum_mul n (fun i => ind ((hcDecode n j) i)) (w (hcDecode n j))
    //   : Σ_i (ind (S i) · w S) = (Σ_i ind (S i)) · w S
    //   The RHS `(Σ_i ind (S i)) · w S` δ-folds to `setSize n S · w S`, so this
    //   inhabits `(inner_swapped j) = (target_j j)`.
    let per_j = {
        let mut cj = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&p2n);
        let (j_id, j) = cj.fresh_local(fin_pow.clone());
        let s = c.decode(&n, &j);
        // ind_fn := fun (i : Fin n) => ind (S i)
        let ind_fn = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let s_i = Expr::app(s.clone(), i.clone());
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, c.ind_app(s_i)))
        };
        let w_s = Expr::app(w.clone(), s.clone());
        let body = Expr::apps(c.fin_sum_mul.clone(), [n.clone(), ind_fn, w_s]);
        cj.finish_child(cj.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
    };

    // step2 : Σ_j (Σ_i F i j) = Σ_j (setSize n S · w S)
    //   [Fin.sum_congr (2^n) inner_swapped target_j per_j]
    let step2 = Expr::apps(
        c.fin_sum_congr.clone(),
        [p2n.clone(), inner_swapped.clone(), target_j.clone(), per_j],
    );

    // Whole chain: LHS  =(step1)= mid  =(step2)= RHS, via Eq.trans.
    // LHS δ-folds from `Σ_i Σ_j F i j`; RHS δ-folds to
    // `subsetSum n (fun S => setSize n S · w S)`.
    let lhs_summand = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let g = c.coord_fn(&ch, &n, &w, &i);
        let body = Expr::apps(c.subset_sum.clone(), [n.clone(), g]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let lhs = c.fin_sum(n.clone(), lhs_summand);
    let mid = c.fin_sum(p2n.clone(), inner_swapped);
    let rhs = Expr::apps(c.subset_sum.clone(), [n.clone(), c.size_fn(&b, &n, &w)]);

    let u1 = Level::succ(Level::zero());
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1]);
    let body = Expr::apps(eq_trans, [c.rat.clone(), lhs, mid, rhs, step1, step2]);

    let e = b.mk_lam(w_id, BinderInfo::Default, w_ty, body);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_set_size_is_reducible_definition() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_set_size().expect("register_set_size");
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.setSize"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("setSize value must check against its type");
    }

    #[test]
    fn test_subset_sum_double_count_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_double_count()
            .expect("register_subset_sum_double_count");
        let name = Name::from_string("BoolAnalysis.subsetSum_double_count");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_double_count proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "subsetSum_double_count must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_double_count's transitive axiom closure must be empty"
        );
    }
}
