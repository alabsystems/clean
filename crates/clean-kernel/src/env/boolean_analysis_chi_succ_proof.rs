// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.chi_succ` — the character coordinate
//! peel: a parity character on the `(n+1)`-cube factors as its `n`-cube
//! restriction (drop the top coordinate) times the top-coordinate factor.
//!
//! ```text
//! chi_succ : ∀ (n : Nat) (S x : HCPoint (n+1)),
//!   @Eq Rat (chi (n+1) S x)
//!           (Rat.mul (chi n (fun i => S (Fin.castSucc n i))
//!                            (fun i => x (Fin.castSucc n i)))
//!                    (factor (S (Fin.last n)) (x (Fin.last n))))
//! ```
//!
//! where `factor sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb` is the
//! per-coordinate `chi` factor.
//!
//! Proof: `chi (n+1) S x` δ-unfolds (chi is a reducible Definition) to
//! `Fin.prod (n+1) (factor_fn S x)` where
//! `factor_fn S x := fun (j : Fin (n+1)) => factor (S j) (x j)`. The landed
//! constructive `Fin.prod_succ` peels that to
//! `Rat.mul (Fin.prod n (fun i => factor_fn S x (Fin.castSucc n i))) (factor_fn S x (Fin.last n))`.
//! The prefix `Fin.prod n (fun i => factor (S (castSucc n i)) (x (castSucc n i)))`
//! is byte-for-byte `chi n (S∘castSucc) (x∘castSucc)` after δ-unfolding the inner
//! `chi`, and the top factor is `factor (S (last n)) (x (last n))`. So the RHS of
//! `Fin.prod_succ` is def-eq to the claimed RHS, and `Fin.prod_succ n (factor_fn
//! S x)` is exactly the proof (the kernel accepts the def-eq massage).
//!
//! This is the inductive peel the off-diagonal `E[χ_U] = 0` argument consumes:
//! it separates the top coordinate `n` (where the ±1 halves of the cube split
//! cancel) from the lower-coordinate character that the induction hypothesis
//! governs. Kernel-checked, `ProofQuality::Constructive` (closure ⊆ {`Fin.prod_succ`}
//! ∪ Eq built-ins — axiom-free).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct ChiSuccConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_two: Expr,
    fin_prod: Expr,
    fin_prod_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_succ: Expr,
    bool_rec: Expr,
    chi: Expr,
    eq1: Expr,
}

impl ChiSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational 2, matching chi's body.
        let rat_two = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), two),
                nat_one,
            ],
        );
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_two,
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            fin_prod_succ: Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_succ,
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n, s, x])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn prod(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n, g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }

    /// `fun (_ : Bool) => Rat` — the Type-valued motive for chi's `Bool.rec`.
    fn bool_to_rat_motive(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, _t) = mb.fresh_local(self.bool_.clone());
        let lam = mb.mk_lam(
            t_id,
            BinderInfo::Default,
            self.bool_.clone(),
            self.rat.clone(),
        );
        mb.finish_child(lam)
    }

    /// `factor sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb`,
    /// byte-for-byte the per-coordinate factor `register_chi` builds.
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        let embed = Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_zero.clone(),
                self.rat_one.clone(),
                xb,
            ],
        );
        let two_embed = Expr::apps(self.rat_mul.clone(), [self.rat_two.clone(), embed]);
        let signed = Expr::apps(self.rat_sub.clone(), [self.rat_one.clone(), two_embed]);
        Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_to_rat_motive(parent),
                self.rat_one.clone(),
                signed,
                sb,
            ],
        )
    }

    /// `factor_fn S x := fun (j : Fin m) => factor (S j) (x j)`, the chi product
    /// integrand on `Fin m` (matches `register_chi`'s inner lambda).
    fn factor_fn(&self, parent: &EnvDeclBuilder, m: &Expr, s: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let (j_id, j) = b.fresh_local(fin_m.clone());
        let s_j = Expr::app(s.clone(), j.clone());
        let x_j = Expr::app(x.clone(), j.clone());
        let gated = self.factor(&b, s_j, x_j);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_m, gated))
    }

    /// `fun (i : Fin n) => p (Fin.castSucc n i)` — restrict a `HCPoint (n+1)`
    /// indicator/point to its first `n` coordinates.
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cast_i = Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i]);
        let body = Expr::app(p.clone(), cast_i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

fn build_type(c: &ChiSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    // LHS: chi (n+1) S x
    let lhs = c.chi(sn.clone(), s.clone(), x.clone());

    // RHS prefix: chi n (S∘castSucc) (x∘castSucc)
    let s_res = c.restrict(&b, &n, &s);
    let x_res = c.restrict(&b, &n, &x);
    let chi_pre = c.chi(n.clone(), s_res, x_res);

    // RHS top factor: factor (S (last n)) (x (last n))
    let last_n = Expr::apps(c.fin_last.clone(), [n.clone()]);
    let s_last = Expr::app(s.clone(), last_n.clone());
    let x_last = Expr::app(x.clone(), last_n);
    let top = c.factor(&b, s_last, x_last);

    let rhs = c.mul(chi_pre, top);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &ChiSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    // Fin.prod_succ n (factor_fn (n+1) S x)
    //   : Fin.prod (n+1) (factor_fn S x)
    //       = Rat.mul (Fin.prod n (fun i => factor_fn S x (castSucc n i)))
    //                 (factor_fn S x (last n))
    // The LHS is def-eq to `chi (n+1) S x` (chi δ-unfolds to Fin.prod (n+1) ...);
    // the RHS is def-eq to the claimed `Rat.mul (chi n …) (factor …)`. So this
    // proof term has the goal type up to def-eq.
    let factor_fn = c.factor_fn(&b, &sn, &s, &x);
    let proof = Expr::apps(c.fin_prod_succ.clone(), [n.clone(), factor_fn]);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_succ` as a kernel-checked, constructive
    /// theorem. Idempotent.
    pub(crate) fn register_chi_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_fin_prod_succ_theorem()?;

        let c = ChiSuccConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_chi_succ_theorem()
            .expect("register_chi_succ_theorem");
        env
    }

    /// `chi_succ` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof term
    /// re-checks under C1.
    #[test]
    fn test_chi_succ_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.chi_succ"))
            .expect("chi_succ should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "chi_succ must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_succ proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string("BoolAnalysis.chi_succ")),
            Some(ProofQuality::Constructive),
            "chi_succ must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string("BoolAnalysis.chi_succ"))
                .expect("deps")
                .is_empty(),
            "chi_succ's transitive axiom closure must be empty"
        );
    }
}
