// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.chi_mul_chi` — the cube-tensor
//! factorization that merges two parity characters at a point into a single
//! `Fin.prod` of per-coordinate products.
//!
//! `chi_mul_chi : ∀ (n : Nat) (S T x : HCPoint n),`
//! `  Rat.mul (chi n S x) (chi n T x)`
//! `    = Fin.prod n (fun i => Rat.mul (factor S x i) (factor T x i))`
//!
//! where `factor S x i = @Bool.rec (fun _ => Rat) Rat.one (signed (x i)) (S i)`
//! is the per-coordinate `chi` factor (`signed (x i) = 1 - 2·⟦x i⟧`).
//!
//! Proof: `chi n S x` δ-unfolds (it is a reducible Definition) to
//! `Fin.prod n (factor S x)`, so `Rat.mul (chi n S x) (chi n T x)` is
//! definitionally `Rat.mul (Fin.prod n (factor S x)) (Fin.prod n (factor T x))`.
//! The landed constructive `Fin.prod_mul` gives
//! `Fin.prod n (fun i => factor S x i · factor T x i)`
//! `  = Fin.prod n (factor S x) · Fin.prod n (factor T x)`,
//! so `Eq.symm (Fin.prod_mul n (factor S x) (factor T x))` is exactly the
//! (def-eq) proof of the goal. No induction needed here — the induction lives
//! inside the already-landed `Fin.prod_mul`.
//!
//! This is the first reusable building block on the orthonormality path: it
//! moves `χ_S·χ_T` from "product of two characters" into "single product whose
//! per-coordinate factor a later step sums over `x_i ∈ {0,1}`". Kernel-checked,
//! `ProofQuality::Constructive` (closure ⊆ {`Fin.prod_mul`, `Eq.symm`}, both
//! axiom-free).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the `chi_mul_chi` proof.
struct ChiMulConsts {
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
    fin_prod_mul: Expr,
    bool_rec: Expr,
    eq_symm: Expr,
}

impl ChiMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ, nat_one.clone());
        // `Rat.mk (Int.ofNat 2) 1` — the rational constant 2, matching `chi`'s body.
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
            fin_prod_mul: Expr::const_(Name::from_string("Fin.prod_mul"), vec![]),
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
        }
    }

    /// `Fin n`.
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// `BoolAnalysis.HCPoint n`.
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }

    /// `BoolAnalysis.chi n S x`.
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            [n, s, x],
        )
    }

    /// `Rat.mul a b`.
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    /// `Fin.prod n g`.
    fn prod(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n, g])
    }

    /// `@Eq Rat lhs rhs`.
    fn eq_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.rat.clone(), lhs, rhs],
        )
    }

    /// `fun (_ : Bool) => Rat` — the shared `Bool.rec` motive (universe 1).
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

    /// The per-coordinate `chi` factor function `factor S x`:
    /// `fun (i : Fin n) =>`
    /// `  @Bool.rec (fun _ => Rat) Rat.one`
    /// `    (Rat.sub Rat.one (Rat.mul 2 (@Bool.rec (fun _ => Rat) Rat.zero Rat.one (x i))))`
    /// `    (S i)`.
    ///
    /// This is byte-for-byte the inner factor `register_chi` builds, so
    /// `Fin.prod n (factor S x)` is def-eq to `chi n S x`.
    fn factor_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());

        // ⟦x i⟧ = @Bool.rec (fun _ => Rat) Rat.zero Rat.one (x i)
        let x_i = Expr::app(x.clone(), i.clone());
        let embed = Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_to_rat_motive(&b),
                self.rat_zero.clone(),
                self.rat_one.clone(),
                x_i,
            ],
        );
        // 1 - 2·⟦x i⟧
        let two_embed = Expr::apps(self.rat_mul.clone(), [self.rat_two.clone(), embed]);
        let signed = Expr::apps(self.rat_sub.clone(), [self.rat_one.clone(), two_embed]);

        // @Bool.rec (fun _ => Rat) Rat.one <signed> (S i)
        let s_i = Expr::app(s.clone(), i.clone());
        let gated = Expr::apps(
            self.bool_rec.clone(),
            [
                self.bool_to_rat_motive(&b),
                self.rat_one.clone(),
                signed,
                s_i,
            ],
        );
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, gated);
        b.finish_child(lam)
    }
}

/// `fun (i : Fin n) => Rat.mul (factor S x i) (factor T x i)` — the pointwise
/// product of the two characters' per-coordinate factors. Built by β-applying
/// the two factor lambdas to `i`, exactly the `fun i => a i · b i` shape
/// `Fin.prod_mul`'s LHS produces.
fn pointwise_factor_mul(
    c: &ChiMulConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    s: &Expr,
    t: &Expr,
    x: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let factor_s = c.factor_fn(&b, n, s, x);
    let factor_t = c.factor_fn(&b, n, t, x);
    let body = c.mul(Expr::app(factor_s, i.clone()), Expr::app(factor_t, i));
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

fn build_type(c: &ChiMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let lhs = c.mul(
        c.chi(n.clone(), s.clone(), x.clone()),
        c.chi(n.clone(), t.clone(), x.clone()),
    );
    let rhs = c.prod(n.clone(), pointwise_factor_mul(c, &b, &n, &s, &t, &x));
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &ChiMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let factor_s = c.factor_fn(&b, &n, &s, &x);
    let factor_t = c.factor_fn(&b, &n, &t, &x);

    // Fin.prod_mul n (factor S x) (factor T x)
    //   : Fin.prod n (fun i => factor S x i · factor T x i)
    //       = Fin.prod n (factor S x) · Fin.prod n (factor T x)
    let prod_mul = Expr::apps(
        c.fin_prod_mul.clone(),
        [n.clone(), factor_s.clone(), factor_t.clone()],
    );

    let pointwise = c.prod(n.clone(), pointwise_factor_mul(c, &b, &n, &s, &t, &x));
    let prod_prod = c.mul(c.prod(n.clone(), factor_s), c.prod(n.clone(), factor_t));

    // Eq.symm flips `pointwise = prod·prod` into `prod·prod = pointwise`.
    // The kernel accepts the LHS `prod·prod` as def-eq to `chi S x · chi T x`.
    let proof = Expr::apps(
        c.eq_symm.clone(),
        [c.rat.clone(), pointwise, prod_prod, prod_mul],
    );

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_mul_chi` as a kernel-checked, constructive
    /// theorem.
    ///
    /// `∀ (n : Nat) (S T x : HCPoint n),`
    /// `  chi n S x * chi n T x = Fin.prod n (fun i => factor S x i * factor T x i)`.
    ///
    /// Depends on `BoolAnalysis.chi` / `Fin.prod` (the Stage-1 foundations) and
    /// the landed constructive `Fin.prod_mul`. Idempotent.
    pub(crate) fn register_chi_mul_chi_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_mul_chi");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_fin_prod_mul_theorem()?;

        let c = ChiMulConsts::new();
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
        env
    }

    /// `chi_mul_chi` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof
    /// term re-checks under C1.
    #[test]
    fn test_chi_mul_chi_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.chi_mul_chi"))
            .expect("chi_mul_chi should be registered by init_boolean_analysis");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "chi_mul_chi must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_mul_chi proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string("BoolAnalysis.chi_mul_chi")),
            Some(ProofQuality::Constructive),
            "chi_mul_chi must be Constructive (no admitted-axiom dependency)"
        );
        assert!(
            env.axiom_deps(&Name::from_string("BoolAnalysis.chi_mul_chi"))
                .expect("deps")
                .is_empty(),
            "chi_mul_chi's transitive axiom closure must be empty"
        );
    }
}
