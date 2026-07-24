// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.sum_smul` (scalar homogeneity of finite sums).
//!
//! `∀ (n : Nat) (c : Rat) (f : Fin n → Rat),
//!     Fin.sum n (fun i => Rat.mul c (f i)) = Rat.mul c (Fin.sum n f)`
//!
//! Induction over the faithful `Fin.sum` Nat.rec carrier.
//! - Base (`n = 0`): both `Fin.sum 0 _` ι-reduce to `Rat.zero`, so the goal is
//!   `Rat.zero = Rat.mul c Rat.zero`, closed by `Eq.symm (Rat.mul_zero c)`.
//! - Step (`n = k+1`): `Fin.sum (k+1) g` ι-reduces (`Fin.sum_succ`) to
//!   `Rat.add (Fin.sum k (g ∘ Fin.castSucc)) (g (Fin.last k))`. The scaled
//!   function commutes with the cast prefix (`(scaled c f) ∘ castSucc ≡
//!   scaled c (f ∘ castSucc)` definitionally), so the induction hypothesis at
//!   `(c, f ∘ castSucc)` rewrites the prefix; `Rat.left_distrib` then refactors
//!   `Rat.mul c P + Rat.mul c L` back into `Rat.mul c (P + L) = Rat.mul c
//!   (Fin.sum (k+1) f)`.
//!
//! Closure: `Nat.rec`, `Fin.castSucc`, `Fin.last`, `Rat.add`, `Rat.mul`,
//! `Rat.zero`, `Eq`/`Eq.trans`/`Eq.symm`/`congrArg`, and the constructive
//! `Rat.mul_zero` / `Rat.left_distrib` theorems — no domain axiom.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinSumSmulConsts {
    base: FinSumConsts,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    rat_mul_zero: Expr,
    rat_left_distrib: Expr,
}

impl FinSumSmulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            base: FinSumConsts::new(),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            rat_mul_zero: Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            rat_left_distrib: Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.base.rat_mul.clone(), a), b)
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.base.rat_add.clone(), a), b)
    }

    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.base.fin_sum.clone(), n), f)
    }

    fn eq_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.base.rat_eq(lhs, rhs)
    }

    fn fin_to_rat(&self, n: Expr) -> Expr {
        self.base.fin_to_rat(n)
    }

    fn eq_trans(&self, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.base.rat.clone(), a, b, d, h1, h2],
        )
    }

    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.base.rat.clone(), a, b, h])
    }

    /// `@congrArg Rat Rat a b g h : g a = g b`.
    fn congr_rat(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.base.rat.clone(), self.base.rat.clone(), a, b, g, h],
        )
    }
}

/// `fun (i : Fin n) => Rat.mul c (f i)` — the scaled summand function.
fn scaled_fn(cst: &FinSumSmulConsts, parent: &EnvDeclBuilder, n: Expr, c: Expr, f: Expr) -> Expr {
    let fin_n = Expr::app(cst.base.fin.clone(), n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = cst.mul(c, Expr::app(f, i));
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// `fun (i : Fin k) => f (Fin.castSucc k i)` — the cast prefix of `f`.
fn cast_succ_fn(cst: &FinSumSmulConsts, parent: &EnvDeclBuilder, k: Expr, f: Expr) -> Expr {
    let fin_k = Expr::app(cst.base.fin.clone(), k.clone());
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_k.clone());
    let cast_i = Expr::app(Expr::app(cst.fin_cast_succ.clone(), k), i);
    let body = Expr::app(f, cast_i);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_k, body);
    b.finish_child(lam)
}

/// `fun (x : Rat) => Rat.add x right` — used to `congrArg` the left summand.
fn add_right_fn(cst: &FinSumSmulConsts, parent: &EnvDeclBuilder, right: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(cst.base.rat.clone());
    let body = cst.add(x, right);
    let lam = b.mk_lam(x_id, BinderInfo::Default, cst.base.rat.clone(), body);
    b.finish_child(lam)
}

fn build_type(cst: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(cst.base.nat.clone());
    let (c_id, c) = b.fresh_local(cst.base.rat.clone());
    let f_type = cst.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let lhs = cst.sum(
        n.clone(),
        scaled_fn(cst, &b, n.clone(), c.clone(), f.clone()),
    );
    let rhs = cst.mul(c.clone(), cst.sum(n.clone(), f));
    let concl = cst.eq_rat(lhs, rhs);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_type, concl);
    let ty = b.mk_pi(c_id, BinderInfo::Default, cst.base.rat.clone(), ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, cst.base.nat.clone(), ty);
    b.finish(ty)
}

/// Motive: `fun (k : Nat) => ∀ (c : Rat) (f : Fin k → Rat),
///   Fin.sum k (scaled c f) = Rat.mul c (Fin.sum k f)`.
fn build_motive(cst: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(cst.base.nat.clone());
    let (c_id, c) = b.fresh_local(cst.base.rat.clone());
    let f_type = cst.fin_to_rat(k.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let lhs = cst.sum(
        k.clone(),
        scaled_fn(cst, &b, k.clone(), c.clone(), f.clone()),
    );
    let rhs = cst.mul(c.clone(), cst.sum(k.clone(), f));
    let body = cst.eq_rat(lhs, rhs);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_type, body);
    let pi_c = b.mk_pi(c_id, BinderInfo::Default, cst.base.rat.clone(), pi_f);
    let lam = b.mk_lam(k_id, BinderInfo::Default, cst.base.nat.clone(), pi_c);
    b.finish(lam)
}

/// Base case `motive 0`: `fun (c) (f : Fin 0 → Rat) =>
///   Eq.symm (Rat.mul_zero c)` at `Rat.zero = Rat.mul c Rat.zero`.
fn build_base(cst: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (c_id, c) = b.fresh_local(cst.base.rat.clone());
    let f_type = cst.fin_to_rat(cst.nat_zero.clone());
    let (f_id, _f) = b.fresh_local(f_type.clone());
    // Rat.mul_zero c : Rat.mul c Rat.zero = Rat.zero
    let mul_c_zero = cst.mul(c.clone(), cst.base.rat_zero.clone());
    let h = Expr::app(cst.rat_mul_zero.clone(), c.clone());
    // Eq.symm : Rat.zero = Rat.mul c Rat.zero
    let proof = cst.eq_symm(mul_c_zero, cst.base.rat_zero.clone(), h);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, proof);
    let val = b.mk_lam(c_id, BinderInfo::Default, cst.base.rat.clone(), val);
    b.finish(val)
}

/// Step case `motive k → motive (k+1)`.
fn build_step(cst: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(cst.base.nat.clone());

    // IH : ∀ (c) (f : Fin k → Rat), Fin.sum k (scaled c f) = Rat.mul c (Fin.sum k f)
    let ih_type = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let (c_id, c) = bb.fresh_local(cst.base.rat.clone());
        let f_type = cst.fin_to_rat(k.clone());
        let (f_id, f) = bb.fresh_local(f_type.clone());
        let lhs = cst.sum(
            k.clone(),
            scaled_fn(cst, &bb, k.clone(), c.clone(), f.clone()),
        );
        let rhs = cst.mul(c.clone(), cst.sum(k.clone(), f));
        let body = cst.eq_rat(lhs, rhs);
        let pi_f = bb.mk_pi(f_id, BinderInfo::Default, f_type, body);
        let pi_c = bb.mk_pi(c_id, BinderInfo::Default, cst.base.rat.clone(), pi_f);
        bb.finish_child(pi_c)
    };
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(cst.nat_succ.clone(), k.clone());
    let (c_id, c) = b.fresh_local(cst.base.rat.clone());
    let f_type_succ = cst.fin_to_rat(succ_k.clone());
    let (f_id, f) = b.fresh_local(f_type_succ.clone());

    // f_cast = fun i : Fin k => f (Fin.castSucc k i)
    let f_cast = cast_succ_fn(cst, &b, k.clone(), f.clone());
    // P = Fin.sum k f_cast ; L = f (Fin.last k)
    let prefix_sum = cst.sum(k.clone(), f_cast.clone());
    let last_val = Expr::app(f.clone(), Expr::app(cst.fin_last.clone(), k.clone()));

    // LHS (after ι on Fin.sum (k+1)):
    //   Fin.sum k ((scaled c f) ∘ castSucc) + (scaled c f)(last)
    //   ≡ Fin.sum k (scaled c f_cast) + Rat.mul c L     (definitionally)
    let scaled_prefix = cst.sum(
        k.clone(),
        scaled_fn(cst, &b, k.clone(), c.clone(), f_cast.clone()),
    );
    let mul_c_last = cst.mul(c.clone(), last_val.clone());
    let lhs = cst.add(scaled_prefix.clone(), mul_c_last.clone());

    // mid = Rat.mul c P + Rat.mul c L   (after IH rewrites the prefix)
    let mul_c_prefix = cst.mul(c.clone(), prefix_sum.clone());
    let mid = cst.add(mul_c_prefix.clone(), mul_c_last.clone());

    // RHS = Rat.mul c (Fin.sum (k+1) f) ≡ Rat.mul c (P + L)   (ι on Fin.sum_succ)
    let p_plus_l = cst.add(prefix_sum.clone(), last_val.clone());
    let rhs = cst.mul(c.clone(), p_plus_l.clone());

    // step1 : lhs = mid    via congrArg (· + Rat.mul c L) (IH c f_cast)
    let ih_app = Expr::app(Expr::app(ih.clone(), c.clone()), f_cast.clone());
    let step1_fn = add_right_fn(cst, &b, mul_c_last.clone());
    let step1 = cst.congr_rat(scaled_prefix, mul_c_prefix, step1_fn, ih_app);

    // step2 : mid = rhs    via Eq.symm (Rat.left_distrib c P L)
    //   Rat.left_distrib c P L : Rat.mul c (P + L) = Rat.mul c P + Rat.mul c L
    let distrib = Expr::apps(
        cst.rat_left_distrib.clone(),
        [c.clone(), prefix_sum.clone(), last_val.clone()],
    );
    let step2 = cst.eq_symm(rhs.clone(), mid.clone(), distrib);

    // proof : lhs = rhs
    let proof = cst.eq_trans(lhs, mid, rhs, step1, step2);

    let val = b.mk_lam(f_id, BinderInfo::Default, f_type_succ, proof);
    let val = b.mk_lam(c_id, BinderInfo::Default, cst.base.rat.clone(), val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, cst.base.nat.clone(), val);
    b.finish(val)
}

fn build_value(cst: &FinSumSmulConsts) -> Expr {
    let motive = build_motive(cst);
    let base = build_base(cst);
    let step = build_step(cst);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(cst.base.nat.clone());
    let body = Expr::apps(cst.nat_rec.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, cst.base.nat.clone(), body);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.sum_smul` as a kernel-checked theorem (TCB-shrink: was an
    /// admitted `Declaration::Axiom`).
    pub(crate) fn register_fin_sum_smul_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_smul");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(super::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        self.init_eq()?;
        self.init_rat_field_inst()?;

        let cst = FinSumSmulConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&cst),
            value: build_value(&cst),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_smul_is_theorem_and_axiom_free() {
        let mut env = Environment::new();
        env.init_fin_sum().expect("init_fin_sum");
        let info = env
            .get_const(&Name::from_string("Fin.sum_smul"))
            .expect("Fin.sum_smul registered");
        assert_eq!(
            info.kind,
            super::super::types::ConstantKind::Theorem,
            "Fin.sum_smul must be a kernel-checked Theorem, not an admitted Axiom"
        );
        // Its proof term type-checks against its declared type.
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Fin.sum_smul"), vec![]))
            .expect("Fin.sum_smul should type-check");
    }
}
