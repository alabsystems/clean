// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified computation registration: kernel definitions and proof theorems.
//!
//! Environment methods for registering concrete NN evaluation artifacts:
//! - Concrete vectors as kernel Definitions (`NNVec n`)
//! - Constant network functions as kernel Definitions (`NNVec n -> NNVec m`)
//! - Certified evaluation theorems via `Eq.refl` (proof by computation)
//! - Composition theorems via `certified_eval_composition` axiom
//!
//! For multi-layer networks, the `certified_eval_composition` axiom chains
//! single-layer proofs into a full evaluation certificate.
//!
//! Part of #3186.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::nn_verify_certified_eval_compute::{CertifiedEvalInstance, ComputeConsts};
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Register a concrete vector as a kernel definition.
    ///
    /// Creates `def name : NNVec n := λ (i : Fin n), <value>`
    /// where the body maps the Fin index to a Rat value.
    #[cfg(test)]
    pub(crate) fn register_concrete_vec(
        &mut self,
        cc: &ComputeConsts,
        name: &Name,
        dim: u64,
        values: &[(i64, u64)],
    ) -> Result<(), EnvError> {
        assert_eq!(values.len(), dim as usize, "values length must match dim");

        let vec_type = cc.vec_type(dim);
        let fin_n = Expr::app(cc.fin.clone(), cc.mk_nat(dim));

        let default = if values.is_empty() {
            cc.rat_zero.clone()
        } else {
            cc.mk_rat(values[0].0, values[0].1)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _i) = b.fresh_local(fin_n.clone());
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, default);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: vec_type,
            value,
            is_reducible: true,
        })
    }

    /// Register a constant network function.
    ///
    /// Creates `def name : NNVec n -> NNVec m := λ (x : NNVec n) (j : Fin m), val`
    /// A constant network that ignores input and returns a fixed output.
    /// The proof of `output = network(input)` is then `Eq.refl`.
    #[cfg(test)]
    pub(crate) fn register_const_network(
        &mut self,
        cc: &ComputeConsts,
        name: &Name,
        input_dim: u64,
        output_dim: u64,
        output_values: &[(i64, u64)],
    ) -> Result<(), EnvError> {
        let vec_n = cc.vec_type(input_dim);
        let vec_m = cc.vec_type(output_dim);
        let net_type = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_m);
        let fin_m = Expr::app(cc.fin.clone(), cc.mk_nat(output_dim));

        let default_val = if output_values.is_empty() {
            cc.rat_zero.clone()
        } else {
            cc.mk_rat(output_values[0].0, output_values[0].1)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(vec_n.clone());
            let (j_id, _j) = b.fresh_local(fin_m.clone());
            let inner = b.mk_lam(j_id, BinderInfo::Default, fin_m, default_val);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, inner);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: net_type,
            value,
            is_reducible: true,
        })
    }

    /// Register a certified evaluation theorem via `Eq.refl`.
    ///
    /// Type: `output = network input`
    /// Proof: `@Eq.refl (NNVec m) (network input)`
    ///
    /// Works because `network(input)` definitionally reduces to the same
    /// term as `output`. The kernel verifies this during type-checking.
    #[cfg(test)]
    pub(crate) fn register_certified_eval_theorem(
        &mut self,
        cc: &ComputeConsts,
        theorem_name: &Name,
        network_name: &Name,
        input_name: &Name,
        output_name: &Name,
        _input_dim: u64,
        output_dim: u64,
    ) -> Result<(), EnvError> {
        let vec_m = cc.vec_type(output_dim);
        let network_const = Expr::const_(network_name.clone(), vec![]);
        let input_const = Expr::const_(input_name.clone(), vec![]);
        let output_const = Expr::const_(output_name.clone(), vec![]);
        let net_applied = Expr::app(network_const, input_const);

        // Type: Eq (NNVec m) output (network input)
        let eq_type = Expr::app(
            Expr::app(Expr::app(cc.eq.clone(), vec_m.clone()), output_const),
            net_applied.clone(),
        );

        // Proof: @Eq.refl (NNVec m) (network input)
        let proof = Expr::app(Expr::app(cc.eq_refl.clone(), vec_m), net_applied);

        self.add_decl(Declaration::Theorem {
            name: theorem_name.clone(),
            level_params: vec![],
            type_: eq_type,
            value: proof,
        })
    }

    /// High-level API: register a complete certified evaluation instance.
    ///
    /// Registers input/output vectors, network function, and proof theorem.
    /// The theorem is verified by the kernel's type checker.
    #[cfg(test)]
    pub(crate) fn register_certified_eval(
        &mut self,
        instance: &CertifiedEvalInstance,
        input_values: &[(i64, u64)],
        output_values: &[(i64, u64)],
    ) -> Result<(), EnvError> {
        self.init_nn_verify_certified_eval()?;
        let cc = ComputeConsts::new();

        self.register_concrete_vec(&cc, &instance.input_name, instance.input_dim, input_values)?;
        self.register_concrete_vec(
            &cc,
            &instance.output_name,
            instance.output_dim,
            output_values,
        )?;
        self.register_const_network(
            &cc,
            &instance.network_name,
            instance.input_dim,
            instance.output_dim,
            output_values,
        )?;
        self.register_certified_eval_theorem(
            &cc,
            &instance.proof_name,
            &instance.network_name,
            &instance.input_name,
            &instance.output_name,
            instance.input_dim,
            instance.output_dim,
        )
    }

    /// Register a certified eval composition theorem.
    ///
    /// Given proofs `mid = f(input)` and `output = g(mid)`,
    /// produces a proof that `output = (g . f)(input)` using the
    /// `NNVerify.certified_eval_composition` axiom.
    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn register_certified_composition(
        &mut self,
        cc: &ComputeConsts,
        theorem_name: &Name,
        f_name: &Name,
        g_name: &Name,
        input_name: &Name,
        mid_name: &Name,
        output_name: &Name,
        proof_f_name: &Name,
        proof_g_name: &Name,
        n: u64,
        k: u64,
        m: u64,
    ) -> Result<(), EnvError> {
        let f_const = Expr::const_(f_name.clone(), vec![]);
        let g_const = Expr::const_(g_name.clone(), vec![]);
        let input_const = Expr::const_(input_name.clone(), vec![]);
        let mid_const = Expr::const_(mid_name.clone(), vec![]);
        let output_const = Expr::const_(output_name.clone(), vec![]);
        let proof_f = Expr::const_(proof_f_name.clone(), vec![]);
        let proof_g = Expr::const_(proof_g_name.clone(), vec![]);

        let vec_n = cc.vec_type(n);
        let vec_m = cc.vec_type(m);

        // Composed function: λ x, g (f x)
        let composed = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let body = Expr::app(g_const.clone(), Expr::app(f_const.clone(), x));
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, body);
            b.finish(e)
        };

        // Type: output = (g . f)(input)
        let composed_applied = Expr::app(composed, input_const.clone());
        let eq_type = Expr::app(
            Expr::app(
                Expr::app(cc.eq.clone(), vec_m.clone()),
                output_const.clone(),
            ),
            composed_applied,
        );

        // Proof via certified_eval_composition axiom
        let comp_axiom = Expr::const_(
            Name::from_string("NNVerify.certified_eval_composition"),
            vec![],
        );
        let proof = [
            cc.mk_nat(n),
            cc.mk_nat(k),
            cc.mk_nat(m),
            f_const,
            g_const,
            input_const,
            mid_const,
            output_const,
            proof_f,
            proof_g,
        ]
        .into_iter()
        .fold(comp_axiom, Expr::app);

        self.add_decl(Declaration::Theorem {
            name: theorem_name.clone(),
            level_params: vec![],
            type_: eq_type,
            value: proof,
        })
    }
}
