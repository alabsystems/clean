// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified computation mode: kernel-verified eval on concrete inputs.
//!
//! Registers axioms and theorems for certified evaluation of neural networks.
//! Given a network and concrete input, certified evaluation produces an output
//! together with a kernel-verifiable proof that the output is correct.
//!
//! ## Axioms
//!
//! - **`eval_trace_sound`**: If an eval trace is verified, the final output
//!   equals the network applied to the input. This is the fundamental
//!   soundness guarantee of certified evaluation.
//!
//! - **`eval_certificate_complete`**: Every correct evaluation has a
//!   verifiable certificate. Completeness ensures we can always produce
//!   a proof for correct evaluations.
//!
//! - **`eval_deterministic`**: The same input always produces the same
//!   output (functional correctness of network evaluation).
//!
//! - **`certified_eval_composition`**: Composing certified evaluations
//!   for chained networks yields a certified evaluation of the composite.
//!
//! - **`eval_within_bounds`**: If input lies within IBP bounds, the
//!   output lies within the IBP output bounds. This connects certified
//!   eval to the IBP verification pipeline.
//!
//! Part of #3186.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::nn_verify_certified_eval_defs::CertEvalConsts;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Initialize certified evaluation definitions and axioms.
    ///
    /// Depends on: `init_nn_verify_types()`, `init_eq()`, `init_list()`.
    #[cfg(test)]
    pub(crate) fn init_nn_verify_certified_eval(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_certified_eval_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_eq()?;
        self.init_list()?;

        let c = CertEvalConsts::new();

        // Definitions
        self.register_concrete_input(&c)?;
        self.register_concrete_output(&c)?;
        self.register_eval_trace(&c)?;
        self.register_eval_certificate(&c)?;
        self.register_eval_matches_spec(&c)?;

        // Axioms / Theorems
        self.register_eval_trace_sound(&c)?;
        self.register_eval_certificate_complete(&c)?;
        self.register_eval_deterministic(&c)?;
        self.register_certified_eval_composition(&c)?;
        self.register_eval_within_bounds(&c)?;

        self.nn_verify_certified_eval_init = true;
        Ok(())
    }

    /// Register `NNVerify.eval_trace_sound`:
    /// ```text
    /// axiom eval_trace_sound (n m layers : Nat)
    ///   (network : NNVec n -> NNVec m)
    ///   (input : NNVec n)
    ///   (output : NNVec m)
    ///   (trace : eval_trace layers n)
    ///   (cert : eval_certificate layers n) :
    ///   output = network input
    /// ```
    ///
    /// If the eval trace and certificate are verified, the output equals
    /// the network applied to the input.
    #[cfg(test)]
    fn register_eval_trace_sound(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (layers_id, layers) = b.fresh_local(c.nat.clone());

            let vec_n = c.vec_of(n.clone());
            let vec_m = c.vec_of(m.clone());
            // network : NNVec n -> NNVec m
            let net_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_m.clone());
            let (net_id, network) = b.fresh_local(net_ty.clone());
            let (input_id, input) = b.fresh_local(vec_n.clone());
            let (output_id, output) = b.fresh_local(vec_m.clone());
            // trace : eval_trace layers n
            let trace_ty = Expr::app(Expr::app(c.eval_trace.clone(), layers.clone()), n.clone());
            let (trace_id, _trace) = b.fresh_local(trace_ty.clone());
            // cert : eval_certificate layers n
            let cert_ty = Expr::app(
                Expr::app(c.eval_certificate.clone(), layers.clone()),
                n.clone(),
            );
            let (cert_id, _cert) = b.fresh_local(cert_ty.clone());

            // conclusion: output = network input
            let net_applied = Expr::app(network, input);
            let conclusion = c.mk_eq(vec_m.clone(), output, net_applied);

            let r = b.mk_pi(cert_id, BinderInfo::Default, cert_ty, conclusion);
            let r = b.mk_pi(trace_id, BinderInfo::Default, trace_ty, r);
            let r = b.mk_pi(output_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(input_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(net_id, BinderInfo::Default, net_ty, r);
            let r = b.mk_pi(layers_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.eval_trace_sound"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.eval_certificate_complete`:
    /// ```text
    /// axiom eval_certificate_complete (n m layers : Nat)
    ///   (network : NNVec n -> NNVec m)
    ///   (input : NNVec n)
    ///   (output : NNVec m)
    ///   (h : output = network input) :
    ///   eval_certificate layers n
    /// ```
    ///
    /// Every correct evaluation has a verifiable certificate.
    #[cfg(test)]
    fn register_eval_certificate_complete(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (layers_id, layers) = b.fresh_local(c.nat.clone());

            let vec_n = c.vec_of(n.clone());
            let vec_m = c.vec_of(m.clone());
            let net_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_m.clone());
            let (net_id, network) = b.fresh_local(net_ty.clone());
            let (input_id, input) = b.fresh_local(vec_n.clone());
            let (output_id, output) = b.fresh_local(vec_m.clone());

            // h : output = network input
            let net_applied = Expr::app(network, input);
            let eq_prop = c.mk_eq(vec_m.clone(), output, net_applied);
            let (h_id, _h) = b.fresh_local(eq_prop.clone());

            // conclusion: eval_certificate layers n
            let cert_ty = Expr::app(Expr::app(c.eval_certificate.clone(), layers), n);

            let r = b.mk_pi(h_id, BinderInfo::Default, eq_prop, cert_ty);
            let r = b.mk_pi(output_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(input_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(net_id, BinderInfo::Default, net_ty, r);
            let r = b.mk_pi(layers_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.eval_certificate_complete"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.eval_deterministic`:
    /// ```text
    /// axiom eval_deterministic (n m : Nat)
    ///   (network : NNVec n -> NNVec m)
    ///   (input : NNVec n)
    ///   (out1 out2 : NNVec m)
    ///   (h1 : out1 = network input)
    ///   (h2 : out2 = network input) :
    ///   out1 = out2
    /// ```
    ///
    /// Same input always produces the same output (functional correctness).
    #[cfg(test)]
    fn register_eval_deterministic(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());

            let vec_n = c.vec_of(n);
            let vec_m = c.vec_of(m);
            let net_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_m.clone());
            let (net_id, network) = b.fresh_local(net_ty.clone());
            let (input_id, input) = b.fresh_local(vec_n.clone());
            let (out1_id, out1) = b.fresh_local(vec_m.clone());
            let (out2_id, out2) = b.fresh_local(vec_m.clone());

            // h1 : out1 = network input
            let net_input = Expr::app(network.clone(), input.clone());
            let h1_ty = c.mk_eq(vec_m.clone(), out1.clone(), net_input.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            // h2 : out2 = network input
            let h2_ty = c.mk_eq(vec_m.clone(), out2.clone(), net_input);
            let (h2_id, _h2) = b.fresh_local(h2_ty.clone());

            // conclusion: out1 = out2
            let conclusion = c.mk_eq(vec_m.clone(), out1, out2);

            let r = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, conclusion);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_pi(out2_id, BinderInfo::Default, vec_m.clone(), r);
            let r = b.mk_pi(out1_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(input_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(net_id, BinderInfo::Default, net_ty, r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.eval_deterministic"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.certified_eval_composition`:
    /// ```text
    /// axiom certified_eval_composition (n k m : Nat)
    ///   (f : NNVec n -> NNVec k)
    ///   (g : NNVec k -> NNVec m)
    ///   (input : NNVec n)
    ///   (mid : NNVec k)
    ///   (output : NNVec m)
    ///   (hf : mid = f input)
    ///   (hg : output = g mid) :
    ///   output = (fun x => g (f x)) input
    /// ```
    ///
    /// Composing certified evals for chained networks is certified.
    #[cfg(test)]
    fn register_certified_eval_composition(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());

            let vec_n = c.vec_of(n);
            let vec_k = c.vec_of(k);
            let vec_m = c.vec_of(m);

            // f : NNVec n -> NNVec k
            let f_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_k.clone());
            let (f_id, f_net) = b.fresh_local(f_ty.clone());
            // g : NNVec k -> NNVec m
            let g_ty = Expr::pi(BinderInfo::Default, vec_k.clone(), vec_m.clone());
            let (g_id, g_net) = b.fresh_local(g_ty.clone());

            let (input_id, input) = b.fresh_local(vec_n.clone());
            let (mid_id, mid) = b.fresh_local(vec_k.clone());
            let (output_id, output) = b.fresh_local(vec_m.clone());

            // hf : mid = f input
            let f_input = Expr::app(f_net.clone(), input.clone());
            let hf_ty = c.mk_eq(vec_k.clone(), mid.clone(), f_input.clone());
            let (hf_id, _hf) = b.fresh_local(hf_ty.clone());
            // hg : output = g mid
            let g_mid = Expr::app(g_net.clone(), mid);
            let hg_ty = c.mk_eq(vec_m.clone(), output.clone(), g_mid);
            let (hg_id, _hg) = b.fresh_local(hg_ty.clone());

            // conclusion: output = g (f input)
            let composed = Expr::app(g_net, f_input);
            let conclusion = c.mk_eq(vec_m.clone(), output, composed);

            let r = b.mk_pi(hg_id, BinderInfo::Default, hg_ty, conclusion);
            let r = b.mk_pi(hf_id, BinderInfo::Default, hf_ty, r);
            let r = b.mk_pi(output_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(mid_id, BinderInfo::Default, vec_k, r);
            let r = b.mk_pi(input_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.certified_eval_composition"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.eval_within_bounds`:
    /// ```text
    /// axiom eval_within_bounds (n m : Nat)
    ///   (network : NNVec n -> NNVec m)
    ///   (input_bounds : IntervalBounds n)
    ///   (output_bounds : IntervalBounds m)
    ///   (input : NNVec n)
    ///   (h_in : IntervalBounds.contains n input_bounds input)
    ///   (h_out_eq : network input = output)
    ///   (h_bounds : forall x, contains n input_bounds x ->
    ///               contains m output_bounds (network x)) :
    ///   IntervalBounds.contains m output_bounds output
    /// ```
    ///
    /// If input is within IBP bounds and the network maps all bounded
    /// inputs to bounded outputs, then the concrete output is within bounds.
    #[cfg(test)]
    fn register_eval_within_bounds(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());

            let vec_n = c.vec_of(n.clone());
            let vec_m = c.vec_of(m.clone());

            // network : NNVec n -> NNVec m
            let net_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_m.clone());
            let (net_id, network) = b.fresh_local(net_ty.clone());

            let ib_n = c.ib_of(n.clone());
            let ib_m = c.ib_of(m.clone());
            let (in_bounds_id, in_bounds) = b.fresh_local(ib_n.clone());
            let (out_bounds_id, out_bounds) = b.fresh_local(ib_m.clone());
            let (input_id, input) = b.fresh_local(vec_n.clone());
            let (output_id, output) = b.fresh_local(vec_m.clone());

            // h_in : contains n input_bounds input
            let h_in_ty = c.contains(n.clone(), in_bounds.clone(), input.clone());
            let (h_in_id, _h_in) = b.fresh_local(h_in_ty.clone());

            // h_out_eq : network input = output
            let net_input = Expr::app(network.clone(), input);
            let h_out_eq_ty = c.mk_eq(vec_m.clone(), net_input, output.clone());
            let (h_out_eq_id, _h_out_eq) = b.fresh_local(h_out_eq_ty.clone());

            // h_bounds : forall x, contains n input_bounds x ->
            //            contains m output_bounds (network x)
            let h_bounds_ty = {
                let mut bh = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bh.fresh_local(vec_n.clone());
                let contains_x = c.contains(n.clone(), in_bounds.clone(), x.clone());
                let net_x = Expr::app(network, x);
                let contains_out = c.contains(m.clone(), out_bounds.clone(), net_x);
                let (hx_id, _hx) = bh.fresh_local(contains_x.clone());
                let inner = bh.mk_pi(hx_id, BinderInfo::Default, contains_x, contains_out);
                let r = bh.mk_pi(x_id, BinderInfo::Default, vec_n.clone(), inner);
                bh.finish_child(r)
            };
            let (h_bounds_id, _h_bounds) = b.fresh_local(h_bounds_ty.clone());

            // conclusion: contains m output_bounds output
            let conclusion = c.contains(m, out_bounds, output);

            let r = b.mk_pi(h_bounds_id, BinderInfo::Default, h_bounds_ty, conclusion);
            let r = b.mk_pi(h_out_eq_id, BinderInfo::Default, h_out_eq_ty, r);
            let r = b.mk_pi(h_in_id, BinderInfo::Default, h_in_ty, r);
            let r = b.mk_pi(output_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(input_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(out_bounds_id, BinderInfo::Default, ib_m, r);
            let r = b.mk_pi(in_bounds_id, BinderInfo::Default, ib_n, r);
            let r = b.mk_pi(net_id, BinderInfo::Default, net_ty, r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.eval_within_bounds"),
            level_params: vec![],
            type_: ty,
        })
    }
}
