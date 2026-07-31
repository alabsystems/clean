// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for feasible interpolation formalization.
//!
//! Registers the foundational types and definitions needed to state
//! Pudlak's feasible interpolation theorem and its consequences for
//! proof complexity lower bounds.
//!
//! Feasible interpolation (Krajicek 1997, Pudlak 1997): resolution proofs
//! yield interpolants computable in polynomial time from the proof. This
//! connects proof complexity to circuit complexity, enabling lower bounds
//! on proof length via monotone circuit lower bounds (Razborov 1985).
//!
//! Key result chain:
//! 1. Resolution proofs -> feasible interpolants (Pudlak)
//! 2. Feasible interpolants -> monotone circuits (structural)
//! 3. Monotone circuit lower bounds (Razborov) -> resolution lower bounds
//! 4. DAG-like vs tree-like separation (exponential gap)
//!
//! Type and operation definitions live here; theorem registrations are in
//! `feasible_interpolation_theorems.rs`.
//!
//! Reference: Pudlak (1997), "Lower bounds for resolution and cutting plane
//!            proofs and monotone computations";
//!            Razborov (1985), "Lower bounds on the monotone complexity of
//!            some Boolean functions";
//!            Krajicek (1997), "Interpolation theorems, lower bounds for
//!            proof systems, and independence results for bounded arithmetic".

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants used across all feasible interpolation declarations.
#[cfg(test)]
pub(super) struct FeasibleInterpolationConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.PropFormula : Type (from craig_interpolation)
    pub(super) prop_formula: Expr,
    /// ProofTheory.Resolution.Proof : Type (from craig_interpolation)
    pub(super) res_proof: Expr,
}

#[cfg(test)]
impl FeasibleInterpolationConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop_formula: Expr::const_(Name::from_string("ProofTheory.PropFormula"), vec![]),
            res_proof: Expr::const_(Name::from_string("ProofTheory.Resolution.Proof"), vec![]),
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize feasible interpolation declarations for Pudlak's theorem.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_craig_interpolation()`.
    #[cfg(test)]
    pub(crate) fn init_feasible_interpolation(&mut self) -> Result<(), EnvError> {
        if self.feasible_interpolation_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_craig_interpolation()?;

        let c = FeasibleInterpolationConsts::new();
        // Definitions
        self.register_feasible_interpolant(&c)?;
        self.register_communication_complexity(&c)?;
        self.register_monotone_circuit(&c)?;
        self.register_monotone_circuit_size(&c)?;
        self.register_dag_like_proof(&c)?;
        // Theorems (in feasible_interpolation_theorems.rs)
        self.register_pudlak_feasible_interpolation(&c)?;
        self.register_interpolant_to_monotone_circuit(&c)?;
        self.register_monotone_circuit_lower_bound(&c)?;
        self.register_feasible_interpolation_lower_bound(&c)?;
        self.register_dag_vs_tree_separation(&c)?;

        self.feasible_interpolation_init = true;
        Ok(())
    }

    // ====================================================================
    // Definition 1: FeasibleInterpolant
    // ====================================================================

    /// `FeasibleInterpolant (a b : PropFormula) (p : Resolution.Proof) : Type`
    ///
    /// An interpolant that is computable in time polynomial in the size of
    /// the resolution proof `p`. This is stronger than mere existence of an
    /// interpolant (Craig's theorem): the interpolant can be efficiently
    /// extracted from the proof structure.
    ///
    /// Abstractly wraps a PropFormula together with a polynomial-time
    /// computability witness.
    #[cfg(test)]
    fn register_feasible_interpolant(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.FeasibleInterpolant"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let (p_id, _) = b.fresh_local(c.res_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.res_proof.clone(),
                c.type0.clone(),
            );
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.FeasibleInterpolant"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 2: communication_complexity
    // ====================================================================

    /// `communication_complexity (a b : PropFormula) : Nat`
    ///
    /// The communication complexity of the interpolation problem for
    /// formulas A and B: the minimum number of bits that must be exchanged
    /// in a two-party protocol where Alice holds an assignment to A-variables
    /// and Bob holds an assignment to B-variables, in order to determine
    /// whether the combined assignment satisfies A AND B.
    ///
    /// Reference: Krajicek (1998), "Interpolation and approximate semantic
    ///            derivations".
    #[cfg(test)]
    fn register_communication_complexity(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.communication_complexity"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_formula.clone(),
                c.nat.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.communication_complexity"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 3: monotone_circuit
    // ====================================================================

    /// `monotone_circuit : Type`
    ///
    /// A monotone Boolean circuit: a directed acyclic graph of AND and OR
    /// gates with no negation gates. Inputs are propositional variables
    /// (non-negated). Monotone circuits compute monotone Boolean functions.
    ///
    /// Constructors:
    /// - `Input (v : Nat)` — input variable
    /// - `And (c1 c2 : monotone_circuit)` — conjunction gate
    /// - `Or (c1 c2 : monotone_circuit)` — disjunction gate
    #[cfg(test)]
    fn register_monotone_circuit(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let mc = Expr::const_(Name::from_string("ProofTheory.monotone_circuit"), vec![]);
        if self
            .get_const(&Name::from_string("ProofTheory.monotone_circuit"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.monotone_circuit"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Input constructor: (v : Nat) -> monotone_circuit
        let input_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), mc.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.monotone_circuit.Input"),
            level_params: vec![],
            type_: input_ty,
        })?;
        // And constructor: (c1 c2 : monotone_circuit) -> monotone_circuit
        let and_ty = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, _) = b.fresh_local(mc.clone());
            let (c2_id, _) = b.fresh_local(mc.clone());
            let e = b.mk_pi(c2_id, BinderInfo::Default, mc.clone(), mc.clone());
            let e = b.mk_pi(c1_id, BinderInfo::Default, mc.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.monotone_circuit.And"),
            level_params: vec![],
            type_: and_ty,
        })?;
        // Or constructor: (c1 c2 : monotone_circuit) -> monotone_circuit
        let or_ty = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, _) = b.fresh_local(mc.clone());
            let (c2_id, _) = b.fresh_local(mc.clone());
            let e = b.mk_pi(c2_id, BinderInfo::Default, mc.clone(), mc.clone());
            let e = b.mk_pi(c1_id, BinderInfo::Default, mc.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.monotone_circuit.Or"),
            level_params: vec![],
            type_: or_ty,
        })
    }

    // ====================================================================
    // Definition 4: monotone_circuit_size
    // ====================================================================

    /// `monotone_circuit_size (c : monotone_circuit) : Nat`
    ///
    /// The size of a monotone circuit: the number of gates (AND and OR nodes).
    /// Input nodes contribute 0 to the size.
    #[cfg(test)]
    fn register_monotone_circuit_size(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let mc = Expr::const_(Name::from_string("ProofTheory.monotone_circuit"), vec![]);
        if self
            .get_const(&Name::from_string("ProofTheory.monotone_circuit_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, mc, c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.monotone_circuit_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 5: dag_like_proof
    // ====================================================================

    /// `dag_like_proof : Type`
    ///
    /// A DAG-like resolution proof where derived clauses may be reused
    /// (shared subtrees). In contrast, tree-like proofs
    /// (ResComplexity.TreeResProof) require each derived clause to be
    /// rederived at every use site. DAG-like proofs can be exponentially
    /// more compact than tree-like proofs.
    ///
    /// Constructors:
    /// - `Axiom (cl : PropFormula)` — leaf: an axiom clause
    /// - `Resolve (p1 p2 : Nat) (v : Nat)` — resolve on variable v,
    ///   referencing previously derived clauses by index
    #[cfg(test)]
    fn register_dag_like_proof(&mut self, c: &FeasibleInterpolationConsts) -> Result<(), EnvError> {
        let dag = Expr::const_(Name::from_string("ProofTheory.dag_like_proof"), vec![]);
        if self
            .get_const(&Name::from_string("ProofTheory.dag_like_proof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.dag_like_proof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Axiom constructor: (cl : PropFormula) -> dag_like_proof
        let axiom_ty = Expr::pi(BinderInfo::Default, c.prop_formula.clone(), dag.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.dag_like_proof.Axiom"),
            level_params: vec![],
            type_: axiom_ty,
        })?;
        // Resolve constructor: (p1 p2 : Nat) (v : Nat) -> dag_like_proof
        // p1, p2 are indices into the proof DAG (referencing earlier lines)
        let resolve_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p1_id, _) = b.fresh_local(c.nat.clone());
            let (p2_id, _) = b.fresh_local(c.nat.clone());
            let (v_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), dag.clone());
            let e = b.mk_pi(p2_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(p1_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.dag_like_proof.Resolve"),
            level_params: vec![],
            type_: resolve_ty,
        })
    }
}
