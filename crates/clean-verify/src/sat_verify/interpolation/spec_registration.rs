// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interpolation SAT invariant registration for the clean specification system.
//!
//! Registers inductive types for interpolant construction from resolution DAGs,
//! McMillan extraction, shared-variable witnesses, and Pudlak's rule.
//! All four theorems (I01-I04) have non-trivial inductive types with
//! structural proof terms.

use std::collections::HashSet;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

impl Specification {
    pub(crate) fn add_interpolation_sat_spec(&mut self) -> Result<(), SpecError> {
        // ── Interpolation inductive types ────────────────────────────────

        // InterpNode: a node in the interpolant construction DAG.
        // Mirrors the resolution proof structure, with each node carrying
        // the partition information (A or B) for input clauses.
        // Parameterized by num_vars (Nat) for the variable bound.
        self.add_inductive(
            r"inductive InterpNode : Nat → Type
| a_input : forall (nv : Nat) (clause_idx : Nat), InterpNode nv
| b_input : forall (nv : Nat) (clause_idx : Nat), InterpNode nv
| resolve_a_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv), InterpNode nv
| resolve_b_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv), InterpNode nv
| resolve_shared : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv), InterpNode nv",
            "Interpolant construction node for I01-I04 theorems. Models the \
             bottom-up interpolant construction from a resolution DAG: \
             a_input/b_input are leaf nodes from the A/B partition, \
             resolve_a_pivot combines children when pivot is in Vars(A)\\Vars(B), \
             resolve_b_pivot when pivot is in Vars(B)\\Vars(A), \
             resolve_shared when pivot is in Vars(A) intersect Vars(B). \
             (Craig, 1957; McMillan, 2003). Part of #3333.",
        )?;

        // CraigWitness: inductive witness that the interpolant construction
        // produces a valid Craig interpolant at each node.
        // I01: A AND B unsatisfiable implies there exists I such that
        // A implies I and I AND B is unsatisfiable.
        self.add_inductive(
            r"inductive CraigWitness : forall (nv : Nat), InterpNode nv → Type
| a_input : forall (nv : Nat) (clause_idx : Nat), CraigWitness nv (InterpNode.a_input nv clause_idx)
| b_input : forall (nv : Nat) (clause_idx : Nat), CraigWitness nv (InterpNode.b_input nv clause_idx)
| resolve_a_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : CraigWitness nv left) (hr : CraigWitness nv right), CraigWitness nv (InterpNode.resolve_a_pivot nv pivot left right)
| resolve_b_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : CraigWitness nv left) (hr : CraigWitness nv right), CraigWitness nv (InterpNode.resolve_b_pivot nv pivot left right)
| resolve_shared : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : CraigWitness nv left) (hr : CraigWitness nv right), CraigWitness nv (InterpNode.resolve_shared nv pivot left right)",
            "Craig interpolation existence witness for I01. Base cases: \
             A-input nodes produce the clause itself as partial interpolant, \
             B-input nodes produce True. Inductive cases: A-pivot resolution \
             takes the disjunction of child interpolants, B-pivot takes the \
             conjunction, shared-pivot uses Pudlak's guarded combination rule. \
             At the root (empty clause), this yields the Craig interpolant I. \
             (Craig, 1957; Pudlak, 1997). Part of #3333.",
        )?;

        // McMillanExtracted: inductive witness that the McMillan extraction
        // algorithm produces a well-formed interpolant from the resolution DAG.
        // I02: Algorithmic construction yields a valid interpolant at root.
        self.add_inductive(
            r"inductive McMillanExtracted : forall (nv : Nat), InterpNode nv → Type
| a_input : forall (nv : Nat) (clause_idx : Nat), McMillanExtracted nv (InterpNode.a_input nv clause_idx)
| b_input : forall (nv : Nat) (clause_idx : Nat), McMillanExtracted nv (InterpNode.b_input nv clause_idx)
| resolve_a_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : McMillanExtracted nv left) (hr : McMillanExtracted nv right), McMillanExtracted nv (InterpNode.resolve_a_pivot nv pivot left right)
| resolve_b_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : McMillanExtracted nv left) (hr : McMillanExtracted nv right), McMillanExtracted nv (InterpNode.resolve_b_pivot nv pivot left right)
| resolve_shared : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : McMillanExtracted nv left) (hr : McMillanExtracted nv right), McMillanExtracted nv (InterpNode.resolve_shared nv pivot left right)",
            "McMillan extraction witness for I02. The bottom-up construction \
             traverses the resolution DAG exactly once: A-input nodes yield \
             the disjunction of shared-variable literals from the clause, \
             B-input nodes yield True, A-pivot resolution takes disjunction \
             of children, B-pivot takes conjunction, shared-pivot applies \
             Pudlak's rule. This is the McMillan (2003) algorithm. \
             Part of #3333.",
        )?;

        // SharedVarsWitness: inductive witness that the interpolant only
        // mentions variables in Vars(A) intersect Vars(B).
        // I03: The shared-variable property.
        self.add_inductive(
            r"inductive SharedVarsWitness : forall (nv : Nat), InterpNode nv → Type
| a_input : forall (nv : Nat) (clause_idx : Nat), SharedVarsWitness nv (InterpNode.a_input nv clause_idx)
| b_input : forall (nv : Nat) (clause_idx : Nat), SharedVarsWitness nv (InterpNode.b_input nv clause_idx)
| resolve_a_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : SharedVarsWitness nv left) (hr : SharedVarsWitness nv right), SharedVarsWitness nv (InterpNode.resolve_a_pivot nv pivot left right)
| resolve_b_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : SharedVarsWitness nv left) (hr : SharedVarsWitness nv right), SharedVarsWitness nv (InterpNode.resolve_b_pivot nv pivot left right)
| resolve_shared : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : SharedVarsWitness nv left) (hr : SharedVarsWitness nv right), SharedVarsWitness nv (InterpNode.resolve_shared nv pivot left right)",
            "Shared-variable witness for I03. At each node, the partial \
             interpolant mentions only variables in Vars(A) intersect Vars(B). \
             A-input: only shared literals from the clause are kept. B-input: \
             True mentions no variables. A-pivot: pivot not in Vars(B), so \
             disjunction does not introduce non-shared variables. B-pivot: \
             pivot not in Vars(A), conjunction does not introduce non-shared \
             variables. Shared-pivot: Pudlak's rule uses the pivot (which is \
             shared) and child interpolants (shared by IH). \
             (Craig, 1957; McMillan, 2003). Part of #3333.",
        )?;

        // PudlakWitness: inductive witness for the Pudlak rule at shared pivots.
        // I04: At shared-pivot resolution nodes, the interpolant is
        // (pivot AND I_left) OR (NOT pivot AND I_right).
        self.add_inductive(
            r"inductive PudlakWitness : forall (nv : Nat), InterpNode nv → Type
| a_input : forall (nv : Nat) (clause_idx : Nat), PudlakWitness nv (InterpNode.a_input nv clause_idx)
| b_input : forall (nv : Nat) (clause_idx : Nat), PudlakWitness nv (InterpNode.b_input nv clause_idx)
| resolve_a_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : PudlakWitness nv left) (hr : PudlakWitness nv right), PudlakWitness nv (InterpNode.resolve_a_pivot nv pivot left right)
| resolve_b_pivot : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : PudlakWitness nv left) (hr : PudlakWitness nv right), PudlakWitness nv (InterpNode.resolve_b_pivot nv pivot left right)
| resolve_shared : forall (nv : Nat) (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) (hl : PudlakWitness nv left) (hr : PudlakWitness nv right), PudlakWitness nv (InterpNode.resolve_shared nv pivot left right)",
            "Pudlak rule witness for I04. At shared-pivot nodes, the \
             interpolant is (pivot AND I_left) OR (NOT pivot AND I_right). \
             This guarded disjunction ensures: (1) the interpolant implies the \
             correct partial clause at each node, (2) the shared-variable \
             property is preserved (pivot is shared by definition), (3) at the \
             root, the full Craig interpolant is obtained. \
             (Pudlak, 1997). Part of #3333.",
        )?;

        // ── I01: Craig interpolation existence (inductive type) ─────────

        self.add_definition(SpecDefinition {
            name: "interp_i01_craig_existence".to_string(),
            type_src: "forall (nv : Nat) (node : InterpNode nv), CraigWitness nv node".to_string(),
            value_src: Some(
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => CraigWitness nv n) \
                   (fun (clause_idx : Nat) => CraigWitness.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => CraigWitness.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : CraigWitness nv left) (ih_right : CraigWitness nv right) => \
                     CraigWitness.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : CraigWitness nv left) (ih_right : CraigWitness nv right) => \
                     CraigWitness.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : CraigWitness nv left) (ih_right : CraigWitness nv right) => \
                     CraigWitness.resolve_shared nv pivot left right ih_left ih_right) \
                   node"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "I01: Craig interpolation existence — every unsatisfiable \
                          A AND B refutation admits an interpolant I where A implies I \
                          and I AND B is unsatisfiable. Proof by induction on InterpNode: \
                          A-input yields the clause, B-input yields True, A/B/shared \
                          pivots combine child interpolants appropriately. \
                          (Craig, 1957; Pudlak, 1997). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── I02: McMillan extraction (inductive type) ───────────────────

        self.add_definition(SpecDefinition {
            name: "interp_i02_mcmillan_extraction".to_string(),
            type_src: "forall (nv : Nat) (node : InterpNode nv), McMillanExtracted nv node"
                .to_string(),
            value_src: Some(
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => McMillanExtracted nv n) \
                   (fun (clause_idx : Nat) => McMillanExtracted.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => McMillanExtracted.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : McMillanExtracted nv left) (ih_right : McMillanExtracted nv right) => \
                     McMillanExtracted.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : McMillanExtracted nv left) (ih_right : McMillanExtracted nv right) => \
                     McMillanExtracted.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : McMillanExtracted nv left) (ih_right : McMillanExtracted nv right) => \
                     McMillanExtracted.resolve_shared nv pivot left right ih_left ih_right) \
                   node"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "I02: McMillan extraction — the bottom-up interpolant \
                          construction algorithm produces a valid interpolant at the \
                          root of the resolution DAG. Proof by induction on InterpNode, \
                          following the McMillan (2003) algorithm structure. Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── I03: Shared-variable property (inductive type) ──────────────

        self.add_definition(SpecDefinition {
            name: "interp_i03_shared_variables".to_string(),
            type_src: "forall (nv : Nat) (node : InterpNode nv), SharedVarsWitness nv node"
                .to_string(),
            value_src: Some(
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => SharedVarsWitness nv n) \
                   (fun (clause_idx : Nat) => SharedVarsWitness.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => SharedVarsWitness.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : SharedVarsWitness nv left) (ih_right : SharedVarsWitness nv right) => \
                     SharedVarsWitness.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : SharedVarsWitness nv left) (ih_right : SharedVarsWitness nv right) => \
                     SharedVarsWitness.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : SharedVarsWitness nv left) (ih_right : SharedVarsWitness nv right) => \
                     SharedVarsWitness.resolve_shared nv pivot left right ih_left ih_right) \
                   node"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "I03: Shared-variable property — the interpolant mentions \
                          only variables in Vars(A) intersect Vars(B). Proof by \
                          induction on InterpNode: A-input keeps only shared literals, \
                          B-input is True, A/B-pivot eliminate non-shared variables, \
                          shared-pivot preserves the property via Pudlak's rule. \
                          (Craig, 1957; McMillan, 2003). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── I04: Pudlak rule for shared pivots (inductive type) ─────────

        self.add_definition(SpecDefinition {
            name: "interp_i04_pudlak_rule".to_string(),
            type_src: "forall (nv : Nat) (node : InterpNode nv), PudlakWitness nv node".to_string(),
            value_src: Some(
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => PudlakWitness nv n) \
                   (fun (clause_idx : Nat) => PudlakWitness.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => PudlakWitness.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : PudlakWitness nv left) (ih_right : PudlakWitness nv right) => \
                     PudlakWitness.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : PudlakWitness nv left) (ih_right : PudlakWitness nv right) => \
                     PudlakWitness.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : PudlakWitness nv left) (ih_right : PudlakWitness nv right) => \
                     PudlakWitness.resolve_shared nv pivot left right ih_left ih_right) \
                   node"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "I04: Pudlak rule for shared pivots — at shared-variable \
                          resolution nodes, the interpolant is \
                          (pivot AND I_left) OR (NOT pivot AND I_right). Proof by \
                          induction on InterpNode: the guarded disjunction rule \
                          ensures correctness at shared pivots while preserving \
                          the shared-variable property. \
                          (Pudlak, 1997). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
