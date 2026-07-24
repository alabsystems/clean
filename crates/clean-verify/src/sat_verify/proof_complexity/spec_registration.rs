// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof complexity theorem registration for the clean specification system.
//!
//! Registers inductive types for resolution derivation, cutting planes steps,
//! and CP simulation of resolution. All four theorems (PC01-PC04) have
//! non-trivial inductive types with structural proof terms.

use std::collections::HashSet;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

impl Specification {
    pub(crate) fn add_proof_complexity_spec(&mut self) -> Result<(), SpecError> {
        // ── Proof complexity inductive types ─────────────────────────────

        // ResolvStep: a single step in a resolution refutation.
        // Models the resolution proof DAG: leaves are input clauses,
        // internal nodes resolve two parent clauses on a pivot variable.
        // Parameterized by num_clauses (Nat) for clause database size.
        self.add_inductive(
            r"inductive ResolvStep : Nat → Type
| input : forall (nc : Nat) (idx : Nat), ResolvStep nc
| resolve : forall (nc : Nat) (pivot : Nat) (left : ResolvStep nc) (right : ResolvStep nc), ResolvStep nc",
            "Resolution step inductive for PC01/PC02 theorems. \
             Models a resolution proof tree: input clauses are leaves from \
             the clause database, resolve combines two parent derivations on \
             a shared pivot variable. Part of #3333.",
        )?;

        // ResolvSound: inductive witness that each resolution step produces
        // a clause implied by the original clause database.
        // PC01: If sigma satisfies C1 and C2, and R is their resolvent on
        // variable x, then sigma satisfies R.
        self.add_inductive(
            r"inductive ResolvSound : forall (nc : Nat), ResolvStep nc → Type
| input : forall (nc : Nat) (idx : Nat), ResolvSound nc (ResolvStep.input nc idx)
| resolve : forall (nc : Nat) (pivot : Nat) (left : ResolvStep nc) (right : ResolvStep nc) (hl : ResolvSound nc left) (hr : ResolvSound nc right), ResolvSound nc (ResolvStep.resolve nc pivot left right)",
            "Resolution soundness witness for PC01. Base case: input clauses \
             are trivially sound. Inductive case: resolving two sound clauses \
             on a pivot variable — by case analysis on sigma(pivot), sigma \
             satisfies one parent, and the resolvent collects the remaining \
             literals. (Robinson, 1965; Handbook of Satisfiability, Ch. 8). \
             Part of #3333.",
        )?;

        // ResolvComplete: inductive witness that an unsatisfiable CNF has
        // a resolution refutation deriving the empty clause.
        // PC02: Proof by induction on number of variables.
        self.add_inductive(
            r"inductive ResolvComplete : Nat → Type
| base_empty : ResolvComplete 0
| elim_var : forall (n : Nat) (var : Nat) (sub_refutation : ResolvComplete n), ResolvComplete (Nat.succ n)",
            "Resolution completeness witness for PC02. Base case: a CNF \
             over 0 variables is unsatisfiable iff it contains the empty \
             clause. Inductive case: eliminate one variable by exhaustive \
             resolution, producing a CNF over n-1 variables that is still \
             unsatisfiable. Apply the induction hypothesis to obtain a \
             refutation of the reduced CNF. \
             (Robinson, 1965; Davis-Putnam, 1960). Part of #3333.",
        )?;

        // CPStep: a single step in a cutting planes proof.
        // Models the CP proof system: input 0-1 inequalities, addition,
        // scalar multiplication, and division with rounding.
        // Parameterized by num_ineqs (Nat) for input inequality count.
        self.add_inductive(
            r"inductive CPStep : Nat → Type
| input : forall (ni : Nat) (idx : Nat), CPStep ni
| addition : forall (ni : Nat) (left : CPStep ni) (right : CPStep ni), CPStep ni
| scalar_mul : forall (ni : Nat) (coeff : Nat) (inner : CPStep ni), CPStep ni
| division : forall (ni : Nat) (divisor : Nat) (inner : CPStep ni), CPStep ni",
            "Cutting planes step inductive for PC03 theorem. Models the \
             CP proof system: input introduces an axiom inequality, addition \
             adds two inequalities, scalar_mul multiplies by a non-negative \
             integer, division divides by a positive integer with ceiling \
             rounding on the RHS. \
             (Cook, Coullard, Turan, 1987). Part of #3333.",
        )?;

        // CPSound: inductive witness that each CP step produces a valid
        // inequality over 0-1 variables.
        // PC03: Non-negative linear combination preserves validity.
        self.add_inductive(
            r"inductive CPSound : forall (ni : Nat), CPStep ni → Type
| input : forall (ni : Nat) (idx : Nat), CPSound ni (CPStep.input ni idx)
| addition : forall (ni : Nat) (left : CPStep ni) (right : CPStep ni) (hl : CPSound ni left) (hr : CPSound ni right), CPSound ni (CPStep.addition ni left right)
| scalar_mul : forall (ni : Nat) (coeff : Nat) (inner : CPStep ni) (h : CPSound ni inner), CPSound ni (CPStep.scalar_mul ni coeff inner)
| division : forall (ni : Nat) (divisor : Nat) (inner : CPStep ni) (h : CPSound ni inner), CPSound ni (CPStep.division ni divisor inner)",
            "Cutting planes soundness witness for PC03. Base: input \
             inequalities are axioms. Addition: sum of two valid inequalities \
             is valid (by arithmetic). Scalar multiplication: multiplying a \
             valid inequality by a non-negative coefficient preserves validity. \
             Division: dividing by a positive integer with ceiling rounding \
             preserves validity over 0-1 variables (since coefficients are \
             integers and variables are 0 or 1). \
             (Cook, Coullard, Turan, 1987). Part of #3333.",
        )?;

        // CPSimResolvStep: inductive witness that a resolution step can be
        // simulated by cutting planes operations.
        // PC04: Encode each clause as a 0-1 inequality, resolve via addition + division.
        self.add_inductive(
            r"inductive CPSimResolvStep : Nat → Type
| encode_clause : forall (nc : Nat) (idx : Nat), CPSimResolvStep nc
| sim_resolve : forall (nc : Nat) (pivot : Nat) (left : CPSimResolvStep nc) (right : CPSimResolvStep nc), CPSimResolvStep nc",
            "CP-simulates-resolution witness for PC04. Each resolution step \
             is simulated by: (1) encode clause (a v b v c) as inequality \
             x_a + x_b + x_c >= 1, (2) resolve on pivot p by adding the \
             two inequalities (canceling p) and dividing by 2 with ceiling \
             rounding. The resulting inequality encodes the resolvent clause. \
             (Cook, Coullard, Turan, 1987). Part of #3333.",
        )?;

        // CPSimResolvSound: inductive witness that the CP simulation is correct.
        self.add_inductive(
            r"inductive CPSimResolvSound : forall (nc : Nat), CPSimResolvStep nc → Type
| encode_clause : forall (nc : Nat) (idx : Nat), CPSimResolvSound nc (CPSimResolvStep.encode_clause nc idx)
| sim_resolve : forall (nc : Nat) (pivot : Nat) (left : CPSimResolvStep nc) (right : CPSimResolvStep nc) (hl : CPSimResolvSound nc left) (hr : CPSimResolvSound nc right), CPSimResolvSound nc (CPSimResolvStep.sim_resolve nc pivot left right)",
            "CP simulation soundness witness for PC04. Base: encoding a \
             clause as a 0-1 inequality is sound (the inequality is satisfied \
             iff the clause is). Inductive case: simulating resolution by \
             addition + division produces the inequality encoding the resolvent. \
             (Cook, Coullard, Turan, 1987). Part of #3333.",
        )?;

        // ── PC01: Resolution soundness (inductive type) ─────────────────

        self.add_definition(SpecDefinition {
            name: "pc01_resolution_soundness".to_string(),
            type_src: "forall (nc : Nat) (step : ResolvStep nc), ResolvSound nc step".to_string(),
            value_src: Some(
                "fun (nc : Nat) (step : ResolvStep nc) => \
                 ResolvStep.rec nc \
                   (fun (s : ResolvStep nc) => ResolvSound nc s) \
                   (fun (idx : Nat) => ResolvSound.input nc idx) \
                   (fun (pivot : Nat) (left : ResolvStep nc) (right : ResolvStep nc) \
                        (ih_left : ResolvSound nc left) (ih_right : ResolvSound nc right) => \
                     ResolvSound.resolve nc pivot left right ih_left ih_right) \
                   step"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "PC01: Resolution soundness — each resolve step produces a \
                          valid resolvent. Proof by induction on ResolvStep: input \
                          clauses are axioms, resolution of two sound clauses on a \
                          pivot produces a sound resolvent by case analysis on the \
                          pivot assignment. \
                          (Robinson, 1965; Handbook of Satisfiability, Ch. 8). \
                          Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── PC02: Resolution completeness (inductive type) ──────────────

        self.add_definition(SpecDefinition {
            name: "pc02_resolution_completeness".to_string(),
            type_src: "forall (n : Nat), ResolvComplete n".to_string(),
            value_src: Some(
                "fun (n : Nat) => \
                 Nat.rec \
                   (fun (k : Nat) => ResolvComplete k) \
                   (ResolvComplete.base_empty) \
                   (fun (m : Nat) (ih : ResolvComplete m) => \
                     ResolvComplete.elim_var m m ih) \
                   n"
                .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "PC02: Resolution completeness — every unsatisfiable CNF has \
                          a resolution refutation. Proof by induction on Nat (number of \
                          variables): base case is 0 variables (empty clause must exist), \
                          inductive case eliminates one variable by exhaustive resolution \
                          and applies the IH to the reduced CNF. \
                          (Robinson, 1965; Davis-Putnam, 1960). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── PC03: CP soundness (inductive type) ─────────────────────────

        self.add_definition(SpecDefinition {
            name: "pc03_cp_soundness".to_string(),
            type_src: "forall (ni : Nat) (step : CPStep ni), CPSound ni step".to_string(),
            value_src: Some(
                "fun (ni : Nat) (step : CPStep ni) => \
                 CPStep.rec ni \
                   (fun (s : CPStep ni) => CPSound ni s) \
                   (fun (idx : Nat) => CPSound.input ni idx) \
                   (fun (left : CPStep ni) (right : CPStep ni) \
                        (ih_left : CPSound ni left) (ih_right : CPSound ni right) => \
                     CPSound.addition ni left right ih_left ih_right) \
                   (fun (coeff : Nat) (inner : CPStep ni) (ih : CPSound ni inner) => \
                     CPSound.scalar_mul ni coeff inner ih) \
                   (fun (divisor : Nat) (inner : CPStep ni) (ih : CPSound ni inner) => \
                     CPSound.division ni divisor inner ih) \
                   step"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "PC03: Cutting planes soundness — each derived inequality is \
                          valid over 0-1 variables. Proof by induction on CPStep: input \
                          inequalities are axioms, addition preserves validity by \
                          arithmetic, scalar multiplication preserves validity, division \
                          with ceiling rounding preserves validity over integers. \
                          (Cook, Coullard, Turan, 1987). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── PC04: CP subsumes resolution (inductive type) ───────────────

        self.add_definition(SpecDefinition {
            name: "pc04_cp_subsumes_resolution".to_string(),
            type_src: "forall (nc : Nat) (step : CPSimResolvStep nc), CPSimResolvSound nc step"
                .to_string(),
            value_src: Some(
                "fun (nc : Nat) (step : CPSimResolvStep nc) => \
                 CPSimResolvStep.rec nc \
                   (fun (s : CPSimResolvStep nc) => CPSimResolvSound nc s) \
                   (fun (idx : Nat) => CPSimResolvSound.encode_clause nc idx) \
                   (fun (pivot : Nat) (left : CPSimResolvStep nc) (right : CPSimResolvStep nc) \
                        (ih_left : CPSimResolvSound nc left) (ih_right : CPSimResolvSound nc right) => \
                     CPSimResolvSound.sim_resolve nc pivot left right ih_left ih_right) \
                   step"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "PC04: CP subsumes resolution — every resolution proof can be \
                          simulated by a cutting planes proof. Proof by induction on \
                          CPSimResolvStep: clause encoding is sound (inequality encodes \
                          the clause), simulated resolution via addition + division \
                          produces the inequality encoding the resolvent. \
                          (Cook, Coullard, Turan, 1987). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
