// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT Proof-DAG Interpolation
//!
//! Computes Craig interpolants for unsatisfiable SMT proof DAGs partitioned into
//! `A` and `B` assumptions. The implementation follows a McMillan-style
//! recursion over proof steps, adds a Pudlak-style rule for shared resolution
//! pivots, and delegates theory lemmas to lightweight EUF and LRA handlers.
//! The resulting interpolants are quantifier-free formulas that mention only
//! symbols shared between the two partitions.

use std::collections::{HashMap, HashSet};

use num_rational::Rational64;
use thiserror::Error;

use super::dag::{
    SmtProofDag, SmtProofStep, SmtSort, SmtStepId, SmtSymbol, SmtTerm, SmtTermId, SmtTheory,
    TheoryLemmaDetail,
};
use super::lra::{self, ArithRelation, LinearInequality};

/// Partition of input assumptions into the `A` and `B` sides of interpolation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SmtPartition {
    /// Assumption steps belonging to the `A` partition.
    pub a_assumptions: HashSet<SmtStepId>,
    /// Assumption steps belonging to the `B` partition.
    pub b_assumptions: HashSet<SmtStepId>,
    /// Variables shared by the two partitions.
    pub shared_variables: HashSet<String>,
}

impl SmtPartition {
    /// Recompute the partition's shared-variable set from the proof DAG.
    pub fn compute_shared_variables(
        &mut self,
        dag: &SmtProofDag,
    ) -> Result<(), InterpolationError> {
        let analysis = PartitionAnalysis::from_partition(dag, self)?;
        self.shared_variables = analysis.shared_variables;
        Ok(())
    }
}

/// Quantifier-free SMT interpolant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtInterpolant {
    /// Shared variable.
    Var(String, SmtSort),
    /// Boolean constant.
    BoolConst(bool),
    /// Negation.
    Not(Box<SmtInterpolant>),
    /// Conjunction.
    AndType(Box<SmtInterpolant>, Box<SmtInterpolant>),
    /// Disjunction.
    Or(Box<SmtInterpolant>, Box<SmtInterpolant>),
    /// Linear arithmetic atom.
    LinearIneq {
        /// Variable coefficients in normalized form.
        coefficients: Vec<(String, Rational64)>,
        /// Constant term.
        constant: Rational64,
        /// Arithmetic relation.
        relation: ArithRelation,
    },
    /// Equality between shared variables.
    Eq(String, String),
    /// Shared uninterpreted function or predicate application.
    App(String, Vec<SmtInterpolant>),
}

impl SmtInterpolant {
    fn not(inner: Self) -> Self {
        match inner.simplify() {
            Self::BoolConst(value) => Self::BoolConst(!value),
            Self::Not(nested) => *nested,
            other => Self::Not(Box::new(other)),
        }
    }

    fn and(lhs: Self, rhs: Self) -> Self {
        match (lhs.simplify(), rhs.simplify()) {
            (Self::BoolConst(false), _) | (_, Self::BoolConst(false)) => Self::BoolConst(false),
            (Self::BoolConst(true), other) | (other, Self::BoolConst(true)) => other,
            (left, right) if left == right => left,
            (left, right) => Self::AndType(Box::new(left), Box::new(right)),
        }
    }

    fn or(lhs: Self, rhs: Self) -> Self {
        match (lhs.simplify(), rhs.simplify()) {
            (Self::BoolConst(true), _) | (_, Self::BoolConst(true)) => Self::BoolConst(true),
            (Self::BoolConst(false), other) | (other, Self::BoolConst(false)) => other,
            (left, right) if left == right => left,
            (left, right) => Self::Or(Box::new(left), Box::new(right)),
        }
    }

    fn linear_ineq(ineq: LinearInequality) -> Self {
        Self::LinearIneq {
            coefficients: ineq.coefficients,
            constant: ineq.constant,
            relation: ineq.relation,
        }
        .simplify()
    }

    fn simplify(self) -> Self {
        match self {
            Self::Not(inner) => Self::not(*inner),
            Self::AndType(lhs, rhs) => Self::and(*lhs, *rhs),
            Self::Or(lhs, rhs) => Self::or(*lhs, *rhs),
            Self::Eq(lhs, rhs) if lhs == rhs => Self::BoolConst(true),
            Self::LinearIneq {
                coefficients,
                constant,
                relation,
            } => {
                let normalized = normalize_linear_inequality(LinearInequality {
                    coefficients,
                    constant,
                    relation,
                });
                if normalized.coefficients.is_empty() {
                    Self::BoolConst(evaluate_constant_relation(
                        normalized.constant,
                        normalized.relation,
                    ))
                } else {
                    Self::LinearIneq {
                        coefficients: normalized.coefficients,
                        constant: normalized.constant,
                        relation: normalized.relation,
                    }
                }
            }
            other => other,
        }
    }
}

/// Errors encountered while constructing an SMT interpolant.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum InterpolationError {
    /// The proof DAG contains no steps.
    #[error("empty SMT proof")]
    EmptyProof,
    /// The partition is malformed or inconsistent with the DAG.
    #[error("invalid partition: {0}")]
    InvalidPartition(String),
    /// Interpolation requires shared variables but none are available.
    #[error("no shared variables available for interpolation")]
    NoSharedVariables,
    /// The theory or lemma kind is not supported by this interpolator.
    #[error("unsupported theory: {0}")]
    UnsupportedTheory(String),
    /// Internal interpolation failure.
    #[error("internal interpolation error: {0}")]
    InternalError(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolClass {
    ALocal,
    BLocal,
    Shared,
    Constant,
}

#[derive(Debug, Clone)]
struct PartitionAnalysis {
    a_variables: HashSet<String>,
    b_variables: HashSet<String>,
    shared_variables: HashSet<String>,
    shared_function_symbols: HashSet<String>,
    a_assumption_atoms: HashSet<SmtTermId>,
    b_assumption_atoms: HashSet<SmtTermId>,
}

impl PartitionAnalysis {
    fn from_partition(
        dag: &SmtProofDag,
        partition: &SmtPartition,
    ) -> Result<Self, InterpolationError> {
        let overlap: HashSet<_> = partition
            .a_assumptions
            .intersection(&partition.b_assumptions)
            .copied()
            .collect();
        if !overlap.is_empty() {
            return Err(InterpolationError::InvalidPartition(
                "assumption step appears in both partitions".to_string(),
            ));
        }

        let mut a_variables = HashSet::new();
        let mut b_variables = HashSet::new();
        let mut a_functions = HashSet::new();
        let mut b_functions = HashSet::new();
        let mut a_assumption_atoms = HashSet::new();
        let mut b_assumption_atoms = HashSet::new();

        for &step_id in &partition.a_assumptions {
            let term_id = assumption_term_id(dag, step_id)?;
            a_assumption_atoms.insert(canonical_atom(dag, term_id));
            collect_term_symbols(dag, term_id, &mut a_variables, &mut a_functions)?;
        }
        for &step_id in &partition.b_assumptions {
            let term_id = assumption_term_id(dag, step_id)?;
            b_assumption_atoms.insert(canonical_atom(dag, term_id));
            collect_term_symbols(dag, term_id, &mut b_variables, &mut b_functions)?;
        }

        for (index, step) in dag.steps.iter().enumerate() {
            let step_id = SmtStepId(index as u32);
            if matches!(step, SmtProofStep::Assume(_))
                && !partition.a_assumptions.contains(&step_id)
                && !partition.b_assumptions.contains(&step_id)
            {
                return Err(InterpolationError::InvalidPartition(format!(
                    "assumption step {:?} is not assigned to A or B",
                    step_id
                )));
            }
        }

        let shared_variables: HashSet<String> =
            a_variables.intersection(&b_variables).cloned().collect();
        if !partition.shared_variables.is_empty() && partition.shared_variables != shared_variables
        {
            return Err(InterpolationError::InvalidPartition(
                "provided shared variables do not match DAG-derived shared variables".to_string(),
            ));
        }

        let shared_function_symbols: HashSet<String> =
            a_functions.intersection(&b_functions).cloned().collect();

        Ok(Self {
            a_variables,
            b_variables,
            shared_variables,
            shared_function_symbols,
            a_assumption_atoms,
            b_assumption_atoms,
        })
    }

    fn classify_variables<'a, I>(&self, variables: I) -> SymbolClass
    where
        I: Iterator<Item = &'a String>,
    {
        let vars: Vec<&String> = variables.collect();
        if vars.is_empty() {
            return SymbolClass::Constant;
        }
        if vars
            .iter()
            .any(|name| self.shared_variables.contains(*name))
        {
            return SymbolClass::Shared;
        }
        if vars.iter().all(|name| self.a_variables.contains(*name)) {
            return SymbolClass::ALocal;
        }
        if vars.iter().all(|name| self.b_variables.contains(*name)) {
            return SymbolClass::BLocal;
        }
        SymbolClass::Shared
    }

    fn classify_term(
        &self,
        dag: &SmtProofDag,
        term_id: SmtTermId,
    ) -> Result<SymbolClass, InterpolationError> {
        if let Some(class) = self.classify_assumption_atom(canonical_atom(dag, term_id)) {
            return Ok(class);
        }

        let mut variables = HashSet::new();
        let mut functions = HashSet::new();
        collect_term_symbols(dag, term_id, &mut variables, &mut functions)?;
        let var_class = self.classify_variables(variables.iter());
        if matches!(var_class, SymbolClass::Shared) {
            return Ok(SymbolClass::Shared);
        }
        if !functions.is_empty()
            && functions
                .iter()
                .any(|symbol| self.shared_function_symbols.contains(symbol))
        {
            return Ok(SymbolClass::Shared);
        }
        Ok(var_class)
    }

    fn classify_linear_inequality(&self, ineq: &LinearInequality) -> SymbolClass {
        self.classify_variables(ineq.coefficients.iter().map(|(name, _)| name))
    }

    fn classify_assumption_atom(&self, atom: SmtTermId) -> Option<SymbolClass> {
        let in_a = self.a_assumption_atoms.contains(&atom);
        let in_b = self.b_assumption_atoms.contains(&atom);
        match (in_a, in_b) {
            (true, true) => Some(SymbolClass::Shared),
            (true, false) => Some(SymbolClass::ALocal),
            (false, true) => Some(SymbolClass::BLocal),
            (false, false) => None,
        }
    }
}

/// Compute a Craig interpolant for an SMT proof DAG.
pub fn interpolate_smt_proof(
    dag: &SmtProofDag,
    partition: &SmtPartition,
) -> Result<SmtInterpolant, InterpolationError> {
    if dag.num_steps() == 0 {
        return Err(InterpolationError::EmptyProof);
    }

    let analysis = PartitionAnalysis::from_partition(dag, partition)?;
    let root = root_step_id(dag)?;
    let mut memo = HashMap::new();
    interpolate_step(dag, root, partition, &analysis, &mut memo).map(SmtInterpolant::simplify)
}

fn interpolate_step(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    partition: &SmtPartition,
    analysis: &PartitionAnalysis,
    memo: &mut HashMap<SmtStepId, SmtInterpolant>,
) -> Result<SmtInterpolant, InterpolationError> {
    if let Some(interpolant) = memo.get(&step_id) {
        return Ok(interpolant.clone());
    }

    let step = dag.step(step_id).ok_or_else(|| {
        InterpolationError::InternalError(format!("missing proof step {:?}", step_id))
    })?;

    let interpolant = match step {
        SmtProofStep::Assume(term_id) => {
            interpolate_assume(dag, step_id, *term_id, partition, analysis)
        }
        SmtProofStep::Resolution {
            premises, pivot, ..
        } => interpolate_resolution(dag, premises, *pivot, partition, analysis, memo),
        SmtProofStep::TheoryLemma {
            theory,
            kind,
            clause,
        } => interpolate_theory_lemma(dag, *theory, kind, clause, analysis),
        SmtProofStep::Step { rule, .. } => Err(InterpolationError::UnsupportedTheory(format!(
            "step rule {rule}"
        ))),
        SmtProofStep::Anchor { end_step, .. } => {
            interpolate_step(dag, *end_step, partition, analysis, memo)
        }
    }?;

    let simplified = interpolant.simplify();
    memo.insert(step_id, simplified.clone());
    Ok(simplified)
}

fn interpolate_assume(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    term_id: SmtTermId,
    partition: &SmtPartition,
    analysis: &PartitionAnalysis,
) -> Result<SmtInterpolant, InterpolationError> {
    if partition.a_assumptions.contains(&step_id) {
        Ok(literal_to_interpolant(dag, term_id, analysis)
            .unwrap_or(SmtInterpolant::BoolConst(false)))
    } else if partition.b_assumptions.contains(&step_id) {
        Ok(SmtInterpolant::BoolConst(true))
    } else {
        Err(InterpolationError::InvalidPartition(format!(
            "assumption step {:?} is not assigned to A or B",
            step_id
        )))
    }
}

fn interpolate_resolution(
    dag: &SmtProofDag,
    premises: &[SmtStepId],
    pivot: Option<SmtTermId>,
    partition: &SmtPartition,
    analysis: &PartitionAnalysis,
    memo: &mut HashMap<SmtStepId, SmtInterpolant>,
) -> Result<SmtInterpolant, InterpolationError> {
    if premises.is_empty() {
        return Err(InterpolationError::InternalError(
            "resolution step has no premises".to_string(),
        ));
    }
    if premises.len() == 1 {
        return interpolate_step(dag, premises[0], partition, analysis, memo);
    }
    if premises.len() != 2 {
        return Err(InterpolationError::InternalError(format!(
            "resolution interpolation currently supports binary steps, found {} premises",
            premises.len()
        )));
    }

    let left_clause = dag.step_clause(premises[0]).ok_or_else(|| {
        InterpolationError::InternalError(format!("premise {:?} has no clause", premises[0]))
    })?;
    let right_clause = dag.step_clause(premises[1]).ok_or_else(|| {
        InterpolationError::InternalError(format!("premise {:?} has no clause", premises[1]))
    })?;

    let left = interpolate_step(dag, premises[0], partition, analysis, memo)?;
    let right = interpolate_step(dag, premises[1], partition, analysis, memo)?;
    let pivot_id = match pivot.or_else(|| infer_resolution_pivot(dag, left_clause, right_clause)) {
        Some(term_id) => term_id,
        None => {
            return Err(InterpolationError::InternalError(
                "could not infer resolution pivot".to_string(),
            ))
        }
    };

    apply_resolution_rule(
        dag,
        pivot_id,
        left_clause,
        right_clause,
        left,
        right,
        analysis,
    )
}

fn apply_resolution_rule(
    dag: &SmtProofDag,
    pivot: SmtTermId,
    left_clause: &[SmtTermId],
    right_clause: &[SmtTermId],
    left: SmtInterpolant,
    right: SmtInterpolant,
    analysis: &PartitionAnalysis,
) -> Result<SmtInterpolant, InterpolationError> {
    match analysis.classify_term(dag, pivot)? {
        SymbolClass::ALocal => Ok(SmtInterpolant::or(left, right)),
        SymbolClass::BLocal => Ok(SmtInterpolant::and(left, right)),
        SymbolClass::Shared | SymbolClass::Constant => {
            let pivot_formula = literal_to_interpolant(dag, pivot, analysis).ok_or_else(|| {
                InterpolationError::InternalError(
                    "shared pivot cannot be represented in the interpolant language".to_string(),
                )
            })?;

            let left_has_pivot = clause_contains_literal(left_clause, pivot);
            let right_has_pivot = clause_contains_literal(right_clause, pivot);
            let left_has_complement = clause_contains_complement(dag, left_clause, pivot);
            let right_has_complement = clause_contains_complement(dag, right_clause, pivot);

            if left_has_pivot && right_has_complement {
                Ok(SmtInterpolant::and(
                    SmtInterpolant::or(pivot_formula.clone(), left),
                    SmtInterpolant::or(SmtInterpolant::not(pivot_formula), right),
                ))
            } else if right_has_pivot && left_has_complement {
                Ok(SmtInterpolant::and(
                    SmtInterpolant::or(SmtInterpolant::not(pivot_formula.clone()), left),
                    SmtInterpolant::or(pivot_formula, right),
                ))
            } else {
                Ok(SmtInterpolant::and(
                    SmtInterpolant::or(pivot_formula.clone(), left),
                    SmtInterpolant::or(SmtInterpolant::not(pivot_formula), right),
                ))
            }
        }
    }
}

fn interpolate_theory_lemma(
    dag: &SmtProofDag,
    theory: SmtTheory,
    kind: &TheoryLemmaDetail,
    clause: &[SmtTermId],
    analysis: &PartitionAnalysis,
) -> Result<SmtInterpolant, InterpolationError> {
    match kind {
        TheoryLemmaDetail::LraFarkas { coefficients } => {
            interpolate_lra_farkas(dag, clause, coefficients, analysis)
        }
        TheoryLemmaDetail::EufTransitive
        | TheoryLemmaDetail::EufCongruent
        | TheoryLemmaDetail::EufCongruentPred
        | TheoryLemmaDetail::EufGeneric => interpolate_euf_lemma(dag, clause, analysis),
        _ => Err(InterpolationError::UnsupportedTheory(theory.to_string())),
    }
}

fn interpolate_lra_farkas(
    dag: &SmtProofDag,
    clause: &[SmtTermId],
    coefficients: &[(i64, i64)],
    analysis: &PartitionAnalysis,
) -> Result<SmtInterpolant, InterpolationError> {
    if clause.is_empty() {
        return Err(InterpolationError::InternalError(
            "LRA Farkas lemma has an empty clause".to_string(),
        ));
    }
    if clause.len() != coefficients.len() {
        return Err(InterpolationError::InternalError(format!(
            "LRA Farkas lemma has {} literals but {} coefficients",
            clause.len(),
            coefficients.len()
        )));
    }

    let zero = Rational64::from_integer(0);
    let mut selected_inequalities = Vec::new();
    let mut selected_weights = Vec::new();
    let mut saw_a_like = false;
    let mut saw_b_only = false;

    for (&lit, &(numerator, denominator)) in clause.iter().zip(coefficients.iter()) {
        if denominator == 0 {
            return Err(InterpolationError::InternalError(
                "LRA Farkas coefficient has zero denominator".to_string(),
            ));
        }
        let weight = Rational64::new(numerator, denominator);
        if weight < zero {
            return Err(InterpolationError::InternalError(
                "LRA Farkas coefficient is negative".to_string(),
            ));
        }

        let inequality = lra::extract_conflict_inequality(dag, lit).ok_or_else(|| {
            InterpolationError::UnsupportedTheory(
                "LRA interpolation requires linear arithmetic conflict atoms".to_string(),
            )
        })?;

        let literal_class = conflict_atom_from_clause_literal(dag, lit)
            .and_then(|atom| analysis.classify_assumption_atom(atom))
            .unwrap_or_else(|| analysis.classify_linear_inequality(&inequality));

        match literal_class {
            SymbolClass::ALocal | SymbolClass::Shared | SymbolClass::Constant => {
                saw_a_like = true;
                if weight != zero {
                    selected_inequalities.push(inequality);
                    selected_weights.push(weight);
                }
            }
            SymbolClass::BLocal => {
                saw_b_only = true;
            }
        }
    }

    if !saw_a_like && saw_b_only {
        return Ok(SmtInterpolant::BoolConst(true));
    }
    if analysis.shared_variables.is_empty() {
        return Ok(SmtInterpolant::BoolConst(false));
    }
    if selected_inequalities.is_empty() {
        return Err(InterpolationError::NoSharedVariables);
    }

    let combined =
        lra::weighted_sum(&selected_inequalities, &selected_weights).ok_or_else(|| {
            InterpolationError::UnsupportedTheory(
                "LRA interpolation does not support disequalities in Farkas certificates"
                    .to_string(),
            )
        })?;
    let projected = project_linear_inequality(combined, &analysis.shared_variables);
    Ok(SmtInterpolant::linear_ineq(projected))
}

fn interpolate_euf_lemma(
    dag: &SmtProofDag,
    clause: &[SmtTermId],
    analysis: &PartitionAnalysis,
) -> Result<SmtInterpolant, InterpolationError> {
    let mut equalities = Vec::new();
    let mut shared_terms = Vec::new();

    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if let Some(eq) = equality_to_interpolant(dag, lhs, rhs, analysis) {
                equalities.push(eq);
                continue;
            }
        }
        if let Some((lhs, rhs)) = dag.as_negated_equality(lit) {
            if let Some(eq) = equality_to_interpolant(dag, lhs, rhs, analysis) {
                equalities.push(eq);
                continue;
            }
        }
        if let Some(term) = literal_to_interpolant(dag, lit, analysis) {
            shared_terms.push(term);
        }
    }

    if let Some(interpolant) = equalities.into_iter().reduce(SmtInterpolant::and) {
        return Ok(interpolant);
    }
    if let Some(interpolant) = shared_terms.into_iter().reduce(SmtInterpolant::and) {
        return Ok(interpolant);
    }
    if analysis.shared_variables.is_empty() {
        return Err(InterpolationError::NoSharedVariables);
    }
    Ok(SmtInterpolant::BoolConst(false))
}

fn literal_to_interpolant(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    analysis: &PartitionAnalysis,
) -> Option<SmtInterpolant> {
    if let Some((lhs, rhs)) = dag.as_equality(term_id) {
        return equality_to_interpolant(dag, lhs, rhs, analysis);
    }
    if let Some((lhs, rhs)) = dag.as_negated_equality(term_id) {
        return equality_to_interpolant(dag, lhs, rhs, analysis).map(SmtInterpolant::not);
    }
    if let Some(ineq) = term_to_linear_interpolant(dag, term_id, analysis) {
        return Some(ineq);
    }

    match dag.term(term_id)? {
        SmtTerm::Var(name, sort) => {
            if analysis.shared_variables.contains(name) {
                Some(SmtInterpolant::Var(name.clone(), sort.clone()))
            } else {
                None
            }
        }
        SmtTerm::Bool(value) => Some(SmtInterpolant::BoolConst(*value)),
        SmtTerm::Not(inner) => {
            literal_to_interpolant(dag, *inner, analysis).map(SmtInterpolant::not)
        }
        SmtTerm::App(symbol, args) => {
            let name = symbol_key(symbol);
            if !analysis.shared_function_symbols.contains(&name) {
                return None;
            }
            let mut converted_args = Vec::with_capacity(args.len());
            for &arg in args {
                converted_args.push(literal_to_interpolant(dag, arg, analysis)?);
            }
            Some(SmtInterpolant::App(name, converted_args))
        }
        _ => None,
    }
}

fn equality_to_interpolant(
    dag: &SmtProofDag,
    lhs: SmtTermId,
    rhs: SmtTermId,
    analysis: &PartitionAnalysis,
) -> Option<SmtInterpolant> {
    match (dag.term(lhs)?, dag.term(rhs)?) {
        (SmtTerm::Var(left, _), SmtTerm::Var(right, _))
            if analysis.shared_variables.contains(left)
                && analysis.shared_variables.contains(right) =>
        {
            Some(SmtInterpolant::Eq(left.clone(), right.clone()).simplify())
        }
        _ => None,
    }
}

fn term_to_linear_interpolant(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    analysis: &PartitionAnalysis,
) -> Option<SmtInterpolant> {
    let inequality = match dag.term(term_id)? {
        SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
            let relation = relation_from_name(op)?;
            lra::extract_linear_atom(dag, args[0], args[1], relation)?
        }
        SmtTerm::Not(inner) => {
            let inner_term = dag.term(*inner)?;
            match inner_term {
                SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
                    let relation = negate_relation(relation_from_name(op)?);
                    lra::extract_linear_atom(dag, args[0], args[1], relation)?
                }
                _ => return None,
            }
        }
        _ => return None,
    };

    if inequality
        .coefficients
        .iter()
        .all(|(name, _)| analysis.shared_variables.contains(name))
    {
        Some(SmtInterpolant::linear_ineq(inequality))
    } else {
        None
    }
}

fn root_step_id(dag: &SmtProofDag) -> Result<SmtStepId, InterpolationError> {
    if dag.num_steps() == 0 {
        return Err(InterpolationError::EmptyProof);
    }

    let mut current = SmtStepId((dag.num_steps() - 1) as u32);
    loop {
        match dag.step(current) {
            Some(SmtProofStep::Anchor { end_step, .. }) => current = *end_step,
            Some(_) => return Ok(current),
            None => {
                return Err(InterpolationError::InternalError(format!(
                    "missing root step {:?}",
                    current
                )))
            }
        }
    }
}

fn assumption_term_id(
    dag: &SmtProofDag,
    step_id: SmtStepId,
) -> Result<SmtTermId, InterpolationError> {
    match dag.step(step_id) {
        Some(SmtProofStep::Assume(term_id)) => Ok(*term_id),
        Some(_) => Err(InterpolationError::InvalidPartition(format!(
            "step {:?} is not an assumption",
            step_id
        ))),
        None => Err(InterpolationError::InvalidPartition(format!(
            "assumption step {:?} does not exist",
            step_id
        ))),
    }
}

fn canonical_atom(dag: &SmtProofDag, term_id: SmtTermId) -> SmtTermId {
    match dag.term(term_id) {
        Some(SmtTerm::Not(inner)) => *inner,
        _ => term_id,
    }
}

fn conflict_atom_from_clause_literal(dag: &SmtProofDag, lit: SmtTermId) -> Option<SmtTermId> {
    match dag.term(lit) {
        Some(SmtTerm::Not(inner)) => Some(canonical_atom(dag, *inner)),
        Some(_) => Some(canonical_atom(dag, lit)),
        None => None,
    }
}

fn collect_term_symbols(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    variables: &mut HashSet<String>,
    functions: &mut HashSet<String>,
) -> Result<(), InterpolationError> {
    let mut bound = HashSet::new();
    collect_term_symbols_with_bound(dag, term_id, variables, functions, &mut bound)
}

fn collect_term_symbols_with_bound(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    variables: &mut HashSet<String>,
    functions: &mut HashSet<String>,
    bound: &mut HashSet<String>,
) -> Result<(), InterpolationError> {
    let term = dag.term(term_id).ok_or_else(|| {
        InterpolationError::InternalError(format!("missing SMT term {:?}", term_id))
    })?;

    match term {
        SmtTerm::Var(name, _) => {
            if !bound.contains(name) {
                variables.insert(name.clone());
            }
        }
        SmtTerm::App(symbol, args) => {
            functions.insert(symbol_key(symbol));
            for &arg in args {
                collect_term_symbols_with_bound(dag, arg, variables, functions, bound)?;
            }
        }
        SmtTerm::Not(inner) => {
            collect_term_symbols_with_bound(dag, *inner, variables, functions, bound)?;
        }
        SmtTerm::Ite(cond, then_branch, else_branch) => {
            collect_term_symbols_with_bound(dag, *cond, variables, functions, bound)?;
            collect_term_symbols_with_bound(dag, *then_branch, variables, functions, bound)?;
            collect_term_symbols_with_bound(dag, *else_branch, variables, functions, bound)?;
        }
        SmtTerm::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_term_symbols_with_bound(dag, *value, variables, functions, bound)?;
            }
            let mut inserted = Vec::with_capacity(bindings.len());
            for (name, _) in bindings {
                if bound.insert(name.clone()) {
                    inserted.push(name.clone());
                }
            }
            collect_term_symbols_with_bound(dag, *body, variables, functions, bound)?;
            for name in inserted {
                bound.remove(&name);
            }
        }
        SmtTerm::Forall(vars, body) | SmtTerm::Exists(vars, body) => {
            let mut inserted = Vec::with_capacity(vars.len());
            for (name, _) in vars {
                if bound.insert(name.clone()) {
                    inserted.push(name.clone());
                }
            }
            collect_term_symbols_with_bound(dag, *body, variables, functions, bound)?;
            for name in inserted {
                bound.remove(&name);
            }
        }
        SmtTerm::Bool(_)
        | SmtTerm::Int(_)
        | SmtTerm::Rational(_, _)
        | SmtTerm::BitVec(_, _)
        | SmtTerm::Str(_) => {}
    }

    Ok(())
}

fn infer_resolution_pivot(
    dag: &SmtProofDag,
    left_clause: &[SmtTermId],
    right_clause: &[SmtTermId],
) -> Option<SmtTermId> {
    left_clause
        .iter()
        .find(|&&lit| {
            right_clause
                .iter()
                .copied()
                .any(|other| dag.are_complementary(lit, other))
        })
        .copied()
}

fn clause_contains_literal(clause: &[SmtTermId], pivot: SmtTermId) -> bool {
    clause.contains(&pivot)
}

fn clause_contains_complement(dag: &SmtProofDag, clause: &[SmtTermId], pivot: SmtTermId) -> bool {
    clause
        .iter()
        .copied()
        .any(|lit| lit != pivot && dag.are_complementary(lit, pivot))
}

fn relation_from_name(name: &str) -> Option<ArithRelation> {
    match name {
        "<=" => Some(ArithRelation::Le),
        "<" => Some(ArithRelation::Lt),
        ">=" => Some(ArithRelation::Ge),
        ">" => Some(ArithRelation::Gt),
        "=" => Some(ArithRelation::Eq),
        "distinct" => Some(ArithRelation::Distinct),
        _ => None,
    }
}

fn negate_relation(relation: ArithRelation) -> ArithRelation {
    match relation {
        ArithRelation::Le => ArithRelation::Gt,
        ArithRelation::Lt => ArithRelation::Ge,
        ArithRelation::Ge => ArithRelation::Lt,
        ArithRelation::Gt => ArithRelation::Le,
        ArithRelation::Eq => ArithRelation::Distinct,
        ArithRelation::Distinct => ArithRelation::Eq,
    }
}

fn symbol_key(symbol: &SmtSymbol) -> String {
    match symbol {
        SmtSymbol::Named(name) => name.clone(),
        SmtSymbol::Indexed(name, indexes) => {
            let suffix = indexes
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(",");
            format!("{name}[{suffix}]")
        }
    }
}

fn project_linear_inequality(
    inequality: LinearInequality,
    shared_variables: &HashSet<String>,
) -> LinearInequality {
    let mut combined: HashMap<String, Rational64> = HashMap::new();
    for (name, coeff) in inequality.coefficients {
        if shared_variables.contains(&name) {
            let entry = combined
                .entry(name)
                .or_insert_with(|| Rational64::from_integer(0));
            *entry += coeff;
        }
    }
    let mut coefficients: Vec<(String, Rational64)> = combined
        .into_iter()
        .filter(|(_, coeff)| *coeff != Rational64::from_integer(0))
        .collect();
    coefficients.sort_by(|left, right| left.0.cmp(&right.0));

    LinearInequality {
        coefficients,
        constant: inequality.constant,
        relation: inequality.relation,
    }
}

fn normalize_linear_inequality(inequality: LinearInequality) -> LinearInequality {
    let mut combined: HashMap<String, Rational64> = HashMap::new();
    for (name, coeff) in inequality.coefficients {
        let entry = combined
            .entry(name)
            .or_insert_with(|| Rational64::from_integer(0));
        *entry += coeff;
    }
    let mut coefficients: Vec<(String, Rational64)> = combined
        .into_iter()
        .filter(|(_, coeff)| *coeff != Rational64::from_integer(0))
        .collect();
    coefficients.sort_by(|left, right| left.0.cmp(&right.0));

    LinearInequality {
        coefficients,
        constant: inequality.constant,
        relation: inequality.relation,
    }
}

fn evaluate_constant_relation(constant: Rational64, relation: ArithRelation) -> bool {
    let zero = Rational64::from_integer(0);
    match relation {
        ArithRelation::Le => constant <= zero,
        ArithRelation::Lt => constant < zero,
        ArithRelation::Ge => constant >= zero,
        ArithRelation::Gt => constant > zero,
        ArithRelation::Eq => constant == zero,
        ArithRelation::Distinct => constant != zero,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bool_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        dag.add_term(SmtTerm::Var(name.to_string(), SmtSort::Bool))
    }

    fn int_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        dag.add_term(SmtTerm::Var(name.to_string(), SmtSort::Int))
    }

    fn not(dag: &mut SmtProofDag, inner: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::Not(inner))
    }

    fn int_const(dag: &mut SmtProofDag, value: i64) -> SmtTermId {
        dag.add_term(SmtTerm::Int(value))
    }

    fn app(dag: &mut SmtProofDag, name: &str, args: Vec<SmtTermId>) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(name.to_string()), args))
    }

    fn eq(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        app(dag, "=", vec![lhs, rhs])
    }

    fn le(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        app(dag, "<=", vec![lhs, rhs])
    }

    fn ge(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        app(dag, ">=", vec![lhs, rhs])
    }

    fn add(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        app(dag, "+", vec![lhs, rhs])
    }

    fn function_app(dag: &mut SmtProofDag, name: &str, arg: SmtTermId) -> SmtTermId {
        app(dag, name, vec![arg])
    }

    fn predicate_app(dag: &mut SmtProofDag, name: &str, arg: SmtTermId) -> SmtTermId {
        app(dag, name, vec![arg])
    }

    fn build_partition(
        dag: &SmtProofDag,
        a_assumptions: &[SmtStepId],
        b_assumptions: &[SmtStepId],
    ) -> SmtPartition {
        let mut partition = SmtPartition {
            a_assumptions: a_assumptions.iter().copied().collect(),
            b_assumptions: b_assumptions.iter().copied().collect(),
            shared_variables: HashSet::new(),
        };
        let result = partition.compute_shared_variables(dag);
        assert!(result.is_ok(), "partition should compute shared variables");
        partition
    }

    fn shared_vars(interpolant: &SmtInterpolant) -> HashSet<String> {
        fn visit(term: &SmtInterpolant, vars: &mut HashSet<String>) {
            match term {
                SmtInterpolant::Var(name, _) => {
                    vars.insert(name.clone());
                }
                SmtInterpolant::Not(inner) => visit(inner, vars),
                SmtInterpolant::AndType(lhs, rhs) | SmtInterpolant::Or(lhs, rhs) => {
                    visit(lhs, vars);
                    visit(rhs, vars);
                }
                SmtInterpolant::LinearIneq { coefficients, .. } => {
                    for (name, _) in coefficients {
                        vars.insert(name.clone());
                    }
                }
                SmtInterpolant::Eq(lhs, rhs) => {
                    vars.insert(lhs.clone());
                    vars.insert(rhs.clone());
                }
                SmtInterpolant::App(_, args) => {
                    for arg in args {
                        visit(arg, vars);
                    }
                }
                SmtInterpolant::BoolConst(_) => {}
            }
        }

        let mut vars = HashSet::new();
        visit(interpolant, &mut vars);
        vars
    }

    #[test]
    fn test_partition_shared_variables() {
        let mut dag = SmtProofDag::new();
        let x = int_var(&mut dag, "x");
        let y = int_var(&mut dag, "y");
        let zero = int_const(&mut dag, 0);
        let one = int_const(&mut dag, 1);
        let x_plus_y = add(&mut dag, x, y);
        let a_term = le(&mut dag, x, zero);
        let b_term = ge(&mut dag, x_plus_y, one);
        let a_step = dag.add_step(SmtProofStep::Assume(a_term));
        let b_step = dag.add_step(SmtProofStep::Assume(b_term));

        let mut partition = SmtPartition {
            a_assumptions: [a_step].into_iter().collect(),
            b_assumptions: [b_step].into_iter().collect(),
            shared_variables: HashSet::new(),
        };
        let result = partition.compute_shared_variables(&dag);
        assert!(result.is_ok(), "shared variables should compute");
        assert_eq!(
            partition.shared_variables,
            ["x".to_string()].into_iter().collect()
        );
    }

    #[test]
    fn test_pure_propositional_interpolation() {
        let mut dag = SmtProofDag::new();
        let p = bool_var(&mut dag, "p");
        let q = bool_var(&mut dag, "q");
        let not_p = not(&mut dag, p);
        let not_q = not(&mut dag, q);

        let a_p = dag.add_step(SmtProofStep::Assume(p));
        let a_q = dag.add_step(SmtProofStep::Assume(q));
        let b_not_p = dag.add_step(SmtProofStep::Assume(not_p));
        let b_not_q = dag.add_step(SmtProofStep::Assume(not_q));
        let root = dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![a_p, b_not_p],
            pivot: Some(p),
        });

        let partition = build_partition(&dag, &[a_p, a_q], &[b_not_p, b_not_q]);
        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert!(
            interpolant.is_ok(),
            "pure propositional interpolation should succeed"
        );
        assert_eq!(
            interpolant.ok(),
            Some(SmtInterpolant::Var("p".to_string(), SmtSort::Bool))
        );
        assert_eq!(root, SmtStepId(4));
    }

    #[test]
    fn test_lra_farkas_interpolation() {
        let mut dag = SmtProofDag::new();
        let x = int_var(&mut dag, "x");
        let zero = int_const(&mut dag, 0);
        let one = int_const(&mut dag, 1);
        let a_atom = le(&mut dag, x, zero);
        let b_atom = ge(&mut dag, x, one);
        let a_step = dag.add_step(SmtProofStep::Assume(a_atom));
        let b_step = dag.add_step(SmtProofStep::Assume(b_atom));
        let not_a_atom = not(&mut dag, a_atom);
        let not_b_atom = not(&mut dag, b_atom);
        let lemma = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Lra,
            kind: TheoryLemmaDetail::LraFarkas {
                coefficients: vec![(1, 1), (1, 1)],
            },
            clause: vec![not_a_atom, not_b_atom],
        });

        let partition = build_partition(&dag, &[a_step], &[b_step]);
        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert!(interpolant.is_ok(), "LRA interpolation should succeed");
        assert_eq!(
            interpolant.ok(),
            Some(SmtInterpolant::LinearIneq {
                coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
                constant: Rational64::from_integer(0),
                relation: ArithRelation::Le,
            })
        );
        assert_eq!(lemma, SmtStepId(2));
    }

    #[test]
    fn test_euf_congruence_interpolation() {
        let mut dag = SmtProofDag::new();
        let a = int_var(&mut dag, "a");
        let b = int_var(&mut dag, "b");
        let f_a = function_app(&mut dag, "f", a);
        let f_b = function_app(&mut dag, "f", b);
        let eq_ab = eq(&mut dag, a, b);
        let eq_fafb = eq(&mut dag, f_a, f_b);
        let a_step = dag.add_step(SmtProofStep::Assume(eq_ab));
        let p_f_a = predicate_app(&mut dag, "P", f_a);
        let shared_f = dag.add_step(SmtProofStep::Assume(p_f_a));
        let not_eq_fafb = not(&mut dag, eq_fafb);
        let b_step = dag.add_step(SmtProofStep::Assume(not_eq_fafb));
        let not_eq_ab = not(&mut dag, eq_ab);
        let _lemma = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Euf,
            kind: TheoryLemmaDetail::EufCongruent,
            clause: vec![not_eq_ab, eq_fafb],
        });

        let partition = build_partition(&dag, &[a_step, shared_f], &[b_step]);
        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert!(interpolant.is_ok(), "EUF interpolation should succeed");
        assert_eq!(
            interpolant.ok(),
            Some(SmtInterpolant::Eq("a".to_string(), "b".to_string()))
        );
    }

    #[test]
    fn test_mixed_theory_interpolation() {
        let mut dag = SmtProofDag::new();
        let x = int_var(&mut dag, "x");
        let zero = int_const(&mut dag, 0);
        let one = int_const(&mut dag, 1);
        let a_atom = le(&mut dag, x, zero);
        let b_atom = ge(&mut dag, x, one);
        let a_step = dag.add_step(SmtProofStep::Assume(a_atom));
        let b_step = dag.add_step(SmtProofStep::Assume(b_atom));
        let not_a_atom = not(&mut dag, a_atom);
        let not_b_atom = not(&mut dag, b_atom);
        let lemma_clause = vec![not_a_atom, not_b_atom];
        let lemma = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Lra,
            kind: TheoryLemmaDetail::LraFarkas {
                coefficients: vec![(1, 1), (1, 1)],
            },
            clause: lemma_clause,
        });
        let mid_clause = vec![not_b_atom];
        let mid = dag.add_step(SmtProofStep::Resolution {
            clause: mid_clause,
            premises: vec![a_step, lemma],
            pivot: Some(a_atom),
        });
        let _root = dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![b_step, mid],
            pivot: Some(b_atom),
        });

        let partition = build_partition(&dag, &[a_step], &[b_step]);
        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert!(interpolant.is_ok(), "mixed interpolation should succeed");
        assert_eq!(
            interpolant.ok(),
            Some(SmtInterpolant::LinearIneq {
                coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
                constant: Rational64::from_integer(0),
                relation: ArithRelation::Le,
            })
        );
    }

    #[test]
    fn test_shared_variable_extraction() {
        let mut dag = SmtProofDag::new();
        let x = int_var(&mut dag, "x");
        let y = int_var(&mut dag, "y");
        let lhs = add(&mut dag, x, y);
        let a_atom = le(&mut dag, lhs, y);
        let one = int_const(&mut dag, 1);
        let b_atom = ge(&mut dag, x, one);
        let a_step = dag.add_step(SmtProofStep::Assume(a_atom));
        let b_step = dag.add_step(SmtProofStep::Assume(b_atom));
        let not_a_atom = not(&mut dag, a_atom);
        let not_b_atom = not(&mut dag, b_atom);
        let lemma = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Lra,
            kind: TheoryLemmaDetail::LraFarkas {
                coefficients: vec![(1, 1), (1, 1)],
            },
            clause: vec![not_a_atom, not_b_atom],
        });

        let partition = build_partition(&dag, &[a_step], &[b_step]);
        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert!(interpolant.is_ok(), "interpolation should succeed");
        let vars = shared_vars(&interpolant.unwrap_or(SmtInterpolant::BoolConst(false)));
        assert_eq!(vars, ["x".to_string()].into_iter().collect());
        assert_eq!(lemma, SmtStepId(2));
    }

    #[test]
    fn test_invalid_partition_overlap() {
        let mut dag = SmtProofDag::new();
        let p = bool_var(&mut dag, "p");
        let assume = dag.add_step(SmtProofStep::Assume(p));
        let partition = SmtPartition {
            a_assumptions: [assume].into_iter().collect(),
            b_assumptions: [assume].into_iter().collect(),
            shared_variables: HashSet::new(),
        };

        let result = interpolate_smt_proof(&dag, &partition);
        assert_eq!(
            result.err(),
            Some(InterpolationError::InvalidPartition(
                "assumption step appears in both partitions".to_string()
            ))
        );
    }

    #[test]
    fn test_trivial_a_unsat() {
        let mut dag = SmtProofDag::new();
        let false_term = dag.add_term(SmtTerm::Bool(false));
        let a_step = dag.add_step(SmtProofStep::Assume(false_term));
        let partition = build_partition(&dag, &[a_step], &[]);

        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert_eq!(interpolant.ok(), Some(SmtInterpolant::BoolConst(false)));
    }

    #[test]
    fn test_trivial_b_unsat() {
        let mut dag = SmtProofDag::new();
        let false_term = dag.add_term(SmtTerm::Bool(false));
        let b_step = dag.add_step(SmtProofStep::Assume(false_term));
        let partition = build_partition(&dag, &[], &[b_step]);

        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert_eq!(interpolant.ok(), Some(SmtInterpolant::BoolConst(true)));
    }

    #[test]
    fn test_empty_proof_error() {
        let dag = SmtProofDag::new();
        let partition = SmtPartition::default();
        let result = interpolate_smt_proof(&dag, &partition);
        assert_eq!(result.err(), Some(InterpolationError::EmptyProof));
    }

    #[test]
    fn test_interpolant_simplify() {
        let folded = SmtInterpolant::and(
            SmtInterpolant::or(
                SmtInterpolant::BoolConst(false),
                SmtInterpolant::Var("p".to_string(), SmtSort::Bool),
            ),
            SmtInterpolant::not(SmtInterpolant::BoolConst(false)),
        );
        assert_eq!(folded, SmtInterpolant::Var("p".to_string(), SmtSort::Bool));
    }

    #[test]
    fn test_a_input_no_shared_vars() {
        let mut dag = SmtProofDag::new();
        let q = bool_var(&mut dag, "q");
        let a_step = dag.add_step(SmtProofStep::Assume(q));
        let partition = build_partition(&dag, &[a_step], &[]);

        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert_eq!(interpolant.ok(), Some(SmtInterpolant::BoolConst(false)));
    }

    #[test]
    fn test_b_input_always_true() {
        let mut dag = SmtProofDag::new();
        let q = bool_var(&mut dag, "q");
        let b_step = dag.add_step(SmtProofStep::Assume(q));
        let partition = build_partition(&dag, &[], &[b_step]);

        let interpolant = interpolate_smt_proof(&dag, &partition);
        assert_eq!(interpolant.ok(), Some(SmtInterpolant::BoolConst(true)));
    }

    #[test]
    fn test_resolution_a_only_pivot() {
        let mut dag = SmtProofDag::new();
        let a = bool_var(&mut dag, "a");
        let not_a = not(&mut dag, a);
        let left_step = dag.add_step(SmtProofStep::Assume(a));
        let right_step = dag.add_step(SmtProofStep::Assume(not_a));
        let partition = build_partition(&dag, &[left_step, right_step], &[]);
        let analysis = match PartitionAnalysis::from_partition(&dag, &partition) {
            Ok(analysis) => analysis,
            Err(error) => panic!("partition analysis should succeed: {error}"),
        };

        let result = apply_resolution_rule(
            &dag,
            a,
            &[a],
            &[not_a],
            SmtInterpolant::BoolConst(true),
            SmtInterpolant::BoolConst(false),
            &analysis,
        );
        assert_eq!(result.ok(), Some(SmtInterpolant::BoolConst(true)));
    }

    #[test]
    fn test_resolution_b_only_pivot() {
        let mut dag = SmtProofDag::new();
        let b = bool_var(&mut dag, "b");
        let not_b = not(&mut dag, b);
        let left_step = dag.add_step(SmtProofStep::Assume(b));
        let right_step = dag.add_step(SmtProofStep::Assume(not_b));
        let partition = build_partition(&dag, &[], &[left_step, right_step]);
        let analysis = match PartitionAnalysis::from_partition(&dag, &partition) {
            Ok(analysis) => analysis,
            Err(error) => panic!("partition analysis should succeed: {error}"),
        };

        let result = apply_resolution_rule(
            &dag,
            b,
            &[b],
            &[not_b],
            SmtInterpolant::BoolConst(true),
            SmtInterpolant::BoolConst(false),
            &analysis,
        );
        assert_eq!(result.ok(), Some(SmtInterpolant::BoolConst(false)));
    }
}
