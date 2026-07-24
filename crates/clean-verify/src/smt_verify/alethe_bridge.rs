// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge between the Alethe text parser and the SMT proof verifier.
//!
//! The Alethe parser ([`alethe_parser`]) produces its own AST types optimized
//! for parsing. The verifier pipeline consumes [`dag::SmtProofDag`]. This
//! module converts between the two representations.
//!
//! The conversion is a straightforward structural mapping: the parser and
//! DAG types share the same semantic structure but are separate Rust types
//! to allow each module to evolve independently.

use std::collections::{BTreeMap, HashMap};

use super::alethe_parser;
use super::dag;

/// Convert an Alethe-parser proof DAG to the verifier's canonical DAG format.
///
/// This conversion performs **hash-consing** (term deduplication): structurally
/// identical parser terms are mapped to a single DAG term ID. This is critical
/// for theory-heavy proofs where the parser creates fresh arena entries for
/// each textual occurrence of a term, causing the resolution checker's
/// ID-based pivot matching to fail on duplicate terms.
///
/// Steps and declarations are converted structurally with term IDs remapped
/// through the deduplication table.
#[must_use]
pub(crate) fn alethe_to_dag(parsed: alethe_parser::SmtProofDag) -> dag::SmtProofDag {
    let mut converter = DedupConverter::new();
    converter.convert_all_terms(&parsed.terms);
    let steps = parsed
        .steps
        .into_iter()
        .map(|step| converter.convert_step(step))
        .collect();
    let declarations = convert_declarations(parsed.declarations);

    dag::SmtProofDag {
        terms: converter.dag_terms,
        steps,
        declarations,
    }
}

/// Stateful converter that deduplicates terms via hash-consing.
///
/// Maintains a mapping from old parser term IDs to new (deduplicated) DAG
/// term IDs, and a reverse map from DAG term structure to DAG term ID for
/// detecting duplicates.
struct DedupConverter {
    /// The deduplicated term arena being built.
    dag_terms: Vec<dag::SmtTerm>,
    /// Maps each parser `SmtTermId` to the corresponding (deduplicated) DAG `SmtTermId`.
    id_map: Vec<dag::SmtTermId>,
    /// Reverse map: DAG term structure -> DAG term ID, for hash-consing.
    term_to_id: HashMap<dag::SmtTerm, dag::SmtTermId>,
}

impl DedupConverter {
    fn new() -> Self {
        Self {
            dag_terms: Vec::new(),
            id_map: Vec::new(),
            term_to_id: HashMap::new(),
        }
    }

    /// Convert all parser terms, populating the id_map and dag_terms.
    ///
    /// Terms are processed in arena order (index 0, 1, 2, ...). Because
    /// children always have lower indices than their parents in the parser
    /// arena, every child ID is already mapped when we process a parent.
    fn convert_all_terms(&mut self, parser_terms: &[alethe_parser::SmtTerm]) {
        self.id_map.reserve(parser_terms.len());
        for parser_term in parser_terms {
            let dag_term = self.convert_term(parser_term);
            let dag_id = if let Some(&existing_id) = self.term_to_id.get(&dag_term) {
                existing_id
            } else {
                let new_id = dag::SmtTermId(self.dag_terms.len() as u32);
                self.term_to_id.insert(dag_term.clone(), new_id);
                self.dag_terms.push(dag_term);
                new_id
            };
            self.id_map.push(dag_id);
        }
    }

    /// Convert a single parser term to a DAG term, remapping child IDs
    /// through the deduplication table.
    fn convert_term(&self, term: &alethe_parser::SmtTerm) -> dag::SmtTerm {
        match term {
            alethe_parser::SmtTerm::Var(name, sort) => {
                dag::SmtTerm::Var(name.clone(), convert_sort(sort.clone()))
            }
            alethe_parser::SmtTerm::Bool(v) => dag::SmtTerm::Bool(*v),
            alethe_parser::SmtTerm::Int(v) => dag::SmtTerm::Int(*v),
            alethe_parser::SmtTerm::Rational(n, d) => dag::SmtTerm::Rational(*n, *d),
            alethe_parser::SmtTerm::BitVec(v, w) => dag::SmtTerm::BitVec(*v, *w),
            alethe_parser::SmtTerm::Str(s) => dag::SmtTerm::Str(s.clone()),
            alethe_parser::SmtTerm::App(symbol, args) => {
                dag::SmtTerm::App(convert_symbol(symbol.clone()), self.remap_term_ids(args))
            }
            alethe_parser::SmtTerm::Not(inner) => dag::SmtTerm::Not(self.remap_term_id(*inner)),
            alethe_parser::SmtTerm::Ite(c, t, e) => dag::SmtTerm::Ite(
                self.remap_term_id(*c),
                self.remap_term_id(*t),
                self.remap_term_id(*e),
            ),
            alethe_parser::SmtTerm::Let(bindings, body) => {
                let dag_bindings = bindings
                    .iter()
                    .map(|(name, id)| (name.clone(), self.remap_term_id(*id)))
                    .collect();
                dag::SmtTerm::Let(dag_bindings, self.remap_term_id(*body))
            }
            alethe_parser::SmtTerm::Forall(vars, body) => {
                let dag_vars = vars
                    .iter()
                    .map(|(name, sort)| (name.clone(), convert_sort(sort.clone())))
                    .collect();
                dag::SmtTerm::Forall(dag_vars, self.remap_term_id(*body))
            }
            alethe_parser::SmtTerm::Exists(vars, body) => {
                let dag_vars = vars
                    .iter()
                    .map(|(name, sort)| (name.clone(), convert_sort(sort.clone())))
                    .collect();
                dag::SmtTerm::Exists(dag_vars, self.remap_term_id(*body))
            }
        }
    }

    /// Remap a single parser term ID through the deduplication table.
    fn remap_term_id(&self, id: alethe_parser::SmtTermId) -> dag::SmtTermId {
        self.id_map[id.0 as usize]
    }

    /// Remap a slice of parser term IDs through the deduplication table.
    fn remap_term_ids(&self, ids: &[alethe_parser::SmtTermId]) -> Vec<dag::SmtTermId> {
        ids.iter().map(|id| self.remap_term_id(*id)).collect()
    }

    /// Convert a proof step, remapping all term and step IDs.
    fn convert_step(&self, step: alethe_parser::SmtProofStep) -> dag::SmtProofStep {
        match step {
            alethe_parser::SmtProofStep::Assume(t) => {
                dag::SmtProofStep::Assume(self.remap_term_id(t))
            }
            alethe_parser::SmtProofStep::Resolution {
                clause,
                premises,
                pivot,
            } => dag::SmtProofStep::Resolution {
                clause: self.remap_term_ids(&clause),
                premises: convert_step_ids(premises),
                pivot: pivot.map(|p| self.remap_term_id(p)),
            },
            alethe_parser::SmtProofStep::TheoryLemma {
                theory,
                kind,
                clause,
            } => dag::SmtProofStep::TheoryLemma {
                theory: convert_theory(theory),
                kind: convert_theory_lemma_detail(kind),
                clause: self.remap_term_ids(&clause),
            },
            alethe_parser::SmtProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => dag::SmtProofStep::Step {
                rule: convert_rule_kind(rule),
                clause: self.remap_term_ids(&clause),
                premises: convert_step_ids(premises),
                args: self.remap_term_ids(&args),
            },
            alethe_parser::SmtProofStep::Anchor {
                end_step,
                variables,
            } => dag::SmtProofStep::Anchor {
                end_step: convert_step_id(end_step),
                variables: variables
                    .into_iter()
                    .map(|(name, sort)| (name, convert_sort(sort)))
                    .collect(),
            },
        }
    }
}

/// Return the number of terms that were deduplicated (removed as duplicates).
///
/// This is a diagnostic helper: `original_count - dag.num_terms()` gives the
/// number of duplicate entries eliminated.
#[must_use]
pub(crate) fn dedup_stats(original_term_count: usize, dag: &dag::SmtProofDag) -> usize {
    original_term_count.saturating_sub(dag.num_terms())
}

fn convert_sort(sort: alethe_parser::SmtSort) -> dag::SmtSort {
    match sort {
        alethe_parser::SmtSort::Bool => dag::SmtSort::Bool,
        alethe_parser::SmtSort::Int => dag::SmtSort::Int,
        alethe_parser::SmtSort::Real => dag::SmtSort::Real,
        alethe_parser::SmtSort::BitVec(w) => dag::SmtSort::BitVec(w),
        alethe_parser::SmtSort::Array(k, v) => {
            dag::SmtSort::Array(Box::new(convert_sort(*k)), Box::new(convert_sort(*v)))
        }
        alethe_parser::SmtSort::String => dag::SmtSort::String,
        alethe_parser::SmtSort::Named(name) => dag::SmtSort::Named(name),
    }
}

fn convert_symbol(symbol: alethe_parser::SmtSymbol) -> dag::SmtSymbol {
    match symbol {
        alethe_parser::SmtSymbol::Named(name) => dag::SmtSymbol::Named(name),
        alethe_parser::SmtSymbol::Indexed(name, indices) => dag::SmtSymbol::Indexed(name, indices),
    }
}

fn convert_step_id(id: alethe_parser::SmtStepId) -> dag::SmtStepId {
    dag::SmtStepId(id.0)
}

fn convert_step_ids(ids: Vec<alethe_parser::SmtStepId>) -> Vec<dag::SmtStepId> {
    ids.into_iter().map(convert_step_id).collect()
}

fn convert_theory(theory: alethe_parser::SmtTheory) -> dag::SmtTheory {
    match theory {
        alethe_parser::SmtTheory::Core => dag::SmtTheory::Core,
        alethe_parser::SmtTheory::Euf => dag::SmtTheory::Euf,
        alethe_parser::SmtTheory::Lra => dag::SmtTheory::Lra,
        alethe_parser::SmtTheory::Lia => dag::SmtTheory::Lia,
        alethe_parser::SmtTheory::Bv => dag::SmtTheory::Bv,
        alethe_parser::SmtTheory::Arrays => dag::SmtTheory::Arrays,
        alethe_parser::SmtTheory::Fp => dag::SmtTheory::Fp,
        alethe_parser::SmtTheory::Strings => dag::SmtTheory::Strings,
    }
}

fn convert_theory_lemma_detail(kind: alethe_parser::TheoryLemmaDetail) -> dag::TheoryLemmaDetail {
    match kind {
        alethe_parser::TheoryLemmaDetail::EufTransitive => dag::TheoryLemmaDetail::EufTransitive,
        alethe_parser::TheoryLemmaDetail::EufCongruent => dag::TheoryLemmaDetail::EufCongruent,
        alethe_parser::TheoryLemmaDetail::EufCongruentPred => {
            dag::TheoryLemmaDetail::EufCongruentPred
        }
        alethe_parser::TheoryLemmaDetail::LraFarkas { coefficients } => {
            dag::TheoryLemmaDetail::LraFarkas { coefficients }
        }
        alethe_parser::TheoryLemmaDetail::LiaGeneric { annotation } => {
            dag::TheoryLemmaDetail::LiaGeneric {
                annotation: convert_lia_detail(annotation),
                coefficients: None,
            }
        }
        alethe_parser::TheoryLemmaDetail::BvBitBlast { gate_type, width } => {
            dag::TheoryLemmaDetail::BvBitBlast { gate_type, width }
        }
        alethe_parser::TheoryLemmaDetail::ArraySelectStore { index_eq } => {
            dag::TheoryLemmaDetail::ArraySelectStore { index_eq }
        }
        alethe_parser::TheoryLemmaDetail::ArrayExtensionality => {
            dag::TheoryLemmaDetail::ArrayExtensionality
        }
        alethe_parser::TheoryLemmaDetail::FpToBv { operation } => {
            dag::TheoryLemmaDetail::FpToBv { operation }
        }
        alethe_parser::TheoryLemmaDetail::StringLength => dag::TheoryLemmaDetail::StringLength,
        alethe_parser::TheoryLemmaDetail::StringContent => dag::TheoryLemmaDetail::StringContent,
        alethe_parser::TheoryLemmaDetail::StringNormalForm => {
            dag::TheoryLemmaDetail::StringNormalForm
        }
        alethe_parser::TheoryLemmaDetail::Generic => dag::TheoryLemmaDetail::Generic,
    }
}

fn convert_lia_detail(detail: alethe_parser::LiaDetail) -> dag::LiaDetail {
    match detail {
        alethe_parser::LiaDetail::BoundsGap => dag::LiaDetail::BoundsGap,
        alethe_parser::LiaDetail::Divisibility => dag::LiaDetail::Divisibility,
        alethe_parser::LiaDetail::CuttingPlane { divisor } => {
            dag::LiaDetail::CuttingPlane { divisor }
        }
        alethe_parser::LiaDetail::FarkasOnly => dag::LiaDetail::FarkasOnly,
    }
}

/// Convert an Alethe parser rule kind to the verifier's canonical rule kind.
///
/// The parser has a flat enum (e.g., `AndType`, `Or`, `Not*` variants for all
/// boolean connectives). The dag's `AletheRuleKind` parameterizes some rules
/// (e.g., `AndPos(u32)`, `OrNeg(u32)`) and omits some compound boolean
/// rules that the parser recognizes. Non-matching parser rules map to
/// `dag::AletheRuleKind::Other`.
fn convert_rule_kind(rule: alethe_parser::AletheRuleKind) -> dag::AletheRuleKind {
    match rule {
        alethe_parser::AletheRuleKind::True => dag::AletheRuleKind::True,
        alethe_parser::AletheRuleKind::False => dag::AletheRuleKind::False,
        alethe_parser::AletheRuleKind::NotTrue => dag::AletheRuleKind::NotTrue,
        alethe_parser::AletheRuleKind::NotFalse => dag::AletheRuleKind::NotFalse,

        // Parser AndPos has no index; dag AndPos requires u32.
        // Without argument parsing we default to index 0.
        alethe_parser::AletheRuleKind::AndPos => dag::AletheRuleKind::AndPos(0),
        alethe_parser::AletheRuleKind::AndNeg => dag::AletheRuleKind::AndNeg,
        alethe_parser::AletheRuleKind::OrPos => dag::AletheRuleKind::OrPos,
        alethe_parser::AletheRuleKind::OrNeg => dag::AletheRuleKind::OrNeg(0),

        alethe_parser::AletheRuleKind::ImpliesPos => dag::AletheRuleKind::ImpliesPos,
        alethe_parser::AletheRuleKind::ImpliesNeg1 => dag::AletheRuleKind::ImpliesNeg1,
        alethe_parser::AletheRuleKind::ImpliesNeg2 => dag::AletheRuleKind::ImpliesNeg2,
        alethe_parser::AletheRuleKind::EquivPos1 => dag::AletheRuleKind::EquivPos1,
        alethe_parser::AletheRuleKind::EquivPos2 => dag::AletheRuleKind::EquivPos2,
        alethe_parser::AletheRuleKind::EquivNeg1 => dag::AletheRuleKind::EquivNeg1,
        alethe_parser::AletheRuleKind::EquivNeg2 => dag::AletheRuleKind::EquivNeg2,
        alethe_parser::AletheRuleKind::ItePos1 => dag::AletheRuleKind::ItePos1,
        alethe_parser::AletheRuleKind::ItePos2 => dag::AletheRuleKind::ItePos2,
        alethe_parser::AletheRuleKind::IteNeg1 => dag::AletheRuleKind::IteNeg1,
        alethe_parser::AletheRuleKind::IteNeg2 => dag::AletheRuleKind::IteNeg2,
        alethe_parser::AletheRuleKind::Contraction => dag::AletheRuleKind::Contraction,

        alethe_parser::AletheRuleKind::Resolution => dag::AletheRuleKind::Resolution,
        alethe_parser::AletheRuleKind::ThResolution => dag::AletheRuleKind::ThResolution,

        alethe_parser::AletheRuleKind::Refl => dag::AletheRuleKind::Refl,
        alethe_parser::AletheRuleKind::Symm => dag::AletheRuleKind::Symm,
        alethe_parser::AletheRuleKind::Trans => dag::AletheRuleKind::Trans,
        alethe_parser::AletheRuleKind::Cong => dag::AletheRuleKind::Cong,

        alethe_parser::AletheRuleKind::EqReflexive => dag::AletheRuleKind::EqReflexive,
        alethe_parser::AletheRuleKind::EqTransitive => dag::AletheRuleKind::EqTransitive,
        alethe_parser::AletheRuleKind::EqCongruent => dag::AletheRuleKind::EqCongruent,
        alethe_parser::AletheRuleKind::EqCongruentPred => dag::AletheRuleKind::EqCongruentPred,

        alethe_parser::AletheRuleKind::LaGeneric => dag::AletheRuleKind::LaGeneric,
        alethe_parser::AletheRuleKind::LaTautology => dag::AletheRuleKind::LaTautology,
        alethe_parser::AletheRuleKind::LaDisequality => dag::AletheRuleKind::LaDisequality,
        alethe_parser::AletheRuleKind::LaTotality => dag::AletheRuleKind::LaTotality,
        alethe_parser::AletheRuleKind::LaMultPos => {
            dag::AletheRuleKind::Other("la_mult_pos".to_string())
        }
        alethe_parser::AletheRuleKind::LaMultNeg => {
            dag::AletheRuleKind::Other("la_mult_neg".to_string())
        }

        alethe_parser::AletheRuleKind::LiaGeneric => dag::AletheRuleKind::LiaGeneric,

        alethe_parser::AletheRuleKind::BvBitblast => dag::AletheRuleKind::BvBitblast,

        alethe_parser::AletheRuleKind::ReadOverWritePos => dag::AletheRuleKind::ReadOverWritePos,
        alethe_parser::AletheRuleKind::ReadOverWriteNeg => dag::AletheRuleKind::ReadOverWriteNeg,
        alethe_parser::AletheRuleKind::Extensionality => dag::AletheRuleKind::Extensionality,

        alethe_parser::AletheRuleKind::FpToBv => dag::AletheRuleKind::FpToBv,

        alethe_parser::AletheRuleKind::StringLength => dag::AletheRuleKind::StringLength,
        alethe_parser::AletheRuleKind::StringDecompose => dag::AletheRuleKind::StringDecompose,
        alethe_parser::AletheRuleKind::StringCodeInj => dag::AletheRuleKind::StringCodeInj,

        alethe_parser::AletheRuleKind::ForallInst => dag::AletheRuleKind::ForallInst,
        alethe_parser::AletheRuleKind::Skolem => dag::AletheRuleKind::Skolem,

        alethe_parser::AletheRuleKind::Subproof => dag::AletheRuleKind::Subproof,
        alethe_parser::AletheRuleKind::Bind => dag::AletheRuleKind::Bind,

        alethe_parser::AletheRuleKind::AllSimplify => dag::AletheRuleKind::AllSimplify,
        alethe_parser::AletheRuleKind::BoolSimplify => dag::AletheRuleKind::BoolSimplify,
        alethe_parser::AletheRuleKind::ArithSimplify => dag::AletheRuleKind::ArithSimplify,

        alethe_parser::AletheRuleKind::Hole => dag::AletheRuleKind::Hole,
        alethe_parser::AletheRuleKind::Drup => dag::AletheRuleKind::Drup,
        alethe_parser::AletheRuleKind::Trust => dag::AletheRuleKind::Trust,

        // Compound boolean rules that the parser tracks but the verifier
        // treats as generic step rules.
        alethe_parser::AletheRuleKind::AndType
        | alethe_parser::AletheRuleKind::NotAnd
        | alethe_parser::AletheRuleKind::Or
        | alethe_parser::AletheRuleKind::NotOr
        | alethe_parser::AletheRuleKind::Implies
        | alethe_parser::AletheRuleKind::NotImplies1
        | alethe_parser::AletheRuleKind::NotImplies2
        | alethe_parser::AletheRuleKind::Equiv
        | alethe_parser::AletheRuleKind::NotEquiv1
        | alethe_parser::AletheRuleKind::NotEquiv2
        | alethe_parser::AletheRuleKind::Ite
        | alethe_parser::AletheRuleKind::NotIte1
        | alethe_parser::AletheRuleKind::NotIte2
        | alethe_parser::AletheRuleKind::XorPos1
        | alethe_parser::AletheRuleKind::XorPos2
        | alethe_parser::AletheRuleKind::XorNeg1
        | alethe_parser::AletheRuleKind::XorNeg2 => {
            dag::AletheRuleKind::Other(rule.name().to_string())
        }

        alethe_parser::AletheRuleKind::Custom(name) => dag::AletheRuleKind::Other(name),
    }
}

fn convert_declarations(
    decls: BTreeMap<String, alethe_parser::SmtSort>,
) -> BTreeMap<String, dag::SmtSort> {
    decls
        .into_iter()
        .map(|(name, sort)| (name, convert_sort(sort)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::alethe_parser::parse_alethe;

    #[test]
    fn test_alethe_to_dag_basic_resolution() {
        let input = r#"
            (declare-const p Bool)
            (assume h1 p)
            (step t1 (cl (not p)) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let dag = alethe_to_dag(parsed);
        // With hash-consing, the two occurrences of `p` are deduplicated
        // to a single term. We get: p (Var), not(p) => 2 unique terms.
        assert_eq!(dag.num_terms(), 2);
        assert_eq!(dag.num_steps(), 3); // assume, trust, resolution
    }

    #[test]
    fn test_alethe_to_dag_preserves_term_references() {
        let input = r#"
            (declare-const x Int)
            (declare-const y Int)
            (assume h1 (= x y))
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let dag = alethe_to_dag(parsed);
        // The assume step should reference a valid (remapped) term.
        match dag.step(dag::SmtStepId(0)) {
            Some(dag::SmtProofStep::Assume(t)) => {
                assert!(dag.term(*t).is_some());
            }
            other => panic!("expected assume, found {other:?}"),
        }
    }

    #[test]
    fn test_alethe_to_dag_euf_theory_lemma() {
        let input = r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-const c U)
            (step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let dag = alethe_to_dag(parsed);
        match dag.step(dag::SmtStepId(0)) {
            Some(dag::SmtProofStep::TheoryLemma {
                theory,
                kind,
                clause,
            }) => {
                assert_eq!(*theory, dag::SmtTheory::Euf);
                assert!(matches!(kind, dag::TheoryLemmaDetail::EufTransitive));
                assert_eq!(clause.len(), 3);
            }
            other => panic!("expected EUF theory lemma, found {other:?}"),
        }
    }

    #[test]
    fn test_alethe_to_dag_declarations() {
        let input = r#"
            (declare-const x Int)
            (declare-const y Real)
            (declare-const z Bool)
            (assume h1 z)
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let dag = alethe_to_dag(parsed);
        assert_eq!(dag.declarations.get("x"), Some(&dag::SmtSort::Int));
        assert_eq!(dag.declarations.get("y"), Some(&dag::SmtSort::Real));
        assert_eq!(dag.declarations.get("z"), Some(&dag::SmtSort::Bool));
    }

    /// Test that hash-consing deduplicates structurally identical terms.
    ///
    /// This proof uses `p` in multiple steps: assume(p), cl(not p), and
    /// a resolution that refers to both. Without dedup, the parser creates
    /// separate arena entries for each `p` occurrence (typically 3: one in
    /// assume, one in not(p), and one implicit). With dedup, the Var("p")
    /// term is stored once and all references share the same ID.
    #[test]
    fn test_dedup_merges_identical_terms() {
        let input = r#"
            (declare-const p Bool)
            (assume h1 p)
            (step t1 (cl (not p)) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let parser_term_count = parsed.terms.len();
        let dag = alethe_to_dag(parsed);

        // The parser creates 3 entries: p (h1), p (inside not), not(p).
        // After dedup: p, not(p) => 2 unique terms.
        assert_eq!(parser_term_count, 3, "parser should produce 3 raw terms");
        assert_eq!(dag.num_terms(), 2, "dedup should reduce to 2 unique terms");

        // Verify the assume and the not(p) both reference the same p ID.
        let assume_term_id = match dag.step(dag::SmtStepId(0)) {
            Some(dag::SmtProofStep::Assume(t)) => *t,
            other => panic!("expected assume, found {other:?}"),
        };
        let not_inner_id = match dag.step(dag::SmtStepId(1)) {
            Some(dag::SmtProofStep::TheoryLemma { clause, .. }) => match dag.term(clause[0]) {
                Some(dag::SmtTerm::Not(inner)) => *inner,
                other => panic!("expected Not term, found {other:?}"),
            },
            other => panic!("expected theory lemma, found {other:?}"),
        };
        assert_eq!(
            assume_term_id, not_inner_id,
            "assume(p) and not(p) must share the same p term ID after dedup"
        );
    }

    /// Test dedup on a theory-heavy proof with repeated equality terms.
    ///
    /// This is the core scenario that motivates hash-consing: when a term
    /// like `(= a b)` appears in multiple clauses, the resolution checker
    /// needs them to share the same ID for pivot matching.
    #[test]
    fn test_dedup_euf_repeated_equalities() {
        let input = r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (assume h1 (= a b))
            (step t1 (cl (not (= a b))) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let parser_term_count = parsed.terms.len();
        let dag = alethe_to_dag(parsed);

        // Without dedup: a, b, (= a b), a', b', (= a' b'), not((= a' b'))
        // = 7 parser terms (a and b repeated inside second (= a b)).
        // With dedup: a, b, (= a b), not((= a b)) = 4 unique terms.
        assert!(
            dag.num_terms() < parser_term_count,
            "dedup should reduce term count: {} < {}",
            dag.num_terms(),
            parser_term_count
        );

        // Verify that assume(= a b) and not(= a b) share the same (= a b) ID.
        let assume_eq_id = match dag.step(dag::SmtStepId(0)) {
            Some(dag::SmtProofStep::Assume(t)) => *t,
            other => panic!("expected assume, found {other:?}"),
        };
        let not_eq_inner = match dag.step(dag::SmtStepId(1)) {
            Some(dag::SmtProofStep::TheoryLemma { clause, .. }) => match dag.term(clause[0]) {
                Some(dag::SmtTerm::Not(inner)) => *inner,
                other => panic!("expected Not, found {other:?}"),
            },
            other => panic!("expected theory lemma, found {other:?}"),
        };
        assert_eq!(
            assume_eq_id, not_eq_inner,
            "(= a b) in assume and not(= a b) must share the same inner ID"
        );

        // Verify complementarity works with shared IDs.
        assert!(
            dag.are_complementary(assume_eq_id, dag::SmtTermId(not_eq_inner.0 + 1))
                || dag.are_complementary(
                    assume_eq_id,
                    // The not(= a b) term is the one after (= a b) in the arena
                    match dag.step(dag::SmtStepId(1)) {
                        Some(dag::SmtProofStep::TheoryLemma { clause, .. }) => clause[0],
                        _ => panic!("expected theory lemma"),
                    }
                ),
            "are_complementary should work on deduplicated terms"
        );
    }

    /// Test dedup_stats helper.
    #[test]
    fn test_dedup_stats_reports_savings() {
        let input = r#"
            (declare-const p Bool)
            (assume h1 p)
            (step t1 (cl (not p)) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;
        let parsed = parse_alethe(input).expect("should parse");
        let original_count = parsed.terms.len();
        let dag = alethe_to_dag(parsed);
        let savings = dedup_stats(original_count, &dag);
        assert_eq!(savings, 1, "one duplicate term should be eliminated");
    }
}
