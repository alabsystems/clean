// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-checker agreement properties: multiple proof systems must agree on
//! whether a formula is UNSAT. These properties catch soundness regressions
//! where one checker accepts a refutation that others reject.

use crate::sat_verify::cdcl::proof_logging::{verify_proof_log, ProofLog, ProofStep};
use crate::sat_verify::frat::{verify_frat, FratClauseId, FratStep};
use crate::sat_verify::lrat::{ClauseId, LratChecker, LratStep};
use crate::sat_verify::proof_complexity::resolution::ResolutionProof;
use crate::sat_verify::types::Lit;

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    /// Cross-checker agreement: for {v} AND {-v}, DRAT, LRAT, FRAT, and
    /// Resolution must all agree the formula is UNSAT.
    #[test]
    fn prop_cross_all_checkers_agree_on_complementary_units(
        v in 1i32..=20,
    ) {
        // DRAT.
        let drat_log = ProofLog {
            original_clauses: vec![vec![v], vec![-v]],
            steps: vec![ProofStep::Add(vec![])],
        };
        let drat = verify_proof_log(&drat_log);
        prop_assert!(drat.valid, "DRAT should verify {{v}} AND {{-v}}");

        // LRAT.
        let mut checker = LratChecker::new(v as u32);
        checker.add_original(ClauseId(1), &[Lit(v)]).expect("add1");
        checker.add_original(ClauseId(2), &[Lit(-v)]).expect("add2");
        let lrat = checker
            .verify_proof(&[LratStep::Add {
                id: ClauseId(3),
                clause: vec![],
                hints: vec![1, 2],
            }])
            .expect("lrat");
        prop_assert!(lrat.refuted, "LRAT should refute");

        // FRAT.
        let frat_steps = vec![
            FratStep::Original { id: FratClauseId(1), clause: vec![v] },
            FratStep::Original { id: FratClauseId(2), clause: vec![-v] },
            FratStep::Lemma { id: FratClauseId(3), clause: vec![] },
            FratStep::Finalize { id: FratClauseId(3) },
        ];
        let frat = verify_frat(&[vec![v], vec![-v]], &frat_steps).expect("frat");
        prop_assert!(frat.valid, "FRAT should verify");

        // Resolution.
        let mut res = ResolutionProof::new();
        res.add_input(vec![v]);
        res.add_input(vec![-v]);
        prop_assert!(res.add_resolve(0, 1, v).is_ok());
        prop_assert!(res.verify(), "resolution should verify");
    }

    /// Cross-checker soundness: on a clearly-SAT formula, no checker accepts
    /// a refutation via simple empty-clause addition.
    #[test]
    fn prop_cross_all_checkers_reject_sat_refutation(
        v in 1i32..=10,
    ) {
        let formula = vec![vec![v]]; // trivially SAT: assign v=true

        // DRAT: empty clause not RUP from {v} alone.
        let drat_log = ProofLog {
            original_clauses: formula.clone(),
            steps: vec![ProofStep::Add(vec![])],
        };
        prop_assert!(
            !verify_proof_log(&drat_log).valid,
            "DRAT accepted false refutation of SAT formula"
        );

        // LRAT: deriving empty from {v} must fail.
        let mut checker = LratChecker::new(v as u32);
        checker.add_original(ClauseId(1), &[Lit(v)]).expect("add");
        let lrat_res = checker.add_derived(ClauseId(2), &[], &[1]);
        prop_assert!(
            lrat_res.is_err(),
            "LRAT accepted false refutation of SAT formula"
        );

        // FRAT: empty lemma not RUP/RAT from {v} alone.
        let frat_steps = vec![
            FratStep::Original { id: FratClauseId(1), clause: vec![v] },
            FratStep::Lemma { id: FratClauseId(2), clause: vec![] },
        ];
        let frat_res = verify_frat(&formula, &frat_steps);
        let valid = frat_res.map(|r| r.valid).unwrap_or(false);
        prop_assert!(!valid, "FRAT accepted false refutation of SAT formula");
    }
}
