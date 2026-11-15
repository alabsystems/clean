use carcara::{checker::*, parser};

fn run_test(problem: &str, proof: &str, expected_result: bool) {
    let (problem, proof, rare_rules, mut pool) =
        parser::parse_instance(problem, proof, None, parser::Config::default()).unwrap();

    let got = ProofChecker::new(&mut pool, &rare_rules, Config::new()).check(&problem, &proof);

    assert_eq!(got.is_ok(), expected_result);
}

#[test]
fn test_reached_empty_clause() {
    run_test("(declare-const x Int)", "(step t1 (cl) :rule hole)", true);
    run_test(
        "",
        "(anchor :step t0)
                  (step t0.t1 (cl) :rule hole)
                  (step t0 (cl false) :rule subproof)",
        false,
    );
    run_test(
        "",
        "(anchor :step t0)
                  (step t0.t1 (cl) :rule hole)
                  (step t0 (cl false) :rule subproof)
                  (step t1 (cl) :rule hole)",
        true,
    );
}

// Added in Clean: `assume` matches premises modulo n-ary sugar, but the unary `-` is negation,
// not the one-argument form of `-`. Upstream Carcara accepted both `false` cases (see
// third-party/carcara/DOWNSTREAM.md).
#[test]
fn test_assume_does_not_drop_negation() {
    let problem = "(declare-const r Real) (assert (= r (- 5.0)))";
    run_test(
        problem,
        "(assume h (= r 5.0)) (step t1 (cl) :rule hole)",
        false,
    );
    run_test(
        problem,
        "(assume h (= (- 5.0) r)) (step t1 (cl) :rule hole)",
        true,
    );
    run_test(
        "(declare-const r Real) (assert (= r r))",
        "(assume h (= r (- r))) (step t1 (cl) :rule hole)",
        false,
    );
}

// Added in Clean: the scoping of anchor variables (checker/scoping.rs) is checked in the shared
// step core, so the sequential and the parallel checker must agree on it. The first two proofs
// were accepted by upstream Carcara: a premise in which `x` is the declared constant is used
// inside an anchor that rebinds `x`, and a closing rule exports the constrained `x`.
#[test]
fn test_anchor_scoping_in_both_checkers() {
    use std::sync::Arc;

    let problem = "
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-const a U)
        (declare-const b U)
        (declare-const x U)
        (assert (= x b))
    ";
    let cases = [
        (
            "(assume h (= x b))
            (anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P b))) :rule cong :premises (h))
            (step t1 (cl (= (let ((x a)) (P x)) (P b))) :rule let)
            (step t2 (cl) :rule hole)",
            false,
        ),
        (
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (let ((x a)) (P x)) (P x))) :rule let)
            (step t2 (cl) :rule hole)",
            false,
        ),
        (
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P a))) :rule refl)
            (step t1 (cl (= (let ((x a)) (P x)) (P a))) :rule let)
            (step t2 (cl) :rule hole)",
            true,
        ),
    ];
    for (proof, expected) in cases {
        run_test(problem, proof, expected);
        for num_threads in [1, 4] {
            let (problem, proof, rare_rules, pool) =
                parser::parse_instance(problem, proof, None, parser::Config::default()).unwrap();
            let (scheduler, usage) = Scheduler::new(num_threads, &proof);
            let mut checker = ParallelProofChecker::new(
                Arc::new(pool),
                Config::new(),
                &problem.prelude,
                &usage,
                128 * 1024 * 1024,
                rare_rules,
            );
            let got = checker.check(&problem, &proof, &scheduler);
            assert_eq!(
                got.is_ok(),
                expected,
                "parallel checker with {num_threads} threads"
            );
        }
    }
}
