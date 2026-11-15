// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RM1 elaborator fixes from the K5 re-measurement (2026-10-22, L2 of the
//! proven-core plan), each a positive fixture plus one-theorem mutations.
//!
//! | fixture | K5 item | before |
//! |---|---|---|
//! | `implies_fuel` | root blocker 1, `TrustIr.Pred.impliesFuel` | elaboration never finished |
//! | `join_chain_simp` | root blocker 1's `simp [Pred.impliesFuel]` | simp's equations re-expanded every join (25 GiB) |
//! | `join_point_gates` | the join point's gates | (new: one definition per gate) |
//! | `do_triple_match` | probe a5, `semBinOp` | `Unknown identifier: a` |
//! | `where_wf` | probe b2 | `where`/`let rec` well-founded recursion refused |
//!
//! The fixtures live in `tests/rm1_elab_fixes/`. Lean 4.8.0 accepts every
//! fixture (`lean <file>`, exit 0) and refuses each mutation in [`MUTATIONS`]
//! at its one changed theorem (exit 1). Each test here asserts Clean's
//! verdict is the same. A mutated theorem states a wrong value, so it is
//! accepted only if the definition it reads computes the wrong thing: the
//! pair checks the lowering, not just that something elaborates. A mutation
//! must fail at its own theorem and with a value-mismatch error, not because
//! elaboration gave up somewhere else.
//!
//! Every test runs under a one-minute hang detector: the regressions these
//! fixtures guard against (the per-constructor expansion, simp substituting
//! a join) do not fail, they run without bound.
//!
//! The pipeline is the one `clean check` drives
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`).

use std::sync::mpsc;
use std::time::Duration;

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, take_join_outcomes, FileContext,
    JoinOutcome,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::{parse_file_with_diagnostics, SurfaceDecl};

/// Run `body` on its own thread and fail if it has not finished within a
/// minute. A hang detector, not a latency budget: every body here finishes
/// in seconds.
fn within_a_minute(what: &str, body: impl FnOnce() + Send + 'static) {
    let (done, finished) = mpsc::channel();
    let worker = std::thread::Builder::new()
        .name(what.to_string())
        .stack_size(256 << 20)
        .spawn(move || {
            body();
            let _ = done.send(());
        })
        .expect("spawn the test body");
    match finished.recv_timeout(Duration::from_secs(60)) {
        Ok(()) => worker.join().expect("test body"),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            // The body panicked: re-raise its panic.
            if let Err(panic) = worker.join() {
                std::panic::resume_unwind(panic);
            }
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("hang detector: `{what}` did not finish within one minute")
        }
    }
}

/// The name a declaration registers, for the ones a fixture uses.
fn decl_name(decl: &SurfaceDecl) -> String {
    match decl {
        SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => name.to_string(),
        SurfaceDecl::Inductive { name, .. } | SurfaceDecl::Namespace { name, .. } => {
            name.to_string()
        }
        _ => String::from("<other>"),
    }
}

/// One top-level declaration's result.
struct DeclResult {
    name: String,
    error: Option<String>,
    join_outcomes: Vec<JoinOutcome>,
}

/// Elaborate every declaration of `source` in order.
fn elaborate(source: &str) -> (Environment, Vec<DeclResult>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let report =
        parse_file_with_diagnostics(source).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    assert!(
        report.diagnostics.is_empty(),
        "fixture must parse without recovery: {:?}",
        report.diagnostics
    );
    let decls = report.decls;
    let _ = take_join_outcomes();
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let error = elaborate_decl_and_register(&mut env, &processed)
            .err()
            .map(|e| e.to_string());
        results.push(DeclResult {
            name: decl_name(decl),
            error,
            join_outcomes: take_join_outcomes(),
        });
    }
    (env, results)
}

fn failures(results: &[DeclResult]) -> Vec<(&str, &str)> {
    results
        .iter()
        .filter_map(|r| r.error.as_deref().map(|e| (r.name.as_str(), e)))
        .collect()
}

/// Every declaration of the positive fixture elaborates and kernel-checks,
/// and each named theorem is registered with no axiom underneath.
fn assert_accepted(env: &Environment, results: &[DeclResult], theorems: &[&str]) {
    let failed = failures(results);
    assert!(
        failed.is_empty(),
        "positive fixture must elaborate: {failed:#?}"
    );
    for theorem in theorems {
        let name = Name::from_string(theorem);
        assert!(
            env.get_const(&name).is_some(),
            "`{theorem}` must be registered"
        );
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("`{theorem}` must have an axiom closure"));
        assert!(
            deps.is_empty(),
            "`{theorem}` must be axiom-free, got {deps:?}"
        );
    }
}

const IMPLIES_FUEL: &str = include_str!("rm1_elab_fixes/implies_fuel.lean");
const JOIN_CHAIN_SIMP: &str = include_str!("rm1_elab_fixes/join_chain_simp.lean");
const JOIN_POINT_GATES: &str = include_str!("rm1_elab_fixes/join_point_gates.lean");
const DO_TRIPLE_MATCH: &str = include_str!("rm1_elab_fixes/do_triple_match.lean");
const WHERE_WF: &str = include_str!("rm1_elab_fixes/where_wf.lean");

/// One mutation: in `fixture`, the theorem `theorem` reads `from` and is
/// rewritten to `to`, a value Lean 4.8.0 refuses.
struct Mutation {
    fixture: &'static str,
    source: &'static str,
    theorem: &'static str,
    from: &'static str,
    to: &'static str,
}

const MUTATIONS: &[Mutation] = &[
    Mutation {
        fixture: "implies_fuel",
        source: IMPLIES_FUEL,
        theorem: "implies_index",
        from: "(.InUniverse 1 .Index) = false := rfl",
        to: "(.InUniverse 1 .Index) = true := rfl",
    },
    Mutation {
        fixture: "implies_fuel",
        source: IMPLIES_FUEL,
        theorem: "implies_conj_left",
        from: "(.Conj [.NonZero, .NonNull]) .NonNull = true := rfl",
        to: "(.Conj [.NonZero, .NonNull]) .NonNull = false := rfl",
    },
    Mutation {
        fixture: "join_chain_simp",
        source: JOIN_CHAIN_SIMP,
        theorem: "chain_deep",
        from: "chain 1 .q3 .q4 = false := by simp [chain]",
        to: "chain 1 .q3 .q4 = true := by simp [chain]",
    },
    Mutation {
        fixture: "join_point_gates",
        source: JOIN_POINT_GATES,
        theorem: "gApplied_c2",
        from: "gApplied .c2 false = 3 := rfl",
        to: "gApplied .c2 false = 2 := rfl",
    },
    Mutation {
        fixture: "join_point_gates",
        source: JOIN_POINT_GATES,
        theorem: "gRec_three",
        from: "gRec 3 true = 21 := rfl",
        to: "gRec 3 true = 12 := rfl",
    },
    Mutation {
        fixture: "join_point_gates",
        source: JOIN_POINT_GATES,
        theorem: "gLetOpen_c1",
        from: "gLetOpen .c1 false = 3 := rfl",
        to: "gLetOpen .c1 false = 2 := rfl",
    },
    Mutation {
        fixture: "do_triple_match",
        source: DO_TRIPLE_MATCH,
        theorem: "addv_vec",
        from: "addv 1 (.vec [1, 2]) (.vec [3]) = .ok 4 := rfl",
        to: "addv 1 (.vec [1, 2]) (.vec [3]) = .ok 5 := rfl",
    },
    Mutation {
        fixture: "do_triple_match",
        source: DO_TRIPLE_MATCH,
        theorem: "addv_bool",
        from: "addv 0 (.bool true) (.bool true) = .ok 1 := rfl",
        to: "addv 0 (.bool true) (.bool true) = .ok 0 := rfl",
    },
    Mutation {
        fixture: "do_triple_match",
        source: DO_TRIPLE_MATCH,
        theorem: "a5Add_ok",
        from: "a5Add 0 (.int 2) (.int 3) = .ok 5 := rfl",
        to: "a5Add 0 (.int 2) (.int 3) = .ok 6 := rfl",
    },
    Mutation {
        fixture: "do_triple_match",
        source: DO_TRIPLE_MATCH,
        theorem: "a5Add_tag",
        from: "a5Add 1 (.int 2) (.int 3) = .error \"type error\" := rfl",
        to: "a5Add 1 (.int 2) (.int 3) = .ok 5 := rfl",
    },
    Mutation {
        fixture: "where_wf",
        source: WHERE_WF,
        theorem: "countUp_three",
        from: "countUp_three : countUp 3 = 3 := by decide",
        to: "countUp_three : countUp 3 = 4 := by decide",
    },
    Mutation {
        fixture: "where_wf",
        source: WHERE_WF,
        theorem: "sumTo_four",
        from: "sumTo 4 = 6 := by decide",
        to: "sumTo 4 = 7 := by decide",
    },
    Mutation {
        fixture: "where_wf",
        source: WHERE_WF,
        theorem: "passLast_three",
        from: "passLast 3 10 = 13 := by decide",
        to: "passLast 3 10 = 12 := by decide",
    },
    Mutation {
        fixture: "where_wf",
        source: WHERE_WF,
        theorem: "twoHelpers_three",
        from: "twoHelpers 3 = 9 := by decide",
        to: "twoHelpers 3 = 8 := by decide",
    },
    Mutation {
        fixture: "where_wf",
        source: WHERE_WF,
        theorem: "b2_countUp_three",
        from: "B2.countUp 3 = 3 := by decide",
        to: "B2.countUp 3 = 4 := by decide",
    },
];

/// Every mutation of `fixture` is refused at its own theorem, with a value
/// mismatch, and nothing else in the fixture fails.
fn assert_mutations_refused(fixture: &str) {
    let mutations: Vec<&Mutation> = MUTATIONS.iter().filter(|m| m.fixture == fixture).collect();
    assert!(!mutations.is_empty(), "`{fixture}` has mutations");
    for m in mutations {
        assert_eq!(
            m.source.matches(m.from).count(),
            1,
            "`{}`: the mutated text occurs once",
            m.theorem
        );
        let mutated = m.source.replace(m.from, m.to);
        let (_, results) = elaborate(&mutated);
        let failed = failures(&results);
        assert_eq!(
            failed.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
            vec![m.theorem],
            "only the mutated theorem `{}` may fail: {failed:#?}",
            m.theorem
        );
        let error = failed[0].1;
        assert!(
            is_value_mismatch(error),
            "`{}` must be refused for its value, not because elaboration gave up: {error}",
            m.theorem
        );
    }
}

/// The errors a false `rfl`, `decide` or `simp` goal produces.
fn is_value_mismatch(error: &str) -> bool {
    let error = error.to_lowercase();
    [
        "type mismatch",
        "decide",
        "not definitionally equal",
        "rfl",
        "simp",
    ]
    .iter()
    .any(|needle| error.contains(needle))
}

#[test]
fn implies_fuel_shape_elaborates_and_computes() {
    within_a_minute("implies_fuel", || {
        let (env, results) = elaborate(IMPLIES_FUEL);
        assert_accepted(
            &env,
            &results,
            &[
                "implies_bottom",
                "implies_refl",
                "implies_conj_left",
                "implies_disj_left",
                "implies_member",
                "implies_space_mismatch",
                "implies_index",
            ],
        );
        let fuel = results
            .iter()
            .find(|r| r.name == "P.impliesFuel")
            .expect("impliesFuel");
        assert!(
            fuel.join_outcomes.contains(&JoinOutcome::Applied),
            "impliesFuel's catch-alls go through join points: {:?}",
            fuel.join_outcomes
        );
    });
}

#[test]
fn implies_fuel_shape_mutations_are_refused() {
    within_a_minute("implies_fuel mutations", || {
        assert_mutations_refused("implies_fuel")
    });
}

/// A chain of `depth` catch-all matches, alternating between two
/// discriminants of a nine-constructor type, under a two-discriminant match
/// with a catch-all (the skeleton of `impliesFuel`).
fn catch_all_chain(depth: usize) -> String {
    let mut out = String::from(
        "inductive Q where\n  | q0 : Int → Q\n  | q1 : Nat → Q\n  | q2 : Nat → Bool → Q\n  \
         | q3 : Q\n  | q4 : Q\n  | q5 : List Q → Q\n  | q6 : List Q → Q\n  | top : Q\n  \
         | bot : Q\n\n\
         def chain : Nat → Q → Q → Bool\n  | 0, _, _ => false\n  | n + 1, a, b =>\n    \
         match a, b with\n    | .bot, _ => true\n    | _, .bot => false\n    \
         | _, .top => true\n    | .top, _ => false\n    | a, b =>\n",
    );
    let mut indent = String::from("      ");
    for level in 0..depth {
        let discriminant = if level % 2 == 0 { "b" } else { "a" };
        let ctor = level % 5;
        out.push_str(&format!("{indent}match {discriminant} with\n"));
        out.push_str(&format!("{indent}| .q{ctor} .. => chain n a b\n"));
        out.push_str(&format!("{indent}| _ =>\n"));
        indent.push_str("  ");
    }
    out.push_str(&format!("{indent}false\n"));
    out
}

/// Each catch-all body is elaborated once, so the definition grows by a
/// constant per nesting level. The constructor-per-minor expansion this
/// replaced multiplied it by the number of uncovered constructors (about
/// eight) per level: depth 5 took 190 s and depth 12 would not finish, which
/// the hang detector reports.
#[test]
fn catch_all_chain_grows_linearly() {
    within_a_minute("catch_all_chain", || {
        let size = |depth: usize| {
            let (env, results) = elaborate(&catch_all_chain(depth));
            let failed = failures(&results);
            assert!(
                failed.is_empty(),
                "depth {depth} must elaborate: {failed:#?}"
            );
            let chain = results.iter().find(|r| r.name == "chain").expect("chain");
            let applied = chain
                .join_outcomes
                .iter()
                .filter(|o| **o == JoinOutcome::Applied)
                .count();
            assert!(
                applied >= depth,
                "every level's catch-all goes through a join point: {:?}",
                chain.join_outcomes
            );
            let info = env
                .get_const(&Name::from_string("chain"))
                .expect("`chain` must be registered");
            format!("{:?}", info.value.as_ref().expect("`chain` has a value")).len()
        };
        let shallow = size(6);
        let deep = size(12);
        assert!(
            deep < 4 * shallow,
            "depth 12 must be at most a constant factor larger than depth 6: {deep} vs {shallow}"
        );
    });
}

/// `simp [chain]` over the depth-8 chain: simp's equation synthesis keeps
/// each join a `let`. Substituting it re-expands every level (8 GB and still
/// growing after eight minutes), which the hang detector reports.
#[test]
fn simp_over_join_points_stays_linear() {
    within_a_minute("join_chain_simp", || {
        let (env, results) = elaborate(JOIN_CHAIN_SIMP);
        assert_accepted(&env, &results, &["chain_bot", "chain_deep"]);
    });
}

#[test]
fn simp_over_join_points_mutation_is_refused() {
    within_a_minute("join_chain_simp mutation", || {
        assert_mutations_refused("join_chain_simp")
    });
}

/// Each definition of `join_point_gates.lean` is declined by exactly the
/// gate it is named for (and `gApplied` goes through the join point, its own
/// `| p => j p` arm declined as the rewrite's call), and every definition
/// still computes Lean's value.
#[test]
fn join_point_gates_each_decline_their_shape() {
    within_a_minute("join_point_gates", || {
        use JoinOutcome as O;
        let (env, results) = elaborate(JOIN_POINT_GATES);
        assert_accepted(
            &env,
            &results,
            &[
                "gApplied_c0",
                "gApplied_c2",
                "gPlain_c3",
                "gRefutable_c3",
                "gHyp_c1",
                "gLetOpen_c1",
                "gOpen_c1",
                "gOpenList_c1",
                "gDep_val",
                "gDepInner_val",
                "gRec_three",
            ],
        );
        for (decl, expected) in [
            ("gApplied", O::Applied),
            ("gPlain", O::PlainBody),
            ("gRefutable", O::RefutableCatchAll),
            ("gHyp", O::DiscriminantHypothesis),
            ("gLetOpen", O::ExpectedTypeUnknown),
            // An unascribed header's result is a metavariable (8c866b7fe,
            // as in Lean), so the match's expected type is open.
            ("gOpen", O::ExpectedTypeOpen),
            ("gOpenList", O::ExpectedTypeOpen),
            ("gDep", O::MotiveMentionsDiscriminant),
            ("gDepInner", O::DependentMotive),
            ("gRec", O::RecursionArgument),
        ] {
            let outcomes = &results
                .iter()
                .find(|r| r.name == decl)
                .unwrap_or_else(|| panic!("`{decl}` is in the fixture"))
                .join_outcomes;
            assert!(
                outcomes.contains(&expected),
                "`{decl}` must be declined by {expected:?}: {outcomes:?}"
            );
            if expected == O::Applied {
                assert!(
                    outcomes.contains(&O::JoinCall),
                    "the rewritten `| p => j p` arm is declined as the join's own call: {outcomes:?}"
                );
            } else {
                assert!(
                    !outcomes.contains(&O::Applied),
                    "`{decl}` must not go through a join point: {outcomes:?}"
                );
            }
        }
    });
}

#[test]
fn join_point_gates_mutations_are_refused() {
    within_a_minute("join_point_gates mutations", || {
        assert_mutations_refused("join_point_gates")
    });
}

/// A non-exhaustive match whose catch-all lowering would leave the join's
/// internal match partial: the join is type-checked against `S → C`,
/// declined, and the old lowering names the match non-exhaustive (Lean
/// 4.8.0: `missing cases`) rather than the kernel refusing an ill-typed
/// `let`.
#[test]
fn ill_typed_join_is_declined_and_the_match_reported_non_exhaustive() {
    within_a_minute("ill-typed join", || {
        let (_, results) = elaborate(
            "inductive Shape where\n  | top\n  | interval (lo hi : Nat)\n\n\
             def Shape.partialImpliesM (x y : Shape) : Bool :=\n  match x, y with\n  \
             | _, .top => true\n  | .interval a b, .interval c d => c ≤ a && b ≤ d\n",
        );
        let partial = results
            .iter()
            .find(|r| r.name == "Shape.partialImpliesM")
            .expect("partialImpliesM");
        assert!(
            partial.join_outcomes.contains(&JoinOutcome::JoinIllTyped),
            "the partial join is declined by its type check: {:?}",
            partial.join_outcomes
        );
        let error = partial
            .error
            .as_deref()
            .expect("a non-exhaustive match is refused");
        assert!(
            error.contains("non-exhaustive"),
            "refused as non-exhaustive, not by the kernel: {error}"
        );
    });
}

#[test]
fn do_triple_match_elaborates_and_computes() {
    within_a_minute("do_triple_match", || {
        let (env, results) = elaborate(DO_TRIPLE_MATCH);
        assert_accepted(
            &env,
            &results,
            &[
                "addv_vec",
                "addv_int",
                "addv_bool",
                "addv_err",
                "a5Add_ok",
                "a5Add_tag",
            ],
        );
    });
}

#[test]
fn do_triple_match_mutations_are_refused() {
    within_a_minute("do_triple_match mutations", || {
        assert_mutations_refused("do_triple_match")
    });
}

#[test]
fn where_well_founded_helper_elaborates_and_computes() {
    within_a_minute("where_wf", || {
        let (env, results) = elaborate(WHERE_WF);
        assert_accepted(
            &env,
            &results,
            &[
                "countUp_three",
                "sumTo_four",
                "passLast_three",
                "twoHelpers_three",
                "b2_countUp_three",
            ],
        );
    });
}

#[test]
fn where_well_founded_mutations_are_refused() {
    within_a_minute("where_wf mutations", || {
        assert_mutations_refused("where_wf")
    });
}
