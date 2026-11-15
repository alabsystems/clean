// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Two elaborator soundness defects R146 recorded (K5 blocker list), and the
//! siblings a probe hunt found, each pinned by a positive fixture plus
//! one-theorem mutations.
//!
//! | fixture | defect | before |
//! |---|---|---|
//! | `binder_type_order` | a binder's type taken from the argument, a numeral `let`, or an invented instance carrier, where Lean unifies it from the body; a dropped `@[default_instance]` on an instance | `m2 = 110` (Lean: 210), `mOpen = 212` (Lean: 112), `mLet = 110` (Lean: 210), `dfOpen = 5` (Lean: 4) accepted |
//! | `let_rec_scope` | a `let rec go`'s recursive call resolved to an outer local `go` (a sibling `where` helper, a parameter) | `twoGoS.other 3 = 101` (Lean: 3) accepted |
//! | `order_guards` | the Lean-order alternatives where Lean settles a metavariable early: a `let rec` header defaults a pending numeral; a multi-parameter goal that names a constant still may not have an open input pinned by the latest instance; operator numerals and `let mut` postpone too; out-parameters and the expected type still reach the term | `lrCapture = 210` (Lean: 110), `tgLet = 105` (Lean: 5), `c2Redex = 110` (Lean: 210) accepted |
//! | `order_guards_default` | a user `@[default_instance]` taken by the head-first order before the argument pinned the carrier | `dRedex = 105` (Lean: 5) accepted |
//!
//! The fixtures live in `tests/elab_binder_scope_fidelity/`. Lean 4.8.0
//! accepts both fixtures (`lean <file>`, exit 0) and refuses each mutation
//! in [`MUTATIONS`] (exit 1); several mutations state the value Clean used to
//! compute. Each test asserts Clean's verdict is the same, at the mutated
//! theorem and for its value. [`ILL_TYPED`] is refused by Lean 4.8.0 and must
//! be refused here too.
//!
//! Every test runs under a one-minute hang detector. The pipeline is the one
//! `clean check` drives
//! (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register_with_context`), with the file context that
//! carries `@[default_instance]`.

use std::sync::mpsc;
use std::time::Duration;

use clean_elab::{
    elaborate_decl_and_register, elaborate_decl_and_register_with_context,
    preprocess_decl_with_context, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::{parse_file_with_diagnostics, SurfaceDecl};

/// Run `body` on its own thread and fail if it has not finished within a
/// minute. A hang detector, not a latency budget.
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
            if let Err(panic) = worker.join() {
                std::panic::resume_unwind(panic);
            }
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("hang detector: `{what}` did not finish within one minute")
        }
    }
}

fn decl_name(decl: &SurfaceDecl) -> String {
    match decl {
        SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => name.to_string(),
        SurfaceDecl::Inductive { name, .. } | SurfaceDecl::Namespace { name, .. } => {
            name.to_string()
        }
        _ => String::from("<other>"),
    }
}

/// Elaborate every declaration of `source` in order: each one's name and
/// error, if any.
fn elaborate(source: &str) -> (Environment, Vec<(String, Option<String>)>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let report =
        parse_file_with_diagnostics(source).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    assert!(
        report.diagnostics.is_empty(),
        "fixture must parse without recovery: {:?}",
        report.diagnostics
    );
    let mut results = Vec::new();
    for decl in &report.decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let error = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .err()
            .map(|e| e.to_string());
        results.push((decl_name(decl), error));
    }
    (env, results)
}

fn failures(results: &[(String, Option<String>)]) -> Vec<(&str, &str)> {
    results
        .iter()
        .filter_map(|(name, error)| error.as_deref().map(|e| (name.as_str(), e)))
        .collect()
}

/// Every declaration elaborates and each named theorem is registered with
/// no axiom underneath.
fn assert_accepted(source: &str, theorems: &[&str]) {
    let (env, results) = elaborate(source);
    let failed = failures(&results);
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

const BINDER_TYPE_ORDER: &str = include_str!("elab_binder_scope_fidelity/binder_type_order.lean");
const LET_REC_SCOPE: &str = include_str!("elab_binder_scope_fidelity/let_rec_scope.lean");
const ORDER_GUARDS: &str = include_str!("elab_binder_scope_fidelity/order_guards.lean");
const ORDER_GUARDS_DEFAULT: &str =
    include_str!("elab_binder_scope_fidelity/order_guards_default.lean");

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
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "m2_eq",
        from: "m2 = 210 := rfl",
        to: "m2 = 110 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mNat_five",
        from: "mNat 5 = 210 := rfl",
        to: "mNat 5 = 110 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mTwo_eq",
        from: "mTwo = 215 := rfl",
        to: "mTwo = 115 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mMatch_eq",
        from: "mMatch = 210 := rfl",
        to: "mMatch = 110 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mIf_eq",
        from: "mIf = 105 := rfl",
        to: "mIf = 5 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mOpen_eq",
        from: "mOpen = 112 := rfl",
        to: "mOpen = 212 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mLet_eq",
        from: "mLet = 210 := rfl",
        to: "mLet = 110 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mHave_eq",
        from: "mHave = 210 := rfl",
        to: "mHave = 110 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mDo_eq",
        from: "mDo = 210 := rfl",
        to: "mDo = 110 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mLetNat_eq",
        from: "mLetNat = 0 := rfl",
        to: "mLetNat = 1 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mHead_eq",
        from: "mHead = 11 := rfl",
        to: "mHead = 12 := rfl",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "twoGoS_three",
        from: "twoGoS 3 = 103 := by decide",
        to: "twoGoS 3 = 201 := by decide",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "other_three",
        from: "twoGoS.other 3 = 3 := by decide",
        to: "twoGoS.other 3 = 101 := by decide",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "other_go_three",
        from: "twoGoS.other.go 3 = 3 := by decide",
        to: "twoGoS.other.go 3 = 100 := by decide",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "tg_other_three",
        from: "N.tg.other 3 = 6 := by decide",
        to: "N.tg.other 3 = 102 := by decide",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "paramGo_three",
        from: "paramGo (· + 100) = 3 := by decide",
        to: "paramGo (· + 100) = 103 := by decide",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "selfParam_three",
        from: "selfParam (· + 100) 3 = 103 := by decide",
        to: "selfParam (· + 100) 3 = 3 := by decide",
    },
    Mutation {
        fixture: "let_rec_scope",
        source: LET_REC_SCOPE,
        theorem: "shadows_five",
        from: "shadows 5 = 114 := by decide",
        to: "shadows 5 = 115 := by decide",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "mTwice_eq",
        from: "mTwice = 10 := rfl",
        to: "mTwice = 210 := rfl",
    },
    Mutation {
        fixture: "binder_type_order",
        source: BINDER_TYPE_ORDER,
        theorem: "dfOpen_eq",
        from: "dfOpen = 4 := rfl",
        to: "dfOpen = 5 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrCapture_eq",
        from: "lrCapture = 110 := rfl",
        to: "lrCapture = 210 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrHave_eq",
        from: "lrHave = 110 := rfl",
        to: "lrHave = 210 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrNoUse_eq",
        from: "lrNoUse = 110 := rfl",
        to: "lrNoUse = 210 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrSum_eq",
        from: "lrSum = 110 := rfl",
        to: "lrSum = 210 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrAfterPin_eq",
        from: "lrAfterPin = 210 := rfl",
        to: "lrAfterPin = 110 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrRedex_eq",
        from: "lrRedex = 210 := rfl",
        to: "lrRedex = 110 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "lrRedexNumLet_eq",
        from: "lrRedexNumLet = 110 := rfl",
        to: "lrRedexNumLet = 210 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "numDiv_eq",
        from: "numDiv = 206 := rfl",
        to: "numDiv = 106 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "numSub_eq",
        from: "numSub = 200 := rfl",
        to: "numSub = 100 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "mutLet_eq",
        from: "mutLet = 210 := rfl",
        to: "mutLet = 110 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "tgLet_eq",
        from: "tgLet = 5 := rfl",
        to: "tgLet = 105 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "tgRedex_eq",
        from: "tgRedex = 5 := rfl",
        to: "tgRedex = 105 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "c2Redex_eq",
        from: "c2Redex = 210 := rfl",
        to: "c2Redex = 110 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "c2Let_eq",
        from: "c2Let = 210 := rfl",
        to: "c2Let = 110 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "tg2Redex_eq",
        from: "tg2Redex = 210 := rfl",
        to: "tg2Redex = 110 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "orElseNone_eq",
        from: "orElseNone = some 3 := rfl",
        to: "orElseNone = some 4 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "cvOut_eq",
        from: "cvOut = 100 := rfl",
        to: "cvOut = 5 := rfl",
    },
    Mutation {
        fixture: "order_guards",
        source: ORDER_GUARDS,
        theorem: "negRedex_eq",
        from: "negRedex = -5 := rfl",
        to: "negRedex = 5 := rfl",
    },
    Mutation {
        fixture: "order_guards_default",
        source: ORDER_GUARDS_DEFAULT,
        theorem: "dRedex_eq",
        from: "dRedex = 5 := rfl",
        to: "dRedex = 105 := rfl",
    },
    Mutation {
        fixture: "order_guards_default",
        source: ORDER_GUARDS_DEFAULT,
        theorem: "aRedex_eq",
        from: "aRedex = 5 := rfl",
        to: "aRedex = 105 := rfl",
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
        let error = failed[0].1.to_lowercase();
        assert!(
            ["type mismatch", "decide", "not definitionally equal", "rfl"]
                .iter()
                .any(|needle| error.contains(needle)),
            "`{}` must be refused for its value, not because elaboration gave up: {error}",
            m.theorem
        );
    }
}

#[test]
fn binder_types_follow_the_body() {
    within_a_minute("binder_type_order", || {
        assert_accepted(
            BINDER_TYPE_ORDER,
            &[
                "m2_eq",
                "mNat_five",
                "mTwo_eq",
                "mMatch_eq",
                "mIf_eq",
                "mOpen_eq",
                "mLet_eq",
                "mHave_eq",
                "mDo_eq",
                "mLetNat_eq",
                "mHead_eq",
                "mTwice_eq",
                "dfOpen_eq",
            ],
        )
    });
}

#[test]
fn binder_type_mutations_are_refused() {
    within_a_minute("binder_type_order mutations", || {
        assert_mutations_refused("binder_type_order")
    });
}

/// Lean 4.8.0 types `k : Int` from the first ascription, so `k - 7` is an
/// `Int` the `Nat` sum cannot take. Typing `k` from the argument instead
/// (`Nat`) accepted it.
const ILL_TYPED: &str = "def m3 : Nat := (fun k => Int.toNat ((k : Int) - 7) + (k - 7)) 5\n";

#[test]
fn a_body_that_lean_finds_ill_typed_stays_refused() {
    within_a_minute("ill_typed", || {
        let (_, results) = elaborate(ILL_TYPED);
        let failed = failures(&results);
        assert_eq!(
            failed.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
            vec!["m3"],
            "`m3` must be refused: {results:#?}"
        );
    });
}

#[test]
fn let_rec_names_resolve_to_the_innermost_binding() {
    within_a_minute("let_rec_scope", || {
        assert_accepted(
            LET_REC_SCOPE,
            &[
                "twoGoS_three",
                "other_three",
                "other_go_three",
                "tg_other_three",
                "paramGo_three",
                "selfParam_three",
                "shadows_five",
            ],
        )
    });
}

#[test]
fn let_rec_scope_mutations_are_refused() {
    within_a_minute("let_rec_scope mutations", || {
        assert_mutations_refused("let_rec_scope")
    });
}

/// The same `@[default_instance]` answer without a file context (the
/// `elaborate_decl_and_register` entry): the environment's record of the
/// attribute drives the defaulting, not registration order.
#[test]
fn default_instance_answers_without_a_file_context() {
    within_a_minute("default_instance_no_context", || {
        let source = "class Df (α : Type) where\n  v : Nat\n\
                      instance dfNat : Df Nat where v := 3\n\
                      @[default_instance] instance dfBool : Df Bool where v := 4\n\
                      instance dfNat2 : Df Nat where v := 5\n\
                      def dfGet {α : Type} [Df α] : Nat := Df.v (α := α)\n\
                      def dfOpen : Nat := dfGet\n\
                      theorem dfOpen_eq : dfOpen = 4 := rfl\n";
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        let report = parse_file_with_diagnostics(source).expect("parses");
        for decl in &report.decls {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            if let Err(e) = elaborate_decl_and_register(&mut env, &processed) {
                panic!("`{}` must elaborate: {e}", decl_name(decl));
            }
        }
    });
}

#[test]
fn lean_order_stands_down_where_lean_settles_early() {
    within_a_minute("order_guards", || {
        assert_accepted(
            ORDER_GUARDS,
            &[
                "lrCapture_eq",
                "lrHave_eq",
                "lrNoUse_eq",
                "lrSum_eq",
                "lrAfterPin_eq",
                "lrRedex_eq",
                "lrRedexNumLet_eq",
                "numDiv_eq",
                "numSub_eq",
                "mutLet_eq",
                "tgLet_eq",
                "tgRedex_eq",
                "c2Redex_eq",
                "c2Let_eq",
                "tg2Redex_eq",
                "orElseNone_eq",
                "cvOut_eq",
                "negRedex_eq",
            ],
        )
    });
}

#[test]
fn order_guard_mutations_are_refused() {
    within_a_minute("order_guards mutations", || {
        assert_mutations_refused("order_guards")
    });
}

#[test]
fn a_user_default_instance_waits_for_the_argument() {
    within_a_minute("order_guards_default", || {
        assert_accepted(ORDER_GUARDS_DEFAULT, &["dRedex_eq", "aRedex_eq"])
    });
}

#[test]
fn user_default_instance_mutations_are_refused() {
    within_a_minute("order_guards_default mutations", || {
        assert_mutations_refused("order_guards_default")
    });
}

/// The let-chain decides WHETHER a β-redex elaborates; Lean's order only
/// decides what it means. Lean 4.8.0 accepts this one (`xs : List Int` from
/// the ascription, 106). Until R163 the let-chain typed `xs : List Nat` from
/// the argument, had no coercion to `List Int` and refused it; its numerals
/// now wait for the body (`let _ := [5]` leaves `List ?α` open), so the
/// let-chain elaborates it, at Lean's value. The gate itself stands: a redex
/// the let-chain refuses is still refused.
const LET_CHAIN_GATE: &str = "class Tag (α : Type) where\n  tag : α → Nat\n\
                              instance : Tag Nat := ⟨fun x => x⟩\n\
                              instance : Tag Int := ⟨fun x => x.toNat + 100⟩\n\
                              def gate : Nat := (fun xs => (xs : List Int).length + Tag.tag (xs.headD 0)) [5]\n\
                              theorem gate_eq : gate = 106 := rfl\n";

#[test]
fn the_let_chain_decides_whether_a_redex_elaborates() {
    within_a_minute("let_chain_gate", || {
        assert_accepted(LET_CHAIN_GATE, &["gate_eq"]);
        let (_, results) = elaborate(&LET_CHAIN_GATE.replace("gate = 106", "gate = 6"));
        let failed = failures(&results);
        assert_eq!(
            failed.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
            vec!["gate_eq"],
            "`gate = 6` must be refused (Lean 4.8.0: 106): {results:#?}"
        );
    });
}
