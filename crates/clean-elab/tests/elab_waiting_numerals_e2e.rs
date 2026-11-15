// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Numerals whose carrier is still open wait, as in Lean, for the rest of the
//! term to pin it (R163): the false-accept tail R157 left open, each class
//! pinned by a positive fixture plus one-theorem mutations.
//!
//! | fixture | what waits | before |
//! |---|---|---|
//! | `waiting_numerals` | a numeral in a `let` value (`id 5`, `max 5 3`, `(5, 0)`, `some 5`, `let k : _`, `(5 : _)`, `have k : _`, `k + 1`, a pattern `let`, an `if`, a `fun`), in the body of such a `let` (`k - 7`, `if k = 5`), in a `let mut` reassignment and a `for` collection, in a `do` bind's action, in a β-redex's head; and where Lean settles it early (a `let rec` header) or the old order stays (`-5`) | `wId = 110` (Lean 210), `wMut = 112` (212), `wFor = 106` (206), `wBind = 110` (210), `wRedexSub = 105` (205) accepted |
//! | `waiting_defaults` | a user `@[default_instance]` (default priority) applies after the body, before the numerals' `Nat` | `dNum = 5` (Lean 105), `dFnNat = 105` (5), `dTwo = 212` (112) accepted |
//! | `waiting_defaults_low` | a user default at priority 50, below `instOfNatNat`'s 100, applies after the numerals | `dFnNum = 105` (Lean 5) accepted |
//!
//! The fixtures live in `tests/elab_waiting_numerals/`. Lean 4.8.0 accepts
//! each fixture (`lean <file>`, exit 0) and refuses each mutation in
//! [`MUTATIONS`] (exit 1); most mutations state the value Clean used to
//! compute. Each test asserts Clean's verdict is the same, at the mutated
//! theorem and for its value. [`POW`] and [`HEAD`] pin two statements Lean
//! refuses that a waiting numeral would otherwise make Clean accept.
//!
//! Every test runs under a one-minute hang detector. The pipeline is the one
//! `clean check` drives (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register_with_context`), with the file context that
//! carries `@[default_instance]`.

use std::sync::mpsc;
use std::time::Duration;

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
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

#[path = "elab_waiting_numerals/mutations.rs"]
mod mutations;
use mutations::*;

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
fn open_numerals_wait_for_the_term() {
    within_a_minute("waiting_numerals", || {
        assert_accepted(
            WAITING_NUMERALS,
            &[
                "wId_eq",
                "wMax_eq",
                "wPair_eq",
                "wSome_eq",
                "wHole_eq",
                "wAscrHole_eq",
                "wHaveHole_eq",
                "wChain_eq",
                "wPat_eq",
                "wIf_eq",
                "wFn_eq",
                "wBodySub_eq",
                "wDecide_eq",
                "wMut_eq",
                "wFor_eq",
                "wBind_eq",
                "wRedexSub_eq",
                "wRedexHead_eq",
                "wLetRec_eq",
                "wNeg_eq",
                "wNatOnly_eq",
                "wNested_eq",
            ],
        )
    });
}

#[test]
fn waiting_numeral_mutations_are_refused() {
    within_a_minute("waiting_numerals mutations", || {
        assert_mutations_refused("waiting_numerals")
    });
}

#[test]
fn a_user_default_instance_applies_before_the_numerals() {
    within_a_minute("waiting_defaults", || {
        assert_accepted(
            WAITING_DEFAULTS,
            &[
                "dNum_eq",
                "dId_eq",
                "dFnNat_eq",
                "dFnNum_eq",
                "dTwo_eq",
                "dVar_eq",
                "dDo_eq",
                "dRedex_eq",
                "dPinNat_eq",
            ],
        )
    });
}

#[test]
fn user_default_mutations_are_refused() {
    within_a_minute("waiting_defaults mutations", || {
        assert_mutations_refused("waiting_defaults")
    });
}

#[test]
fn a_low_priority_user_default_applies_after_the_numerals() {
    within_a_minute("waiting_defaults_low", || {
        assert_accepted(
            WAITING_DEFAULTS_LOW,
            &[
                "dNum_eq",
                "dId_eq",
                "dFnNat_eq",
                "dFnNum_eq",
                "dTwo_eq",
                "dVar_eq",
                "dDo_eq",
                "dRedex_eq",
                "dPinNat_eq",
            ],
        )
    });
}

#[test]
fn low_priority_default_mutations_are_refused() {
    within_a_minute("waiting_defaults_low mutations", || {
        assert_mutations_refused("waiting_defaults_low")
    });
}

/// Lean 4.8.0 refuses `pw` itself (`2 ^ 3` asks for `HPow Nat Nat Int`): it
/// settles a power's operands through the `HPow`/`Pow`/`OfNat` default
/// instances together, which waiting numerals do not model, so a value under
/// `^` does not wait. Letting it wait accepted `pw = 216`.
const POW: &str = "class Tag (α : Type) where\n  tag : α → Nat\n\
                   instance : Tag Nat := ⟨fun x => x⟩\n\
                   instance : Tag Int := ⟨fun x => x.toNat + 100⟩\n\
                   def pw : Nat := let k := 2 ^ 3; Tag.tag (k : Int) + Tag.tag k\n\
                   theorem pw_216 : pw = 216 := by decide\n";

#[test]
fn a_power_does_not_wait() {
    within_a_minute("pow", || {
        let (_, results) = elaborate(POW);
        let failed = failures(&results);
        assert!(
            failed.iter().any(|(name, _)| *name == "pw_216"),
            "`pw = 216` must be refused: {results:#?}"
        );
    });
}

/// Lean 4.8.0 types `xs : List Int` from the first ascription and computes
/// 210, which needs `Inhabited Int`. Clean's prelude may lack that instance;
/// the waiting order then refuses `gHead` (a ground goal Lean's typing needs
/// has no instance) rather than retyping it in the eager order, where `xs :
/// List Nat` made `gHead = 110` provable.
const HEAD: &str = "class Tag (α : Type) where\n  tag : α → Nat\n\
                    instance : Tag Nat := ⟨fun x => x⟩\n\
                    instance : Tag Int := ⟨fun x => x.toNat + 100⟩\n\
                    def gHead : Nat := (fun xs => Tag.tag ((xs.head! : Int)) + Tag.tag xs.head!) [5]\n\
                    theorem gHead_110 : gHead = 110 := rfl\n";

#[test]
fn lean_typing_that_needs_a_missing_instance_is_not_retyped() {
    within_a_minute("head", || {
        let (_, results) = elaborate(HEAD);
        let failed = failures(&results);
        assert!(
            failed.iter().any(|(name, _)| *name == "gHead_110"),
            "`gHead = 110` must be refused: {results:#?}"
        );
    });
}

/// `waiting_settle`: an application whose result is an open `outParam` (R163 review fixes).
#[test]
fn an_open_out_param_result_settles_the_numerals() {
    within_a_minute("waiting_settle", || {
        assert_accepted(
            WAITING_SETTLE,
            &[
                "oGet_eq",
                "oGetList_eq",
                "oGetLet_eq",
                "oGetDo_eq",
                "oGetRedex_eq",
                "oGetBind_eq",
                "oHAdd_eq",
                "oHPow_eq",
                "oHMulDo_eq",
                "oHSubId_eq",
                "oInBody_eq",
                "oUnrelatedDo_eq",
                "oShl_eq",
                "oLocalArg_eq",
                "oLambdaInputs_eq",
                "rEq_eq",
                "rLt_eq",
                "rEqId_eq",
                "rBeq_eq",
                "rBne_eq",
                "rApp_eq",
                "cBinop_eq",
                "cNatIdx_eq",
                "cGround_eq",
                "cAfter_eq",
            ],
        )
    });
}

#[test]
fn out_param_settle_mutations_are_refused() {
    within_a_minute("waiting_settle mutations", || {
        assert_mutations_refused("waiting_settle")
    });
}

/// `waiting_sync`: a nested redex and a `have` that needs no computation (R163 review fixes).
#[test]
fn nested_redexes_and_annotations_keep_numerals_waiting() {
    within_a_minute("waiting_sync", || {
        assert_accepted(WAITING_SYNC, &["sNestedRedex_eq", "sHaveSelf_eq"])
    });
}

#[test]
fn sync_mutations_are_refused() {
    within_a_minute("waiting_sync mutations", || {
        assert_mutations_refused("waiting_sync")
    });
}

/// `waiting_ofnat_default`: a user `OfNat` default at the default priority (R163 review fixes).
#[test]
fn a_user_ofnat_default_decides_open_numerals() {
    within_a_minute("waiting_ofnat_default", || {
        assert_accepted(
            WAITING_OFNAT_DEFAULT,
            &[
                "wBare_eq",
                "wLet_eq",
                "wId_eq",
                "wPair_eq",
                "wSome_eq",
                "wFun_eq",
                "wHole_eq",
                "wAscr_eq",
                "wBodyLit_eq",
                "wRedex_eq",
                "wDo_eq",
                "wBind_eq",
                "wMut_eq",
                "wNatPin_eq",
                "wIntPin_eq",
                "wTopTag_eq",
            ],
        )
    });
}

#[test]
fn user_ofnat_default_mutations_are_refused() {
    within_a_minute("waiting_ofnat_default mutations", || {
        assert_mutations_refused("waiting_ofnat_default")
    });
}

/// `waiting_ofnat_default_100`: a user `OfNat` default at priority 100 (R163 review fixes).
#[test]
fn a_user_ofnat_default_at_the_nat_tier_decides_open_numerals() {
    within_a_minute("waiting_ofnat_default_100", || {
        assert_accepted(
            WAITING_OFNAT_DEFAULT_100,
            &[
                "wBare_eq",
                "wLet_eq",
                "wId_eq",
                "wPair_eq",
                "wSome_eq",
                "wFun_eq",
                "wHole_eq",
                "wAscr_eq",
                "wBodyLit_eq",
                "wRedex_eq",
                "wDo_eq",
                "wBind_eq",
                "wMut_eq",
                "wNatPin_eq",
                "wIntPin_eq",
                "wTopTag_eq",
            ],
        )
    });
}

#[test]
fn user_ofnat_default_100_mutations_are_refused() {
    within_a_minute("waiting_ofnat_default_100 mutations", || {
        assert_mutations_refused("waiting_ofnat_default_100")
    });
}

/// `waiting_ofnat_default_low`: a user `OfNat` default at priority 50 (R163 review fixes).
#[test]
fn a_user_ofnat_default_below_the_nat_tier_loses_to_nat() {
    within_a_minute("waiting_ofnat_default_low", || {
        assert_accepted(
            WAITING_OFNAT_DEFAULT_LOW,
            &[
                "wBare_eq",
                "wLet_eq",
                "wId_eq",
                "wPair_eq",
                "wSome_eq",
                "wFun_eq",
                "wHole_eq",
                "wAscr_eq",
                "wBodyLit_eq",
                "wRedex_eq",
                "wDo_eq",
                "wBind_eq",
                "wMut_eq",
                "wNatPin_eq",
                "wIntPin_eq",
                "wTopTag_eq",
                "wWait_eq",
            ],
        )
    });
}

#[test]
fn user_ofnat_default_low_mutations_are_refused() {
    within_a_minute("waiting_ofnat_default_low mutations", || {
        assert_mutations_refused("waiting_ofnat_default_low")
    });
}

/// `waiting_defaults_tie`: a user default at priority 100 (R163 review fixes).
#[test]
fn a_user_default_at_the_numerals_priority_applies_after_them() {
    within_a_minute("waiting_defaults_tie", || {
        assert_accepted(
            WAITING_DEFAULTS_TIE,
            &["tSub_eq", "tIdSub_eq", "tFn_eq", "tMut_eq", "tBind_eq"],
        )
    });
}

#[test]
fn tie_default_mutations_are_refused() {
    within_a_minute("waiting_defaults_tie mutations", || {
        assert_mutations_refused("waiting_defaults_tie")
    });
}

/// `waiting_defaults_above`: a user default at priority 101 (R163 review fixes).
#[test]
fn a_user_default_just_above_the_numerals_applies_first() {
    within_a_minute("waiting_defaults_above", || {
        assert_accepted(WAITING_DEFAULTS_ABOVE, &["tSub_eq"])
    });
}

#[test]
fn above_default_mutations_are_refused() {
    within_a_minute("waiting_defaults_above mutations", || {
        assert_mutations_refused("waiting_defaults_above")
    });
}

const PIN_PRELUDE: &str = "class Tag (α : Type) where\n  tag : α → Nat\n\
                           instance : Tag Nat := ⟨fun x => x⟩\n\
                           instance : Tag Int := ⟨fun x => x.toNat + 100⟩\n";

const PIN_W: &str = "structure W where v : Nat\n\
                     instance : Tag W := ⟨fun w => w.v + 1000⟩\n\
                     @[default_instance] instance instW {n : Nat} : OfNat W n := ⟨⟨n⟩⟩\n";

/// Definitions Lean 4.8.0 refuses, each with the value an earlier draft of
/// R163 accepted: `rfl` (or `Eq.refl`, `decide … = true`) checked against an
/// annotation that only holds once a waiting numeral is computed (Lean: type
/// mismatch, the numeral's instance is still pending), the drain's check that
/// a waiting numeral's value meets its literal (`k = 7`), and programs a user
/// `OfNat` default makes ill-typed (`Max W`, a `for` over `W`s). Each pin's
/// control is a neighbour Lean accepts and Clean must accept too.
const LEAN_REFUSES: &[(&str, &str, &str)] = &[
    (
        "rfl_open_carrier",
        "def d : Nat := let k := 5; have _h : k - 7 = -2 := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := let k := 5; have _h : k = k := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "eq_refl_open_carrier",
        "def d : Nat := let k := 5; have _h : k - 7 = -2 := Eq.refl _; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := let k := 5; have _h : k = k := Eq.refl _; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "do_have_rfl_open_carrier",
        "def d : Nat := Id.run do\n  let k := 5\n  have _h : k - 7 = -2 := rfl\n  return Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := Id.run do\n  let k := 5\n  have _h : k = k := rfl\n  return Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "decide_rfl_open_carrier",
        "def d : Nat := let k := 5; have _h : decide (k - 7 = -2) = true := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := let k := 5; have _h : decide (k = k) = decide (k = k) := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "have_computed_literal",
        "def d : Nat := let k := 5; have _h : k + 1 = 6 := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := let k := 5; have _h : k + 1 = k + 1 := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "redex_have_computed_literal",
        "def d : Nat := (fun k => have _h : k + 1 = 6 := rfl; Tag.tag (k : Int)) 5\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := (fun k => have _h : k = k := rfl; Tag.tag (k : Int)) 5\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "redex_rfl_open_carrier",
        "def d : Nat := (fun k => have _h : k - 7 = -2 := rfl; Tag.tag (k : Int)) 5\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := (fun k => have _h : k - 7 = k - 7 := rfl; Tag.tag (k : Int)) 5\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
    (
        "have_wrong_literal",
        "def d : Nat := let k := 5; have _h : k = 7 := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
        "def d : Nat := let k := 5; have _h : k = k := rfl; Tag.tag (k : Int)\n\
         theorem d_eq : d = 105 := rfl\n",
    ),
];

/// As [`LEAN_REFUSES`], under a user `OfNat W` default ([`PIN_W`]).
const LEAN_REFUSES_W: &[(&str, &str, &str)] = &[
    (
        "max_over_w",
        "def d : Nat := let k := max 5 3; Tag.tag k\ntheorem d_eq : d = 5 := rfl\n",
        "def d : Nat := let k := id 5; Tag.tag k\ntheorem d_eq : d = 1005 := rfl\n",
    ),
    (
        "for_over_w",
        "def d : Nat := Id.run do\n  let mut s := 0\n  for i in [1, 2] do\n    s := s + i\n  return Tag.tag s\n\
         theorem d_eq : d = 3 := rfl\n",
        "def d : Nat := Id.run do\n  let mut s := id 5\n  s := s\n  return Tag.tag s\n\
         theorem d_eq : d = 1005 := rfl\n",
    ),
];

fn assert_refused_with_control(prelude: &str, pins: &[(&str, &str, &str)]) {
    for (what, refused, control) in pins {
        let (_, results) = elaborate(&format!("{prelude}{refused}"));
        let failed = failures(&results);
        assert!(
            failed.iter().any(|(name, _)| *name == "d"),
            "`{what}`: Lean 4.8.0 refuses `d`, so must Clean: {results:#?}"
        );
        let (_, results) = elaborate(&format!("{prelude}{control}"));
        let failed = failures(&results);
        assert!(
            failed.is_empty(),
            "`{what}` control: Lean 4.8.0 accepts it, so must Clean: {failed:#?}"
        );
    }
}

#[test]
fn checks_lean_refuses_at_a_waiting_numeral_are_refused() {
    within_a_minute("lean refuses", || {
        assert_refused_with_control(PIN_PRELUDE, LEAN_REFUSES)
    });
}

#[test]
fn programs_a_user_ofnat_default_makes_ill_typed_are_refused() {
    within_a_minute("lean refuses under W", || {
        assert_refused_with_control(&format!("{PIN_PRELUDE}{PIN_W}"), LEAN_REFUSES_W)
    });
}

/// Theorems Lean 4.8.0 refuses because the definition has another value.
/// `wrong_value_after_postponed_rfl`: Lean postpones `rfl` here (its
/// unifier is stuck on the pending instances, not refuted) and passes it
/// once `k : Int`, so `d` is 205; Clean refuses the annotation check, and
/// must not fall back to the eager order, which proves `d = 105` at `Nat`.
const WRONG_VALUES: &[(&str, &str)] = &[(
    "wrong_value_after_postponed_rfl",
    "def d : Nat := let k := 5; have _h : k * 2 = k + k := rfl; Tag.tag (k - 7) + Tag.tag (k : Int)\n\
     theorem d_eq : d = 105 := rfl\n",
)];

#[test]
fn values_lean_refuses_after_a_postponed_check_are_refused() {
    within_a_minute("wrong values", || {
        for (what, source) in WRONG_VALUES {
            let (_, results) = elaborate(&format!("{PIN_PRELUDE}{source}"));
            let failed = failures(&results);
            assert!(
                failed
                    .iter()
                    .any(|(name, _)| *name == "d" || *name == "d_eq"),
                "`{what}`: Lean 4.8.0 refuses `d_eq`, so must Clean: {results:#?}"
            );
        }
    });
}
