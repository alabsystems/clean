// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests exercising common Lean 4 declaration patterns.
//!
//! Each test parses real Lean 4 surface syntax via `parse_file`, then
//! elaborates and registers into an `Environment::with_prelude()`.
//! The suite measures elaboration coverage across the most frequent
//! declaration forms found in Lean 4 codebases.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse all declarations from `code`, preprocess through `FileContext`,
/// elaborate each, and register into `env`.  Returns the list of results.
fn elab_file(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    code: &str,
) -> Vec<Result<ElabResult, crate::ElabError>> {
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, file_ctx);
            elaborate_decl_and_register_with_context(env, &processed, file_ctx)
        })
        .collect()
}

#[test]
fn test_r159_omega_mod_lt_does_not_claim_unrelated_overloads_or_f_of_zero() {
    // The dedicated lane must disengage before reconstruction when `%`, `<`,
    // or the apparent zero is not definitionally the canonical Nat operation.
    // In particular, an arbitrary application ending in literal zero is not
    // itself zero. The remainder of omega may solve or reject the theorem, but
    // it must not be preempted by this lane's reconstruction error.
    for (label, code) in [
        (
            "custom HMod",
            "def customHMod : HMod Nat Nat Nat := ⟨fun _ _ => 0⟩\n\
             theorem t (n k : Nat) (h : 0 < k) : \
               @LT.lt Nat instLTNat (@HMod.hMod Nat Nat Nat customHMod n k) k := by omega\n",
        ),
        (
            "custom LT",
            "def customLT : LT Nat := ⟨fun _ _ => True⟩\n\
             theorem t (n k : Nat) (h : 0 < k) : \
               @LT.lt Nat customLT (n % k) k := by omega\n",
        ),
        (
            "application ending in zero",
            "def f (n : Nat) : Nat := n + 1\n\
             theorem t (n k : Nat) (h : f 0 < k) : n % k < k := by omega\n",
        ),
    ] {
        let results = elab_file_prelude(code).1;
        assert!(
            results.first().is_some_and(Result::is_ok),
            "{label}: setup declaration must elaborate: {results:?}",
        );
        assert!(
            !format!("{results:?}").contains("nat-mod bound: kernel rejected"),
            "{label}: the Nat.mod_lt lane claimed a noncanonical goal or hypothesis: {results:?}",
        );
    }
}

/// Convenience wrapper: fresh prelude env + fresh file context.
fn elab_file_prelude(code: &str) -> (Environment, Vec<Result<ElabResult, crate::ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let results = elab_file(&mut env, &mut file_ctx, code);
    (env, results)
}

/// Assert that every result in the list succeeded.
fn assert_all_ok(results: &[Result<ElabResult, crate::ElabError>], context: &str) {
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "{context}: declaration {i} failed: {:?}",
            r.as_ref().err().unwrap()
        );
    }
}

// ---------------------------------------------------------------------------
// 1. Basic definition with type annotation
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_basic_def_with_type_annotation() {
    let code = "def add1 (n : Nat) : Nat := n + 1\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "basic def");

    // The definition should be registered in the environment.
    assert!(
        env.get_const(&Name::from_string("add1")).is_some(),
        "add1 should be registered"
    );

    // Should produce a Definition variant.
    match results[0].as_ref().unwrap() {
        ElabResult::Definition { name, ty, .. } => {
            assert_eq!(*name, Name::from_string("add1"));
            // Type should be Nat -> Nat (a Pi type).
            assert!(
                matches!(ty.kind(), clean_kernel::ExprKind::Pi(_, _, _)),
                "add1 type should be a Pi (Nat -> Nat), got {:?}",
                ty.kind()
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 2. Theorem with sorry
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_theorem_with_sorry() {
    let code = "theorem trivial_sorry : True := sorry\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "theorem sorry");

    assert!(
        env.get_const(&Name::from_string("trivial_sorry")).is_some(),
        "trivial_sorry should be registered"
    );

    match results[0].as_ref().unwrap() {
        ElabResult::Theorem { name, .. } => {
            assert_eq!(*name, Name::from_string("trivial_sorry"));
        }
        other => panic!("expected Theorem, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 3. Structure with fields
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_structure_with_fields() {
    let code = "structure Point where\n  x : Nat\n  y : Nat\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "structure");

    assert!(
        env.get_const(&Name::from_string("Point")).is_some(),
        "Point should be registered"
    );

    match results[0].as_ref().unwrap() {
        ElabResult::Structure {
            name,
            field_names,
            num_params,
            ctor_name,
            ..
        } => {
            assert_eq!(*name, Name::from_string("Point"));
            assert_eq!(*num_params, 0);
            assert_eq!(field_names.len(), 2);
            assert_eq!(field_names[0], Name::from_string("x"));
            assert_eq!(field_names[1], Name::from_string("y"));
            assert_eq!(*ctor_name, Name::from_string("Point.mk"));
        }
        other => panic!("expected Structure, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 4. Inductive with constructors
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_inductive_with_constructors() {
    // Use pipe-prefix constructor syntax common in Lean 4.
    let code = "inductive MyBool\n| myTrue\n| myFalse\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "inductive");

    assert!(
        env.get_const(&Name::from_string("MyBool")).is_some(),
        "MyBool should be registered"
    );

    match results[0].as_ref().unwrap() {
        ElabResult::Inductive {
            name,
            constructors,
            num_params,
            ..
        } => {
            assert_eq!(*name, Name::from_string("MyBool"));
            assert_eq!(*num_params, 0);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, Name::from_string("MyBool.myTrue"));
            assert_eq!(constructors[1].0, Name::from_string("MyBool.myFalse"));
        }
        other => panic!("expected Inductive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 5. Class declaration
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_class_declaration() {
    // `class` elaborates as a Structure with class_info = Some(_).
    let code = "class HasSize (α : Type) where\n  size : α → Nat\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "class");

    assert!(
        env.get_const(&Name::from_string("HasSize")).is_some(),
        "HasSize should be registered"
    );

    match results[0].as_ref().unwrap() {
        ElabResult::Structure {
            name,
            class_info,
            field_names,
            ..
        } => {
            assert_eq!(*name, Name::from_string("HasSize"));
            assert!(
                class_info.is_some(),
                "class declaration should have class_info"
            );
            assert!(
                field_names.iter().any(|n| n.to_string() == "size"),
                "HasSize should have a 'size' field"
            );
        }
        other => panic!("expected Structure (class), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 6. Namespace + qualified access
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_namespace_qualified_access() {
    let code = "\
namespace Foo
def bar := 0
end Foo
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "namespace");

    // The definition should be registered under the qualified name.
    assert!(
        env.get_const(&Name::from_string("Foo.bar")).is_some(),
        "Foo.bar should be registered via namespace qualification"
    );
}

// ---------------------------------------------------------------------------
// 7. Section with variable
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_section_with_variable() {
    let code = "\
section
variable (n : Nat)
def addN (m : Nat) : Nat := m + n
end
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "section with variable");

    assert!(
        env.get_const(&Name::from_string("addN")).is_some(),
        "addN should be registered"
    );
}

// ---------------------------------------------------------------------------
// 8. Pattern match (equation-style def)
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_pattern_match_def() {
    // Equation-style pattern matching definition, common Lean 4 idiom.
    let code = "\
def isZero : Nat → Bool
  | 0 => true
  | _ => false
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "pattern match def");

    assert!(
        env.get_const(&Name::from_string("isZero")).is_some(),
        "isZero should be registered"
    );

    match results[0].as_ref().unwrap() {
        ElabResult::Definition { name, .. } => {
            assert_eq!(*name, Name::from_string("isZero"));
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 9. Recursive function
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_recursive_function() {
    // Lean 4 equation-style recursive definition.
    // Uses `Nat.succ n` pattern instead of `n + 1` to avoid needing HAdd
    // pattern matching on the LHS.
    let code = "\
def factorial : Nat → Nat
  | 0 => 1
  | Nat.succ n => (Nat.succ n) * factorial n
";
    let (env, results) = elab_file_prelude(code);

    // Task 3, slice 1: equation-form recursive defs are normalized into the
    // named-binder + `match` shape and lowered through the inductive's `.rec`.
    // `factorial` must now elaborate, register, and pass the full kernel type
    // check (run by `elaborate_decl_and_register`). Previously this surfaced as
    // `TooManyArguments` because the self-name was left as a `Nat`-typed
    // placeholder; that gap is closed.
    match &results[0] {
        Ok(ElabResult::Definition { name, .. }) => {
            assert_eq!(*name, Name::from_string("factorial"));
            assert!(
                env.get_const(&Name::from_string("factorial")).is_some(),
                "factorial should be registered (kernel-checked) on success"
            );
        }
        other => panic!("expected factorial to elaborate as a Definition, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 10. Multiple declarations: def + theorem using the def
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_multiple_decls_def_then_theorem() {
    let code = "\
def myConst : Nat := 42
theorem myConst_eq : myConst = 42 := sorry
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "multiple decls");

    assert!(
        env.get_const(&Name::from_string("myConst")).is_some(),
        "myConst should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("myConst_eq")).is_some(),
        "myConst_eq should be registered"
    );

    match results[0].as_ref().unwrap() {
        ElabResult::Definition { name, .. } => {
            assert_eq!(*name, Name::from_string("myConst"));
        }
        other => panic!("expected Definition for myConst, got {other:?}"),
    }
    match results[1].as_ref().unwrap() {
        ElabResult::Theorem { name, .. } => {
            assert_eq!(*name, Name::from_string("myConst_eq"));
        }
        other => panic!("expected Theorem for myConst_eq, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Regression: #3395 lambda def with monad return type free variables
// ---------------------------------------------------------------------------

#[test]
fn test_corpus_lambda_def_with_monad_return_type_no_free_vars() {
    // Minimal repro from #3395: `def throwUB : Sem a := fun _s => Except.error SemError.ub`
    // The implicit `a` should be auto-bound, not left as a free variable.
    let code = r#"
inductive SemError where
  | ub : SemError

abbrev Sem (a : Type) := StateT Nat (Except SemError) a

def throwUB : Sem a := fun _s => Except.error SemError.ub
"#;
    let (env, results) = elab_file_prelude(code);

    // All three declarations should succeed.
    assert_all_ok(&results, "lambda def with monad return type (#3395)");

    // throwUB should be registered in the environment.
    assert!(
        env.get_const(&Name::from_string("throwUB")).is_some(),
        "throwUB should be registered"
    );
}

// ---------------------------------------------------------------------------
// Pattern matching on nested inductive types (#3396)
// ---------------------------------------------------------------------------

#[test]
fn test_nested_inductive_match_elaboration() {
    let code = r#"
inductive Value where
  | int : Nat -> Nat -> Value
  | float : Nat -> Value
  | bool : Bool -> Value
  | aggregate : List Value -> Value

def Value.isInt : Value -> Bool
  | Value.int _ _ => true
  | Value.float _ => false
  | Value.bool _ => false
  | Value.aggregate _ => false
"#;
    let (env, results) = elab_file_prelude(code);

    assert_all_ok(&results, "nested inductive match elaboration (#3396)");

    assert!(
        env.get_const(&Name::from_string("Value.isInt")).is_some(),
        "Value.isInt should be registered"
    );
}

#[test]
fn test_nested_inductive_match_returns_field() {
    let code = r#"
inductive Value where
  | int : Nat -> Nat -> Value
  | float : Nat -> Value
  | bool : Bool -> Value
  | aggregate : List Value -> Value

def Value.describe : Value -> Nat
  | Value.int w _ => w
  | Value.float _ => 0
  | Value.bool _ => 0
  | Value.aggregate _ => 0
"#;
    let (env, results) = elab_file_prelude(code);

    assert_all_ok(&results, "nested inductive match returning field (#3396)");

    assert!(
        env.get_const(&Name::from_string("Value.describe"))
            .is_some(),
        "Value.describe should be registered"
    );
}

/// #3420: Pattern matching on nested inductive with wildcard — sorry-free.
///
/// Verifies that match expressions on inductives with nested `List Self`
/// constructors produce sorry-free elaboration when using wildcard arms.
/// The auxiliary type minors (for `Value._List`) must use proper terms
/// (re-elaborated wildcard body or nullary constructor) instead of sorry.
#[test]
fn test_nested_inductive_match_wildcard_no_sorry() {
    let code = r#"
inductive Value where
  | int : Nat -> Nat -> Value
  | ptr : Nat -> Value
  | nullPtr : Value
  | aggregate : List Value -> Value

def Value.isPtr : Value -> Bool
  | Value.ptr _ => true
  | _ => false

def Value.isNull : Value -> Bool
  | Value.nullPtr => true
  | _ => false
"#;
    let (env, results) = elab_file_prelude(code);

    assert_all_ok(&results, "nested inductive wildcard match (#3420)");

    assert!(
        env.get_const(&Name::from_string("Value.isPtr")).is_some(),
        "Value.isPtr should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("Value.isNull")).is_some(),
        "Value.isNull should be registered"
    );

    // Verify NO sorry in the elaborated definitions
    let is_ptr_info = env
        .get_const(&Name::from_string("Value.isPtr"))
        .expect("Value.isPtr should exist");
    if let Some(ref val) = is_ptr_info.value {
        assert!(
            !val.has_sorry(),
            "Value.isPtr should not contain sorry (#3420)"
        );
    }

    let is_null_info = env
        .get_const(&Name::from_string("Value.isNull"))
        .expect("Value.isNull should exist");
    if let Some(ref val) = is_null_info.value {
        assert!(
            !val.has_sorry(),
            "Value.isNull should not contain sorry (#3420)"
        );
    }
}

/// Track H: a constructor field bound by destructuring a nested-aux occurrence
/// (`lanes : Value._List` from `.vector lanes`) coerces back into the real
/// container (`List Value`) when passed to a function/argument expecting it.
///
/// Before the reverse aux→container coercion, `executableLanePayloadMatches
/// lanes` (the trust-ir `getVectorElement` shape) historically failed because
/// the elaborator exposed the temporary `Value._List` mirror instead of the
/// declared `List Value` field. Nested restore now removes that mirror and
/// restores constructor signatures directly, so no coercion constant is needed
/// or allowed; the def must elaborate and kernel-check sorry-free as written.
#[test]
fn test_nested_aux_field_coerces_to_container_argument() {
    let code = r#"
inductive Value where
  | int : Nat -> Nat -> Value
  | vector : List Value -> Value

def payloadMatch (lanes : List Value) : Bool := lanes.length == 4

def getLane (v : Value) (index : Nat) : Option Value :=
  match v with
  | Value.vector lanes =>
    if payloadMatch lanes then lanes.get? index else none
  | _ => none
"#;
    let (env, results) = elab_file_prelude(code);

    assert_all_ok(
        &results,
        "nested-aux field → container argument coercion (Track H)",
    );

    // Restore is representation-transparent: no temporary auxiliary or
    // conversion helper may leak into the public environment.
    assert!(
        env.get_const(&Name::from_string("Value._List.toContainer"))
            .is_none(),
        "nested restore must erase Value._List.toContainer"
    );
    let vector = env
        .get_constructor(&Name::from_string("Value.vector"))
        .expect("Value.vector should be registered");
    assert!(
        !vector
            .type_
            .collect_constants()
            .iter()
            .any(|name| name.to_string().contains("._List")),
        "Value.vector must expose its declared List Value field after restore"
    );

    // The fixed def must be registered and contain NO sorry — the coercion
    // uses the restored field directly, not a placeholder.
    let get_lane = env
        .get_const(&Name::from_string("getLane"))
        .expect("getLane should be registered");
    if let Some(ref val) = get_lane.value {
        assert!(
            !val.has_sorry(),
            "getLane should not contain sorry (Track H aux→container coercion)"
        );
    }
}

/// #3396 (FIX-FV, do-block direction): a `match` over a nested inductive
/// *inside a `do` block* must supply the auxiliary mutual motive(s) and aux
/// minor premises, exactly as the plain-`match` lowering does.
///
/// `Value` (with a `List Value` field) lowers to a mutual block `Value` +
/// `Value._List`, so the native `Value.casesOn` is a multi-motive recursor:
/// `Value.casesOn motive_Value motive_List minor… major`. The do-block lowering
/// historically emitted only the primary motive + primary minors, so the first
/// arm landed in the `motive_List` slot and the kernel rejected the term with
/// `expected Value._List → Sort 1`. This mirrors the trust-ir gating decls
/// `getAllocIdFromPtrARC` / `semAlloca` / `semHeapAlloc`, whose bodies are a
/// `do { let s ← getState; match ptrVal with | .ptr a => … | _ => … }`.
#[test]
fn test_do_match_nested_inductive_supplies_aux_motives() {
    // Use the builtin `Option` monad so the test isolates the do-match aux-motive
    // lowering (a user `Monad` instance is a separate, unrelated elaboration
    // path). The do-block body is the `getAllocIdFromPtrARC` shape: a leading
    // `let _ ←` bind followed by a nested-inductive `match` ending in a `_` arm.
    let code = r#"
inductive Value where
  | int : Nat -> Nat -> Value
  | ptr : Nat -> Value
  | aggregate : List Value -> Value
  | nullPtr : Value

def getAddr (v : Value) : Option Nat := do
  let _ ← (some 0 : Option Nat)
  match v with
  | Value.ptr a => pure a
  | Value.nullPtr => none
  | _ => none
"#;
    let (env, results) = elab_file_prelude(code);

    assert_all_ok(
        &results,
        "do-block match over nested inductive supplies aux motives (#3396 FIX-FV)",
    );

    // The do-match decl must be registered AND kernel-clean (no synthetic sorry
    // — the catch-all `_` arm body discharges the dead aux minors).
    let get_addr = env
        .get_const(&Name::from_string("getAddr"))
        .expect("getAddr should be registered");
    if let Some(ref val) = get_addr.value {
        assert!(
            !val.has_sorry(),
            "getAddr (do-match over nested inductive) must be sorry-free"
        );
    }
}

/// #3407: StateT universe over-generalization — exact issue repro.
///
/// When all type arguments are concrete (Nat, String), the resulting
/// abbrev and definitions using it should have concrete universe levels,
/// not polymorphic ones. Previously, `MySem.getState` and `MySem.setState`
/// failed with "Type mismatch: expected Sort(Succ(Param(u_N))), got
/// Sort(Succ(Zero))" because unsolved universe params leaked through.
///
/// Fixed by commit 6fdfd11b1 (three-part fix: meta type level constraint
/// propagation, non-type implicit arg unification, universe param filtering).
#[test]
fn test_statet_universe_concrete_for_concrete_types() {
    let code = r#"
inductive MyError where
  | notFound : MyError

structure MyState where
  counter : Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def MySem.run (m : MySem a) (s : MyState) := StateT.run m s

def MySem.getState : MySem MyState := StateT.get

def MySem.setState (s : MyState) : MySem Unit := StateT.set s
"#;
    let (env, results) = elab_file_prelude(code);

    // All declarations should succeed (no universe mismatch errors).
    assert_all_ok(&results, "StateT concrete universe (#3407)");

    // Verify all concrete-type definitions have no spurious universe params.
    for name in &["MySem", "MySem.run", "MySem.getState", "MySem.setState"] {
        let info = env.get_const(&Name::from_string(name));
        assert!(info.is_some(), "{name} should be registered");
        let info = info.unwrap();
        // MySem.run has the polymorphic `a` parameter, so it may legitimately
        // have level params. But MySem, getState, setState should be concrete.
        if *name != "MySem.run" {
            assert!(
                info.level_params.is_empty(),
                "{name} should have zero universe params, has: {:?}",
                info.level_params
            );
        }
    }
}

/// #3407: Multi-field structure with monadic composition.
///
/// Tests that functions composing multiple StateT operations work correctly
/// with concrete universe levels, including a manual lambda-style definition.
#[test]
fn test_statet_universe_monadic_composition() {
    let code = r#"
inductive MyError where
  | notFound : MyError

structure MyState where
  counter : Nat
  values : List Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def MySem.getState : MySem MyState := StateT.get

def MySem.setState (s : MyState) : MySem Unit := StateT.set s

def MySem.run (m : MySem a) (s : MyState) := StateT.run m s

def MySem.getCounter : MySem Nat := fun s => Except.ok (s.counter, s)
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "StateT monadic composition (#3407)");

    // getCounter should be concrete (no universe params).
    let info = env.get_const(&Name::from_string("MySem.getCounter"));
    assert!(info.is_some(), "MySem.getCounter should be registered");
    assert!(
        info.unwrap().level_params.is_empty(),
        "MySem.getCounter should have zero universe params, has: {:?}",
        info.unwrap().level_params
    );
}

/// #3407: StateT.run application with concrete result type.
///
/// Tests that applying MySem.run to a concrete monadic action produces
/// a result with concrete universe levels and the correct result type.
#[test]
fn test_statet_run_through_abbrev() {
    let code = r#"
inductive MyError where
  | notFound : MyError

structure MyState where
  counter : Nat
  values : List Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def MySem.run (m : MySem a) (s : MyState) := StateT.run m s

def MySem.getState : MySem MyState := StateT.get

def example1 : Except MyError (MyState × MyState) :=
  MySem.run MySem.getState (MyState.mk 0 [])
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "StateT.run through abbrev (#3407)");

    let info = env.get_const(&Name::from_string("example1"));
    assert!(info.is_some(), "example1 should be registered");
    assert!(
        info.unwrap().level_params.is_empty(),
        "example1 should have zero universe params, has: {:?}",
        info.unwrap().level_params
    );
}

// ---------------------------------------------------------------------------
// induction … generalizing … / … using … clauses
//
// Each positive here has been cross-checked against Lean 4 (4.30.0-rc2):
// the exact source below elaborates with empty output + exit 0 under
// `lean <file>`. These tests additionally require the assembled recursor
// proof term to pass Clean's kernel re-check (`elaborate_decl_and_register`).
// ---------------------------------------------------------------------------

/// TOOTH 1 (positive): `generalizing` is REQUIRED here — the succ case applies
/// the induction hypothesis as a function `ih m`, which only type-checks when
/// `generalizing m` makes `ih : ∀ m, k + m = m + k`. Without generalizing,
/// `ih : k + m = m + k` is not a function and `ih m` is ill-typed (Lean rejects
/// the non-generalizing version with "Function expected at ih"). Kernel-checks.
#[test]
fn test_induction_generalizing_add_comm_kernel_checks() {
    let code = r#"
theorem my_add_comm (n m : Nat) : n + m = m + n := by
  induction n generalizing m with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    rw [Nat.succ_add, Nat.add_succ]
    exact congrArg Nat.succ (ih m)
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "induction n generalizing m (add_comm)");
    assert!(
        env.get_const(&Name::from_string("my_add_comm")).is_some(),
        "my_add_comm should be registered after a kernel-checked proof"
    );
}

/// TOOTH 1 (control that generalizing is load-bearing): the SAME proof body
/// WITHOUT `generalizing m` must fail — `ih` is not a function so `ih m` is
/// ill-typed. Fails closed (elaboration error), never over-accepts.
#[test]
fn test_induction_without_generalizing_ih_application_fails() {
    let code = r#"
theorem my_add_comm_nogen (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    rw [Nat.succ_add, Nat.add_succ]
    exact congrArg Nat.succ (ih m)
"#;
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "without generalizing, `ih m` must fail (ih is not a function): {results:?}"
    );
}

/// TOOTH 2 (positive): `induction n using Nat.rec with | zero | succ` — the
/// named recursor override runs the same structural induction. Lean accepts the
/// equivalent source; Clean kernel-checks the assembled `Nat.rec` proof term.
#[test]
fn test_induction_using_nat_rec_kernel_checks() {
    let code = r#"
theorem my_zero_add (n : Nat) : 0 + n = n := by
  induction n using Nat.rec with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "induction n using Nat.rec (zero_add)");
    assert!(
        env.get_const(&Name::from_string("my_zero_add")).is_some(),
        "my_zero_add should be registered after a kernel-checked proof"
    );
}

/// CONTROL: plain `induction n with | zero => rfl | succ k ih => …` still works
/// and kernel-checks (no regression from the AST/clause changes).
#[test]
fn test_induction_plain_still_kernel_checks() {
    let code = r#"
theorem my_zero_add_plain (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "plain induction n (zero_add)");
    assert!(env
        .get_const(&Name::from_string("my_zero_add_plain"))
        .is_some());
}

/// TOOTH 4 (negative, no over-accept): `generalizing q` where `q` is NOT a
/// hypothesis in the goal must fail closed with an elaboration error — never
/// panic, never silently succeed.
#[test]
fn test_induction_generalizing_unknown_hyp_fails_closed() {
    let code = r#"
theorem gen_unknown (n m : Nat) : n + m = m + n := by
  induction n generalizing q with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ k ih => rw [Nat.succ_add, Nat.add_succ, ih]
"#;
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "generalizing over a non-hypothesis `q` must fail closed: {results:?}"
    );
}

/// TOOTH 4 (negative, no over-accept): a wrong `using` recursor — a name that
/// is not a registered recursor — must fail closed, never over-accept.
#[test]
fn test_induction_using_wrong_recursor_fails_closed() {
    let code = r#"
theorem using_wrong (n : Nat) : 0 + n = n := by
  induction n using Nat.notARecursor with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "using a non-recursor name must fail closed: {results:?}"
    );
}

// ---------------------------------------------------------------------------
// List `cases` / `induction`: universe-param leak in the recursor path.
//
// `List.cons : {α : Type u} → α → List α → List α` keeps `List.{u}` in its
// recursive tail field. The `cases` / `induction` tactics extract that field
// type as a minor-premise binder; before the fix, `α := Nat` was substituted
// but the constructor's own level param `u` was NOT, so the assembled
// `List.rec` / `List.casesOn` proof term carried `List.{u} Nat` where the
// kernel expects `List.{0} Nat` and rejected it (leaked-universe fail-closed
// floor). `Option`/`Nat` did not leak because neither has a recursive field
// re-mentioning the inductive at its own level. The fix instantiates the
// constructor's level params from the major premise's ACTUAL levels. Each
// positive below is cross-checked against real Lean 4 (all accepted).
// ---------------------------------------------------------------------------

/// TOOTH 1 (positive): `cases l <;> rfl` on `List Nat`. Kernel-checks the
/// assembled `List.casesOn` term at `List.{0}` (no leaked `u`).
#[test]
fn test_list_cases_kernel_checks_no_universe_leak() {
    let code = r#"
theorem list_cases_refl (l : List Nat) : l = l := by cases l <;> rfl
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "cases l on List Nat");
    assert!(
        env.get_const(&Name::from_string("list_cases_refl"))
            .is_some(),
        "list_cases_refl should be registered after a kernel-checked List.casesOn proof"
    );
}

/// TOOTH 2 (positive): `induction l with | nil | cons h t ih` on `List Nat`.
/// Kernel-checks the assembled `List.rec` term at `List.{0}` (no leaked `u`).
#[test]
fn test_list_induction_kernel_checks_no_universe_leak() {
    let code = r#"
theorem list_induction_refl (l : List Nat) : l = l := by
  induction l with
  | nil => rfl
  | cons h t ih => rfl
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "induction l on List Nat");
    assert!(
        env.get_const(&Name::from_string("list_induction_refl"))
            .is_some(),
        "list_induction_refl should be registered after a kernel-checked List.rec proof"
    );
}

/// TOOTH 4 (positive): a different element type (`List Bool`) is still universe
/// 0, so `cases l` must kernel-check at `List.{0}` exactly as `List Nat` does.
#[test]
fn test_list_bool_cases_kernel_checks() {
    let code = r#"
theorem list_bool_cases_refl (l : List Bool) : l = l := by cases l <;> rfl
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "cases l on List Bool");
    assert!(env
        .get_const(&Name::from_string("list_bool_cases_refl"))
        .is_some());
}

/// NEGATIVE (no over-accept): `cases l <;> rfl` proving `l = []` must fail —
/// the `cons` branch goal `h :: t = []` is not `rfl`-closable. Fail closed
/// (elaboration error), never a panic and never a silent accept. Matches real
/// Lean 4, which rejects the equivalent source.
#[test]
fn test_list_cases_wrong_goal_fails_closed() {
    let code = r#"
theorem list_cases_bad (l : List Nat) : l = [] := by cases l <;> rfl
"#;
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "cases l proving `l = []` must fail closed (cons case is not rfl): {results:?}"
    );
}

/// CONTROL (no regression): `cases`/`induction` on `Option Nat` still
/// kernel-check. Option has no recursive field, so it never leaked `u`; this
/// guards against the fix accidentally breaking the non-leaking path.
#[test]
fn test_option_cases_induction_still_kernel_check() {
    let code = r#"
theorem option_cases_refl (o : Option Nat) : o = o := by cases o <;> rfl
theorem option_induction_refl (o : Option Nat) : o = o := by
  induction o with
  | none => rfl
  | some a => rfl
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "cases/induction on Option Nat");
    assert!(env
        .get_const(&Name::from_string("option_cases_refl"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("option_induction_refl"))
        .is_some());
}

/// `Subtype → base` structure coercion (`↑x = x.val`): a value `x : Subtype p`
/// (i.e. `{a // p a}`) used where its base type is expected coerces to
/// `x.val`, exactly as Lean 4 inserts `instCoeSubtype`. This is pervasive in
/// Mathlib (`Data/Subtype`'s `Subtype.prop (x : Subtype p) : p x := x.2` hit it
/// directly, 0/45 before the fix). The emitted `Subtype.val` application is
/// kernel-re-checked, so the def must register sorry-free.
#[test]
fn test_subtype_value_coerces_to_base_type() {
    // `x : Subtype p` used directly where the base `Nat` is expected.
    let code = r#"
def base {p : Nat -> Prop} (x : Subtype p) : Nat := x
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Subtype → base coercion (direct)");

    let base = env
        .get_const(&Name::from_string("base"))
        .expect("base should be registered");
    if let Some(ref val) = base.value {
        assert!(
            !val.has_sorry(),
            "base should not contain sorry (Subtype.val coercion is a genuine projection)"
        );
    }
}

/// The primary `Data/Subtype` shape: `Subtype.prop (x : Subtype p) : p x := x.2`.
/// `p x` needs `x : Nat` (the base) but `x : Subtype p`, so the coercion must
/// fire inside the predicate application. Before the fix this died with
/// `TypeMismatch { expected: Nat, actual: Subtype }`.
#[test]
fn test_subtype_value_coerces_in_predicate_application() {
    let code = r#"
theorem prop {p : Nat -> Prop} (x : Subtype p) : p x := x.2
"#;
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Subtype → base coercion (predicate application)");
}

/// Regression guard: the EXPLICIT `x.val` projection — which always worked —
/// must keep elaborating unchanged now that the implicit coercion also fires.
#[test]
fn test_subtype_val_projection_still_elaborates() {
    let code = r#"
theorem prop_val {p : Nat -> Prop} (x : Subtype p) : p x.val := x.2
"#;
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "explicit Subtype.val projection");
}

/// No over-coercion: the `Subtype → base` step fires ONLY when the extracted
/// base unifies with the expected type. `Subtype p` (base `Nat`) used where a
/// `Bool` is expected must NOT coerce (no `Nat → Bool` bridge either) — it
/// stays a loud, honest mismatch rather than being silently mis-projected.
#[test]
fn test_subtype_value_does_not_over_coerce_to_unrelated_type() {
    let code = r#"
def bad {p : Nat -> Prop} (x : Subtype p) : Bool := x
"#;
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(std::result::Result::is_err),
        "Subtype p must NOT coerce to Bool (base Nat does not unify with Bool)"
    );
}

/// A PARAMETRIC nested inductive — `Rose α` whose ctor stores `List (Rose α)` —
/// must elaborate a `match` post-B0-B5. The nested aux (`List (Rose α)`) is the
/// erased-and-re-keyed real `List`, so the match lowering must source the aux
/// motive/minors from the recursor with the *parameter* (`α := Nat`) substituted
/// — the param-less recursor-walk alone would leave `α` a dangling bvar. (Adjacent
/// gap to the B0-B5 arc: `block_motive_domains` now instantiates recursor params.)
#[test]
fn test_parametric_nested_inductive_match_elaborates() {
    let code = r#"
inductive Rose (a : Type) where
  | node : a -> List (Rose a) -> Rose a

def Rose.root : Rose Nat -> Nat
  | Rose.node x _ => x
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric nested inductive match");
    assert!(
        env.get_const(&Name::from_string("Rose.root")).is_some(),
        "Rose.root should be registered"
    );
}

/// A PARAMETRIC single-ctor single-field `deriving DecidableEq` (`Box α`) must
/// produce a real decision procedure that REDUCES correctly — not just
/// type-checks. Post-fix (task #14): `block`-free fvar-based builder with
/// projection injectivity (no parametric `noConfusion`). A decision that
/// type-checks but decides wrong would be unsound, so this asserts reduction.
#[test]
fn test_parametric_decidable_eq_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Literal, TypeChecker};
    let code = "inductive Box (a : Type) where\n  | mk : a -> Box a\n  deriving DecidableEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric DecidableEq deriving (Box α)");
    assert!(
        env.get_const(&Name::from_string("instBoxDecidableEq"))
            .is_some(),
        "instBoxDecidableEq should be registered"
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Box.mk"), vec![]),
            [nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let head_ctor = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("instBoxDecidableEq"), vec![]),
            [
                nat.clone(),
                Expr::const_(Name::from_string("Nat.decEq"), vec![]),
                a,
                b,
            ],
        );
        let w = tc.whnf(&app);
        let mut f = &w;
        while let ExprKind::App(g, _) = f.kind() {
            f = g;
        }
        match f.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    // Equal fields ⇒ isTrue; distinct fields ⇒ isFalse (projection injectivity).
    assert_eq!(
        head_ctor(mk(1), mk(1)),
        "Decidable.isTrue",
        "Box.mk 1 = Box.mk 1 must decide isTrue (reduces, not just type-checks)"
    );
    assert_eq!(
        head_ctor(mk(1), mk(2)),
        "Decidable.isFalse",
        "Box.mk 1 = Box.mk 2 must decide isFalse (mk injectivity via projection)"
    );

    // Sound: the instance's axiom closure is empty (no sorry/faked axiom).
    let deps = env
        .axiom_deps(&Name::from_string("instBoxDecidableEq"))
        .expect("axiom_deps for registered instance");
    assert!(
        deps.is_empty(),
        "instBoxDecidableEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Parametric single-ctor single-param-field `deriving BEq` (`Box α`) must
/// produce a real comparison that REDUCES: `Box.mk x == Box.mk y ≡ x == y`,
/// replacing the weak `Bool.true` fallback (task #14). Asserts reduction, not
/// just type-checking.
#[test]
fn test_parametric_beq_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive Box (a : Type) where\n  | mk : a -> Box a\n  deriving BEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric BEq deriving (Box α)");
    assert!(
        env.get_const(&Name::from_string("instBoxBEq")).is_some(),
        "instBoxBEq should be registered"
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Box.mk"), vec![]),
            [nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = |a: Expr, b: Expr| -> String {
        let boxbeq = Expr::apps(
            Expr::const_(Name::from_string("instBoxBEq"), vec![]),
            [nat.clone(), ni.clone()],
        );
        let boxnat = Expr::app(
            Expr::const_(Name::from_string("Box"), vec![Level::zero()]),
            nat.clone(),
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
            [boxnat, boxbeq, a, b],
        );
        let w = tc.whnf(&app);
        match w.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        beq(mk(1), mk(1)),
        "Bool.true",
        "Box.mk 1 == Box.mk 1 must be true"
    );
    assert_eq!(
        beq(mk(1), mk(2)),
        "Bool.false",
        "Box.mk 1 == Box.mk 2 must be false"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instBoxBEq"))
        .expect("axiom_deps for registered instance");
    assert!(
        deps.is_empty(),
        "instBoxBEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Parametric MULTI-param MULTI-field `deriving BEq` (`Pair a b`) — the general
/// N-param/N-field builder folds per-field `BEq.beq` with `Bool.and`. Verifies
/// reduction: equal ⇒ true, differ in EITHER field ⇒ false.
#[test]
fn test_parametric_beq_pair_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code =
        "inductive Pair (a : Type) (b : Type) where\n  | mk : a -> b -> Pair a b\n  deriving BEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric BEq deriving (Pair a b)");
    assert!(
        env.get_const(&Name::from_string("instPairBEq")).is_some(),
        "instPairBEq should be registered"
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |m: u64, n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Pair.mk"), vec![]),
            [nat.clone(), nat.clone(), lit(m), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = |a: Expr, b: Expr| -> String {
        let pbeq = Expr::apps(
            Expr::const_(Name::from_string("instPairBEq"), vec![]),
            [nat.clone(), nat.clone(), ni.clone(), ni.clone()],
        );
        let pnn = Expr::apps(
            Expr::const_(
                Name::from_string("Pair"),
                vec![Level::zero(), Level::zero()],
            ),
            [nat.clone(), nat.clone()],
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
            [pnn, pbeq, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        beq(mk(1, 2), mk(1, 2)),
        "Bool.true",
        "mk 1 2 == mk 1 2 ⇒ true"
    );
    assert_eq!(
        beq(mk(1, 2), mk(9, 2)),
        "Bool.false",
        "differ in field 0 ⇒ false"
    );
    assert_eq!(
        beq(mk(1, 2), mk(1, 9)),
        "Bool.false",
        "differ in field 1 ⇒ false"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instPairBEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instPairBEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Parametric MULTI-CTOR `deriving BEq` (`MyOpt a` = nullary `none2` +
/// unary `some2 : a → MyOpt a`) — the multi-ctor builder nests `casesOn` on both
/// scrutinees: the diagonal (same ctor) folds per-field `BEq.beq`, off-diagonal
/// (distinct ctors) is `Bool.false`. Before this brick the parametric path was
/// gated single-ctor-only and multi-ctor fell through to a weak total
/// `Bool.true` — so `x == y` LIED `true` for distinct values (silent-wrong S2).
/// Verifies the lie is gone: distinct fields ⇒ false, distinct ctors ⇒ false.
#[test]
fn test_parametric_beq_multi_ctor_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code =
        "inductive MyOpt (a : Type) where\n  | none2\n  | some2 : a -> MyOpt a\n  deriving BEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric multi-ctor BEq deriving (MyOpt a)");
    assert!(
        env.get_const(&Name::from_string("instMyOptBEq")).is_some(),
        "instMyOptBEq should be registered"
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let none2 = Expr::apps(
        Expr::const_(Name::from_string("MyOpt.none2"), vec![]),
        [nat.clone()],
    );
    let some2 = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MyOpt.some2"), vec![]),
            [nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = |a: Expr, b: Expr| -> String {
        let obeq = Expr::apps(
            Expr::const_(Name::from_string("instMyOptBEq"), vec![]),
            [nat.clone(), ni.clone()],
        );
        let onat = Expr::app(
            Expr::const_(Name::from_string("MyOpt"), vec![Level::zero()]),
            nat.clone(),
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
            [onat, obeq, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        beq(none2.clone(), none2.clone()),
        "Bool.true",
        "none2 == none2 ⇒ true"
    );
    assert_eq!(
        beq(some2(1), some2(1)),
        "Bool.true",
        "some2 1 == some2 1 ⇒ true"
    );
    assert_eq!(
        beq(some2(1), some2(2)),
        "Bool.false",
        "some2 1 == some2 2 ⇒ false (was the lie)"
    );
    assert_eq!(
        beq(none2.clone(), some2(1)),
        "Bool.false",
        "none2 == some2 1 ⇒ false (distinct ctors)"
    );
    assert_eq!(
        beq(some2(1), none2.clone()),
        "Bool.false",
        "some2 1 == none2 ⇒ false (distinct ctors)"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instMyOptBEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instMyOptBEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Parametric MULTI-ctor MULTI-param `deriving BEq` (`MySum a b` = `inl : a → …`
/// `inr : b → …`) — two field-carrying ctors over distinct parameters. Exercises
/// the off-diagonal `Bool.false` minors and per-parameter `[BEq a] [BEq b]`
/// instance binding. Distinct ctors ⇒ false even when the payloads coincide.
#[test]
fn test_parametric_beq_sum_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive MySum (a : Type) (b : Type) where\n  | inl : a -> MySum a b\n  | inr : b -> MySum a b\n  deriving BEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric multi-ctor BEq deriving (MySum a b)");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let inl = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MySum.inl"), vec![]),
            [nat.clone(), nat.clone(), lit(n)],
        )
    };
    let inr = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MySum.inr"), vec![]),
            [nat.clone(), nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = |a: Expr, b: Expr| -> String {
        let sbeq = Expr::apps(
            Expr::const_(Name::from_string("instMySumBEq"), vec![]),
            [nat.clone(), nat.clone(), ni.clone(), ni.clone()],
        );
        let snn = Expr::apps(
            Expr::const_(
                Name::from_string("MySum"),
                vec![Level::zero(), Level::zero()],
            ),
            [nat.clone(), nat.clone()],
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
            [snn, sbeq, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(beq(inl(1), inl(1)), "Bool.true", "inl 1 == inl 1 ⇒ true");
    assert_eq!(beq(inl(1), inl(2)), "Bool.false", "inl 1 == inl 2 ⇒ false");
    assert_eq!(beq(inr(5), inr(5)), "Bool.true", "inr 5 == inr 5 ⇒ true");
    assert_eq!(
        beq(inl(1), inr(1)),
        "Bool.false",
        "inl 1 == inr 1 ⇒ false (distinct ctors, equal payload)"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instMySumBEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instMySumBEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// RECURSIVE PARAMETRIC `deriving BEq` (`Tree a` with a self-recursive `node`
/// field) — recursive `Tree a` sub-fields compare via the type's OWN BEq (the
/// recursor induction hypothesis), the `a` field via `[BEq a]`. Deep structural
/// comparison must reduce.
#[test]
fn test_parametric_beq_recursive_tree() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive Tree (a : Type) where\n  | leaf\n  | node : Tree a -> a -> Tree a -> Tree a\n  deriving BEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "recursive parametric BEq deriving (Tree a)");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let leaf = Expr::apps(
        Expr::const_(Name::from_string("Tree.leaf"), vec![]),
        [nat.clone()],
    );
    let node = |l: Expr, x: u64, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Tree.node"), vec![]),
            [nat.clone(), l, lit(x), r],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = |a: Expr, b: Expr| -> String {
        let tbeq = Expr::apps(
            Expr::const_(Name::from_string("instTreeBEq"), vec![]),
            [nat.clone(), ni.clone()],
        );
        let tnat = Expr::app(
            Expr::const_(Name::from_string("Tree"), vec![Level::zero()]),
            nat.clone(),
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
            [tnat, tbeq, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    let t1 = node(leaf.clone(), 1, leaf.clone());
    let t1b = node(leaf.clone(), 1, leaf.clone());
    let t2 = node(leaf.clone(), 2, leaf.clone());
    assert_eq!(
        beq(leaf.clone(), leaf.clone()),
        "Bool.true",
        "leaf == leaf ⇒ true"
    );
    assert_eq!(
        beq(t1.clone(), t1b),
        "Bool.true",
        "node leaf 1 leaf == same ⇒ true"
    );
    assert_eq!(beq(t1.clone(), t2), "Bool.false", "differ in value ⇒ false");
    assert_eq!(
        beq(t1.clone(), leaf.clone()),
        "Bool.false",
        "node vs leaf ⇒ false"
    );
    let n1 = node(node(leaf.clone(), 1, leaf.clone()), 2, leaf.clone());
    let n1b = node(node(leaf.clone(), 1, leaf.clone()), 2, leaf.clone());
    let n2 = node(node(leaf.clone(), 9, leaf.clone()), 2, leaf.clone());
    assert_eq!(beq(n1.clone(), n1b), "Bool.true", "deep-equal trees ⇒ true");
    assert_eq!(beq(n1, n2), "Bool.false", "deep-differing leaf ⇒ false");
    let deps = env
        .axiom_deps(&Name::from_string("instTreeBEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instTreeBEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Parametric MULTI-param MULTI-field `deriving DecidableEq` (`Pair a b`) — the
/// general builder decides fields left-to-right via nested `Decidable.casesOn`,
/// `isFalse` by per-field projection injectivity, `isTrue` by an `Eq.trans`
/// congruence chain. Verifies REDUCTION: equal ⇒ isTrue, differ in EITHER field
/// ⇒ isFalse.
#[test]
fn test_parametric_decidable_eq_pair_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Literal, TypeChecker};
    let code = "inductive Pair (a : Type) (b : Type) where\n  | mk : a -> b -> Pair a b\n  deriving DecidableEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric DecidableEq deriving (Pair a b)");
    assert!(
        env.get_const(&Name::from_string("instPairDecidableEq"))
            .is_some(),
        "instPairDecidableEq should be registered"
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |m: u64, n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Pair.mk"), vec![]),
            [nat.clone(), nat.clone(), lit(m), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
    let dec = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("instPairDecidableEq"), vec![]),
            [nat.clone(), nat.clone(), ni.clone(), ni.clone(), a, b],
        );
        let w = tc.whnf(&app);
        let mut f = &w;
        while let ExprKind::App(g, _) = f.kind() {
            f = g;
        }
        match f.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        dec(mk(1, 2), mk(1, 2)),
        "Decidable.isTrue",
        "mk 1 2 = mk 1 2 ⇒ isTrue"
    );
    assert_eq!(
        dec(mk(1, 2), mk(9, 2)),
        "Decidable.isFalse",
        "differ in field 0 ⇒ isFalse"
    );
    assert_eq!(
        dec(mk(1, 2), mk(1, 9)),
        "Decidable.isFalse",
        "differ in field 1 ⇒ isFalse"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instPairDecidableEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instPairDecidableEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Derived `Ord` on a fielded multi-ctor must compare FIELDS, not just the
/// constructor ordinal. `Val.mkA 1` vs `Val.mkA 2` (same ctor) must be
/// `Ordering.lt`, not `Ordering.eq`. (Also exercises the newly-wired `Ord`
/// class in the prelude — previously deriving Ord failed with "Unknown
/// constant: Ord".)
#[test]
fn test_derive_ord_fielded_compares_fields() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive Val where\n  | mkA : Nat -> Val\n  | mkB : Nat -> Val\n  deriving Ord\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "deriving Ord (fielded multi-ctor Val)");
    let inst_name = Name::from_string("instValOrd");
    assert!(
        env.get_const(&inst_name).is_some(),
        "instValOrd should be registered"
    );
    let val = Expr::const_(Name::from_string("Val"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |ctor: &str, n: u64| {
        Expr::app(
            Expr::const_(Name::from_string(&format!("Val.{ctor}")), vec![]),
            lit(n),
        )
    };
    let tc = TypeChecker::new(&env);
    let cmp = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("Ord.compare"), vec![Level::zero()]),
            [val.clone(), Expr::const_(inst_name.clone(), vec![]), a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        cmp(mk("mkA", 1), mk("mkA", 1)),
        "Ordering.eq",
        "mkA 1 vs mkA 1 ⇒ eq"
    );
    assert_eq!(
        cmp(mk("mkA", 1), mk("mkA", 2)),
        "Ordering.lt",
        "mkA 1 vs mkA 2 ⇒ lt (was eq: S3 bug)"
    );
    assert_eq!(
        cmp(mk("mkA", 2), mk("mkA", 1)),
        "Ordering.gt",
        "mkA 2 vs mkA 1 ⇒ gt"
    );
    assert_eq!(
        cmp(mk("mkA", 5), mk("mkB", 1)),
        "Ordering.lt",
        "mkA _ vs mkB _ ⇒ lt (ordinal)"
    );
    assert_eq!(
        cmp(mk("mkB", 1), mk("mkA", 9)),
        "Ordering.gt",
        "mkB _ vs mkA _ ⇒ gt (ordinal)"
    );
}

/// Derived `Ord` on a MULTI-FIELD ctor compares fields lexicographically via
/// the `Ordering.then` chain: the first differing field decides.
#[test]
fn test_derive_ord_multifield_lexicographic() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive P2 where\n  | mk : Nat -> Nat -> P2\n  deriving Ord\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "deriving Ord (multi-field P2)");
    let p2 = Expr::const_(Name::from_string("P2"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |m: u64, n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("P2.mk"), vec![]),
            [lit(m), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let cmp = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("Ord.compare"), vec![Level::zero()]),
            [
                p2.clone(),
                Expr::const_(Name::from_string("instP2Ord"), vec![]),
                a,
                b,
            ],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        cmp(mk(1, 2), mk(1, 2)),
        "Ordering.eq",
        "mk 1 2 vs mk 1 2 ⇒ eq"
    );
    assert_eq!(
        cmp(mk(1, 2), mk(1, 3)),
        "Ordering.lt",
        "second field decides ⇒ lt"
    );
    assert_eq!(
        cmp(mk(1, 9), mk(2, 0)),
        "Ordering.lt",
        "first field dominates ⇒ lt"
    );
    assert_eq!(
        cmp(mk(2, 0), mk(1, 9)),
        "Ordering.gt",
        "first field dominates ⇒ gt"
    );
}

/// Derived `Ord` on a nullary enum compares constructor ordinals (declaration
/// order), the correct behavior for fieldless constructors.
#[test]
fn test_derive_ord_nullary_enum_ordinal() {
    use clean_kernel::{Expr, ExprKind, Level, TypeChecker};
    let code = "inductive Dir where\n  | north\n  | south\n  | east\n  deriving Ord\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "deriving Ord (nullary enum Dir)");
    let dir = Expr::const_(Name::from_string("Dir"), vec![]);
    let c = |name: &str| Expr::const_(Name::from_string(&format!("Dir.{name}")), vec![]);
    let tc = TypeChecker::new(&env);
    let cmp = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("Ord.compare"), vec![Level::zero()]),
            [
                dir.clone(),
                Expr::const_(Name::from_string("instDirOrd"), vec![]),
                a,
                b,
            ],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        cmp(c("north"), c("north")),
        "Ordering.eq",
        "north = north ⇒ eq"
    );
    assert_eq!(
        cmp(c("north"), c("south")),
        "Ordering.lt",
        "north < south ⇒ lt"
    );
    assert_eq!(
        cmp(c("east"), c("north")),
        "Ordering.gt",
        "east > north ⇒ gt"
    );
}

/// PARAMETRIC `deriving Ord` (`Box a` = single ctor `mk : a → Box a`) — threads
/// `{a} [Ord a]` and compares the field via the bound instance. Before this the
/// parametric Ord path was a weak-`eq` fallback (a reachable silent-wrong:
/// `compare (Box.mk 1) (Box.mk 2) ⇒ eq`).
#[test]
fn test_derive_ord_parametric_box() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive Box (a : Type) where\n  | mk : a -> Box a\n  deriving Ord\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric deriving Ord (Box a)");
    assert!(
        env.get_const(&Name::from_string("instBoxOrd")).is_some(),
        "instBoxOrd should be registered"
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let mk = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Box.mk"), vec![]),
            [nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let cmp = |a: Expr, b: Expr| -> String {
        let box_ord = Expr::apps(
            Expr::const_(Name::from_string("instBoxOrd"), vec![]),
            [nat.clone(), ni.clone()],
        );
        let box_nat = Expr::app(
            Expr::const_(Name::from_string("Box"), vec![Level::zero()]),
            nat.clone(),
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("Ord.compare"), vec![Level::zero()]),
            [box_nat, box_ord, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        cmp(mk(1), mk(1)),
        "Ordering.eq",
        "Box.mk 1 vs Box.mk 1 ⇒ eq"
    );
    assert_eq!(
        cmp(mk(1), mk(2)),
        "Ordering.lt",
        "Box.mk 1 vs Box.mk 2 ⇒ lt (was eq: weak fallback)"
    );
    assert_eq!(
        cmp(mk(2), mk(1)),
        "Ordering.gt",
        "Box.mk 2 vs Box.mk 1 ⇒ gt"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instBoxOrd"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instBoxOrd must have EMPTY axiom closure, got {deps:?}"
    );
}

/// PARAMETRIC MULTI-ctor `deriving Ord` (`MyOpt a` = nullary `none2` + unary
/// `some2 : a → MyOpt a`) — nullary diagonal ⇒ `Ordering.eq`, unary diagonal
/// compares the field via `[Ord a]`, off-diagonal compares ctor ordinals
/// (`none2` < `some2`).
#[test]
fn test_derive_ord_parametric_myopt() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code =
        "inductive MyOpt (a : Type) where\n  | none2\n  | some2 : a -> MyOpt a\n  deriving Ord\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric multi-ctor deriving Ord (MyOpt a)");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let none2 = Expr::apps(
        Expr::const_(Name::from_string("MyOpt.none2"), vec![]),
        [nat.clone()],
    );
    let some2 = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MyOpt.some2"), vec![]),
            [nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let cmp = |a: Expr, b: Expr| -> String {
        let o_ord = Expr::apps(
            Expr::const_(Name::from_string("instMyOptOrd"), vec![]),
            [nat.clone(), ni.clone()],
        );
        let o_nat = Expr::app(
            Expr::const_(Name::from_string("MyOpt"), vec![Level::zero()]),
            nat.clone(),
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("Ord.compare"), vec![Level::zero()]),
            [o_nat, o_ord, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        cmp(none2.clone(), none2.clone()),
        "Ordering.eq",
        "none2 = none2 ⇒ eq"
    );
    assert_eq!(
        cmp(some2(1), some2(1)),
        "Ordering.eq",
        "some2 1 = some2 1 ⇒ eq"
    );
    assert_eq!(
        cmp(some2(1), some2(2)),
        "Ordering.lt",
        "some2 1 < some2 2 ⇒ lt"
    );
    assert_eq!(
        cmp(none2.clone(), some2(1)),
        "Ordering.lt",
        "none2 < some2 ⇒ lt (ordinal)"
    );
    assert_eq!(
        cmp(some2(1), none2.clone()),
        "Ordering.gt",
        "some2 > none2 ⇒ gt (ordinal)"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instMyOptOrd"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instMyOptOrd must have EMPTY axiom closure, got {deps:?}"
    );
}

/// RECURSIVE PARAMETRIC `deriving Ord` (`Tree a`) — recursive `Tree a` sub-fields
/// compare via the recursor IH (`Ord.compare`), the `a` field via `[Ord a]`,
/// chained with `Ordering.then`; distinct ctors by ordinal. Deep comparison
/// must reduce.
#[test]
fn test_derive_ord_recursive_tree() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, TypeChecker};
    let code = "inductive Tree (a : Type) where\n  | leaf\n  | node : Tree a -> a -> Tree a -> Tree a\n  deriving Ord\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "recursive parametric Ord deriving (Tree a)");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let leaf = Expr::apps(
        Expr::const_(Name::from_string("Tree.leaf"), vec![]),
        [nat.clone()],
    );
    let node = |l: Expr, x: u64, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Tree.node"), vec![]),
            [nat.clone(), l, lit(x), r],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let cmp = |a: Expr, b: Expr| -> String {
        let tord = Expr::apps(
            Expr::const_(Name::from_string("instTreeOrd"), vec![]),
            [nat.clone(), ni.clone()],
        );
        let tnat = Expr::app(
            Expr::const_(Name::from_string("Tree"), vec![Level::zero()]),
            nat.clone(),
        );
        let app = Expr::apps(
            Expr::const_(Name::from_string("Ord.compare"), vec![Level::zero()]),
            [tnat, tord, a, b],
        );
        match tc.whnf(&app).kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    let t1 = node(leaf.clone(), 1, leaf.clone());
    let t1b = node(leaf.clone(), 1, leaf.clone());
    let t2 = node(leaf.clone(), 2, leaf.clone());
    assert_eq!(
        cmp(leaf.clone(), leaf.clone()),
        "Ordering.eq",
        "leaf = leaf ⇒ eq"
    );
    assert_eq!(
        cmp(t1.clone(), t1b),
        "Ordering.eq",
        "node leaf 1 leaf = same ⇒ eq"
    );
    assert_eq!(
        cmp(t1.clone(), t2.clone()),
        "Ordering.lt",
        "value 1 < 2 ⇒ lt"
    );
    assert_eq!(cmp(t2, t1.clone()), "Ordering.gt", "value 2 > 1 ⇒ gt");
    assert_eq!(
        cmp(leaf.clone(), t1.clone()),
        "Ordering.lt",
        "leaf < node ⇒ lt (ordinal)"
    );
    // deep: differ in a nested leaf's value
    let n1 = node(node(leaf.clone(), 1, leaf.clone()), 5, leaf.clone());
    let n2 = node(node(leaf.clone(), 9, leaf.clone()), 5, leaf.clone());
    assert_eq!(
        cmp(n1.clone(), n2),
        "Ordering.lt",
        "deep first-subtree 1 < 9 ⇒ lt"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instTreeOrd"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instTreeOrd must have EMPTY axiom closure, got {deps:?}"
    );
}

/// RECURSIVE PARAMETRIC `deriving DecidableEq` (`Tree a`) — recursor-driven
/// decision: recursive `Tree a` sub-fields decide via the IH
/// (`(t' : Tree a) → Decidable (t = t')`), the `a` field via `[DecidableEq a]`.
/// Deep decision must reduce to isTrue/isFalse.
#[test]
fn test_derive_decidable_eq_recursive_tree() {
    use clean_kernel::{BigNat, Expr, ExprKind, Literal, TypeChecker};
    let code = "inductive Tree (a : Type) where\n  | leaf\n  | node : Tree a -> a -> Tree a -> Tree a\n  deriving DecidableEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "recursive parametric DecidableEq deriving (Tree a)",
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let leaf = Expr::apps(
        Expr::const_(Name::from_string("Tree.leaf"), vec![]),
        [nat.clone()],
    );
    let node = |l: Expr, x: u64, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Tree.node"), vec![]),
            [nat.clone(), l, lit(x), r],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
    let dec = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("instTreeDecidableEq"), vec![]),
            [nat.clone(), ni.clone(), a, b],
        );
        let w = tc.whnf(&app);
        let mut f = &w;
        while let ExprKind::App(g, _) = f.kind() {
            f = g;
        }
        match f.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    let t1 = node(leaf.clone(), 1, leaf.clone());
    let t1b = node(leaf.clone(), 1, leaf.clone());
    let t2 = node(leaf.clone(), 2, leaf.clone());
    assert_eq!(
        dec(leaf.clone(), leaf.clone()),
        "Decidable.isTrue",
        "leaf = leaf ⇒ isTrue"
    );
    assert_eq!(
        dec(t1.clone(), t1b),
        "Decidable.isTrue",
        "node leaf 1 leaf = same ⇒ isTrue"
    );
    assert_eq!(
        dec(t1.clone(), t2),
        "Decidable.isFalse",
        "differ in value ⇒ isFalse"
    );
    assert_eq!(
        dec(t1.clone(), leaf.clone()),
        "Decidable.isFalse",
        "node vs leaf ⇒ isFalse"
    );
    let n1 = node(node(leaf.clone(), 1, leaf.clone()), 2, leaf.clone());
    let n1b = node(node(leaf.clone(), 1, leaf.clone()), 2, leaf.clone());
    let n2 = node(node(leaf.clone(), 9, leaf.clone()), 2, leaf.clone());
    assert_eq!(
        dec(n1.clone(), n1b),
        "Decidable.isTrue",
        "deep-equal ⇒ isTrue"
    );
    assert_eq!(dec(n1, n2), "Decidable.isFalse", "deep-differing ⇒ isFalse");
    let deps = env
        .axiom_deps(&Name::from_string("instTreeDecidableEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instTreeDecidableEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// GRANDPARENT FIELDS through a PARAMETERIZED `extends` chain (`C a extends B a
/// extends A a`) — a field declared on `A` must be projectable on a `C` value.
/// Mirrors Mathlib's algebraic hierarchy (`Monoid extends Semigroup extends
/// Mul`, all parameterized by the carrier). Previously only a parameterized
/// parent's DIRECT fields were re-exposed, so a grandparent field was a LOUD
/// unknown at the use site.
#[test]
fn test_structure_parameterized_grandparent_field() {
    let code = "structure A (t : Type) where\n  fa : t\nstructure B (t : Type) extends A t where\n  fb : t\nstructure C (t : Type) extends B t where\n  fc : t\ndef getFa (c : C Nat) : Nat := c.fa\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "parameterized grandparent field (C.fa via B via A)",
    );
    assert!(
        env.get_const(&Name::from_string("getFa")).is_some(),
        "getFa should be registered"
    );
}

/// Universe-polymorphic STRUCTURAL recursion: a `def f.{u} (α : Type u) …`
/// recursing on `Nat` via `match`. The self-reference lowers through `Nat.rec`
/// (the recursive call becomes the recursor's IH, never a bare `Const f`), so
/// the whole def — universe params and all — elaborates and kernel-checks. Pins
/// that a universe-poly recursor-lowered def carries its `.{u}` correctly.
#[test]
fn test_universe_poly_structural_recursion() {
    let code = "def rankPoly.{u} (α : Type u) (n : Nat) : Nat := match n with\n  | 0 => 0\n  | Nat.succ m => Nat.succ (rankPoly α m)\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "universe-poly structural recursion");
    assert!(
        env.get_const(&Name::from_string("rankPoly")).is_some(),
        "rankPoly should be registered"
    );
}

/// Built-in `Nat → Int` coercion: `def f (n : Nat) : Int := n` must elaborate.
/// Lean coerces via `NatCast`/`Int.ofNat`; Clean's prelude has no `NatCast`
/// class (nor `Coe Nat Int` instance), so the elaborator applies the built-in
/// `Int.ofNat` widening — the SAME value. Verifies the coerced def kernel-checks
/// and that `f 3` reduces to an `Int.ofNat` application.
#[test]
fn test_nat_to_int_builtin_coercion() {
    use clean_kernel::{ExprKind, TypeChecker};
    let code = "def f (n : Nat) : Int := n\ndef r : Int := f 3\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat->Int built-in coercion");
    let tc = TypeChecker::new(&env);
    let r = env.get_const(&Name::from_string("r")).expect("r missing");
    let w = tc.whnf(r.value.as_ref().expect("r value"));
    match w.kind() {
        ExprKind::App(head, _arg) => assert!(
            matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Int.ofNat"),
            "r = f 3 should reduce to an `Int.ofNat _` application, got head {:?}",
            head.kind()
        ),
        other => panic!("r should reduce to an `Int.ofNat` application, got {other:?}"),
    }
}

/// Built-in `Fin n → Nat` coercion via `@Fin.val n`: `def f (n : Nat) (i : Fin n)
/// : Nat := i` must elaborate + kernel-check (the projection `i.val` Lean's
/// `Fin`→`Nat` coercion yields), with `n` recovered from the `Fin n` type. Very
/// common (array/list indexing). Was `TypeMismatch (Nat vs Fin n)`.
#[test]
fn test_fin_to_nat_builtin_coercion() {
    let (env, results) = elab_file_prelude("def f (n : Nat) (i : Fin n) : Nat := i\n");
    assert_all_ok(&results, "Fin->Nat built-in coercion");
    let f = env
        .get_const(&Name::from_string("f"))
        .expect("f should be registered");
    // Body is `fun (n:Nat) (i:Fin n) => @Fin.val n i`; the `Fin.val` projection
    // renders as a hierarchical name `Str(Str(_,"Fin"),"val")`.
    assert!(
        format!("{:?}", f.value).contains("\"val\""),
        "the coerced body should apply the `Fin.val` projection"
    );
}

/// The built-in `Nat → Int` coercion also fires on a binary-op operand:
/// `def f (n : Nat) : Int := n + 1` elaborates (`n` widens to `Int`, `1 : Int`).
#[test]
fn test_nat_to_int_coercion_in_arithmetic() {
    let (env, results) = elab_file_prelude("def f (n : Nat) : Int := n + 1\n");
    assert_all_ok(&results, "Nat->Int coercion in arithmetic");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered"
    );
}

/// Legacy Lean 4 `structure := (field : T)` syntax (from the lean4_compat
/// corpus, e.g. 389.lean): `structure Foo (A) := (foo : A)` — the `:=` form of a
/// field block — must give `Foo` a real `foo` field. Previously the parser read
/// `structure Foo (A)` as FIELDLESS and choked on `:= (foo : A)`, cascading to
/// every downstream field access. Covers multi-field, multi-name groups, and
/// `extends`. (The full 389.lean also needs the `Coe` prelude class, which is a
/// separate kernel-prelude gap.)
#[test]
fn test_structure_colon_eq_field_syntax() {
    let code = "structure Foo (A : Type) := (foo : A) (foo2 : A)\nstructure Bar (A : Type) extends Foo A := (bar : A)\ndef getFoo (F : Foo Nat) : Nat := F.foo\ndef b : Bar Nat := { foo := 0, foo2 := 9, bar := 1 }\ndef getBar (x : Bar Nat) : Nat := x.bar\ndef getInherited (x : Bar Nat) : Nat := x.foo\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "structure := (fields) syntax");
    for n in ["Foo", "Bar", "getFoo", "b", "getBar", "getInherited"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "{n} should be registered"
        );
    }
}

/// Legacy Lean 4 `class := (field : T)` syntax (lean4_compat corpus, 1102.lean)
/// — the CLASS analogue of the structure `:=` field block. `class C := (u : U)`
/// must give `C` a real `u` field; the class parser previously read it as
/// fieldless and choked on `:= (u : U)`. Covers `extends` chains.
#[test]
fn test_class_colon_eq_field_syntax() {
    let code = "class C1 := (u1 : Unit)\nclass C2 extends C1 := (u2 : Unit)\ndef getU1 (c : C1) : Unit := c.u1\ndef getU2 (c : C2) : Unit := c.u2\ndef getInherited (c : C2) : Unit := c.u1\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "class := (fields) syntax");
    for n in ["C1", "C2", "getU1", "getU2", "getInherited"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "{n} should be registered"
        );
    }
}

/// `inferInstance` term (lean4_compat corpus, 2115.lean): `def foo : C := inferInstance`
/// must synthesize an instance of the expected type `C`. Previously an
/// `UnknownIdent("inferInstance")`. Verifies it resolves the registered instance
/// and reduces to it.
#[test]
fn test_infer_instance_term() {
    use clean_kernel::{ExprKind, TypeChecker};
    let code = "class Widget (α : Type) where\n  val : α\ninstance : Widget Nat where\n  val := 7\ndef w : Widget Nat := inferInstance\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "inferInstance term");
    let w = env
        .get_const(&Name::from_string("w"))
        .expect("w should be registered");
    // `w` should reduce to the synthesized `Widget Nat` instance (a constructor
    // application), not remain a stuck `inferInstance` reference.
    let tc = TypeChecker::new(&env);
    let reduced = tc.whnf(w.value.as_ref().expect("w value"));
    assert!(
        !matches!(reduced.kind(), ExprKind::Const(n, _) if n.to_string() == "inferInstance"),
        "w should resolve to a concrete instance, got {:?}",
        reduced.kind()
    );
}

/// A bare negative numeric literal `-5` (no type annotation) must default to
/// `Int`, not `Nat` (`Nat` has no `Neg`) — Lean's behavior. Previously failed
/// `FailedToSynthesizeInstance { goal: "Neg Nat" }`. (The binop form `-5 + 5`
/// still needs deeper binop-default work — a separate gap.)
#[test]
fn test_bare_negative_literal_defaults_to_int() {
    use clean_kernel::ExprKind;
    let code = "def x := -5\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "bare negative literal");
    let x = env
        .get_const(&Name::from_string("x"))
        .expect("x should be registered");
    assert!(
        matches!(x.type_.kind(), ExprKind::Const(n, _) if n.to_string() == "Int"),
        "bare `-5` should default to Int, got {:?}",
        x.type_.kind()
    );
}

/// `trace_state` is a diagnostic no-op (prints the goal, leaves the proof
/// unchanged). Common in Lean debug/test code (lean4_compat 1235/1681/…); was a
/// hard `UnknownTactic`. `by trace_state; trivial` must still close the goal.
#[test]
fn test_trace_state_is_noop() {
    let (env, results) = elab_file_prelude("theorem t : True := by trace_state; trivial\n");
    assert_all_ok(&results, "trace_state no-op");
    assert!(
        env.get_const(&Name::from_string("t")).is_some(),
        "t should be registered"
    );
}

/// Function composition `f ∘ g` (`Function.comp`, ubiquitous in Lean) — absent
/// from Clean's prelude, so previously `UnknownIdent("Function.comp")`. Desugars
/// to the definitionally-equal `fun x => f (g x)`. Verified with and without a
/// type annotation, and that `(succ ∘ succ) 0` reduces to `2`.
#[test]
fn test_function_comp_operator() {
    use clean_kernel::{BigNat, ExprKind, Literal, TypeChecker};
    let code = "def c : Nat → Nat := Nat.succ ∘ Nat.succ\ndef c2 := Nat.succ ∘ Nat.succ\ndef r : Nat := c 0\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Function.comp ∘");
    for n in ["c", "c2", "r"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "{n} should be registered"
        );
    }
    let tc = TypeChecker::new(&env);
    let r = env.get_const(&Name::from_string("r")).unwrap();
    match tc.whnf(r.value.as_ref().expect("r value")).kind() {
        ExprKind::Lit(Literal::Nat(n)) => assert_eq!(*n, BigNat::Small(2), "(succ∘succ) 0 = 2"),
        other => panic!("r should reduce to 2, got {other:?}"),
    }
}

/// Missing prelude combinators `flip` and `Function.const` — simple defeq
/// lambdas — desugared in-lane (like `∘`). `flip g` ⇒ `fun a b => g b a`;
/// `Function.const β a` ⇒ `fun _ : β => a` (partial `Function.const β` ⇒
/// `fun a (_ : β) => a`). Also confirms literal `Function.comp f g` works (the
/// projection-form of the qualified name, not just the `∘` operator).
#[test]
fn test_flip_and_const_combinators() {
    use clean_kernel::{BigNat, ExprKind, Literal, TypeChecker};
    let code = "def sub2 : Nat → Nat → Nat := fun a b => a - b\ndef fsub : Nat → Nat → Nat := flip sub2\ndef k : Nat → Nat := Function.const Nat 7\ndef comp2 : Nat → Nat := Function.comp Nat.succ Nat.succ\ndef r1 : Nat := fsub 1 5\ndef r2 : Nat := k 99\ndef r3 : Nat := comp2 0\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "flip / Function.const / literal Function.comp");
    let tc = TypeChecker::new(&env);
    let reduces = |name: &str, expected: u64| {
        let c = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} missing"));
        match tc.whnf(c.value.as_ref().expect("value")).kind() {
            ExprKind::Lit(Literal::Nat(n)) => assert_eq!(*n, BigNat::Small(expected), "{name}"),
            other => panic!("{name} did not reduce to a Nat literal: {other:?}"),
        }
    };
    reduces("r1", 4); // flip sub2 1 5 = sub2 5 1 = 4
    reduces("r2", 7); // const Nat 7 99 = 7
    reduces("r3", 2); // (succ ∘ succ) 0 = 2
}

/// Missing prelude combinators `Function.uncurry` / `Function.curry` (used as
/// values), desugared in-lane to their defeq lambdas: `Function.uncurry g` ⇒
/// `fun p => g p.fst p.snd`, `Function.curry g` ⇒ `fun a b => g ⟨a, b⟩`.
#[test]
fn test_uncurry_curry_combinators() {
    use clean_kernel::{BigNat, ExprKind, Literal, TypeChecker};
    let code = "def add : Nat → Nat → Nat := fun a b => a + b\ndef uadd : Nat × Nat → Nat := Function.uncurry add\ndef padd : Nat × Nat → Nat := fun p => p.fst + p.snd\ndef cadd : Nat → Nat → Nat := Function.curry padd\ndef r1 : Nat := uadd (3, 4)\ndef r2 : Nat := cadd 5 6\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Function.uncurry / Function.curry");
    let tc = TypeChecker::new(&env);
    let reduces = |name: &str, expected: u64| {
        let c = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} missing"));
        match tc.whnf(c.value.as_ref().expect("value")).kind() {
            ExprKind::Lit(Literal::Nat(n)) => assert_eq!(*n, BigNat::Small(expected), "{name}"),
            other => panic!("{name} did not reduce to a Nat literal: {other:?}"),
        }
    };
    reduces("r1", 7); // uncurry add (3,4) = add 3 4 = 7
    reduces("r2", 11); // curry padd 5 6 = padd (5,6) = 11
}

/// `partial def` (non-structural recursion, ubiquitous in real Lean). Lean
/// treats it as an opaque/unsafe constant: the body is not termination-checked
/// and the constant does not reduce. Clean registers `name : T` opaquely so the
/// body's self-reference resolves. SOUNDNESS: requires `Inhabited T` — a
/// `partial def` of an uninhabited type must FAIL (else `f : False` is minted).
#[test]
fn test_partial_def_opaque_and_soundness() {
    // Positive: a self-recursive partial def registers.
    let code = "partial def loop (n : Nat) : Nat := if n = 0 then 0 else loop (n - 1)\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "partial def loop");
    assert!(
        env.get_const(&Name::from_string("loop")).is_some(),
        "loop should be registered"
    );

    // SOUNDNESS NEGATIVE: `partial def bad : False := bad` must be REJECTED —
    // registering an opaque `bad : False` would be an unsound false witness.
    let (env2, bad) = elab_file_prelude("partial def bad : False := bad\n");
    assert!(
        bad.iter().any(|r| r.is_err()),
        "partial def of an uninhabited type (False) must fail, got {bad:?}"
    );
    assert!(
        env2.get_const(&Name::from_string("bad")).is_none(),
        "`bad : False` must NOT be registered"
    );
}

/// A `mutual` block of `partial def`s (mutual non-structural recursion — common
/// in interpreters/parsers). Lean compiles them to opaque/unsafe constants;
/// Clean registers each member's signature opaquely so the cross-references
/// resolve. SOUNDNESS: each member is `Inhabited`-guarded (via the same
/// `partial def` path), so a mutual block returning an uninhabited type is
/// rejected — no false witness.
#[test]
fn test_mutual_partial_def_opaque() {
    let code = "mutual\npartial def evenP (n : Nat) : Bool := if n = 0 then true else oddP (n - 1)\npartial def oddP (n : Nat) : Bool := if n = 0 then false else evenP (n - 1)\nend\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "mutual partial evenP/oddP");
    for n in ["evenP", "oddP"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "{n} should be registered"
        );
    }
    // SOUNDNESS: a mutual partial block returning `False` must be rejected.
    let (env2, bad) =
        elab_file_prelude("mutual\npartial def a : False := b\npartial def b : False := a\nend\n");
    assert!(
        bad.iter().any(|r| r.is_err()),
        "mutual partial def of False must fail, got {bad:?}"
    );
    assert!(
        env2.get_const(&Name::from_string("a")).is_none(),
        "`a : False` must NOT be registered"
    );
}

/// `nomatch e` — Lean's empty-match sugar for an *uninhabited* scrutinee. A
/// `False`/`Empty` hypothesis has zero constructors, so the match has no arms
/// and is discharged by the type's **zero-minor recursor**
/// (`@T.rec (fun _ => C) e`) into the expected result type. SOUNDNESS: the
/// emitted recursor application is kernel-re-checked; and `nomatch` on an
/// INHABITED type — which would conjure a value of any type from a real
/// inhabitant — is rejected LOUD (never silently accepted).
#[test]
fn test_nomatch_uninhabited() {
    // Positive: `False` scrutinee, eliminated into an arbitrary data type.
    let (env, results) = elab_file_prelude("def fromFalse (h : False) : Nat := nomatch h\n");
    assert_all_ok(&results, "nomatch on False");
    assert!(
        env.get_const(&Name::from_string("fromFalse")).is_some(),
        "fromFalse should be registered"
    );

    // Positive: `Empty` scrutinee, eliminated into a Prop (exercises the u=0
    // motive-universe path, distinct from the Type case above).
    let (env2, r2) = elab_file_prelude("theorem fromEmpty (h : Empty) : 0 = 1 := nomatch h\n");
    assert_all_ok(&r2, "nomatch on Empty");
    assert!(
        env2.get_const(&Name::from_string("fromEmpty")).is_some(),
        "fromEmpty should be registered"
    );

    // SOUNDNESS NEGATIVE: `nomatch` on an INHABITED type (`Nat` has
    // constructors) must be rejected — otherwise it would fabricate a `False`
    // witness from a genuine `Nat`.
    let (env3, bad) = elab_file_prelude("def conjure (n : Nat) : False := nomatch n\n");
    assert!(
        bad.iter().any(|r| r.is_err()),
        "nomatch on an inhabited type (Nat) must fail, got {bad:?}"
    );
    assert!(
        env3.get_const(&Name::from_string("conjure")).is_none(),
        "`conjure : False` must NOT be registered"
    );
}

/// `nomatch (h : a = b)` where `a`, `b` are DISTINCT constructors — the
/// equation-empty case. The equality is absurd, so it is refuted by the type's
/// `noConfusion` (`@Color.noConfusion Nat Color.red Color.green h : Nat`),
/// whose `noConfusionType` ι-reduces to the result type exactly because the
/// constructor heads differ. SOUNDNESS: the emitted `noConfusion` application is
/// kernel-re-checked; `nomatch` on a NON-refutable equation (same constructor,
/// or a genuine `n = n`) reduces to a function type `≢ C` and is rejected LOUD —
/// it can never fabricate a witness from a real reflexive equality.
#[test]
fn test_nomatch_equation_noconfusion() {
    // Positive: distinct nullary constructors of a user enum.
    let code = "inductive Color where\n  | red\n  | green\ndef fromColorEq (h : Color.red = Color.green) : Nat := nomatch h\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nomatch on Color.red = Color.green");
    assert!(
        env.get_const(&Name::from_string("fromColorEq")).is_some(),
        "fromColorEq should be registered"
    );

    // Positive: primitive `Nat` literals (`(0 : Nat) = 1`) — the literals reduce
    // to `Nat.zero` / `Nat.succ Nat.zero`, distinct ctor heads, so `Nat.noConfusion`
    // refutes the equation just as for the enum.
    let nat_code = "def fromNatEq (h : (0 : Nat) = 1) : Nat := nomatch h\n";
    let (env_n, r_n) = elab_file_prelude(nat_code);
    assert_all_ok(&r_n, "nomatch on (0 : Nat) = 1");
    assert!(
        env_n.get_const(&Name::from_string("fromNatEq")).is_some(),
        "fromNatEq should be registered"
    );

    // SOUNDNESS NEGATIVE: same constructor on both sides (`Color.red = Color.red`)
    // is a REFLEXIVE, satisfiable equation — `noConfusion` does not refute it, so
    // `nomatch` must be rejected (never conjure a `Nat` from a real `rfl`).
    let bad_code = "inductive Color where\n  | red\n  | green\ndef bad (h : Color.red = Color.red) : Nat := nomatch h\n";
    let (env2, bad) = elab_file_prelude(bad_code);
    assert!(
        bad.iter().any(|r| r.is_err()),
        "nomatch on a reflexive equation (Color.red = Color.red) must fail, got {bad:?}"
    );
    assert!(
        env2.get_const(&Name::from_string("bad")).is_none(),
        "`bad` (nomatch on a satisfiable equation) must NOT be registered"
    );
}

/// `nomatch (h : a = b)` where `a`, `b` are distinct constructors of a
/// PARAMETRIC type (`Pair2 α`). The generated `noConfusion` is the v4.30
/// heterogeneous form: the type parameter is threaded on both sides, each
/// parameter gets an `Eq.refl`, and the homogeneous equality is lifted to `HEq`
/// via `heq_of_eq`. SOUNDNESS: distinctness is still enforced by TYPING (the
/// `is_def_eq` gate + kernel re-check); a reflexive equation of the parametric
/// type is rejected LOUD, exactly as in the monomorphic case.
#[test]
fn test_nomatch_equation_noconfusion_parametric() {
    // Positive: distinct nullary constructors of a *parametric* user type.
    let code = "inductive Pair2 (α : Type) where\n  | a\n  | b\ndef fromPairEq {α : Type} (h : (Pair2.a : Pair2 α) = Pair2.b) : Nat := nomatch h\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nomatch on (Pair2.a : Pair2 α) = Pair2.b");
    assert!(
        env.get_const(&Name::from_string("fromPairEq")).is_some(),
        "fromPairEq should be registered"
    );

    // SOUNDNESS NEGATIVE: a reflexive equation of the same parametric type must
    // NOT be refutable.
    let bad_code = "inductive Pair2 (α : Type) where\n  | a\n  | b\ndef badPair {α : Type} (h : (Pair2.a : Pair2 α) = Pair2.a) : Nat := nomatch h\n";
    let (env2, bad) = elab_file_prelude(bad_code);
    assert!(
        bad.iter().any(|r| r.is_err()),
        "nomatch on a reflexive parametric equation must fail, got {bad:?}"
    );
    assert!(
        env2.get_const(&Name::from_string("badPair")).is_none(),
        "`badPair` must NOT be registered"
    );
}

/// A `where` helper defined by pattern-matching EQUATIONS (`| pat => body`),
/// not `:= expr` — e.g. `def f … := go n where go : Nat → Nat | 0 => 0 | _ => 1`.
/// The parser previously required `:=` for where helpers and dropped the
/// equation-form helper, leaving it an unknown identifier. Now the helper
/// desugars through the same `def_match_body` a top-level equation `def` uses,
/// so it elaborates and reduces end-to-end. SOUNDNESS: nothing special — the
/// desugared `fun _x => match _x with …` is ordinary elaborator/kernel material.
/// (A *self-recursive* equation-form where helper additionally needs the
/// where-let-rec elaborator to see the parameter inside the desugared lambda;
/// that remains a separate, loudly-rejected case.)
#[test]
fn test_where_equation_helper_reduces() {
    // Non-recursive equation-form where helper — parses, elaborates, reduces.
    let code = "def classify (n : Nat) : Nat := go n\n  where go : Nat -> Nat\n    | 0 => 0\n    | _ => 1\ntheorem c0 : classify 0 = 0 := rfl\ntheorem c5 : classify 5 = 1 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "where-equation helper `classify`");
    assert!(
        env.get_const(&Name::from_string("classify")).is_some(),
        "classify should be registered"
    );
}

/// A SELF-RECURSIVE `where` helper written with pattern-matching EQUATIONS —
/// `def … := go n where go : Nat → Nat | 0 => 0 | k+1 => (go k) + 2`. Brick 22
/// made this PARSE; the where-let-rec elaborator then rejected it
/// (`WhereLetRecUnsupported "self-recursive with no parameters"`) because the
/// `_x` parameter is hidden inside the desugared `fun _x => match _x …` lambda.
/// Now `try_elab_let_rec_lifted` reuses the top-level equation-def normalization
/// to lift `_x` and routes the helper through the SAME structural-recursion
/// lowering, so it compiles to a real reducing recursor. SOUNDNESS: verified by
/// reduction — `dblw 2 = 4 := rfl` (genuine `Nat.rec`, not opaque) — and a wrong
/// value is rejected.
#[test]
fn test_where_recursive_equation_helper_reduces() {
    let code = "def dblw (n : Nat) : Nat := go n\n  where go : Nat -> Nat\n    | 0 => 0\n    | k+1 => (go k) + 2\ntheorem dw2 : dblw 2 = 4 := rfl\ntheorem dw0 : dblw 0 = 0 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "recursive where-equation helper `dblw`");
    assert!(
        env.get_const(&Name::from_string("dblw")).is_some(),
        "dblw should be registered"
    );

    // SOUNDNESS NEGATIVE: a wrong reduction must fail — the helper genuinely
    // reduces (it is not an opaque/unchecked stand-in).
    let (_env2, bad) =
        elab_file_prelude("def dblw2 (n : Nat) : Nat := go n\n  where go : Nat -> Nat\n    | 0 => 0\n    | k+1 => (go k) + 2\ntheorem wrong : dblw2 2 = 3 := rfl\n");
    assert!(
        bad.iter().any(|r| r.is_err()),
        "dblw2 2 = 3 must fail (dblw2 2 reduces to 4), got {bad:?}"
    );
}

/// A statement-position Unit-valued `if` in do-notation must SEQUENCE as an
/// `m Unit` action before the continuation, not be typed at the block's result
/// type. Previously the with-else path elaborated both branches at the block
/// result (`Nat`), rejecting `pure ()` (`KernelCheckFailed`: Nat vs Unit) — so
/// `if … then pure () else pure ()` and `unless c do body` (which desugars to
/// exactly that shape) both failed. SOUNDNESS: the emitted `Bind.bind` term is
/// kernel-re-checked and reduces (verified by rfl).
#[test]
fn test_do_unit_if_statement_sequences() {
    // Explicit Unit-valued if-statement, then a Nat return — reduces via Id.
    let code = "def aStmt (x : Bool) : Id Nat := do\n  if x then pure () else pure ()\n  return 5\ntheorem ta : aStmt true = 5 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "do Unit if-statement");
    assert!(
        env.get_const(&Name::from_string("aStmt")).is_some(),
        "aStmt should be registered"
    );

    // `unless c do body` desugars to the same Unit-valued if-statement shape.
    let code2 = "def bStmt (x : Bool) : Id Nat := do\n  unless x do pure ()\n  return 7\ntheorem tb : bStmt false = 7 := rfl\n";
    let (env2, r2) = elab_file_prelude(code2);
    assert_all_ok(&r2, "do `unless` statement");
    assert!(
        env2.get_const(&Name::from_string("bStmt")).is_some(),
        "bStmt should be registered"
    );

    // `when c do body` — the mirror of `unless` (`if c then body else pure ()`).
    // Previously `when` was not recognized as a do-statement (`UnknownIdent`).
    let code3 = "def wStmt (x : Bool) : Id Nat := do\n  when x do pure ()\n  return 9\ntheorem tw : wStmt true = 9 := rfl\n";
    let (env3, r3) = elab_file_prelude(code3);
    assert_all_ok(&r3, "do `when` statement");
    assert!(
        env3.get_const(&Name::from_string("wStmt")).is_some(),
        "wStmt should be registered"
    );
}

/// do `try … finally …` must ELABORATE. The elaborator built the `tryFinally`
/// application with nonexistent instance arguments (`MonadFinally m`,
/// `Functor m` — that class is not registered), over-applying the instance-free
/// registered `tryFinally` axiom and failing with a cryptic `NotAFunction`. Now
/// the application mirrors the registered arity exactly (`@tryFinally.{u,v} m α
/// β body fin`) with concrete `(u,v,m,α)` read off the block's expected type
/// (like `mk_bind_app`), and the finalizer elaborated at `m ?β`. SOUNDNESS:
/// `tryFinally` is a pre-existing inhabited axiom; the emitted term is
/// kernel-re-checked — no new axiom, no bypass. (`catch` — untyped needs the
/// exception type inferred from the monad, typed needs the `Sort(u+1)` exception
/// universe — is a separate follow-on.)
#[test]
fn test_do_try_finally_elaborates() {
    let code = "def dtf : Id Nat := do\n  try pure 1 finally pure ()\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "do try/finally");
    assert!(
        env.get_const(&Name::from_string("dtf")).is_some(),
        "dtf should be registered"
    );

    // Typed `catch e : String => …` — `tryCatchThe` (2 levels, instance-free,
    // exception universe = pred of ε's sort).
    let code2 = "def dtct (n : Nat) : Except String Nat := do\n  try\n    pure n\n  catch _ : String => pure 0\n";
    let (env2, r2) = elab_file_prelude(code2);
    assert_all_ok(&r2, "do try/catch (typed)");
    assert!(
        env2.get_const(&Name::from_string("dtct")).is_some(),
        "dtct should be registered"
    );

    // Untyped `catch e => …` — the exception type is inferred from the
    // `Except String` monad (ε = its error-type argument).
    let code3 =
        "def dtcu (n : Nat) : Except String Nat := do\n  try\n    pure n\n  catch _ => pure 0\n";
    let (env3, r3) = elab_file_prelude(code3);
    assert_all_ok(&r3, "do try/catch (untyped, Except monad)");
    assert!(
        env3.get_const(&Name::from_string("dtcu")).is_some(),
        "dtcu should be registered"
    );

    // SOUNDNESS NEGATIVE: an untyped `catch e =>` over a NON-`Except` monad
    // (`Id` has no exception type) must FAIL — never silently accept an
    // unsolved/wrong exception type.
    let bad = "def dtcbad : Id Nat := do\n  try\n    pure 1\n  catch _ => pure 0\n";
    let (envb, rb) = elab_file_prelude(bad);
    assert!(
        rb.iter().any(|r| r.is_err()),
        "untyped catch over `Id` (no exception type) must fail, got {rb:?}"
    );
    assert!(
        envb.get_const(&Name::from_string("dtcbad")).is_none(),
        "`dtcbad` must NOT be registered"
    );
}

/// Eliminator-style elaboration (`elabAsElim`): a recursor applied with its
/// `{motive}` left IMPLICIT — `Nat.rec 0 (fun _ ih => ih + 1) n`. The generic
/// application path inserts a motive metavariable, then checks the first minor
/// against `?motive Nat.zero` (an unsolvable higher-order constraint) and fails.
/// Now `try_elab_recursor_as_elim` synthesizes the non-dependent motive
/// `fun _ : Nat => C` from the expected result type (the tractable param-less,
/// index-less slice). SOUNDNESS: the emitted `@Nat.rec (fun _ => C) …` term is
/// kernel-re-checked and — unlike the try/catch axioms — GENUINELY REDUCES, so a
/// wrong result is caught by rfl.
#[test]
fn test_recursor_implicit_motive_reduces() {
    let code = "def cnt (n : Nat) : Nat := Nat.rec 0 (fun _ ih => ih + 1) n\ntheorem c3 : cnt 3 = 3 := rfl\ntheorem c0 : cnt 0 = 0 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat.rec implicit motive");
    assert!(
        env.get_const(&Name::from_string("cnt")).is_some(),
        "cnt should be registered"
    );

    // SOUNDNESS NEGATIVE: a wrong reduction must fail — the synthesized motive
    // yields a genuinely reducing recursor, not an opaque/unchecked stand-in.
    let (_env2, bad) =
        elab_file_prelude("def cnt2 (n : Nat) : Nat := Nat.rec 0 (fun _ ih => ih + 1) n\ntheorem wrong : cnt2 3 = 4 := rfl\n");
    assert!(
        bad.iter().any(|r| r.is_err()),
        "cnt2 3 = 4 must fail (cnt2 3 reduces to 3), got {bad:?}"
    );

    // PARAMETRIC recursor: `List.rec` (1 type parameter, recovered from the
    // major's type) with an implicit motive — reduces via `List.rec`.
    let (env3, r3) = elab_file_prelude(
        "def len (l : List Nat) : Nat := List.rec 0 (fun _ _ ih => ih + 1) l\ntheorem l3 : len [1, 2, 3] = 3 := rfl\ntheorem l0 : len [] = 0 := rfl\n",
    );
    assert_all_ok(&r3, "List.rec implicit motive (parametric)");
    assert!(
        env3.get_const(&Name::from_string("len")).is_some(),
        "len should be registered"
    );
    // Parametric wrong-value negative.
    let (_env4, bad2) = elab_file_prelude(
        "def len2 (l : List Nat) : Nat := List.rec 0 (fun _ _ ih => ih + 1) l\ntheorem lw : len2 [1, 2] = 5 := rfl\n",
    );
    assert!(
        bad2.iter().any(|r| r.is_err()),
        "len2 [1,2] = 5 must fail (reduces to 2), got {bad2:?}"
    );

    // DEPENDENT motive: `0 + n = n` by induction — the motive is
    // `fun k => 0 + k = k` (the major `n` abstracted out of the expected type),
    // which the constant `fun _ => 0 + n = n` cannot express (`0 + n` is not
    // def-eq `n` for a variable `n`, so the base minor `rfl : 0 + 0 = 0` would
    // be checked at the wrong type). The synthesized motive must be dependent.
    let (env5, r5) = elab_file_prelude(
        "def addComm0 (n : Nat) : 0 + n = n := Nat.rec rfl (fun k ih => congrArg Nat.succ ih) n\n",
    );
    assert_all_ok(&r5, "Nat.rec dependent motive (0 + n = n)");
    assert!(
        env5.get_const(&Name::from_string("addComm0")).is_some(),
        "addComm0 should be registered"
    );

    // `.recOn` (major applied FIRST) with an implicit motive — `Nat.recOn n 0
    // succ` reorders the major before the minors; same synthesis applies.
    let (env6, r6) = elab_file_prelude(
        "def cntOn (n : Nat) : Nat := Nat.recOn n 0 (fun _ ih => ih + 1)\ntheorem co3 : cntOn 3 = 3 := rfl\n",
    );
    assert_all_ok(&r6, "Nat.recOn implicit motive");
    assert!(
        env6.get_const(&Name::from_string("cntOn")).is_some(),
        "cntOn should be registered"
    );
}

/// A typed proof argument must not trigger unsafe expected-result propagation.
///
/// The LRAT checker exposed this with a recursive `List` fold returning `Bool`
/// and an explicit `@List.rec` proof about that fold. In the recursive step,
/// `congrArg ... ih` put the typed identifier `ih` in an open slot, so the
/// element-coercion gate prematurely unified `congrArg`'s higher-order result
/// against the reducible expected equality. The partial assignments later
/// surfaced as a rigid `List.rec`/`Bool.rec` head mismatch. Higher-order result
/// shapes must stay arg-driven; the constructor/container coercion controls
/// below remain expected-type-driven.
#[test]
fn test_typed_value_pin_preserves_congr_arg_over_reducible_list_rec() {
    let code = r#"
set_option autoImplicit false
namespace OpenExpectedRec
structure Lit where
  pos : Bool
  var : Nat
def satLit (a : Nat → Bool) (l : Lit) : Bool := Bool.beq (a l.var) l.pos
def satClause : (Nat → Bool) → List Lit → Bool
  | _, List.nil => false
  | a, List.cons l rest => Bool.or (satLit a l) (satClause a rest)
theorem satClause_id (a : Nat → Bool) (xs : List Lit) :
    satClause a xs = satClause a xs :=
  (@List.rec Lit
    (fun ys : List Lit => @Eq Bool (satClause a ys) (satClause a ys))
    rfl
    (fun l rest ih =>
      congrArg (fun c => Bool.or (satLit a l) c) ih)
    xs)
end OpenExpectedRec
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "typed proof argument in congrArg over a reducible List.rec goal",
    );
    assert!(
        env.get_const(&Name::from_string("OpenExpectedRec.satClause_id"))
            .is_some(),
        "the explicit List.rec proof should register"
    );
}

/// Lean's prefix coercion `↑e` (and `⇑e`). Previously `↑` was an unlexed
/// character → `ParseError`. Now `↑`/`⇑` lex to `Ident("↑")`, so `↑n` parses as
/// `App(Ident("↑"), [n])`, and the elaborator coerces `n` to the expected type
/// via the standard `Coe` machinery. SOUNDNESS: the emitted coercion term is
/// kernel-re-checked.
#[test]
fn test_up_arrow_coercion() {
    // `↑n : Int` coerces `n : Nat` to `Int`.
    let code = "def uc (n : Nat) : Int := ↑n\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "↑n : Int");
    assert!(
        env.get_const(&Name::from_string("uc")).is_some(),
        "uc should be registered"
    );

    // `⇑` (coeFun spelling) lexes to the same coercion.
    let code2 = "def uc2 (n : Nat) : Int := ⇑n\n";
    let (_e2, r2) = elab_file_prelude(code2);
    assert_all_ok(&r2, "⇑n : Int");
}

/// Multiple `where`/`let rec` helpers defined by pattern-matching EQUATIONS.
/// `where f : Nat → Bool | 0 => … | _ => …` followed by another equation helper
/// `g : …` mis-parsed: the where-def-boundary detector (`peek_is_where_def_start`)
/// scanned only for `:=`, but an equation helper's body starts with `|`, so the
/// first helper's last arm body swallowed the next helper (dropped +
/// `ParseError`). Now a depth-0 `|` also marks a where-def start, so every
/// equation-form helper is bounded. (`:=`-form helpers already worked.)
#[test]
fn test_multi_equation_where_helpers() {
    let code = "def classify (n : Nat) : Bool := andBoth n\n  where\n    f : Nat -> Bool\n      | 0 => true\n      | _ => false\n    g : Nat -> Bool\n      | 0 => false\n      | _ => true\n    andBoth : Nat -> Bool\n      | 0 => true\n      | k => f k\ntheorem c0 : classify 0 = true := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "multi equation-form where helpers");
    assert!(
        env.get_const(&Name::from_string("classify")).is_some(),
        "classify should be registered"
    );
}

/// A multi-field instance/structure `where` body whose fields take method
/// BINDERS (`f x := …`). The value-boundary parser stopped only at `ident :=`,
/// so a field with binders (`g x := …`) was not recognized as the next field —
/// the previous field's value swallowed `g x` (`UnknownStructureField "x"`), and
/// the field was dropped. Now the boundary also recognizes `ident binders… :=`
/// (field name newline-leading, binders same-line), so every field parses.
#[test]
fn test_multi_field_instance_with_binders() {
    // Two fields, each with a binder.
    let code = "class C where\n  f : Nat -> Nat\n  g : Nat -> Nat\ninstance : C where\n  f x := x + 1\n  g x := x + 2\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "multi-field instance with binders");

    // `_`-binder fields.
    let code2 = "class D where\n  f : Nat -> Nat\n  g : Nat -> Nat\ninstance : D where\n  f _ := 0\n  g _ := 1\n";
    let (_e2, r2) = elab_file_prelude(code2);
    assert_all_ok(&r2, "multi-field instance with `_` binders");

    // Class-extends-class: the instance provides the inherited (`foo`, from A)
    // and own (`bar`) fields, each with a binder.
    let code3 = "class A (a : Type) where foo : a -> Nat\nclass B (a : Type) extends A a where bar : a -> Nat\ninstance : B Bool where\n  foo _ := 1\n  bar _ := 2\ndef useB : Nat := B.bar true\n";
    let (env3, r3) = elab_file_prelude(code3);
    assert_all_ok(&r3, "class-extends-class instance");
    assert!(
        env3.get_const(&Name::from_string("useB")).is_some(),
        "useB should be registered"
    );
}

/// DEPENDENT inherited field: a parent field whose TYPE depends on an earlier
/// parent field (`w : Wrap n`, `n : Nat`) must still be projectable on a child
/// value (`c.w : Wrap c.n`). The derived child projection's result type is
/// self-dependent (`Wrap (Parent.n (Child.toParent self))`), which the inherited
/// projection builder previously DROPPED (`projection_result_type` bailed on
/// loose bvars), leaving `c.w` a LOUD unknown field.
#[test]
fn test_structure_dependent_inherited_field() {
    let code = "inductive Wrap (n : Nat) : Type where\n  | mk : Wrap n\nstructure Parent where\n  n : Nat\n  w : Wrap n\nstructure Child extends Parent where\n  extra : Nat\ndef getW (c : Child) : Wrap c.n := c.w\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "dependent inherited field (Child.w : Wrap Child.n)",
    );
    assert!(
        env.get_const(&Name::from_string("getW")).is_some(),
        "getW should be registered"
    );
}

/// DEPENDENT inherited field through a PARAMETERIZED parent (`Parent a` with a
/// field `w : Wrap n` depending on `n`). The parameterized flattening path
/// instantiates the parent's type params, so after stripping `self` the only
/// loose bvar is again `self` (bvar 0) — the shared inherited-projection builder
/// retargets it onto `Child.toParent`, exactly like the monomorphic case.
#[test]
fn test_structure_parameterized_dependent_inherited_field() {
    let code = "inductive Wrap (n : Nat) : Type where\n  | mk : Wrap n\nstructure Parent (a : Type) where\n  n : Nat\n  w : Wrap n\n  base : a\nstructure Child (a : Type) extends Parent a where\n  extra : Nat\ndef getW (c : Child Nat) : Wrap c.n := c.w\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "parameterized dependent inherited field (Child.w : Wrap Child.n)",
    );
    assert!(
        env.get_const(&Name::from_string("getW")).is_some(),
        "getW should be registered"
    );
}

/// Grandparent field through a parameterized CLASS `extends` chain (`C2 a extends
/// B2 a extends A2 a`) — Mathlib's actual algebraic-hierarchy shape
/// (`Monoid extends Semigroup extends Mul`, all classes). Classes re-expose
/// parent fields via a SEPARATE path (`build_class_parent_projections`) that
/// previously took only the parent's DIRECT fields, so a grandparent field was a
/// LOUD unknown.
#[test]
fn test_class_parameterized_grandparent_field() {
    let code = "class A2 (t : Type) where\n  fa2 : t -> t\nclass B2 (t : Type) extends A2 t where\n  fb2 : t\nclass C2 (t : Type) extends B2 t where\n  fc2 : t\ndef getFa2 (inst : C2 Nat) (n : Nat) : Nat := inst.fa2 n\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "parameterized grandparent field via CLASS extends",
    );
    assert!(
        env.get_const(&Name::from_string("getFa2")).is_some(),
        "getFa2 should be registered"
    );
}

/// Non-Nat literal patterns in `match` — `Int` (also UInt/etc.) scrutinees.
/// Lowered to the `BEq.beq`/`ite` cascade like String/Char (Nat keeps its
/// `Nat.rec` path). Previously a hard `NotImplemented` ("literal patterns are
/// only supported for Nat scrutinees, got Int"). Verifies REDUCTION.
#[test]
fn test_match_int_literal_patterns() {
    use clean_kernel::{BigNat, ExprKind, Literal, TypeChecker};
    let code = "def classify (i : Int) : Nat := match i with\n  | 0 => 10\n  | 1 => 20\n  | _ => 30\ndef r0 : Nat := classify 0\ndef r1 : Nat := classify 1\ndef r5 : Nat := classify 5\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int literal-pattern match");
    let tc = TypeChecker::new(&env);
    let reduces_to = |name: &str, expected: u64| {
        let c = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} missing"));
        let w = tc.whnf(c.value.as_ref().expect("value"));
        match w.kind() {
            ExprKind::Lit(Literal::Nat(n)) => {
                assert_eq!(*n, BigNat::Small(expected), "{name} value")
            }
            other => panic!("{name} did not reduce to a Nat literal: {other:?}"),
        }
    };
    reduces_to("r0", 10);
    reduces_to("r1", 20);
    reduces_to("r5", 30);
}

/// Parametric MULTI-ctor `deriving DecidableEq` (`MyOpt a` = nullary `none2` +
/// unary `some2 : a → MyOpt a`) — nested `casesOn` on both scrutinees. Diagonal
/// (same ctor) decides fields via projection injectivity / `Eq.trans`
/// congruence; off-diagonal (distinct ctors) is `isFalse` via a `casesOn`
/// discriminator (`disc_i : Ind → Prop`, then `Eq.mp ∘ congrArg`), NOT
/// `noConfusion` (which is heterogeneous for parametric families). Retires the
/// `sorry` fallback. Verifies REDUCTION: equal ⇒ isTrue, differ ⇒ isFalse.
#[test]
fn test_parametric_decidable_eq_multi_ctor_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Literal, TypeChecker};
    let code = "inductive MyOpt (a : Type) where\n  | none2\n  | some2 : a -> MyOpt a\n  deriving DecidableEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "parametric multi-ctor DecidableEq deriving (MyOpt a)",
    );
    assert!(
        env.get_const(&Name::from_string("instMyOptDecidableEq"))
            .is_some(),
        "instMyOptDecidableEq should be registered"
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let none2 = Expr::apps(
        Expr::const_(Name::from_string("MyOpt.none2"), vec![]),
        [nat.clone()],
    );
    let some2 = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MyOpt.some2"), vec![]),
            [nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
    let dec = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("instMyOptDecidableEq"), vec![]),
            [nat.clone(), ni.clone(), a, b],
        );
        let w = tc.whnf(&app);
        let mut f = &w;
        while let ExprKind::App(g, _) = f.kind() {
            f = g;
        }
        match f.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        dec(none2.clone(), none2.clone()),
        "Decidable.isTrue",
        "none2 = none2 ⇒ isTrue"
    );
    assert_eq!(
        dec(some2(1), some2(1)),
        "Decidable.isTrue",
        "some2 1 = some2 1 ⇒ isTrue"
    );
    assert_eq!(
        dec(some2(1), some2(2)),
        "Decidable.isFalse",
        "some2 1 = some2 2 ⇒ isFalse"
    );
    assert_eq!(
        dec(none2.clone(), some2(1)),
        "Decidable.isFalse",
        "none2 = some2 1 ⇒ isFalse (distinct ctors)"
    );
    assert_eq!(
        dec(some2(1), none2.clone()),
        "Decidable.isFalse",
        "some2 1 = none2 ⇒ isFalse (distinct ctors)"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instMyOptDecidableEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instMyOptDecidableEq must have EMPTY axiom closure, got {deps:?}"
    );
}

/// Parametric MULTI-ctor MULTI-param `deriving DecidableEq` (`MySum a b`) — two
/// field-carrying ctors over distinct parameters. Exercises both off-diagonal
/// directions (`inl`/`inr` and `inr`/`inl`) via the `disc` discriminator and
/// per-parameter `[DecidableEq a] [DecidableEq b]`. Distinct ctors ⇒ isFalse
/// even when the payloads coincide.
#[test]
fn test_parametric_decidable_eq_sum_reduces() {
    use clean_kernel::{BigNat, Expr, ExprKind, Literal, TypeChecker};
    let code = "inductive MySum (a : Type) (b : Type) where\n  | inl : a -> MySum a b\n  | inr : b -> MySum a b\n  deriving DecidableEq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "parametric multi-ctor DecidableEq deriving (MySum a b)",
    );
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lit = |n: u64| Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))));
    let inl = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MySum.inl"), vec![]),
            [nat.clone(), nat.clone(), lit(n)],
        )
    };
    let inr = |n: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("MySum.inr"), vec![]),
            [nat.clone(), nat.clone(), lit(n)],
        )
    };
    let tc = TypeChecker::new(&env);
    let ni = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
    let dec = |a: Expr, b: Expr| -> String {
        let app = Expr::apps(
            Expr::const_(Name::from_string("instMySumDecidableEq"), vec![]),
            [nat.clone(), nat.clone(), ni.clone(), ni.clone(), a, b],
        );
        let w = tc.whnf(&app);
        let mut f = &w;
        while let ExprKind::App(g, _) = f.kind() {
            f = g;
        }
        match f.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        dec(inl(1), inl(1)),
        "Decidable.isTrue",
        "inl 1 = inl 1 ⇒ isTrue"
    );
    assert_eq!(
        dec(inl(1), inl(2)),
        "Decidable.isFalse",
        "inl 1 = inl 2 ⇒ isFalse"
    );
    assert_eq!(
        dec(inr(5), inr(5)),
        "Decidable.isTrue",
        "inr 5 = inr 5 ⇒ isTrue"
    );
    assert_eq!(
        dec(inl(1), inr(1)),
        "Decidable.isFalse",
        "inl 1 = inr 1 ⇒ isFalse (distinct ctors)"
    );
    assert_eq!(
        dec(inr(1), inl(1)),
        "Decidable.isFalse",
        "inr 1 = inl 1 ⇒ isFalse (distinct ctors)"
    );
    let deps = env
        .axiom_deps(&Name::from_string("instMySumDecidableEq"))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "instMySumDecidableEq must have EMPTY axiom closure, got {deps:?}"
    );
}

// ---------------------------------------------------------------------------
// Persistent `open`/`export` commands carry namespace state across
// declarations within a file (Lean `open NS` / `export NS (x)` are commands
// whose effect persists to the enclosing scope, not just one declaration).
// ---------------------------------------------------------------------------

#[test]
fn test_open_command_persists_across_decls() {
    let code = "namespace NS\n\
                def helper : Nat := 5\n\
                end NS\n\
                open NS\n\
                def useNs : Nat := helper\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "open command persists");
    assert!(
        env.get_const(&Name::from_string("useNs")).is_some(),
        "useNs should resolve `helper` as `NS.helper` after `open NS`"
    );
}

#[test]
fn test_export_command_persists_across_decls() {
    // `export M (val)` at root adds alias `val` (currNs = root, so `root ++ val
    // = val`) pointing at `M.val`, making the bare short name resolve. (An
    // export *inside* `namespace M` would add the useless self-alias `M.val`.)
    let code = "namespace M\n\
                def val : Nat := 1\n\
                end M\n\
                export M (val)\n\
                def useE : Nat := val\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "export command persists");
    assert!(
        env.get_const(&Name::from_string("useE")).is_some(),
        "useE should resolve exported `val` after `export M (val)`"
    );
}

// ---------------------------------------------------------------------------
// Implicit-lambda insertion (Lean `elabFunBinders`): when the expected type's
// leading binder is implicit/instance-implicit but the surface lambda binder is
// explicit, the implicit is bound automatically without consuming the surface
// binder — `fun x => x : {α} → α → α` elaborates as `fun {α} x => x`.
// ---------------------------------------------------------------------------

#[test]
fn test_implicit_lambda_single() {
    let code = "def fil : {α : Type} -> α -> α := fun x => x\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "implicit-lambda single");
    assert!(env.get_const(&Name::from_string("fil")).is_some());
}

#[test]
fn test_implicit_lambda_two_implicits_one_explicit() {
    let code = "def f2 : {α β : Type} -> (α -> β) -> α -> β := fun f x => f x\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "implicit-lambda two implicits");
    assert!(env.get_const(&Name::from_string("f2")).is_some());
}

#[test]
fn test_implicit_lambda_explicit_then_implicit() {
    // Implicit appears AFTER an explicit binder: `n` binds Nat normally, then
    // `x` (explicit) triggers implicit insertion for `α`.
    let code = "def f7 : Nat -> {α : Type} -> α -> α := fun n x => x\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "implicit-lambda explicit-then-implicit");
    assert!(env.get_const(&Name::from_string("f7")).is_some());
}

#[test]
fn test_implicit_lambda_opt_outs_still_work() {
    // Naming the implicit (`fun {α} x`) or `@fun α x` opts out; these must keep
    // elaborating exactly as before (surface binder is implicit / all-explicit).
    for code in [
        "def g1 : {α : Type} -> α -> α := fun {α} x => x\n",
        "def g2 : {α : Type} -> α -> α := @fun α x => x\n",
        "def g3 : Nat -> Nat := fun x => x\n",
    ] {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, "implicit-lambda opt-out");
    }
}

#[test]
fn test_implicit_lambda_reduces_and_rejects() {
    // POSITIVE: the inserted-implicit identity actually computes — applying it
    // to a concrete Nat reduces to that Nat, proven by `rfl` (kernel-checked).
    let code = "def fil : {α : Type} -> α -> α := fun x => x\n\
                theorem fil_ok : fil (5 : Nat) = 5 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "implicit-lambda reduces (rfl)");
    assert!(env.get_const(&Name::from_string("fil_ok")).is_some());

    // NEGATIVE (loud): implicit insertion must NOT paper over a real type error.
    // Body `x : α` cannot inhabit the declared codomain `Nat`, so this MUST fail
    // — a silent accept here would be unsound.
    let bad = "def bad_impl : {α : Type} -> α -> Nat := fun x => x\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|res| res.is_err()),
        "mismatched body must be rejected loud, not silently accepted"
    );
}

// ---------------------------------------------------------------------------
// A `by`-tactic value in a NAMED-FIELD structure literal `{ f := by tac }`.
// The `surface→syntax→expand→surface` macro roundtrip collapses a nested
// `ByTactic` into `ByTactic([])` (its tactic children discarded), so without a
// bypass the field's tactic block runs zero tactics and leaves the goal
// unsolved. `elab_struct_lit` must receive the field intact.
// ---------------------------------------------------------------------------

#[test]
fn test_struct_lit_named_field_by_tactic_value() {
    // Plain value field via `by exact`.
    let code = "structure W where\n  n : Nat\ndef w : W := { n := by exact 5 }\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "struct-lit named field `by exact`");
    assert!(env.get_const(&Name::from_string("w")).is_some());
}

#[test]
fn test_struct_lit_named_field_proof_by_decide() {
    // Proof field discharged by `by decide` (n > 0 with n := 5).
    let code =
        "structure V where\n  n : Nat\n  h : n > 0\ndef v : V := { n := 5, h := by decide }\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "struct-lit proof field `by decide`");
    assert!(env.get_const(&Name::from_string("v")).is_some());
}

#[test]
fn test_struct_lit_named_field_by_reduces() {
    // SOUNDNESS: the field value the tactic produces is real — the struct's
    // projection computes to it, kernel-checked by `rfl`.
    let code = "structure P where\n  n : Nat\ndef p : P := { n := by exact 7 }\n\
                theorem p_ok : p.n = 7 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "struct-lit by-field reduces (rfl)");
    assert!(env.get_const(&Name::from_string("p_ok")).is_some());

    // NEGATIVE (loud): a tactic that fails to close the field goal must error,
    // not silently accept a hole.
    let bad = "structure Q where\n  h : (2 : Nat) = 3\ndef q : Q := { h := by decide }\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|res| res.is_err()),
        "an unprovable field goal must be rejected loud, not silently accepted"
    );
}

// ---------------------------------------------------------------------------
// A `by`-tactic component of a parenthesized tuple `(by tac, by tac)`. A
// single-term tactic (`exact`/`apply`/`refine`/`change`) must stop at the
// tuple-separator comma; otherwise `exact` swallows `5, by exact 6` as a
// comma-list and the whole tuple collapses into one bogus `by` block.
// ---------------------------------------------------------------------------

#[test]
fn test_tuple_both_components_by_tactic() {
    let code = "def t : Nat × Nat := (by exact 5, by exact 6)\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "tuple (by, by)");
    assert!(env.get_const(&Name::from_string("t")).is_some());
}

#[test]
fn test_tuple_first_component_by_tactic() {
    let code = "def t2 : Nat × Nat := (by exact 5, 6)\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "tuple (by, term)");
    assert!(env.get_const(&Name::from_string("t2")).is_some());
}

#[test]
fn test_tuple_by_reduces_and_exact_single_term_intact() {
    // SOUNDNESS: the tuple components the tactics produce are real — the
    // projections compute, kernel-checked by `rfl`.
    let code = "def t : Nat × Nat := (by exact 5, by exact 6)\n\
                theorem t_fst : t.1 = 5 := rfl\n\
                theorem t_snd : t.2 = 6 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "tuple by reduces (rfl)");
    assert!(env.get_const(&Name::from_string("t_fst")).is_some());
    assert!(env.get_const(&Name::from_string("t_snd")).is_some());

    // REGRESSION: normal single-term `by exact <term>` (incl. an anon-ctor
    // argument whose internal commas must NOT terminate it) still parses.
    let code2 = "def a : Nat := by exact 7\n\
                 def p : Nat × Nat := by exact ⟨1, 2⟩\n";
    let (env2, r2) = elab_file_prelude(code2);
    assert_all_ok(&r2, "single-term exact intact");
    assert!(env2.get_const(&Name::from_string("p")).is_some());
}

// ---------------------------------------------------------------------------
// Anonymous constructor `⟨by tac, by tac⟩`. Brick 39 (`exact`/`apply`/`refine`/
// `change` single-term in the patternless fallback) fixed this whole family too:
// before it, a leading `by` component swallowed the `⟨⟩` separator comma, so
// `⟨by exact 5, by exact 6⟩` collapsed into one bogus component. These lock in
// the broader fix across tuple / Sigma / struct / triple shapes.
// ---------------------------------------------------------------------------

#[test]
fn test_anon_ctor_all_by_tactic_components() {
    for (code, name) in [
        ("def z1 : Nat × Nat := ⟨by exact 5, by exact 6⟩\n", "z1"),
        ("def z2 : Nat × Nat × Nat := ⟨by exact 1, by exact 2, by exact 3⟩\n", "z2"),
        ("structure PairZ where\n  a : Nat\n  b : Nat\ndef z3 : PairZ := ⟨by exact 5, by exact 6⟩\n", "z3"),
        ("def z4 : (n : Nat) × Nat := ⟨by exact 3, by exact 4⟩\n", "z4"),
    ] {
        let (env, results) = elab_file_prelude(code);
        assert_all_ok(&results, "anon-ctor all-by components");
        assert!(env.get_const(&Name::from_string(name)).is_some(), "{name} should register");
    }
}

#[test]
fn test_anon_ctor_by_components_reduce() {
    // SOUNDNESS: the components the tactics produce are real — projections compute.
    let code = "def z : Nat × Nat := ⟨by exact 5, by exact 6⟩\n\
                theorem z_fst : z.1 = 5 := rfl\n\
                theorem z_snd : z.2 = 6 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "anon-ctor by components reduce");
    assert!(env.get_const(&Name::from_string("z_fst")).is_some());
    assert!(env.get_const(&Name::from_string("z_snd")).is_some());
}

// ---------------------------------------------------------------------------
// `cond` — Lean's `Bool`-eliminating conditional (`cond : {α} → Bool → α → α →
// α`), absent from clean's prelude. Resolved on-demand to the definitional
// `fun {α} c x y => Bool.rec (fun _ => α) y x c`, exactly like `id`.
// ---------------------------------------------------------------------------

#[test]
fn test_cond_elaborates_and_reduces() {
    // Both branches reduce (kernel-checked by rfl): cond true x y ⟶ x,
    // cond false x y ⟶ y.
    let code = "def uc : Nat := cond true 1 0\n\
                theorem cond_true : cond true 1 0 = 1 := rfl\n\
                theorem cond_false : cond false 1 0 = 0 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "cond elaborates + reduces");
    assert!(env.get_const(&Name::from_string("uc")).is_some());
    assert!(env.get_const(&Name::from_string("cond_true")).is_some());
    assert!(env.get_const(&Name::from_string("cond_false")).is_some());
}

#[test]
fn test_cond_wrong_value_rejected() {
    // SOUNDNESS: `cond true 1 0` is `1`, NOT `0` — a wrong rfl must fail loud.
    let bad = "theorem cond_bad : cond true 1 0 = 0 := rfl\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        "cond true 1 0 = 0 is false; rfl must be rejected, not accepted"
    );
}

#[test]
fn test_cond_on_bool_variable() {
    // `cond` applied to a runtime Bool variable elaborates and type-checks.
    let code = "def pick (b : Bool) : Nat := cond b 10 20\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "cond on bool variable");
    assert!(env.get_const(&Name::from_string("pick")).is_some());
}

// ---------------------------------------------------------------------------
// Operator-precedence / associativity / binder-scoping faithfulness. A
// regression here would be a SILENT-WRONG (a well-typed term computing the
// wrong value), so these value-check clean against Lean 4's reading. All were
// verified to match Lean during the round-12 silent-wrong sweep.
// ---------------------------------------------------------------------------

#[test]
fn test_operator_precedence_faithful_to_lean() {
    // Each `rfl` holds ONLY if clean parses with Lean's precedence/associativity.
    let good = [
        "theorem p1 : (10 - 3 - 2 : Nat) = 5 := rfl", // `-` left-assoc
        "theorem p2 : (2 ^ 3 ^ 2 : Nat) = 512 := rfl", // `^` right-assoc
        "theorem p3 : (2 + 3 * 4 : Nat) = 14 := rfl", // `*` > `+`
        "theorem p4 : (2 * 2 ^ 3 : Nat) = 16 := rfl", // `^` > `*`
        "theorem p5 : (10 - 3 + 2 : Nat) = 9 := rfl", // `-`/`+` left-assoc
        "theorem p6 : (true || false && false : Bool) = true := rfl", // `&&` > `||`
        "theorem p7 : (!true && false : Bool) = false := rfl", // `!` > `&&`
    ];
    for code in good {
        let (_e, r) = elab_file_prelude(&format!("{code}\n"));
        assert!(
            r.iter().all(|x| x.is_ok()),
            "precedence must match Lean: {code}"
        );
    }
}

#[test]
fn test_binder_shadowing_faithful_to_lean() {
    // Inner binder shadows outer; value distinguishes the two readings.
    let good = [
        "theorem s1 : ((let x := 1; let x := 2; x) : Nat) = 2 := rfl",
        "theorem s2 : ((fun (x : Nat) (x : Nat) => x) 1 2 : Nat) = 2 := rfl",
        "theorem s3 : ((let x := 5; (fun x => x) 9) : Nat) = 9 := rfl",
        "theorem s4 : ((match 0 with | 0 => 100 | 0 => 200 | _ => 300) : Nat) = 100 := rfl",
    ];
    for code in good {
        let (_e, r) = elab_file_prelude(&format!("{code}\n"));
        assert!(
            r.iter().all(|x| x.is_ok()),
            "shadowing must match Lean: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Inline `match` in a non-def-body position (an argument inside `Eq (match…) 5`,
// an app argument, etc.) whose arm body references a pattern binder. The
// `surface → syntax → expand → surface` macro roundtrip mangles a nested
// `match` (losing its scoped gensym bookkeeping — bogus idents / a leaked FVar
// in the motive), so the enclosing application must be routed AROUND macro
// expansion. Marking `Match` retry-sensitive does that, so the match reaches
// its dedicated `elab_match` intact.
// ---------------------------------------------------------------------------

#[test]
fn test_inline_match_struct_reduces() {
    let code = "structure Box where\n  v : Nat\n\
                theorem t : (match (Box.mk 5) with | Box.mk x => x) = 5 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "inline struct match reduces");
    assert!(env.get_const(&Name::from_string("t")).is_some());
}

#[test]
fn test_inline_match_prod_reduces() {
    // Prod (parameterized) inline matches in positions where the expected type
    // is concrete: ascribed, and on the RHS of `Eq` (α pinned by the LHS `20`).
    let code = "theorem tf : ((match (10, 20) with | (a, b) => a : Nat)) = 10 := rfl
\
                theorem ts : 20 = (match (10, 20) with | (a, b) => b) := rfl
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "inline prod match reduces");
    assert!(env.get_const(&Name::from_string("tf")).is_some());
    assert!(env.get_const(&Name::from_string("ts")).is_some());
}

#[test]
fn test_inline_match_app_argument() {
    let code = "def id2 (n : Nat) : Nat := n\n\
                theorem ta : id2 (match (10, 20) with | (a, b) => a) = 10 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "inline match as app arg");
    assert!(env.get_const(&Name::from_string("ta")).is_some());
}

#[test]
fn test_inline_match_wrong_value_rejected() {
    // SOUNDNESS: the match computes 10, NOT 20 — a wrong rfl must fail loud, so
    // the fix routes the match correctly rather than papering it with a metavar.
    let bad = "theorem tb : (match (10, 20) with | (a, b) => a) = 20 := rfl\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        "match (10,20) |(a,b)=>a is 10, not 20; rfl must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Parameterized-scrutinee `match` on the LHS of `Eq`, where the match's result
// type must be inferred FROM the arms (expected = a fresh metavar α pinned later
// by the RHS). The scrutinee must be elaborated with that expected type CLEARED,
// or `Prod.mk 10 20`'s result unifies with α, wrongly setting α := Prod Nat Nat.
// ---------------------------------------------------------------------------

#[test]
fn test_inline_match_prod_eq_lhs_inferred() {
    let code = "theorem tf : (match (10, 20) with | (a, b) => a) = 10 := rfl\n\
                theorem ts : (match (10, 20) with | (a, b) => b) = 20 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "prod match on Eq-LHS, α inferred from arms");
    assert!(env.get_const(&Name::from_string("tf")).is_some());
    assert!(env.get_const(&Name::from_string("ts")).is_some());
}

#[test]
fn test_inline_match_prod_eq_lhs_wrong_value_rejected() {
    // SOUNDNESS: `match (10,20) |(a,b)=>a` is 10, NOT 20 — a wrong rfl must fail.
    let bad = "theorem tb : (match (10, 20) with | (a, b) => a) = 20 := rfl\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        "match (10,20) |(a,b)=>a is 10, not 20; rfl must be rejected"
    );
}

#[test]
fn test_inline_match_option_eq_lhs_inferred() {
    // The same fix generalizes to other parameterized scrutinees (Option).
    let code = "theorem to : (match (some 7) with | some x => x | none => 0) = 7 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "option match on Eq-LHS, α inferred");
    assert!(env.get_const(&Name::from_string("to")).is_some());
}

// ---------------------------------------------------------------------------
// An inline applied lambda whose body is a `match` on the parameter —
// `(fun p => match p with | (a, b) => a + b) (10, 20)`. The `App`'s HEAD (a
// `Paren(Lambda(match …))`) is retry-sensitive, so it must be routed around
// whole-expression macro expansion (which would mangle the nested match and
// rebind its pattern vars at the wrong constructor positions).
// ---------------------------------------------------------------------------

#[test]
fn test_applied_lambda_match_body_reduces() {
    // Annotated param, so the match scrutinee type is known. (An UNannotated
    // `fun p => match p …` needs bidirectional inference from the argument to
    // pin p's type before the body match elaborates — a separate, deeper gap.)
    let code = "theorem c1 : ((fun (p : Nat × Nat) => match p with | (a, b) => a + b) (10, 20) : Nat) = 30 := rfl
\
                theorem c2 : ((fun (p : Nat × Nat) => match p with | (a, b) => a) (10, 20) : Nat) = 10 := rfl
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "applied lambda with match body reduces");
    assert!(env.get_const(&Name::from_string("c1")).is_some());
    assert!(env.get_const(&Name::from_string("c2")).is_some());
}

#[test]
fn test_applied_lambda_match_wrong_value_rejected() {
    // SOUNDNESS: (10,20) → a+b = 30, not 99.
    let bad = "theorem cb : ((fun (p : Nat × Nat) => match p with | (a, b) => a + b) (10, 20) : Nat) = 99 := rfl\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        "a+b for (10,20) is 30, not 99; rfl must be rejected"
    );
}

// ---------------------------------------------------------------------------
// `if h : c then (match/if …) else …` (dependent-if / IfDecidable) with a
// nested match/if in a branch. IfDecidable lacked the standalone macro-expansion
// bypass that plain `if` and `match` have, so the nested block was mangled.
// ---------------------------------------------------------------------------

#[test]
fn test_if_decidable_nested_match_reduces() {
    let code = "theorem c1 : ((if h : (2 = 2) then (match (5, 6) with | (a, b) => a) else 0) : Nat) = 5 := rfl\n\
                theorem c2 : ((if h : (1 = 2) then 7 else (match (8, 9) with | (a, b) => b)) : Nat) = 9 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "if-decidable with nested match reduces");
    assert!(env.get_const(&Name::from_string("c1")).is_some());
    assert!(env.get_const(&Name::from_string("c2")).is_some());
}

#[test]
fn test_if_decidable_nested_wrong_value_rejected() {
    // SOUNDNESS: 2 = 2 is decidably true → then-branch → 5, not 6.
    let bad = "theorem cb : ((if h : (2 = 2) then (match (5, 6) with | (a, b) => a) else 0) : Nat) = 6 := rfl\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        "if-decidable true→5, not 6; rfl must be rejected"
    );
}

// ---------------------------------------------------------------------------
// A field projection whose base carries a `match` — `(⟨match e with …, y⟩ : T).1`.
// `Proj` was not in the macro-expansion bypass list, so the nested match was
// mangled before the projection base could elaborate it.
// ---------------------------------------------------------------------------

#[test]
fn test_proj_of_match_base_reduces() {
    let code = "theorem c1 : ((⟨match (1, 2) with | (a, b) => b, 100⟩ : Nat × Nat).1 : Nat) = 2 := rfl\n\
                theorem c2 : ((⟨7, match (1, 2) with | (a, b) => a⟩ : Nat × Nat).2 : Nat) = 1 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "projection of match-carrying anon-ctor reduces");
    assert!(env.get_const(&Name::from_string("c1")).is_some());
    assert!(env.get_const(&Name::from_string("c2")).is_some());
}

#[test]
fn test_proj_of_match_base_wrong_value_rejected() {
    // SOUNDNESS: (⟨match (1,2)|(a,b)=>b, 100⟩).1 is 2, not 100.
    let bad = "theorem cb : ((⟨match (1, 2) with | (a, b) => b, 100⟩ : Nat × Nat).1 : Nat) = 100 := rfl\n";
    let (_e, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        ".1 is 2, not 100; rfl must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Consolidated regression lock for the term-position macro-collapse family
// (bricks 41-45): a `match`/`if`/anon-ctor used inline in an operator operand,
// argument, or projection must reduce to the right value — guards against a
// regression re-introducing the macro-roundtrip mangling. Each `rfl` holds only
// if the nested block reaches its dedicated elaborator intact.
// ---------------------------------------------------------------------------

#[test]
fn test_term_position_family_reduces() {
    let good = [
        "theorem m1 : ((match (3, 4) with | (a, b) => a) * 10 : Nat) = 30 := rfl",
        "theorem m2 : (5 + (if true then 2 else 9) : Nat) = 7 := rfl",
        "theorem m3 : (100 - (match (1, 2) with | (a, b) => b) : Nat) = 98 := rfl",
        "theorem m4 : ((match (some (3, 4)) with | some p => (match p with | (a, b) => a + b) | none => 0) : Nat) = 7 := rfl",
        "theorem m5 : (Nat.succ (match (1, 2) with | (a, b) => a) : Nat) = 2 := rfl",
        "theorem m6 : ((if h : (2 = 2) then (match (5, 6) with | (a, b) => a) else 0) : Nat) = 5 := rfl",
        "theorem m7 : ((⟨match (1, 2) with | (a, b) => b, 100⟩ : Nat × Nat).1 : Nat) = 2 := rfl",
        "theorem m8 : ((fun (p : Nat × Nat) => match p with | (a, b) => a + b) (10, 20) : Nat) = 30 := rfl",
        "theorem m9 : ((match (10, 20) with | (a, b) => a) = 10) := rfl",
    ];
    for code in good {
        let (_e, r) = elab_file_prelude(&format!("{code}\n"));
        assert!(
            r.iter().all(|x| x.is_ok()),
            "term-position family must reduce: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Coercion in a `match` arm body: an arm whose value has a coercible type
// (`Nat` where the result is `Int`) must get the coercion inserted, like a
// `def … : Int := n` does. Previously the 18+ per-arm elaboration sites did not
// coerce; the general chokepoint fallback now does.
// ---------------------------------------------------------------------------

#[test]
fn test_match_arm_coercion_nat_to_int() {
    let code = "def f (b : Bool) : Int := match b with | true => (1 : Nat) | false => -1\n\
                theorem c1 : f true = 1 := by decide\n\
                theorem c2 : f false = -1 := by decide\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "match arm Nat→Int coercion");
    assert!(env.get_const(&Name::from_string("f")).is_some());
}

#[test]
fn test_match_arm_coercion_var_and_both_nat() {
    let code = "def g (b : Bool) (n : Nat) : Int := match b with | true => n | false => -1\n\
                def h (b : Bool) : Int := match b with | true => (5 : Nat) | false => (6 : Nat)\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "match arm var/both-Nat coercion");
    assert!(env.get_const(&Name::from_string("g")).is_some());
    assert!(env.get_const(&Name::from_string("h")).is_some());
}

#[test]
fn test_match_arm_coercion_soundness() {
    // SOUNDNESS: `g true 5` coerces 5:Nat to 5:Int — the value is right, not wrong.
    let code = "def g (b : Bool) (n : Nat) : Int := match b with | true => n | false => -1\n\
                theorem ok : g true 5 = 5 := by decide\n";
    let (_e, ok) = elab_file_prelude(code);
    assert!(ok.iter().all(|x| x.is_ok()), "g true 5 must equal 5");
    let bad = "def g (b : Bool) (n : Nat) : Int := match b with | true => n | false => -1\n\
               theorem bad : g true 5 = 6 := by decide\n";
    let (_e2, r) = elab_file_prelude(bad);
    assert!(
        r.iter().any(|x| x.is_err()),
        "g true 5 is 5, not 6; must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Element coercion via expected-type propagation into constructor/function args
// (gap A): an ascribed/variable arg landing in an open type-param slot should
// have that slot pinned from the ground expected result FIRST, so the arg then
// coerces to it (Nat→Int). Bare-literal versions already worked.
// ---------------------------------------------------------------------------

#[test]
fn test_element_coercion_into_ctor_args() {
    let code = "def p : Int × Int := ((3 : Nat), (4 : Nat))\n\
                def q : Int × Int := Prod.mk (3 : Nat) (4 : Nat)\n\
                def f (n : Nat) : Option Int := some n\n\
                theorem t1 : p.1 = 3 := by decide\n\
                theorem t2 : q.2 = 4 := by decide\n\
                theorem t3 : f 5 = some 5 := by decide\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "element coercion into ctor/fn args");
    assert!(env.get_const(&Name::from_string("p")).is_some());
    assert!(env.get_const(&Name::from_string("f")).is_some());
}

#[test]
fn test_element_coercion_soundness() {
    // Right value, coercion inserted.
    let good = "def p : Int × Int := ((3 : Nat), (4 : Nat))\ntheorem t : p.1 = 3 := by decide\n";
    assert!(
        elab_file_prelude(good).1.iter().all(|x| x.is_ok()),
        "p.1 must be 3"
    );
    // Wrong value rejected.
    let bad = "def p : Int × Int := ((3 : Nat), (4 : Nat))\ntheorem t : p.1 = 4 := by decide\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "p.1 is 3, not 4"
    );
}

#[test]
fn test_arithmetic_unchanged_by_coercion_pin() {
    // The pre-arg pin must NOT disturb hetero-binop (binop%) arithmetic.
    let good = [
        "theorem a1 : (2 + 3 * 4 : Nat) = 14 := rfl",
        "theorem a2 : (10 - 3 - 2 : Nat) = 5 := rfl",
        "theorem a3 : (2 ^ 3 ^ 2 : Nat) = 512 := rfl",
        "theorem a4 : ((2 : Int) - 5 = -3) := by decide",
        "theorem a5 : (16 / 4 / 2 : Nat) = 2 := rfl",
        "theorem a6 : (100 % 7 : Nat) = 2 := rfl",
    ];
    for code in good {
        assert!(
            elab_file_prelude(&format!("{code}\n"))
                .1
                .iter()
                .all(|x| x.is_ok()),
            "arithmetic must be unchanged: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Structural / container element coercion: a container literal / constructor
// whose expected result pins the element type through the container structure
// (`#[1,2] : Array Int`, `some (some n) : Option (Option Int)`). The pre-arg
// slot-open check now fires when the slot CONTAINS an open metavar (`List ?α`),
// not only when its head is one.
// ---------------------------------------------------------------------------

#[test]
fn test_container_element_coercion() {
    // `#[1, 2] : Array Int` — `Array.mk (List.cons 1 …)`; the element type must
    // pin from the expected `Array Int` through the `List ?α` slot. The def
    // registering AS `Array Int` (kernel-re-checked) is the proof the coercion
    // was inserted — a `List Nat`/`Array Nat` would fail the ascription.
    let code = "def a : Array Int := #[1, 2]
theorem t1 : a.size = 2 := rfl
";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Array Int from bare Nat literals");
    assert!(env.get_const(&Name::from_string("a")).is_some());
    // NEGATIVE: wrong size rejected (value-distinguishing).
    let bad = "def a : Array Int := #[1, 2]
theorem t : a.size = 3 := rfl
";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "size is 2, not 3"
    );
}

#[test]
fn test_container_coercion_soundness_and_arithmetic() {
    // Arithmetic + brick-46/47 element coercion UNCHANGED by the slot-open relax.
    for code in [
        "theorem q1 : (2 + 3 * 4 : Nat) = 14 := rfl",
        "theorem q2 : ((2 : Int) - 5 = -3) := by decide",
        "theorem q3 : (2 ^ 3 ^ 2 : Nat) = 512 := rfl",
        "theorem q4 : (100 % 7 : Nat) = 2 := rfl",
        "def p : Int × Int := ((3 : Nat), (4 : Nat))",
        "def l : List Int := [(1 : Nat), (2 : Nat)]",
        "def f (n : Nat) : Option Int := some n",
    ] {
        assert!(
            elab_file_prelude(&format!(
                "{code}
"
            ))
            .1
            .iter()
            .all(|x| x.is_ok()),
            "must stay correct: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Ascribed-element / nested container coercion (brick-48 residual): the pre-arg
// arg guard now recurses into `Array.mk`/`List.cons`/`some`/`Prod.mk` spines, so
// a nested typed-value element pins each enclosing container's element type.
// ---------------------------------------------------------------------------

#[test]
fn test_ascribed_and_nested_container_coercion() {
    let code = "def b : Array Int := #[(1 : Nat), (2 : Nat)]\n\
                def o : Option (Option Int) := some (some (5 : Nat))\n\
                theorem t1 : b.size = 2 := rfl\n\
                theorem t2 : (o = some (some 5)) := by decide\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "ascribed/nested container coercion");
    assert!(env.get_const(&Name::from_string("b")).is_some());
    assert!(env.get_const(&Name::from_string("o")).is_some());
}

#[test]
fn test_nested_container_soundness_and_regressions() {
    // SOUNDNESS: nested value reduces to the right coerced value.
    let bad = "def o : Option (Option Int) := some (some (5 : Nat))\ntheorem t : (o = some (some 6)) := by decide\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "o is some(some 5), not 6"
    );
    // Bricks 46/47/48 + arithmetic UNCHANGED.
    for code in [
        "def a : Array Int := #[1, 2]",
        "def p : Int × Int := ((3 : Nat), (4 : Nat))",
        "def l : List Int := [(1 : Nat), (2 : Nat)]",
        "def f (n : Nat) : Option Int := some n",
        "theorem q1 : (2 + 3 * 4 : Nat) = 14 := rfl",
        "theorem q2 : ((2 : Int) - 5 = -3) := by decide",
        "theorem q3 : (2 ^ 3 ^ 2 : Nat) = 512 := rfl",
    ] {
        assert!(
            elab_file_prelude(&format!("{code}\n"))
                .1
                .iter()
                .all(|x| x.is_ok()),
            "must stay correct: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Pattern-matching & do-notation VALUE semantics (round-26 sweep verified these
// match Lean): or-patterns, `n+2`, overlapping-first-wins, nested ctor patterns,
// multi-discriminant order, `for` with `break`/`continue`. A regression here
// would be a silent-wrong (well-typed term, wrong value), so value-check them.
// ---------------------------------------------------------------------------

#[test]
fn test_pattern_value_semantics_faithful() {
    let good = [
        "theorem p1 : ((match 1 with | 0 | 1 => 100 | _ => 200) : Nat) = 100 := rfl",
        "theorem p2 : ((match 2 with | 0 | 1 => 100 | _ => 200) : Nat) = 200 := rfl",
        "theorem p3 : ((match 5 with | 0 => 0 | 1 => 1 | n+2 => n) : Nat) = 3 := rfl",
        "theorem p4 : ((match 0 with | 0 => 1 | 0 => 2 | _ => 3) : Nat) = 1 := rfl", // first wins
        "theorem p5 : ((match [3,4,5] with | x :: y :: _ => x + y | _ => 0) : Nat) = 7 := rfl",
        "theorem p6 : ((match (5, 0) with | _, 0 => 1 | 0, _ => 2 | _, _ => 3) : Nat) = 1 := rfl",
    ];
    for code in good {
        let (_e, r) = elab_file_prelude(&format!("{code}\n"));
        assert!(
            r.iter().all(|x| x.is_ok()),
            "pattern value semantics: {code}"
        );
    }
}

#[test]
fn test_do_loop_value_semantics_faithful() {
    let good = [
        // `break` stops the loop (sum 1+2+3 = 6, i=4,5 skipped).
        "def f : Id Nat := do\n  let mut s := 0\n  for i in [1,2,3,4,5] do\n    if i > 3 then break\n    s := s + i\n  pure s\ntheorem t : f.run = 6 := by decide",
        // `continue` skips i=2 (sum 1+3+4 = 8).
        "def g : Id Nat := do\n  let mut s := 0\n  for i in [1,2,3,4] do\n    if i = 2 then continue\n    s := s + i\n  pure s\ntheorem t : g.run = 8 := by decide",
    ];
    for code in good {
        let (_e, r) = elab_file_prelude(&format!("{code}\n"));
        assert!(
            r.iter().all(|x| x.is_ok()),
            "do loop value semantics: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Unannotated lambda param matched inline, applied — `(fun p => match p with |
// (a,b) => a+b) (10,20)`. Rewritten to `let p := (10,20); match p …` so the
// argument pins p's type before the body match elaborates (the annotated form
// already worked via brick 43).
// ---------------------------------------------------------------------------

#[test]
fn test_unannotated_lambda_match_applied() {
    let code = "theorem t1 : ((fun p => match p with | (a, b) => a + b) (10, 20) : Nat) = 30 := by decide\n\
                theorem t2 : ((fun p => match p with | (a, b) => a) (10, 20) : Nat) = 10 := by decide\n\
                theorem t3 : ((fun o => match o with | some x => x | none => 0) (some 7) : Nat) = 7 := by decide\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "unannotated lambda + match on binder, applied");
    assert!(env.get_const(&Name::from_string("t1")).is_some());
}

#[test]
fn test_unannotated_lambda_match_soundness_and_controls() {
    // SOUNDNESS: wrong value rejected.
    let bad = "theorem t : ((fun p => match p with | (a, b) => a + b) (10, 20) : Nat) = 31 := by decide\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "sum is 30, not 31"
    );
    // CONTROLS unchanged: annotated form, non-match body, plain match.
    for code in [
        "theorem c1 : ((fun (p : Nat × Nat) => match p with | (a, b) => a + b) (10, 20) : Nat) = 30 := by decide",
        "theorem c2 : ((fun p => p + 1) 5 : Nat) = 6 := rfl",
        "theorem c3 : ((match (10, 20) with | (a, b) => a) : Nat) = 10 := rfl",
    ] {
        assert!(elab_file_prelude(&format!("{code}\n")).1.iter().all(|x| x.is_ok()),
            "control must stay correct: {code}");
    }
}

// ---------------------------------------------------------------------------
// Case-B: a `match`-valued `let` inside a parenthesized ascription on the LHS
// of `Eq` — `((let x := match e with …; body) : T) = v := rfl`. `Paren(Let …)`
// now re-enters `elaborate` (→ the Let bypass) instead of `expand_macros`, so
// the let value's nested match survives intact.
// ---------------------------------------------------------------------------

#[test]
fn test_paren_let_match_value_on_eq_lhs() {
    let code = "theorem t1 : ((let x := match (7, 8) with | (a, b) => a; x + 1) : Nat) = 8 := rfl\n\
                theorem t2 : ((let x := match (7, 8) with | (a, b) => b; x) : Nat) = 8 := rfl\n\
                theorem t3 : ((let p := match (some 5) with | some n => n | none => 0; p * 2) : Nat) = 10 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "paren-let with match value on Eq-LHS");
    assert!(env.get_const(&Name::from_string("t1")).is_some());
}

#[test]
fn test_paren_let_match_soundness_and_controls() {
    // SOUNDNESS: wrong value rejected.
    let bad = "theorem t : ((let x := match (7, 8) with | (a, b) => a; x + 1) : Nat) = 9 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "value is 8, not 9"
    );
    // CONTROLS: plain match, bare let, brick-41 inline match unchanged.
    for code in [
        "theorem c1 : ((match (7, 8) with | (a, b) => a) : Nat) = 7 := rfl",
        "def c2 : Nat := let x := 5; x + 1",
        "theorem c3 : ((match (Prod.mk 1 2) with | Prod.mk a b => a) = 1) := rfl",
    ] {
        assert!(
            elab_file_prelude(&format!("{code}\n"))
                .1
                .iter()
                .all(|x| x.is_ok()),
            "control must stay correct: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Faithfulness lock: structure-update syntax `{ s with f := v }` and default
// field values `(b : Nat := d)`. A fresh gap-mine (round 29) verified these
// elaborate with Lean-4 value semantics; this pins that so a future structure-
// elaboration change can't silently regress the updated/preserved-field split
// or the default-fill. Each theorem reduces by `rfl` (value-distinguishing);
// the negative confirms a wrong value is rejected loud.
// ---------------------------------------------------------------------------

#[test]
fn test_structure_update_value_semantics_faithful() {
    let code = "structure PP where\n\
                \x20 a : Nat\n\
                \x20 b : Nat\n\
                def p0 : PP := { a := 1, b := 2 }\n\
                theorem u_upd : ({ p0 with b := 5 }).b = 5 := rfl\n\
                theorem u_keep : ({ p0 with b := 5 }).a = 1 := rfl\n\
                theorem u_multi_a : ({ p0 with a := 7, b := 5 }).a = 7 := rfl\n\
                theorem u_multi_b : ({ p0 with a := 7, b := 5 }).b = 5 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "structure-update value semantics");
    assert!(env.get_const(&Name::from_string("u_upd")).is_some());
}

#[test]
fn test_structure_default_field_faithful() {
    let code = "structure QQ where\n\
                \x20 a : Nat\n\
                \x20 b : Nat := 9\n\
                def q0 : QQ := { a := 1 }\n\
                theorem d_default : q0.b = 9 := rfl\n\
                theorem d_explicit : ({ a := 1, b := 3 } : QQ).b = 3 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "structure default field");
}

#[test]
fn test_structure_update_soundness_wrong_value_rejected() {
    // The updated field is 5; asserting it equals 6 must be rejected loud.
    let bad = "structure PP where\n\
               \x20 a : Nat\n\
               \x20 b : Nat\n\
               def p0 : PP := { a := 1, b := 2 }\n\
               theorem u_bad : ({ p0 with b := 5 }).b = 6 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "wrong updated-field value (6 ≠ 5) must be rejected"
    );
    // And the default field is 9, not 8.
    let bad2 = "structure QQ where\n\
                \x20 a : Nat\n\
                \x20 b : Nat := 9\n\
                def q0 : QQ := { a := 1 }\n\
                theorem d_bad : q0.b = 8 := rfl\n";
    assert!(
        elab_file_prelude(bad2).1.iter().any(|x| x.is_err()),
        "wrong default-field value (8 ≠ 9) must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Diamond-inheritance structure literals. `D extends B, C` where both `B` and
// `C` extend a shared `A`: a field of the shared ancestor (`a`) must populate
// BOTH parent subobjects when constructing `{ a := …, b := …, c := …, d := … }`.
// Before the fix the shared field was routed to only the first parent, so the
// second subobject was reported missing its inherited `a` and a valid literal
// was rejected (MissingStructureFields A ["a"]). Round 30 gap-mine.
// ---------------------------------------------------------------------------

#[test]
fn test_diamond_structure_literal_construction() {
    let code = "structure A3 where a : Nat\n\
                structure B3 extends A3 where b : Nat\n\
                structure C3 extends A3 where c : Nat\n\
                structure D3 extends B3, C3 where d : Nat\n\
                def d0 : D3 := { a := 1, b := 2, c := 3, d := 4 }\n\
                theorem dia_a : d0.a = 1 := rfl\n\
                theorem dia_b : d0.b = 2 := rfl\n\
                theorem dia_c : d0.c = 3 := rfl\n\
                theorem dia_d : d0.d = 4 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "diamond structure literal");
    assert!(env.get_const(&Name::from_string("d0")).is_some());
}

#[test]
fn test_diamond_structure_soundness_and_regressions() {
    // SOUNDNESS: a wrong shared-ancestor value is rejected.
    let bad = "structure A3 where a : Nat\n\
               structure B3 extends A3 where b : Nat\n\
               structure C3 extends A3 where c : Nat\n\
               structure D3 extends B3, C3 where d : Nat\n\
               def d0 : D3 := { a := 1, b := 2, c := 3, d := 4 }\n\
               theorem dia_bad : d0.a = 2 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "d0.a is 1, not 2 — must be rejected"
    );
    // SOUNDNESS: omitting the shared-ancestor field still fails loud (missing).
    let missing = "structure A3 where a : Nat\n\
                   structure B3 extends A3 where b : Nat\n\
                   structure C3 extends A3 where c : Nat\n\
                   structure D3 extends B3, C3 where d : Nat\n\
                   def d0 : D3 := { b := 2, c := 3, d := 4 }\n";
    assert!(
        elab_file_prelude(missing).1.iter().any(|x| x.is_err()),
        "omitting shared field `a` must still be reported missing"
    );
    // REGRESSIONS: single-extends, triple-chain, and disjoint multi-extends
    // (no shared ancestor) all still construct correctly.
    for code in [
        "structure A1 where a : Nat\nstructure B1 extends A1 where b : Nat\ndef x : B1 := { a := 1, b := 2 }\ntheorem t : x.a = 1 := rfl",
        "structure A1 where a : Nat\nstructure B1 extends A1 where b : Nat\nstructure C1 extends B1 where c : Nat\ndef x : C1 := { a := 1, b := 2, c := 3 }\ntheorem t : x.a = 1 := rfl",
        "structure AX where x : Nat\nstructure AY where y : Nat\nstructure BB extends AX where b : Nat\nstructure CC extends AY where c : Nat\nstructure DD extends BB, CC where d : Nat\ndef z : DD := { x := 1, y := 2, b := 3, c := 4, d := 5 }\ntheorem t : z.x = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(&format!("{code}\n")).1.iter().all(|x| x.is_ok()),
            "regression must stay correct: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// Function composition APPLIED to an argument: `(f ∘ g) x` / `Function.comp f g x`.
// Clean has no `Function.comp` const — it desugars `f ∘ g` to `fun z => f (g z)`,
// but only for the bare 2-arg combinator. The parser flattens `(f ∘ g) x` to
// `App(Function.comp, [f, g, x])`, which missed that desugar and failed against
// the absent const. Round 31 gap-mine. Now `Function.comp f g x …` desugars to
// `f (g x) …` directly.
// ---------------------------------------------------------------------------

#[test]
fn test_function_comp_applied_to_arg() {
    let code = "def f1 (x : Nat) : Nat := x + 1\n\
                def f2 (x : Nat) : Nat := x * 2\n\
                theorem comp_dot_named : (f1 ∘ f2) 3 = 7 := rfl\n\
                theorem comp_fn_named : (Function.comp f1 f2) 3 = 7 := rfl\n\
                theorem comp_dot_lambda : ((fun x => x + 1) ∘ (fun x => x * 2)) 3 = 7 := rfl\n\
                theorem comp_fn_lambda : (Function.comp (fun x => x + 1) (fun x => x * 2)) 3 = 7 := rfl\n\
                theorem comp_bare_still : (Function.comp f1 f2) = (Function.comp f1 f2) := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "function composition applied to arg");
    assert!(env
        .get_const(&Name::from_string("comp_dot_named"))
        .is_some());
}

#[test]
fn test_function_comp_applied_soundness() {
    // SOUNDNESS: (f1 ∘ f2) 3 = 7, not 8.
    let bad = "def f1 (x : Nat) : Nat := x + 1\n\
               def f2 (x : Nat) : Nat := x * 2\n\
               theorem c_bad : (f1 ∘ f2) 3 = 8 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "(f1 ∘ f2) 3 is 7, not 8 — must be rejected"
    );
    // Order matters: (f2 ∘ f1) 3 = (3+1)*2 = 8, not 7.
    let order = "def f1 (x : Nat) : Nat := x + 1\n\
                 def f2 (x : Nat) : Nat := x * 2\n\
                 theorem c_order : (f2 ∘ f1) 3 = 8 := rfl\n";
    assert!(
        elab_file_prelude(order).1.iter().all(|x| x.is_ok()),
        "(f2 ∘ f1) 3 = (3+1)*2 = 8 must hold"
    );
}

// ---------------------------------------------------------------------------
// Prelude combinators `flip` and `Function.const` APPLIED to arguments —
// `(flip g) a b`, `(Function.const β a) x`. Same family as brick 53 (`(f∘g) x`):
// each desugars to a defeq lambda only in bare form, and the parser nests the
// applied form so the lambda-as-head trips unannotated-binder inference. Now the
// nested application rewrites to the beta-reduced term directly. Round 32.
// ---------------------------------------------------------------------------

#[test]
fn test_flip_and_const_applied() {
    let code = "def sub2 (a b : Nat) : Nat := a - b\n\
                theorem const_applied : (Function.const Nat 5) 99 = 5 := rfl\n\
                theorem const_bare : (Function.const Nat 5) = (Function.const Nat 5) := rfl\n\
                theorem flip_applied : (flip sub2) 3 10 = 7 := rfl\n\
                theorem flip_bare : (flip sub2) = (flip sub2) := rfl\n\
                theorem comp_still : (Function.const Nat 5 ∘ (· + 1)) 3 = 5 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "flip/const applied to arguments");
    assert!(env.get_const(&Name::from_string("flip_applied")).is_some());
}

#[test]
fn test_flip_const_applied_soundness() {
    // flip: (flip sub2) 3 10 = sub2 10 3 = 7, NOT sub2 3 10 = 0 and not 13.
    let bad_flip = "def sub2 (a b : Nat) : Nat := a - b\n\
                    theorem b : (flip sub2) 3 10 = 0 := rfl\n";
    assert!(
        elab_file_prelude(bad_flip).1.iter().any(|x| x.is_err()),
        "(flip sub2) 3 10 = sub2 10 3 = 7, not 0"
    );
    // const: (Function.const Nat 5) 99 = 5, NOT 99.
    let bad_const = "theorem b : (Function.const Nat 5) 99 = 99 := rfl\n";
    assert!(
        elab_file_prelude(bad_const).1.iter().any(|x| x.is_err()),
        "const ignores its arg — result is 5, not 99"
    );
}

// ---------------------------------------------------------------------------
// Building blocks for a real `Ord` instance on a structure (round-33 finding).
// `deriving Ord` currently emits a `sorry` compare for structs-with-fields (all
// three derive handlers) — a non-functional stub. But every piece a *real*
// derivation must produce works today: `Ord.compare` reduces on the field type,
// struct field projection reduces, and a hand-written anonymous-constructor
// instance `⟨fun a b => Ord.compare a.x b.x⟩` elaborates, kernel-checks, and
// reduces. This locks those so a future real Ord codegen has a green target and
// the elaboration/reduction path can't silently regress underneath it.
// ---------------------------------------------------------------------------

#[test]
fn test_ord_compare_and_manual_instance() {
    let code = "theorem oc_lt : Ord.compare 1 2 = Ordering.lt := rfl\n\
                theorem oc_eq : Ord.compare 5 5 = Ordering.eq := rfl\n\
                theorem oc_gt : Ord.compare 9 2 = Ordering.gt := rfl\n\
                structure OS where\n\
                \x20 x : Nat\n\
                instance : Ord OS := ⟨fun a b => Ord.compare a.x b.x⟩\n\
                theorem os_lt : Ord.compare (⟨1⟩ : OS) (⟨2⟩ : OS) = Ordering.lt := rfl\n\
                theorem os_eq : Ord.compare (⟨4⟩ : OS) (⟨4⟩ : OS) = Ordering.eq := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Ord.compare reduction + manual Ord instance");
    assert!(env.get_const(&Name::from_string("os_lt")).is_some());
}

#[test]
fn test_ord_manual_instance_soundness() {
    // The manual compare is by the field: (⟨1⟩ : OS) < (⟨2⟩ : OS) is `.lt`, not `.gt`.
    let bad = "structure OS where\n\
               \x20 x : Nat\n\
               instance : Ord OS := ⟨fun a b => Ord.compare a.x b.x⟩\n\
               theorem os_bad : Ord.compare (⟨1⟩ : OS) (⟨2⟩ : OS) = Ordering.gt := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "1 < 2 by field compare is Ordering.lt, not gt"
    );
}

// ---------------------------------------------------------------------------
// Real `deriving Ord` for single-constructor structs (round-34). Previously all
// three Ord derive handlers emitted `sorry` for a ctor with fields; the active
// one (DeriveOrd2) now builds a real lexicographic `compare` — each field via
// its own `Ord` instance (resolved from env), sequenced with `Ordering.casesOn`.
// ---------------------------------------------------------------------------

#[test]
fn test_deriving_ord_single_field() {
    let code = "structure OS where\n\
                \x20 x : Nat\n\
                deriving Ord\n\
                theorem lt : Ord.compare (⟨1⟩ : OS) (⟨2⟩ : OS) = Ordering.lt := rfl\n\
                theorem eq : Ord.compare (⟨4⟩ : OS) (⟨4⟩ : OS) = Ordering.eq := rfl\n\
                theorem gt : Ord.compare (⟨9⟩ : OS) (⟨2⟩ : OS) = Ordering.gt := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "deriving Ord single field reduces");
    assert!(env.get_const(&Name::from_string("instOSOrd")).is_some());
}

#[test]
fn test_deriving_ord_multi_field_lexicographic() {
    // Lexicographic: first field decides; ties fall through to the second.
    let code = "structure P2 where\n\
                \x20 a : Nat\n\
                \x20 b : Nat\n\
                deriving Ord\n\
                theorem first_decides : Ord.compare (⟨1, 9⟩ : P2) (⟨2, 0⟩ : P2) = Ordering.lt := rfl\n\
                theorem tie_second_lt : Ord.compare (⟨5, 1⟩ : P2) (⟨5, 2⟩ : P2) = Ordering.lt := rfl\n\
                theorem tie_second_gt : Ord.compare (⟨5, 8⟩ : P2) (⟨5, 3⟩ : P2) = Ordering.gt := rfl\n\
                theorem all_eq : Ord.compare (⟨7, 7⟩ : P2) (⟨7, 7⟩ : P2) = Ordering.eq := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "deriving Ord multi-field lexicographic");
}

#[test]
fn test_deriving_ord_soundness() {
    // 1 < 2 by first field is .lt, not .gt.
    let bad = "structure OS where\n\
               \x20 x : Nat\n\
               deriving Ord\n\
               theorem bad : Ord.compare (⟨1⟩ : OS) (⟨2⟩ : OS) = Ordering.gt := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "1 < 2 derives Ordering.lt, not gt"
    );
    // Lexicographic tie-break: (5,1) vs (5,2) is .lt (second field), NOT .eq.
    let bad2 = "structure P2 where\n\
                \x20 a : Nat\n\
                \x20 b : Nat\n\
                deriving Ord\n\
                theorem bad : Ord.compare (⟨5, 1⟩ : P2) (⟨5, 2⟩ : P2) = Ordering.eq := rfl\n";
    assert!(
        elab_file_prelude(bad2).1.iter().any(|x| x.is_err()),
        "equal first field must fall through to second (lt), not report eq"
    );
}

// ---------------------------------------------------------------------------
// Parametric `deriving Ord` (round-35, the brick-55 residual). `derive_ord`'s
// parametric path now builds an fvar telescope resolving each field's `[Ord αᵢ]`
// against the opened constraint binders (mirrors build_beq_value_parametric),
// with the same lexicographic Ordering.casesOn fold as the monomorphic path.
// ---------------------------------------------------------------------------

#[test]
fn test_deriving_ord_parametric() {
    let code = "structure Box (α : Type) where\n\
                \x20 val : α\n\
                deriving Ord\n\
                theorem lt : Ord.compare (⟨1⟩ : Box Nat) (⟨2⟩ : Box Nat) = Ordering.lt := rfl\n\
                theorem eq : Ord.compare (⟨4⟩ : Box Nat) (⟨4⟩ : Box Nat) = Ordering.eq := rfl\n\
                theorem gt : Ord.compare (⟨9⟩ : Box Nat) (⟨2⟩ : Box Nat) = Ordering.gt := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric deriving Ord reduces");
    assert!(env.get_const(&Name::from_string("instBoxOrd")).is_some());
}

#[test]
fn test_deriving_ord_parametric_soundness() {
    let bad = "structure Box (α : Type) where\n\
               \x20 val : α\n\
               deriving Ord\n\
               theorem bad : Ord.compare (⟨1⟩ : Box Nat) (⟨2⟩ : Box Nat) = Ordering.gt := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "1 < 2 by field is Ordering.lt, not gt"
    );
}

// ---------------------------------------------------------------------------
// Bare `default` resolves to `Inhabited.default` (round-36). Clean has no root
// `default` export, so `deriving Inhabited` produced a correct instance that
// `(default : T)` could not reach (UnknownIdent / leaked fvar). Now `default`
// aliases the registered `Inhabited.default`; implicit `{α}` + `[Inhabited α]`
// insertion/synthesis makes it reduce to the type's default.
// ---------------------------------------------------------------------------

#[test]
fn test_bare_default_resolves() {
    let code = "structure S1 where\n\
                \x20 x : Nat\n\
                deriving Inhabited\n\
                def d : S1 := default\n\
                theorem d_field : d.x = 0 := rfl\n\
                theorem inline : (default : S1).x = 0 := rfl\n\
                theorem nat_default : (default : Nat) = 0 := rfl\n\
                theorem bool_default : (default : Bool) = false := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "bare default resolves to Inhabited.default");
    assert!(env.get_const(&Name::from_string("d")).is_some());
}

#[test]
fn test_bare_default_soundness_and_user_shadow() {
    // SOUNDNESS: default Nat is 0, not 1.
    let bad = "theorem t : (default : Nat) = 1 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "default Nat is 0, not 1"
    );
    // A user-defined `default` constant still wins (alias only fires when unresolved).
    let shadow = "def default : Nat := 5\ntheorem t : default = 5 := rfl\n";
    assert!(
        elab_file_prelude(shadow).1.iter().all(|x| x.is_ok()),
        "user-defined `default` must shadow the Inhabited.default alias"
    );
}

// ---------------------------------------------------------------------------
// Faithfulness lock (round-36): mutual inductive types, `Except`-monad do-blocks,
// `@`-explicit application, and Nat bit/pow reduction. A fresh gap-mine verified
// these elaborate + reduce with Lean-4 semantics; this pins them. (Most other
// probes that round were co-tenant missing-prelude-consts — Prod.map, Sum.elim,
// String.toList, Array.foldl, Fin.succ, List.zipWith, Function.uncurry/curry,
// and the whole Coe/CoeFun class hierarchy — recorded, not lockable here.)
// ---------------------------------------------------------------------------

#[test]
fn test_mutual_inductive_and_except_do_faithful() {
    // Mutual/nested inductives (Tree references Forest and vice-versa) define and
    // construct; a recursive size over the mutual pair reduces.
    let code = "mutual\n\
                inductive Tree where\n\
                \x20 | node : Forest → Tree\n\
                inductive Forest where\n\
                \x20 | nil : Forest\n\
                \x20 | cons : Tree → Forest → Forest\n\
                end\n\
                def leaf : Tree := Tree.node Forest.nil\n\
                def f2 : Forest := Forest.cons leaf (Forest.cons leaf Forest.nil)\n\
                theorem t : True := True.intro\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "mutual inductive Tree/Forest");
    assert!(env.get_const(&Name::from_string("f2")).is_some());

    // Except monad do-block reduces.
    let ex = "theorem t : ((do let x ← Except.ok 3; pure (x + 1)) : Except String Nat) = Except.ok 4 := rfl\n";
    assert!(
        elab_file_prelude(ex).1.iter().all(|x| x.is_ok()),
        "Except do-block reduces"
    );
}

#[test]
fn test_at_explicit_and_nat_ops_faithful() {
    let code = "theorem cons : (@List.cons Nat 1 [2, 3]) = [1, 2, 3] := rfl\n\
                theorem land : (Nat.land 6 3) = 2 := rfl\n\
                theorem pow : (2 ^ 3 : Nat) = 8 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "@-explicit application + Nat bit/pow reduction");
    // Soundness: 2^3 is 8, not 9.
    assert!(
        elab_file_prelude("theorem t : (2 ^ 3 : Nat) = 9 := rfl\n")
            .1
            .iter()
            .any(|x| x.is_err()),
        "2^3 is 8, not 9"
    );
}

// ---------------------------------------------------------------------------
// `Function.uncurry`/`Function.curry` fully APPLIED (round-37). Both combinators
// had on-demand arms only for the bare 1-arg form; the fully-applied
// `uncurry g (a,b)` / `curry g a b` fell through to a dot-notation error. Now
// they reduce directly (`uncurry g p = g p.fst p.snd`, `curry g a b = g ⟨a,b⟩`).
// Residual (recorded, NOT fixed): the `(· + ·)` SECTION mis-defaults its operator
// to UInt64 when its operands are projections (a separate section/HAdd bug), and
// partial/nested-applied forms (`(uncurry g) p`, `(curry g a) b`) still hit
// unannotated-binder inference — so this covers named functions / typed lambdas,
// the common case.
// ---------------------------------------------------------------------------

#[test]
fn test_function_uncurry_curry_applied() {
    let code = "def add (a b : Nat) : Nat := a + b\n\
                def addp (p : Nat × Nat) : Nat := p.1 + p.2\n\
                theorem unc : (Function.uncurry add (3, 4)) = 7 := rfl\n\
                theorem unc_l : (Function.uncurry (fun (a : Nat) (b : Nat) => a * b) (3, 4)) = 12 := rfl\n\
                theorem cur : (Function.curry addp 3 4) = 7 := rfl\n\
                theorem cur_l : (Function.curry (fun (p : Nat × Nat) => p.1 * p.2) 3 4) = 12 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Function.uncurry/curry fully applied");
    assert!(env.get_const(&Name::from_string("unc")).is_some());
}

#[test]
fn test_function_uncurry_curry_soundness() {
    // uncurry add (3,4) = 7, not 8.
    let bad = "def add (a b : Nat) : Nat := a + b\n\
               theorem t : (Function.uncurry add (3, 4)) = 8 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "uncurry add (3,4) is 7, not 8"
    );
    // curry passes a=first, b=second: (10,3) → 10-3 = 7 (order-sensitive, not 3-10).
    let order = "def subp (p : Nat × Nat) : Nat := p.1 - p.2\n\
                 theorem t : (Function.curry subp 10 3) = 7 := rfl\n";
    assert!(
        elab_file_prelude(order).1.iter().all(|x| x.is_ok()),
        "curry a=first,b=second: 10-3=7"
    );
}

// ---------------------------------------------------------------------------
// `·`-section applied to non-literal arguments (round-38). A section desugars to
// a lambda with untyped `__cdot_N` binders; applied to projections / bound vars,
// its arithmetic body's HAdd/Add instance resolved the open carrier to UInt64
// before the args pinned it (`(· + ·) p.1 p.2` with `p : Nat×Nat` → "expected
// UInt64, got Nat"). Now a fully-applied section rewrites to a `let`-chain, so
// the argument pins each binder's type first. Works for any operand type.
// ---------------------------------------------------------------------------

#[test]
fn test_cdot_section_applied_to_projections() {
    let code = "def p : Nat × Nat := (3, 4)\n\
                theorem add : ((· + ·) p.1 p.2) = 7 := rfl\n\
                theorem mul : ((· * ·) p.1 p.2) = 12 := rfl\n\
                theorem sub : ((· - ·) p.1 p.2) = 0 := rfl\n\
                def g (x y : Nat) : Nat := (· + ·) x y\n\
                theorem bound : g 3 4 = 7 := rfl\n\
                def q : Int × Int := (10, 3)\n\
                theorem int_sub : ((· - ·) q.1 q.2) = 7 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "cdot section applied to projections / bound vars / Int",
    );
    assert!(env.get_const(&Name::from_string("add")).is_some());
}

#[test]
fn test_cdot_section_soundness_and_controls() {
    // Soundness: (·+·) p.1 p.2 with p=(3,4) is 7, not 8.
    let bad = "def p : Nat × Nat := (3, 4)\n\
               theorem t : ((· + ·) p.1 p.2) = 8 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "3+4 is 7, not 8"
    );
    // Controls: bare-literal section, ascribed section, and a section as a HOF
    // argument all still work (unchanged paths).
    for code in [
        "theorem t : ((· + ·) 3 4) = 7 := rfl",
        "def p : Nat × Nat := (3, 4)\ntheorem t : (((· + ·) : Nat → Nat → Nat) p.1 p.2) = 7 := rfl",
        "theorem t : ([1, 2, 3].map (· * 2)) = [2, 4, 6] := rfl",
    ] {
        assert!(
            elab_file_prelude(&format!("{code}\n"))
                .1
                .iter()
                .all(|x| x.is_ok()),
            "control must stay correct: {code}"
        );
    }
}

// ---------------------------------------------------------------------------
// `And.elim`/`Or.elim` applied (round-39). Both are absent from Clean's prelude
// (a bare `And.elim` fails "cannot extract type name" — dot-notation on the type
// `And`). Resolved on-demand: `And.elim f h` ⇝ `f h.left h.right`, `Or.elim h f
// g` ⇝ `match h with | Or.inl x => f x | Or.inr x => g x`.
// ---------------------------------------------------------------------------

#[test]
fn test_and_or_elim_applied() {
    let code = "theorem ae (p q : Prop) (h : p ∧ q) : q := And.elim (fun _ hq => hq) h\n\
                theorem ae2 (p q : Prop) (h : p ∧ q) : p := And.elim (fun hp _ => hp) h\n\
                theorem oe (p : Prop) (h : p ∨ p) : p := Or.elim h id id\n\
                theorem oe2 (p q : Prop) (h : p ∨ q) : q ∨ p := Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)\n\
                def oe3 (p q : Prop) (h : p ∨ q) := match h with | Or.inl hp => Or.inr hp | Or.inr hq => Or.inl hq\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "And.elim/Or.elim applied");
    assert!(env.get_const(&Name::from_string("ae")).is_some());
}

#[test]
fn test_and_or_elim_soundness() {
    // `And.elim (fun _ hq => hq)` gives `q` from `p ∧ q`; used to prove `p` it
    // is the wrong component and must be rejected.
    let bad = "theorem t (p q : Prop) (h : p ∧ q) : p := And.elim (fun _ hq => hq) h\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "And.elim (fun _ hq => hq) : p ∧ q → q, not p — goal p must be rejected"
    );
    // `Or.elim h f g` demands both branch functions land in the goal; a branch
    // returning the wrong disjunct is rejected.
    let bad2 = "theorem t (p q : Prop) (h : p ∨ q) : q ∨ p := Or.elim h (fun hp => Or.inl hp) (fun hq => Or.inr hq)\n";
    assert!(
        elab_file_prelude(bad2).1.iter().any(|x| x.is_err()),
        "branches must produce `q ∨ p`; `Or.inl hp : p ∨ _` is wrong and must be rejected"
    );
}

// ---------------------------------------------------------------------------
// `Iff.elim` applied (round-40, follows brick 60). Absent from Clean's prelude
// (`Iff.mp`/`Iff.mpr` present); `Iff.elim f h` ⇝ `f h.mp h.mpr`.
// ---------------------------------------------------------------------------

#[test]
fn test_iff_elim_applied() {
    let code = "theorem fwd (a b : Prop) (h : a ↔ b) (ha : a) : b := Iff.elim (fun mp _ => mp ha) h\n\
                theorem bwd (a b : Prop) (h : a ↔ b) (hb : b) : a := Iff.elim (fun _ mpr => mpr hb) h\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Iff.elim applied");
    assert!(env.get_const(&Name::from_string("fwd")).is_some());
}

#[test]
fn test_iff_elim_soundness() {
    // `fun mp _ => mp ha` gives `b` from `a ↔ b`; used for goal `a` it is wrong.
    let bad = "theorem t (a b : Prop) (h : a ↔ b) (ha : a) : a := Iff.elim (fun mp _ => mp ha) h\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "`mp ha : b`, so proving goal `a` with it must be rejected"
    );
}

// ---------------------------------------------------------------------------
// General fully-applied untyped-binder lambda (round-40). Extends the brick-59
// `·`-section rewrite to any `(fun a b … => body) x y …`: the arguments pin each
// binder's type before the body elaborates, so an arithmetic body no longer
// UInt64-defaults and a binder used as a function head no longer fails. This is
// what unblocks the `Iff.elim` desugar (`f h.mp h.mpr` with an untyped `f`).
// ---------------------------------------------------------------------------

#[test]
fn test_general_untyped_binder_lambda_applied() {
    let code = "def p : Nat × Nat := (3, 4)\n\
                theorem arith : ((fun a b => a + b) p.1 p.2) = 7 := rfl\n\
                theorem fnhead : ((fun f x => f x) (fun n => n + 1) 10) = 11 := rfl\n\
                theorem single : ((fun x => x * x) 5) = 25 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "general untyped-binder lambda applied");
    // Soundness: value is 7, not 8.
    assert!(
        elab_file_prelude(
            "def p : Nat × Nat := (3, 4)\ntheorem t : ((fun a b => a + b) p.1 p.2) = 8 := rfl\n"
        )
        .1
        .iter()
        .any(|x| x.is_err()),
        "3+4 is 7, not 8"
    );
}

// ---------------------------------------------------------------------------
// `Not.elim`/`Sum.elim` applied (round-41). Both absent from Clean's prelude.
// `Not.elim h ha` ⇝ `absurd ha h`; `Sum.elim f g s` ⇝
// `match s with | Sum.inl a => f a | Sum.inr b => g b` (scrutinee is last).
// ---------------------------------------------------------------------------

#[test]
fn test_not_elim_and_sum_elim() {
    let code = "theorem ne (p q : Prop) (hp : p) (hnp : ¬p) : q := Not.elim hnp hp\n\
                theorem nf (p : Prop) (hp : p) (hnp : ¬p) : False := Not.elim hnp hp\n\
                theorem se_l : (Sum.elim (fun n => n + 1) (fun n => n * 2) (Sum.inl 5 : Nat ⊕ Nat)) = 6 := rfl\n\
                theorem se_r : (Sum.elim (fun n => n + 1) (fun n => n * 2) (Sum.inr 5 : Nat ⊕ Nat)) = 10 := rfl\n\
                def se_swap (s : Nat ⊕ String) := Sum.elim (fun n => Sum.inr n) (fun str => Sum.inl str) s\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Not.elim / Sum.elim applied");
    assert!(env.get_const(&Name::from_string("ne")).is_some());
}

#[test]
fn test_sum_elim_soundness() {
    // Sum.elim on inl selects the first function: (inl 5) → 5+1 = 6, not 10.
    let bad = "theorem t : (Sum.elim (fun n => n + 1) (fun n => n * 2) (Sum.inl 5 : Nat ⊕ Nat)) = 10 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "Sum.inl 5 selects the first branch (5+1=6), not the second (10)"
    );
}

// ---------------------------------------------------------------------------
// `first | t1 | t2` backtracks when an earlier branch's ATTEMPT fails (round-42).
// `first | rfl | exact h` used to propagate `rfl`'s `TypeMismatch` on a
// non-equality goal instead of falling through to `exact h`; `first` now treats a
// failed term-elaboration (rfl/exact type mismatch, unknown ident, …) as a
// recoverable branch failure, matching Lean 4.
// ---------------------------------------------------------------------------

#[test]
fn test_first_backtracks_on_failed_branch() {
    let code = "theorem a (p : Prop) (hp : p) : p := by first | rfl | exact hp\n\
                theorem b (p : Prop) (hp : p) : p := by first | rfl | assumption | exact hp\n\
                theorem c (p : Prop) (hp : p) : p := by first | exact absurdlyNamedMissing | exact hp\n\
                theorem d : 2 + 2 = 4 := by first | assumption | exact hp | rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "first backtracks past a failed earlier branch");
    assert!(env.get_const(&Name::from_string("a")).is_some());
}

#[test]
fn test_first_all_branches_fail_still_errors() {
    // When EVERY branch fails, `first` must still report an error (not silently
    // succeed): `rfl` and a wrong `exact` both fail to prove `p`.
    let bad = "theorem t (p q : Prop) (hq : q) : p := by first | rfl | exact hq\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "all branches fail (no proof of `p`) — `first` must error, not succeed"
    );
}

// ---------------------------------------------------------------------------
// A patternless no-argument tactic (`skip`, `done`, …) no longer swallows the
// following newline-separated tactic (round-43). `by skip⏎ exact h` used to parse
// `skip` consuming `exact h` (patternless arg parser read across the newline),
// dropping it and leaving the goal unsolved.
// ---------------------------------------------------------------------------

#[test]
fn test_nullary_tactic_does_not_swallow_next() {
    let code = "theorem a (p : Prop) (hp : p) : p := by\n  skip\n  exact hp\n\
                theorem b : 2 + 2 = 4 := by\n  skip\n  rfl\n\
                theorem c (p : Prop) : p → p := by\n  intro h\n  skip\n  exact h\n\
                theorem d (p : Prop) (hp : p) : p := by\n  skip\n  skip\n  exact hp\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "skip does not swallow the next newline tactic");
    assert!(env.get_const(&Name::from_string("a")).is_some());
}

#[test]
fn test_nullary_tactic_soundness() {
    // The following tactic still actually runs: omitting it leaves the goal open.
    let bad = "theorem t (p : Prop) (hp : p) : p := by\n  skip\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "`skip` alone does not prove `p` — must be unsolved"
    );
    // And the next tactic must match the goal: a wrong `exact` is still rejected.
    let bad2 = "theorem t (p q : Prop) (hp : p) (hq : q) : p := by\n  skip\n  exact hq\n";
    assert!(
        elab_file_prelude(bad2).1.iter().any(|x| x.is_err()),
        "`exact hq : q` cannot prove goal `p` even after `skip`"
    );
}

// ---------------------------------------------------------------------------
// Tactic-block indentation + `·` bullet focus (round-43 verification lock). A
// tactic block's continuation must ALIGN with the first tactic's column (Lean 4
// whitespace-sensitivity): an aligned continuation is part of the block, a
// lesser-indented one terminates it. `·` bullets after `constructor`/`refine`
// focus each produced goal. These were verified after the brick-63/64 tactic
// fixes; this pins the whitespace + bullet semantics.
// ---------------------------------------------------------------------------

#[test]
fn test_tactic_block_indentation_and_bullets() {
    // `by <tac1>` on one line, continuation ALIGNED under the first tactic.
    let aligned = "theorem t (p : Prop) : p → p :=\nby intro h\n   exact h\n";
    assert!(
        elab_file_prelude(aligned).1.iter().all(|x| x.is_ok()),
        "aligned by-line continuation is part of the block"
    );
    // `·` bullets after constructor / refine focus each goal.
    let bullets = "theorem c (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  · exact hp\n  · exact hq\n\
                   theorem r (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  refine ⟨?_, ?_⟩\n  · exact hp\n  · exact hq\n";
    assert!(
        elab_file_prelude(bullets).1.iter().all(|x| x.is_ok()),
        "constructor/refine + `·` bullets focus each goal"
    );
}

#[test]
fn test_tactic_block_misaligned_terminates() {
    // A continuation at a LESSER column than the first tactic terminates the
    // block (Lean-4 whitespace): only `intro h` runs, so the goal is unsolved.
    let misaligned = "theorem t (p : Prop) : p → p :=\nby intro h\n  exact h\n";
    assert!(
        elab_file_prelude(misaligned).1.iter().any(|x| x.is_err()),
        "a lesser-indented continuation is outside the block — goal stays open"
    );
}

// ---------------------------------------------------------------------------
// Round-45 verification lock: multi-class `deriving`, non-decimal numeric
// literals, recursive `match`-in-body, and `for`-in-`do` with `mut`. A fresh
// gap-mine verified these elaborate + reduce with Lean-4 semantics; this pins
// them. (The round's failures were co-tenant/large: `[a:b]` ranges, `while` in
// do, `Nat.gcd`/`Array.push`/`Option.filter`/`List.flatMap` absent consts.)
// ---------------------------------------------------------------------------

#[test]
fn test_numeric_bases_and_multi_deriving() {
    let code = "structure Pt where\n  x : Nat\nderiving Repr, BEq\n\
                theorem d_beq : ((⟨5⟩ : Pt) == ⟨5⟩) = true := rfl\n\
                theorem hex : (0xff : Nat) = 255 := rfl\n\
                theorem bin : (0b1010 : Nat) = 10 := rfl\n\
                theorem oct : (0o17 : Nat) = 15 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "multi-class deriving + hex/bin/oct literals");
    // Soundness: 0xff is 255, not 254.
    assert!(
        elab_file_prelude("theorem t : (0xff : Nat) = 254 := rfl\n")
            .1
            .iter()
            .any(|x| x.is_err()),
        "0xff is 255, not 254"
    );
}

#[test]
fn test_recursive_match_body_and_for_do() {
    let code = "def cnt (n : Nat) : Nat := match n with\n  | 0 => 0\n  | m + 1 => 1 + cnt m\n\
                theorem c : cnt 5 = 5 := rfl\n\
                def sumUp : Nat := Id.run do\n  let mut s := 0\n  for i in [1, 2, 3, 4] do\n    s := s + i\n  return s\n\
                theorem s : sumUp = 10 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "recursive match-in-body + for-in-do with mut");
    // Soundness: the recursion actually counts — cnt 5 is 5, not 4.
    assert!(
        elab_file_prelude("def cnt (n : Nat) : Nat := match n with\n  | 0 => 0\n  | m + 1 => 1 + cnt m\ntheorem t : cnt 5 = 4 := rfl\n")
            .1.iter().any(|x| x.is_err()),
        "cnt 5 = 5, not 4"
    );
}

// ---------------------------------------------------------------------------
// Round-46 verification lock: character/string escape sequences, digit-group
// underscore literals, and `Sigma` construction + projection. Verified to
// elaborate + reduce with Lean-4 semantics. (Round failures were niche/co-tenant:
// `×'` PSigma notation parse gap; `String.push` absent const. And the recursion
// edge `| n + 2 => …` is a DELIBERATE fail-closed limit — needs course-of-values
// recursion, a large subsystem.)
// ---------------------------------------------------------------------------

#[test]
fn test_escapes_underscore_literals_and_sigma() {
    let code = "theorem nl : ('\\n'.toNat) = 10 := rfl\n\
                theorem tab : ('\\t'.toNat) = 9 := rfl\n\
                theorem str : (\"a\\tb\".length) = 3 := rfl\n\
                theorem us : (1_000_000 : Nat) = 1000000 := rfl\n\
                theorem sfst : ((⟨3, 4⟩ : Σ _ : Nat, Nat).1) = 3 := rfl\n\
                theorem ssnd : ((⟨3, 4⟩ : Σ _ : Nat, Nat).2) = 4 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "escapes + underscore literals + Sigma mk/proj");
    // Soundness: '\n' is 10, not 11; and the underscore literal is 1000000, not off-by-one.
    assert!(
        elab_file_prelude("theorem t : ('\\n'.toNat) = 11 := rfl\n")
            .1
            .iter()
            .any(|x| x.is_err()),
        "'\\n'.toNat is 10, not 11"
    );
    assert!(
        elab_file_prelude("theorem t : (1_000_000 : Nat) = 1000001 := rfl\n")
            .1
            .iter()
            .any(|x| x.is_err()),
        "1_000_000 is 1000000, not 1000001"
    );
}

// ---------------------------------------------------------------------------
// `×'` PSigma notation (round-47). `(x : T) ×' B` already worked; `(_ : T) ×' B`
// (anonymous `_` binder — how Lean pretty-prints a non-dependent PSigma) and the
// bare `A ×' B` form did not parse. Now both desugar to `PSigma (fun _ : A => B)`.
// ---------------------------------------------------------------------------

#[test]
fn test_psigma_prime_notation() {
    let code = "theorem u1 : ((⟨3, 4⟩ : (_ : Nat) ×' Nat).1) = 3 := rfl\n\
                theorem u2 : ((⟨3, 4⟩ : (_ : Nat) ×' Nat).2) = 4 := rfl\n\
                theorem b1 : ((⟨3, 4⟩ : Nat ×' Nat).1) = 3 := rfl\n\
                theorem b2 : ((⟨3, 4⟩ : Nat ×' Nat).2) = 4 := rfl\n\
                theorem named : ((⟨3, 4⟩ : (x : Nat) ×' Nat).1) = 3 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "×' PSigma notation (underscore / bare / named / dependent)",
    );
    assert!(env.get_const(&Name::from_string("u1")).is_some());
}

#[test]
fn test_psigma_prime_soundness() {
    // `.1` of `⟨3, 4⟩` is 3, not 4.
    let bad = "theorem t : ((⟨3, 4⟩ : Nat ×' Nat).1) = 4 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|x| x.is_err()),
        "the first PSigma component of ⟨3, 4⟩ is 3, not 4"
    );
    // `A ×' B` is PSigma, NOT Prod: a Prod-only proof about it should not spuriously pass;
    // the value still round-trips to 3 via PSigma.fst.
    assert!(
        elab_file_prelude("theorem t : ((⟨5, 6⟩ : Nat ×' Nat).2) = 7 := rfl\n")
            .1
            .iter()
            .any(|x| x.is_err()),
        "second component of ⟨5, 6⟩ is 6, not 7"
    );
}

// ---------------------------------------------------------------------------
// `suffices _ : t by tac` — anonymous (`_`) binder name in a tactic-mode
// `suffices`. Lean's `binderIdent` is `ident | "_"`, but `_` lexes to an
// `Underscore` token, so the tactic parser (which only ate `Ident` for the
// name) hit the colon expect on `_` and failed to parse. The named form
// (`suffices h : t by tac`) and the nameless form (`suffices : t by tac`)
// already parsed — only the explicit `_` binder was rejected.
// ---------------------------------------------------------------------------

#[test]
fn test_suffices_underscore_binder() {
    // Anonymous `_` binder: `rfl` discharges the main goal (2+2=4) with the
    // unused `_ : True` in scope; `trivial` then closes the residual `True`.
    let code = "theorem t : 2 + 2 = 4 := by\n  suffices _ : True by rfl\n  trivial\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "suffices _ : True by rfl (anonymous binder)");
    assert!(
        env.get_const(&Name::from_string("t")).is_some(),
        "theorem t should be registered and kernel-checked"
    );

    // Regression: the named and nameless forms must still parse and prove.
    let named = "theorem t : 2 + 2 = 4 := by\n  suffices h : True by rfl\n  trivial\n";
    assert_all_ok(
        &elab_file_prelude(named).1,
        "suffices h : True by rfl (named binder, regression)",
    );
    let nameless = "theorem t : 2 + 2 = 4 := by\n  suffices : True by rfl\n  trivial\n";
    assert_all_ok(
        &elab_file_prelude(nameless).1,
        "suffices : True by rfl (nameless, regression)",
    );
}

#[test]
fn test_suffices_underscore_binder_soundness() {
    // The parse fix must NOT weaken checking: a FALSE main goal is still
    // rejected loud. `rfl` cannot prove `2 + 2 = 5`, so the `suffices _`
    // proof must fail even though the residual `True` is trivially closed.
    let code = "theorem bad : 2 + 2 = 5 := by\n  suffices _ : True by rfl\n  trivial\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "suffices _ : True by rfl must not prove the false goal 2 + 2 = 5"
    );
}

// ---------------------------------------------------------------------------
// Anonymous-constructor pattern `⟨a, b, c⟩` destructuring a single-constructor
// STRUCTURE with N ≥ 3 flat fields. The parser desugars `⟨…⟩` to a right-nested
// binary `Prod.mk`, which lines up with `Prod`/`Sigma` (N = 2) but not a flat
// N-ary structure constructor — so `match x with | ⟨a, b, c⟩ =>` on a 3-field
// structure failed ("cannot extract type name") while the equivalent named
// pattern `| T3.mk a b c =>` and structure projections both worked.
// ---------------------------------------------------------------------------

#[test]
fn test_anon_ctor_pattern_structure_arity3() {
    // Value-distinguishing: the three fields bind in order and sum to 6.
    let code = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                def f (x : T3) : Nat := match x with | \u{27e8}a, b, c\u{27e9} => a + b + c\n\
                theorem t : f \u{27e8}1, 2, 3\u{27e9} = 6 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "match | ⟨a, b, c⟩ => on a 3-field structure");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered and kernel-checked"
    );

    // Field ORDER is respected (not just the sum): weight the fields distinctly.
    let ordered = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                   def g (x : T3) : Nat := match x with | \u{27e8}a, b, c\u{27e9} => a + 10 * b + 100 * c\n\
                   theorem t : g \u{27e8}1, 2, 3\u{27e9} = 321 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(ordered).1,
        "⟨a, b, c⟩ binds fields in order",
    );

    // Arity 4 (deeper right-nested spine) also flattens.
    let four = "structure T4 where\n  a : Nat\n  b : Nat\n  c : Nat\n  d : Nat\n\
                def h (x : T4) : Nat := match x with | \u{27e8}a, b, c, d\u{27e9} => a + b + c + d\n\
                theorem t : h \u{27e8}1, 2, 3, 4\u{27e9} = 10 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(four).1,
        "match | ⟨a, b, c, d⟩ => on a 4-field structure",
    );
}

#[test]
fn test_anon_ctor_pattern_structure_soundness() {
    // The remap+flatten must not weaken checking: a wrong projected value is
    // rejected loud. `⟨1, 2, 3⟩.a + .b + .c = 6`, so `= 7` must fail.
    let code = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                def f (x : T3) : Nat := match x with | \u{27e8}a, b, c\u{27e9} => a + b + c\n\
                theorem bad : f \u{27e8}1, 2, 3\u{27e9} = 7 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "⟨a, b, c⟩ destructuring must still reject the wrong value 7 (1+2+3=6)"
    );

    // A genuine Prod anon-ctor pattern (N = 2, right-nested) is untouched and
    // still works at arity 3 via the type's own nesting.
    let prod = "def p (x : Nat \u{00d7} Nat \u{00d7} Nat) : Nat := match x with | \u{27e8}a, b, c\u{27e9} => a + b + c\n\
                theorem t : p (1, 2, 3) = 6 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(prod).1,
        "Prod anon-ctor pattern still works (regression)",
    );
}

// ---------------------------------------------------------------------------
// Anonymous-constructor pattern `⟨a, b⟩` destructuring a 2-field NATIVE
// STRUCTURE. `⟨…⟩` desugars to a binary `Prod.mk`, which the placeholder path
// mishandled for a plain user structure (shape-unification "Discriminant 2 vs
// 3") even though it lines up arity-wise — the remap now resolves it to the
// real `T2.mk` (a native structure has a field-name table, distinguishing it
// from `And`/`Exists`/`Iff`, which keep the placeholder path).
// ---------------------------------------------------------------------------

#[test]
fn test_anon_ctor_pattern_structure_arity2() {
    // Value-distinguishing + field order: weight the two fields distinctly.
    let code = "structure T2 where\n  a : Nat\n  b : Nat\n\
                def f (x : T2) : Nat := match x with | \u{27e8}a, b\u{27e9} => a + 10 * b\n\
                theorem t : f \u{27e8}3, 4\u{27e9} = 43 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "match | ⟨a, b⟩ => on a 2-field structure");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered and kernel-checked"
    );

    // The `fun ⟨a, b⟩ =>` sugar (desugars to the same match) also works.
    let fun_form = "structure T2 where\n  a : Nat\n  b : Nat\n\
                    def g : T2 \u{2192} Nat := fun \u{27e8}a, b\u{27e9} => a + 10 * b\n\
                    theorem t : g \u{27e8}3, 4\u{27e9} = 43 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(fun_form).1,
        "fun ⟨a, b⟩ => on a 2-field structure",
    );

    // Soundness: a wrong projected value is still rejected (3 + 10*4 = 43 ≠ 40).
    let bad = "structure T2 where\n  a : Nat\n  b : Nat\n\
               def f (x : T2) : Nat := match x with | \u{27e8}a, b\u{27e9} => a + 10 * b\n\
               theorem bad : f \u{27e8}3, 4\u{27e9} = 40 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "2-field ⟨a, b⟩ destructuring must reject the wrong value 40"
    );
}

#[test]
fn test_anon_ctor_pattern_n2_builtins_regression() {
    // The N = 2 extension must not disturb the built-in 2-field shapes. `And`
    // (no field table) keeps the placeholder path; `Sigma`/`Subtype` (field
    // table) are remapped to their real ctor, whose lowering is identical.
    let and_case =
        "theorem t (h : True \u{2227} True) : True := match h with | \u{27e8}a, _b\u{27e9} => a\n";
    assert_all_ok(&elab_file_prelude(and_case).1, "And ⟨a, b⟩ still works");

    let sigma = "def f (s : Sigma (fun _ : Nat => Nat)) : Nat := match s with | \u{27e8}a, b\u{27e9} => a + b\n\
                 theorem t : f \u{27e8}3, 4\u{27e9} = 7 := rfl\n";
    assert_all_ok(&elab_file_prelude(sigma).1, "Sigma ⟨a, b⟩ still works");

    let subtype =
        "def f (s : {n : Nat // n = n}) : Nat := match s with | \u{27e8}a, _h\u{27e9} => a\n\
                   theorem t : f \u{27e8}5, rfl\u{27e9} = 5 := rfl\n";
    assert_all_ok(&elab_file_prelude(subtype).1, "Subtype ⟨a, h⟩ still works");
}

// ---------------------------------------------------------------------------
// LOCK (round 51): nested anonymous-constructor destructuring — `⟨a, ⟨x, y⟩⟩`
// where the second field is itself a structure — exercises the brick-67/68
// remap in a NESTED position (the inner `⟨x, y⟩` matches the field structure).
// Also locks multi-discriminant anon-ctor patterns `match p, q with | ⟨a,b⟩,
// ⟨c,d⟩ =>`. Both value-verified; a regression guard for the anon-ctor family.
// ---------------------------------------------------------------------------

#[test]
fn test_anon_ctor_pattern_nested_struct() {
    // `⟨a, ⟨x, y⟩⟩` on `Nested { a : Nat, p : Pair }` binds a, x, y in order.
    let code = "structure Pair where\n  x : Nat\n  y : Nat\n\
                structure Nested where\n  a : Nat\n  p : Pair\n\
                def f (n : Nested) : Nat := match n with | \u{27e8}a, \u{27e8}x, y\u{27e9}\u{27e9} => a + 10 * x + 100 * y\n\
                theorem t : f \u{27e8}1, \u{27e8}2, 3\u{27e9}\u{27e9} = 321 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested anon-ctor pattern ⟨a, ⟨x, y⟩⟩");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered and kernel-checked"
    );

    // Soundness: wrong value rejected (1 + 20 + 300 = 321 ≠ 320).
    let bad = "structure Pair where\n  x : Nat\n  y : Nat\n\
               structure Nested where\n  a : Nat\n  p : Pair\n\
               def f (n : Nested) : Nat := match n with | \u{27e8}a, \u{27e8}x, y\u{27e9}\u{27e9} => a + 10 * x + 100 * y\n\
               theorem bad : f \u{27e8}1, \u{27e8}2, 3\u{27e9}\u{27e9} = 320 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "nested ⟨a, ⟨x, y⟩⟩ must reject the wrong value 320"
    );
}

#[test]
fn test_anon_ctor_pattern_multi_discriminant() {
    // Two anon-ctor patterns across a multi-discriminant match.
    let code = "def f (p : Nat \u{00d7} Nat) (q : Nat \u{00d7} Nat) : Nat := \
                match p, q with | \u{27e8}a, b\u{27e9}, \u{27e8}c, d\u{27e9} => a + 10 * b + 100 * c + 1000 * d\n\
                theorem t : f (1, 2) (3, 4) = 4321 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "multi-discriminant anon-ctor patterns ⟨a,b⟩, ⟨c,d⟩",
    );

    // Soundness: wrong value rejected.
    let bad = "def f (p : Nat \u{00d7} Nat) (q : Nat \u{00d7} Nat) : Nat := \
               match p, q with | \u{27e8}a, b\u{27e9}, \u{27e8}c, d\u{27e9} => a + 10 * b + 100 * c + 1000 * d\n\
               theorem bad : f (1, 2) (3, 4) = 4320 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "multi-discriminant anon-ctor must reject the wrong value 4320"
    );
}

// ---------------------------------------------------------------------------
// `let ⟨a, b, c⟩ := e; body` destructuring a STRUCTURE. The `⟨…⟩` let form was
// desugared to `Prod.fst`/`Prod.snd` projections, which assume a `Prod` and
// failed ("expected Prod") on a non-`Prod` structure — even though the
// equivalent `match e with | ⟨a, b, c⟩ =>` worked. It now desugars to a
// single-arm match, routing through the anon-ctor remap.
// ---------------------------------------------------------------------------

#[test]
fn test_let_anon_ctor_destructure_structure() {
    // N = 3 structure, field-order-weighted.
    let code = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                def f : Nat := let \u{27e8}a, b, c\u{27e9} := (\u{27e8}1, 2, 3\u{27e9} : T3); a + 10 * b + 100 * c\n\
                theorem t : f = 321 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "let ⟨a, b, c⟩ := (… : T3) destructure");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered and kernel-checked"
    );

    // N = 2 structure.
    let two = "structure T2 where\n  a : Nat\n  b : Nat\n\
               def f : Nat := let \u{27e8}a, b\u{27e9} := (\u{27e8}3, 4\u{27e9} : T2); a + 10 * b\n\
               theorem t : f = 43 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(two).1,
        "let ⟨a, b⟩ := (… : T2) destructure",
    );

    // Soundness: wrong value rejected (1 + 20 + 300 = 321 ≠ 320).
    let bad = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
               def f : Nat := let \u{27e8}a, b, c\u{27e9} := (\u{27e8}1, 2, 3\u{27e9} : T3); a + 10 * b + 100 * c\n\
               theorem bad : f = 320 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "let ⟨a, b, c⟩ destructure must reject the wrong value 320"
    );
}

#[test]
fn test_let_anon_ctor_destructure_prod_regression() {
    // The `⟨…⟩` change must not regress a Prod scrutinee (still works via the
    // match desugar) and the `(…)` tuple form (still uses Prod projections).
    let angle_prod = "def f : Nat := let \u{27e8}a, b\u{27e9} := (3, 4); a + 10 * b\n\
                      theorem t : f = 43 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(angle_prod).1,
        "let ⟨a, b⟩ := prod (regression)",
    );

    let paren_prod = "def f : Nat := let (a, b) := (3, 4); a + 10 * b\n\
                      theorem t : f = 43 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(paren_prod).1,
        "let (a, b) := prod (regression)",
    );

    // 3-element Prod via angle form.
    let angle_prod3 =
        "def f : Nat := let \u{27e8}a, b, c\u{27e9} := (1, 2, 3); a + 10 * b + 100 * c\n\
                       theorem t : f = 321 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(angle_prod3).1,
        "let ⟨a, b, c⟩ := prod3 (regression)",
    );
}

// ---------------------------------------------------------------------------
// `rcases`/`obtain`/`rintro ⟨a, b, c⟩` destructuring a user STRUCTURE. The
// rintro/rcases engine's "destructible" check was a hardcoded allow-list
// (And/Exists/Sigma/Prod/PProd), so a user `structure` — a genuine
// single-constructor inductive that `cases` and named `| mk … =>` patterns
// already destructure — was wrongly reported "not destructurable". The check
// now also admits any native structure (via its field table).
// ---------------------------------------------------------------------------

#[test]
fn test_rcases_obtain_structure_destructure() {
    // `obtain ⟨a, b, c⟩` on a 3-field structure, field-order-weighted.
    let obtain = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                  def f (h : T3) : Nat := by obtain \u{27e8}a, b, c\u{27e9} := h; exact a + 10 * b + 100 * c\n\
                  theorem t : f \u{27e8}1, 2, 3\u{27e9} = 321 := rfl\n";
    let (env, results) = elab_file_prelude(obtain);
    assert_all_ok(&results, "obtain ⟨a, b, c⟩ on a 3-field structure");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered and kernel-checked"
    );

    // `rcases … with` and `rintro` forms.
    let rcases = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                  def f (h : T3) : Nat := by rcases h with \u{27e8}a, b, c\u{27e9}; exact a + 10 * b + 100 * c\n\
                  theorem t : f \u{27e8}1, 2, 3\u{27e9} = 321 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(rcases).1,
        "rcases h with ⟨a, b, c⟩ on a structure",
    );
    let rintro = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
                  def f : T3 \u{2192} Nat := by rintro \u{27e8}a, b, c\u{27e9}; exact a + 10 * b + 100 * c\n\
                  theorem t : f \u{27e8}1, 2, 3\u{27e9} = 321 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(rintro).1,
        "rintro ⟨a, b, c⟩ on a structure",
    );

    // Nested: `obtain ⟨a, x, y⟩` flattens into the `Pair` field.
    let nested = "structure Pair where\n  x : Nat\n  y : Nat\n\
                  structure Nested where\n  a : Nat\n  p : Pair\n\
                  def f (h : Nested) : Nat := by obtain \u{27e8}a, x, y\u{27e9} := h; exact a + 10 * x + 100 * y\n\
                  theorem t : f \u{27e8}1, \u{27e8}2, 3\u{27e9}\u{27e9} = 321 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(nested).1,
        "obtain ⟨a, x, y⟩ nested through a Pair field",
    );
}

#[test]
fn test_rcases_obtain_structure_soundness() {
    // The relaxed destructible check must not weaken proving: a wrong value is
    // still rejected (1 + 20 + 300 = 321 ≠ 320).
    let bad = "structure T3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
               def f (h : T3) : Nat := by obtain \u{27e8}a, b, c\u{27e9} := h; exact a + 10 * b + 100 * c\n\
               theorem bad : f \u{27e8}1, 2, 3\u{27e9} = 320 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "obtain ⟨a, b, c⟩ destructure must reject the wrong value 320"
    );

    // Regression: obtain on And/Exists/Prod still works (the hardcoded
    // connectives are unchanged).
    let and_case = "theorem t (h : True \u{2227} True) : True := by obtain \u{27e8}a, _b\u{27e9} := h; exact a\n";
    assert_all_ok(
        &elab_file_prelude(and_case).1,
        "obtain ⟨a, b⟩ on And (regression)",
    );
    let exists_case = "theorem t (h : \u{2203} n : Nat, n = 5) : True := by obtain \u{27e8}_w, _hw\u{27e9} := h; exact True.intro\n";
    assert_all_ok(
        &elab_file_prelude(exists_case).1,
        "obtain ⟨w, hw⟩ on Exists (regression)",
    );
    let prod_case =
        "def f (h : Nat \u{00d7} Nat) : Nat := by obtain \u{27e8}a, b\u{27e9} := h; exact a + b\n\
                     theorem t : f (3, 4) = 7 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(prod_case).1,
        "obtain ⟨a, b⟩ on Prod (regression)",
    );
}

// ---------------------------------------------------------------------------
// `bif c then t else e` — Lean 4's Bool conditional (`Init/Prelude`), sugar for
// `cond c t e`. Unlike `if`, it needs no `Decidable` instance. It was unhandled
// (`bif` lexed as a plain identifier → UnknownIdent); it now parses to an
// application of the `cond` combinator.
// ---------------------------------------------------------------------------

#[test]
fn test_bif_bool_conditional() {
    // Value-distinguishing: true → then, false → else (weighted branches).
    let code = "def f (b : Bool) : Nat := bif b then 10 else 20\n\
                theorem t1 : f true = 10 := rfl\n\
                theorem t2 : f false = 20 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "bif b then 10 else 20");
    assert!(
        env.get_const(&Name::from_string("f")).is_some(),
        "f should be registered and kernel-checked"
    );

    // `bif` on a literal reduces, and nests.
    let nested = "def g : Nat := bif true then (bif false then 1 else 2) else 3\n\
                  theorem t : g = 2 := rfl\n";
    assert_all_ok(&elab_file_prelude(nested).1, "nested bif reduces to 2");
}

#[test]
fn test_bif_bool_conditional_soundness() {
    // The desugaring must preserve `cond`'s branch semantics: `bif true` takes
    // the THEN branch, so `f true = 20` (the else value) must be rejected.
    let code = "def f (b : Bool) : Nat := bif b then 10 else 20\n\
                theorem bad : f true = 20 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "bif true then 10 else 20 must be 10, not 20"
    );
}

// ---------------------------------------------------------------------------
// `(·.1)` — a `·`-section with a NUMERIC projection. The lexer treated the
// `.1` after `·` as a leading-dot float (`0.1`), so `(·.1)` desugared to
// `fun x => x 0.1` (an application) and failed; `(·.snd)` (named projection)
// worked. `·` now counts as an expression boundary, so `·.1` is a projection.
// ---------------------------------------------------------------------------

#[test]
fn test_cdot_numeric_projection_section() {
    // `(·.1)`/`(·.2)` applied — value-distinguishing on which field is picked.
    let one = "theorem t : ((\u{00b7}.1) (3, 4)) = 3 := rfl\n";
    assert_all_ok(&elab_file_prelude(one).1, "(·.1) (3, 4) = 3");
    let two = "theorem t : ((\u{00b7}.2) (3, 4)) = 4 := rfl\n";
    assert_all_ok(&elab_file_prelude(two).1, "(·.2) (3, 4) = 4");

    // Ascribed section and `List.map (·.1)` — the common Mathlib idiom.
    let ascribed =
        "def f : Nat \u{00d7} Nat \u{2192} Nat := (\u{00b7}.1)\ntheorem t : f (3, 4) = 3 := rfl\n";
    assert_all_ok(&elab_file_prelude(ascribed).1, "def f := (·.1)");
    let mapped = "def f : List (Nat \u{00d7} Nat) := [(1, 2), (3, 4)]\ntheorem t : (f.map (\u{00b7}.1)) = [1, 3] := rfl\n";
    assert_all_ok(&elab_file_prelude(mapped).1, "f.map (·.1) = [1, 3]");

    // Named projection section still works (regression).
    let named = "theorem t : ((\u{00b7}.snd) (3, 4)) = 4 := rfl\n";
    assert_all_ok(&elab_file_prelude(named).1, "(·.snd) still works");
}

#[test]
fn test_cdot_numeric_projection_soundness() {
    // The section picks field 1, so `(·.1) (3, 4) = 4` (the second field) must
    // be rejected — the fix must not accept the wrong projection.
    let bad = "theorem bad : ((\u{00b7}.1) (3, 4)) = 4 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "(·.1) selects field 1 (=3), so `= 4` must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Bare `not` — Lean 4's `Init/Prelude` root export for `Bool.not`. Clean
// registered `Bool.not` but not the bare alias, so `not b` was `UnknownIdent`
// (or `TooManyArguments` once applied). Resolved on-demand to `Bool.not`
// (same shape as `default`→`Inhabited.default` and `cond`).
// ---------------------------------------------------------------------------

#[test]
fn test_bare_not_alias() {
    // Value-distinguishing: `not true = false`, `not false = true`.
    let code = "theorem t1 : not true = false := rfl\ntheorem t2 : not false = true := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "not true = false / not false = true",
    );

    // Applied/nested + used in a recursive Bool def (the original probe shape).
    let nested = "theorem t : not (not true) = true := rfl\n";
    assert_all_ok(&elab_file_prelude(nested).1, "not (not true) = true");
    let rec = "def even : Nat \u{2192} Bool\n  | 0 => true\n  | n+1 => not (even n)\ntheorem t : even 10 = true := rfl\n";
    assert_all_ok(&elab_file_prelude(rec).1, "recursive even using `not`");
}

#[test]
fn test_bare_not_alias_soundness() {
    // `not true = true` must be rejected (the alias must resolve to real
    // `Bool.not`, not silently accept).
    let bad = "theorem bad : not true = true := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "not true = false, so `not true = true` must be rejected"
    );

    // A user-defined `not` still wins over the alias.
    let shadow = "def not (n : Nat) : Nat := n + 1\ntheorem t : not 5 = 6 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(shadow).1,
        "user `def not` shadows the Bool.not alias",
    );
}

// ---------------------------------------------------------------------------
// LOCK (round 57): nested list/constructor patterns that DO destructure and
// reduce — single-level nested ctor (`some x :: _`), a var element at the 2nd
// cons position (`some x :: _ :: _`), a var cons (`x :: y :: _`), and a plain
// Option match. Constructor patterns at the 2nd+ cons position are covered by
// the curried-nesting regression family below. These locks guard the original
// working shapes against regression.
// ---------------------------------------------------------------------------

#[test]
fn test_nested_list_patterns_working_lock() {
    // Single-level nested ctor: the tail is a var, so the element ctor `some x`
    // is the only nested casesOn — value-distinguishing.
    let one = "def f : List (Option Nat) \u{2192} Nat\n  | some x :: _ => x + 100\n  | _ => 0\n\
               theorem t : f [some 5] = 105 := rfl\n";
    assert_all_ok(&elab_file_prelude(one).1, "some x :: _ nested ctor element");

    // Var element at the 2nd cons position (no nested ctor there).
    let varelem =
        "def f : List (Option Nat) \u{2192} Nat\n  | some x :: _ :: _ => x + 10\n  | _ => 0\n\
                   theorem t : f [some 5, none] = 15 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(varelem).1,
        "some x :: _ :: _ var element",
    );

    // Var cons (two variable elements).
    let varcons = "def f : List Nat \u{2192} Nat\n  | x :: y :: _ => x + 10 * y\n  | _ => 0\n\
                   theorem t : f [3, 4, 5] = 43 := rfl\n";
    assert_all_ok(&elab_file_prelude(varcons).1, "x :: y :: _ var cons");

    // Plain Option match reduces.
    let opt = "def f : Option Nat \u{2192} Nat\n  | some x => x + 1\n  | none => 0\n\
               theorem t : f (some 5) = 6 := rfl\n";
    assert_all_ok(&elab_file_prelude(opt).1, "plain Option match");

    // Soundness on a working shape: `some x :: _ => x + 100`, so `f [some 5] = 5` (wrong) rejected.
    let bad = "def f : List (Option Nat) \u{2192} Nat\n  | some x :: _ => x + 100\n  | _ => 0\n\
               theorem bad : f [some 5] = 5 := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "f [some 5] = 105, so `= 5` must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Bare `xor` — Lean 4's `Init/Prelude` root export for `Bool.xor`. Clean
// registered `Bool.xor` but not the bare alias (same as `not`→`Bool.not`).
// ---------------------------------------------------------------------------

#[test]
fn test_bare_xor_alias() {
    // Value-distinguishing: the full xor truth table reduces.
    let code = "theorem t1 : xor true false = true := rfl\n\
                theorem t2 : xor false true = true := rfl\n\
                theorem t3 : xor true true = false := rfl\n\
                theorem t4 : xor false false = false := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "xor truth table");

    // Used inside a def + a nested expression.
    let used = "def parityBit (a b : Bool) : Bool := xor a b\ntheorem t : parityBit true false = true := rfl\n";
    assert_all_ok(&elab_file_prelude(used).1, "xor in a def");
}

#[test]
fn test_bare_xor_alias_soundness() {
    // `xor true true = false`, so `= true` must be rejected.
    let bad = "theorem bad : xor true true = true := rfl\n";
    assert!(
        elab_file_prelude(bad).1.iter().any(|r| r.is_err()),
        "xor true true = false, so `= true` must be rejected"
    );

    // A user-defined `xor` still wins over the alias.
    let shadow = "def xor (n : Nat) : Nat := n * 2\ntheorem t : xor 5 = 10 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(shadow).1,
        "user `def xor` shadows the Bool.xor alias",
    );
}

// ---------------------------------------------------------------------------
// Round-59 discovery lock — real Lean 4 *core* reduction behaviors that Clean
// elaborates AND kernel-checks today.  Each entry is a self-contained snippet
// whose `:= rfl` (or term) proof only registers if the underlying reduction /
// defeq actually succeeds in Clean's kernel.  Sourced from a 6-domain
// valid-Lean-4.30 candidate sweep (statem/except, dependent-elim, class
// resolution, structure eta/projection, Nat/Int arith, string/list ops); the
// 38 that pass are locked here as a cross-domain regression net.
//
// KNOWN GAPS (16, NOT in-lane — deliberately excluded; see
// memory/lean4-gap-backlog for the categorized record):
//   * prelude-completeness (missing stdlib consts, co-tenant kernel/prelude):
//       List.take, List.drop, Except.map, Except.mapError, Except.tryCatch,
//       Except.toOption, Int.natAbs
//     -> the qualified name is unregistered, so elab falls to generalized
//        field-projection on the type constructor and dies in get_type_name
//        ("cannot extract type name from Pi(Type -> Type)").
//   * prelude-instance non-reduction in do-blocks (co-tenant):
//       Except do-throw, ExceptT-over-Id, StateM modify/get
//       (Bind.bind / MonadExcept.throw / Id.run / StateT.run stay unreduced).
//   * recursor / dependent-elim (kernel / architectural):
//       @Eq.rec raw application, Nat.rec (motive := ...) named-arg binding,
//       `h ▸ x` over an indexed type family, dependent match return type,
//       cast∘congrArg∘Eq.trans transport chain, compare (Ord) instance head.

#[test]
fn test_r59_core_reduction_lock() {
    // (name, self-contained Lean source). All MUST elaborate + kernel-check.
    let locked: &[(&str, &str)] = &[
        // -- statem/except that reduce --
        ("except_bind_operator_instance", "example : ((Except.ok 4 : Except String Nat) >>= fun n => (Except.ok (n + 1) : Except String Nat)) = Except.ok 5 := rfl"),
        ("id_run_do_monadic_bind", "example : (Id.run do let x ← pure 3; pure (x + 1)) = 4 := rfl"),
        // -- dependent-elim that reduce --
        ("eq_mpr_rfl_reduces", "theorem eq_mpr_rfl : Eq.mpr (rfl : Nat = Nat) 5 = 5 := rfl"),
        ("cast_rfl_reduces", "theorem cast_rfl : cast (rfl : Nat = Nat) 4 = 4 := rfl"),
        ("subtype_val_projection_reduces", "def subv_s : {x : Nat // x + 0 = x} := ⟨7, rfl⟩\ntheorem subtype_val : subv_s.val = 7 := rfl"),
        ("dependent_dite_uses_proof", "def safe (n : Nat) (_ : n ≠ 0) : Nat := n - 1\ntheorem dite_dep_h : (if h : (3:Nat) = 0 then 0 else safe 3 h) = 2 := rfl"),
        // -- class resolution that reduces --
        ("hetero_op_hadd_hmul_same_type", "theorem hmul_nat : (HMul.hMul (2 : Nat) 3 : Nat) = 6 := rfl\ntheorem hadd_nat : (HAdd.hAdd (4 : Nat) 5 : Nat) = 9 := rfl"),
        ("decide_le_lt_nat", "theorem dec_le : decide ((3 : Nat) ≤ 5) = true := rfl\ntheorem dec_lt : decide ((2 : Nat) < 2) = false := rfl"),
        ("beq_nat_bool", "theorem beq_nat : ((4 : Nat) == 4) = true := rfl\ntheorem bne_nat : ((4 : Nat) == 5) = false := rfl\ntheorem beq_bool : (true == false) = false := rfl"),
        ("decidableeq_string_literal", "theorem str_eq : decide (\"ab\" = \"ab\") = true := rfl\ntheorem str_ne : decide (\"ab\" = \"ba\") = false := rfl"),
        ("class_default_method_invoked", "class Twice (α : Type) where\n  base : α → Nat\n  twice : α → Nat := fun a => base a + base a\ninstance : Twice Nat where base n := n\ntheorem tw : Twice.twice (3 : Nat) = 6 := rfl"),
        ("int_neg_sub_negsucc", "theorem int_sub_neg : (3 : Int) - 10 = -7 := rfl\ntheorem int_neg_add : Neg.neg (5 : Int) + 5 = 0 := rfl"),
        ("min_max_nat", "theorem min_nat : min (3 : Nat) 5 = 3 := rfl\ntheorem max_nat : max (3 : Nat) 5 = 5 := rfl"),
        ("nat_to_int_coercion", "theorem nat_int_coe : (((2 * 3 : Nat)) : Int) = 6 := rfl\ntheorem nat_int_coe0 : ((0 : Nat) : Int) = 0 := rfl"),
        // -- structure eta / projection --
        ("record_literal_field_access", "structure PtA where\n  x : Nat\n  y : Nat\ntheorem c1 : ({ x := 3, y := 5 : PtA }).x = 3 := rfl"),
        ("chained_structure_update", "structure PtB where\n  x : Nat\n  y : Nat\ndef ptb : PtB := { x := 1, y := 2 }\ntheorem c2 : ({ { ptb with x := 10 } with y := 20 }).x = 10 := rfl"),
        ("positional_dot_projection", "structure PairC where\n  a : Nat\n  b : Nat\ndef pairc : PairC := { a := 7, b := 9 }\ntheorem c3 : pairc.1 = 7 ∧ pairc.2 = 9 := ⟨rfl, rfl⟩"),
        ("structure_eta_anon_ctor", "structure PtD where\n  x : Nat\n  y : Nat\ntheorem c4 (p : PtD) : (⟨p.x, p.y⟩ : PtD) = p := rfl"),
        ("nested_projection", "structure InnerE where\n  v : Nat\nstructure OuterE where\n  inner : InnerE\n  w : Nat\ndef oe : OuterE := { inner := { v := 4 }, w := 8 }\ntheorem c5 : oe.inner.v = 4 := rfl"),
        ("computed_default_field", "structure CfgF where\n  base : Nat\n  scaled : Nat := base * 2\ndef cf : CfgF := { base := 5 }\ntheorem c6 : cf.scaled = 10 := rfl"),
        ("single_field_struct_projection", "structure WrapG where\n  val : Nat\ntheorem c7 : (WrapG.mk 42).val = 42 := rfl"),
        ("class_nullary_field_projection", "class HasZeroH (α : Type) where\n  zero : α\ninstance : HasZeroH Nat := ⟨0⟩\ntheorem c8 : (HasZeroH.zero : Nat) = 0 := rfl"),
        ("class_method_projection_applied", "class DoublerI (α : Type) where\n  dbl : α → α\ninstance : DoublerI Nat := ⟨fun n => n + n⟩\ntheorem c9 : DoublerI.dbl 21 = 42 := rfl"),
        // -- Nat/Int arithmetic reduction --
        ("nat_testbit_reduces", "theorem tb : Nat.testBit 13 2 = true := rfl"),
        ("nat_land_lor_def", "def landlor (a b : Nat) : Nat := (a &&& b) + (a ||| b)\ntheorem la : landlor 12 10 = 22 := rfl"),
        ("nat_shift_left_right", "theorem sh : (3 <<< 4 >>> 1 : Nat) = 24 := rfl"),
        ("nat_min_max_clamp", "def clamp (n : Nat) : Nat := Nat.min (Nat.max n 3) 7\ntheorem cl : clamp 10 = 7 := rfl"),
        ("nat_pow_mod", "theorem pm : 2 ^ 8 % 100 = 56 := rfl"),
        ("nat_succ_pred_mul", "theorem sp : Nat.pred (Nat.pred 5) * Nat.succ 2 = 9 := rfl"),
        ("nat_ble_blt_conj", "theorem bp : Nat.ble 3 3 = true ∧ Nat.blt 5 3 = false := ⟨rfl, rfl⟩"),
        ("nat_xor", "theorem xo : (25 ^^^ 7 : Nat) = 30 := rfl"),
        // -- string / list ops that reduce --
        ("string_length_literal", "theorem sl1 : \"hello\".length = 5 := rfl"),
        ("list_reverse_literal", "theorem sl4 : [1, 2, 3, 4].reverse = [4, 3, 2, 1] := rfl"),
        ("list_range_loop", "theorem sl5 : List.range 4 = [0, 1, 2, 3] := rfl"),
        ("list_replicate", "theorem sl6 : List.replicate 3 7 = [7, 7, 7] := rfl"),
        ("list_reverse_of_range", "theorem sl7 : List.reverse (List.range 4) = [3, 2, 1, 0] := rfl"),
        ("list_append_then_length", "theorem sl8 : List.length (List.append [1, 2] [3, 4, 5]) = 5 := rfl"),
        ("list_replicate_nested", "theorem sl9 : List.replicate 2 [1] = [[1], [1]] := rfl"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(
        locked.len(),
        38,
        "expected 38 locked core-reduction behaviors"
    );
}

// ---------------------------------------------------------------------------
// Nested constructor pattern at the 2nd+ cons position (curried-nesting fix).
// A CTOR sub-pattern at a non-last field of an outer constructor previously
// failed KernelCheckFailed because the inner casesOn's motive + covering fallback
// were built at the un-grown branch_ty. These reduce by rfl only if the fix
// grows branch_ty by each abstracted later field's Pi in lockstep.
// ---------------------------------------------------------------------------

#[test]
fn test_nested_ctor_second_position_option() {
    let code = "def f2 : List (Option Nat) → Nat\n  | some x :: none :: _ => x\n  | _ => 0\n\
        theorem f2a : f2 [some 5, none] = 5 := rfl\n\
        theorem f2b : f2 [some 5, some 9] = 0 := rfl\n\
        theorem f2c : f2 [none, none] = 0 := rfl\n\
        theorem f2d : f2 [] = 0 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested ctor 2nd-position (Option)");
}

#[test]
fn test_nested_ctor_both_positions_option() {
    let code = "def g2 : List (Option Nat) → Nat\n  | some x :: some y :: _ => x + y\n  | _ => 0\n\
        theorem g2a : g2 [some 3, some 4] = 7 := rfl\n\
        theorem g2b : g2 [some 3, none] = 0 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested ctor both positions (Option)");
}

#[test]
fn test_nested_ctor_second_position_prod() {
    let code =
        "def h2 : List (Nat × Nat) → Nat\n  | (a, b) :: (c, d) :: _ => a + b + c + d\n  | _ => 0\n\
        theorem h2a : h2 [(1, 2), (3, 4)] = 10 := rfl\n\
        theorem h2b : h2 [(1, 2)] = 0 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested ctor 2nd-position (Prod)");
}

#[test]
fn test_nested_ctor_second_position_wrong_value_rejected() {
    // Value-distinguishing negative: an INCORRECT reduction target must fail
    // to kernel-check (loud), proving the positive rfl above is meaningful.
    let code = "def f2w : List (Option Nat) → Nat\n  | some x :: none :: _ => x\n  | _ => 0\n\
        theorem f2wrong : f2w [some 5, none] = 6 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "wrong-value f2w [some 5, none] = 6 must be rejected, but all decls elaborated OK"
    );
}

#[test]
fn test_nested_ctor_working_neighbors_regression() {
    // Shapes that already worked must stay working (fix is byte-identical for them).
    let code = "def n1 : List (Option Nat) → Nat\n  | some x :: _ => x\n  | _ => 0\n\
        theorem n1a : n1 [some 7] = 7 := rfl\n\
        def n2 : List (Option Nat) → Nat\n  | some x :: _ :: _ => x\n  | _ => 0\n\
        theorem n2a : n2 [some 7, none] = 7 := rfl\n\
        def n3 : List Nat → Nat\n  | x :: y :: _ => x + y\n  | _ => 0\n\
        theorem n3a : n3 [4, 5] = 9 := rfl\n\
        def n4 : List (Option Nat) → Nat\n  | none :: x :: _ => 1\n  | _ => 0\n\
        theorem n4a : n4 [none, some 3] = 1 := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "working-neighbor regression");
}

// ---------------------------------------------------------------------------
// Round-61 lock — deeper nested-constructor-pattern family (guards brick 75).
// Brick 75 (curried-nesting fallback growth) fixed a CTOR sub-pattern at a
// non-last field of an outer constructor. This lock pins the wider family it
// generalises to: 3-level nesting, ctor at 1st/2nd/3rd positions, all-some
// triples, Sum eliminators, user inductives (nullary + with-field), and Prod
// with an Option field. Each `:= rfl` only registers if Clean's kernel actually
// reduces the compiled nested match — a regression here means brick 75 broke.
// ---------------------------------------------------------------------------

#[test]
fn test_r61_deep_nested_ctor_family_lock() {
    let cands: &[(&str, &str)] = &[
        ("3level_nested_option_2nd",
         "def q1 : List (Option (Option Nat)) → Nat\n  | some (some x) :: none :: _ => x\n  | _ => 0\n\
          theorem q1a : q1 [some (some 5), none] = 5 := rfl\n\
          theorem q1b : q1 [some none, none] = 0 := rfl\n"),
        ("ctor_at_1st_and_3rd",
         "def q2 : List (Option Nat) → Nat\n  | some x :: none :: some y :: _ => x + y\n  | _ => 0\n\
          theorem q2a : q2 [some 3, none, some 4] = 7 := rfl\n\
          theorem q2b : q2 [some 3, none, none] = 0 := rfl\n"),
        ("prod_with_option_field_both",
         "def q3 : List (Nat × Option Nat) → Nat\n  | (a, some b) :: (c, none) :: _ => a + b + c\n  | _ => 0\n\
          theorem q3a : q3 [(1, some 2), (3, none)] = 6 := rfl\n\
          theorem q3b : q3 [(1, some 2), (3, some 9)] = 0 := rfl\n"),
        ("all_some_triple",
         "def q4 : List (Option Nat) → Nat\n  | some x :: some y :: some z :: _ => x + y + z\n  | _ => 0\n\
          theorem q4a : q4 [some 1, some 2, some 3] = 6 := rfl\n\
          theorem q4b : q4 [some 1, some 2, none] = 0 := rfl\n"),
        ("ctor_at_3rd_only",
         "def q5 : List (Option Nat) → Nat\n  | _ :: _ :: some x :: _ => x\n  | _ => 0\n\
          theorem q5a : q5 [none, none, some 8] = 8 := rfl\n\
          theorem q5b : q5 [none, none, none] = 0 := rfl\n"),
        ("sum_inl_inr",
         "def q6 : List (Sum Nat Nat) → Nat\n  | Sum.inl x :: Sum.inr y :: _ => x + y\n  | _ => 0\n\
          theorem q6a : q6 [Sum.inl 3, Sum.inr 4] = 7 := rfl\n\
          theorem q6b : q6 [Sum.inl 3, Sum.inl 4] = 0 := rfl\n"),
        ("user_inductive_nullary",
         "inductive Col2 | red | green | blue\n\
          def q7 : List Col2 → Nat\n  | Col2.red :: Col2.green :: _ => 1\n  | _ => 0\n\
          theorem q7a : q7 [Col2.red, Col2.green] = 1 := rfl\n\
          theorem q7b : q7 [Col2.red, Col2.blue] = 0 := rfl\n"),
        ("user_inductive_field_both",
         "inductive Bx2 | mk (n : Nat)\n\
          def q8 : List Bx2 → Nat\n  | Bx2.mk a :: Bx2.mk b :: _ => a + b\n  | _ => 0\n\
          theorem q8a : q8 [Bx2.mk 3, Bx2.mk 4] = 7 := rfl\n\
          theorem q8b : q8 [Bx2.mk 3] = 0 := rfl\n"),
        ("ctor_at_1st_2nd_3rd",
         "def q9 : List (Option Nat) → Nat\n  | some x :: none :: none :: _ => x\n  | _ => 0\n\
          theorem q9a : q9 [some 5, none, none] = 5 := rfl\n\
          theorem q9b : q9 [some 5, none, some 1] = 0 := rfl\n"),
    ];
    for (name, code) in cands {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(cands.len(), 9, "expected 9 deep nested-ctor family locks");
}

// ---------------------------------------------------------------------------
// Bare `compare` resolves to `Ord.compare` on demand (brick 76).
// Lean exports `compare` at the root (`export Ord (compare)`); Clean registers
// the `Ord.compare` projection + `instOrdNat` but not the bare alias, so
// `compare a b` was over-applied (TooManyArguments). elab_ident now routes bare
// `compare` to `Ord.compare`, which synthesizes `[Ord α]` and reduces.
// ---------------------------------------------------------------------------

#[test]
fn test_bare_compare_alias() {
    let code = "theorem cmp_lt : compare (2 : Nat) 7 = Ordering.lt := rfl\n\
        theorem cmp_eq : compare (4 : Nat) 4 = Ordering.eq := rfl\n\
        theorem cmp_gt : compare (9 : Nat) 1 = Ordering.gt := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "bare `compare` resolves to Ord.compare");
    assert!(
        env.get_const(&Name::from_string("cmp_lt")).is_some(),
        "cmp_lt should register"
    );
}

#[test]
fn test_bare_compare_wrong_value_rejected() {
    // Value-distinguishing: an incorrect Ordering must fail to kernel-check.
    let code = "theorem cmp_wrong : compare (2 : Nat) 7 = Ordering.gt := rfl\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "wrong-value compare (2) 7 = .gt must be rejected, but all decls elaborated OK"
    );
}

#[test]
fn test_user_compare_shadows_alias() {
    // A user `def compare` must win over the on-demand Ord.compare alias.
    let code = "def compare (a b : Nat) : Nat := a + b\n\
        theorem uc : compare 2 3 = 5 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "user `def compare` shadows the Ord.compare alias",
    );
}

// ---------------------------------------------------------------------------
// Round-63 discovery lock — verified real-Lean-4-core behaviors across six
// fresh domains (Fin/UInt arith, Option/Sum/Bool eliminators, coercion chains,
// notation, universe-polymorphism, root exports). These 24 elaborate AND
// kernel-reduce today; the coherent 9-candidate universe-poly family (explicit
// `.{u}` levels, poly defs, PProd/PUnit at explicit universes, level arithmetic)
// is the crown jewel. Each `:= rfl` only registers if Clean's kernel performs
// the reduction. Gaps found this round were co-tenant (missing ToBool class,
// Hashable Bool value 1≠11, Fin/UInt OfNat+HXor/HAnd instances, missing prelude
// consts) or large-architectural (custom `notation` grammar extension) — recorded
// in memory/lean4-gap-backlog, not locked.
// ---------------------------------------------------------------------------

#[test]
fn test_r63_discovery_lock() {
    let locked: &[(&str, &str)] = &[
        // -- universe polymorphism (9) --
        ("upoly_id_explicit_level_zero", "def myid.{u} (α : Type u) (a : α) : α := a\ntheorem t : myid.{0} Nat 5 = 5 := rfl"),
        ("upoly_const_two_levels", "def kon.{u, v} (α : Type u) (β : Type v) (a : α) (_ : β) : α := a\ntheorem t : kon.{0, 0} Nat Bool 7 true = 7 := rfl"),
        ("upoly_builtin_id_at_level", "theorem t : @id.{1} Nat 42 = 42 := rfl"),
        ("upoly_punit_eliminate", "def fromUnit.{u} (_ : PUnit.{u}) : Nat := 99\ntheorem t : fromUnit.{1} PUnit.unit = 99 := rfl"),
        ("upoly_pprod_mk_levels", "theorem t : (PProd.mk.{1, 1} (3 : Nat) (4 : Nat)).snd = 4 := rfl"),
        ("upoly_sort_at_prop", "def sortId.{u} (α : Sort u) (a : α) : α := a\ntheorem t : sortId.{0} True True.intro = True.intro := rfl"),
        ("upoly_level_succ_arith", "def selfType.{u} : Type (u + 1) := Type u\ntheorem t : selfType.{0} = Type := rfl"),
        ("upoly_max_via_prod", "def mkP.{u, v} {α : Type u} {β : Type v} (a : α) (b : β) : α × β := (a, b)\ntheorem t : (mkP.{0, 0} (5 : Nat) true).1 = 5 := rfl"),
        ("upoly_id_on_list", "def polyId.{u} {α : Type u} (a : α) : α := a\ntheorem t : polyId.{0} [1, 2, 3] = [1, 2, 3] := rfl"),
        // -- coercion chains that reduce (5) --
        ("coe_bool_sort_prop", "theorem coe_bool_sort_prop : (true : Prop) := rfl"),
        ("coe_decide_bool_prop", "theorem coe_decide_bool_prop : (decide (2 < 5) : Prop) := rfl"),
        ("coe_nat_int_list", "theorem coe_nat_int_list : ([↑(1 : Nat), 2, 3] : List Int) = [1, 2, 3] := rfl"),
        ("coe_nat_int_prod", "theorem coe_nat_int_prod : ((↑(2 : Nat), 5) : Int × Int) = (2, 5) := rfl"),
        ("coe_nat_int_add", "theorem coe_nat_int_add : (↑(3 : Nat) + 4 : Int) = 7 := rfl"),
        // -- Option/Sum/Bool eliminators that reduce (3) --
        ("option_map_getD", "example : (Option.map (· * 2) (some 5)).getD 0 = 10 := rfl"),
        ("sum_elim_inr", "example : Sum.elim (fun n => n + 1) (fun s => s.length) (Sum.inr \"abc\" : Nat ⊕ String) = 3 := rfl"),
        ("bool_rec_explicit_motive", "example : @Bool.rec (fun _ => Nat) 10 20 false = 10 := rfl"),
        // -- UInt8 arithmetic wrap (2) --
        ("u8_sub_underflow", "theorem u8_sub_underflow : (0 : UInt8) - 1 = 255 := rfl"),
        ("u8_ofnat_wrap_tonat", "theorem u8_ofnat_wrap_tonat : (300 : UInt8).toNat = 44 := rfl"),
        // -- local/scoped notation (2) --
        ("local_notation_section", "section\nlocal notation:70 a \" ⊗ \" b => a * b + 1\ntheorem ntlocal : (3 ⊗ 4 : Nat) = 13 := rfl\nend"),
        ("scoped_notation_namespace", "namespace NtN\nscoped notation:70 a \" ⋄ \" b => a + b * b\ntheorem ntscoped : (2 ⋄ 3 : Nat) = 11 := rfl\nend NtN"),
        // -- root exports that already resolve+reduce (3) --
        ("root_toString_bool", "theorem t_tostr : toString true = \"true\" := rfl"),
        ("root_decide_and", "theorem t_decide : decide (True ∧ True) = true := rfl"),
        ("root_absurd", "theorem t_absurd : (0 = 1) → (0 ≠ 1) → False := fun h hn => absurd h hn"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 24, "expected 24 round-63 verified behaviors");
}

// ---------------------------------------------------------------------------
// General `notation` command in simple infix/prefix/postfix shape (brick 77).
// Plain `notation:P a " sym " b => expansion` previously parsed the DECL but
// ParseErrored on USE (the general mixfix form registered no parseable
// operator). custom_notation.rs now maps the infix/prefix/postfix SHAPES of
// `notation` to the fixed-arity machinery, abstracting the named operands into
// a lambda so the template beta-reduces.
// ---------------------------------------------------------------------------

#[test]
fn test_notation_infix_use() {
    let code = "notation:65 a \" <+> \" b => a + b\n\
        theorem nt1 : (3 <+> 4 : Nat) = 7 := rfl\n\
        theorem nt2 : (10 <+> 20 : Nat) = 30 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "notation infix use");
}

#[test]
fn test_notation_infix_template_substitution() {
    // Value-distinguishing: the template `a * b + 1` must substitute a:=3,b:=4.
    let code = "notation:65 a \" ⊗ \" b => a * b + 1\n\
        theorem nt3 : (3 ⊗ 4 : Nat) = 13 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "notation infix template");
}

#[test]
fn test_notation_infix_wrong_value_rejected() {
    let code = "notation:65 a \" <+> \" b => a + b\n\
        theorem ntw : (3 <+> 4 : Nat) = 8 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value (3 <+> 4) = 8 must be rejected"
    );
}

#[test]
fn test_notation_prefix_use() {
    let code = "notation:75 \"∇\" a => a * a * a\n\
        theorem ntp : (∇ 3 : Nat) = 27 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "notation prefix use");
}

#[test]
fn test_notation_postfix_use() {
    let code = "notation:75 a \"²\" => a * a\n\
        theorem nts : (7² : Nat) = 49 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "notation postfix use");
}

#[test]
fn test_notation_infixl_still_works_regression() {
    // The existing infixl path (bare-head expansion) must remain unaffected.
    // (Uses a non-builtin token; `⊕` is Clean's builtin `Sum` operator.)
    let code = "infixl:65 \" ⊗ \" => Nat.add\n\
        theorem ntr : (3 ⊗ 4 : Nat) = 7 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "infixl regression");
}

#[test]
fn test_funext_term_proof_does_not_leak_pi_comparison_fvar() {
    let code = r#"
def TemporalScopeBehavior := Nat → Nat
def temporalScopeDrop (b : TemporalScopeBehavior) (n : Nat) : TemporalScopeBehavior :=
  fun k => b (n + k)
theorem temporal_scope_drop_zero (b : TemporalScopeBehavior) :
    temporalScopeDrop b 0 = b :=
  funext (fun k => congrArg b (Nat.zero_add k))
"#;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "term-style funext scope regression");
    assert!(
        env.get_const(&Name::from_string("temporal_scope_drop_zero"))
            .is_some(),
        "the kernel-checked theorem must be registered"
    );
}

// ---------------------------------------------------------------------------
// Round-65 everyday-Lean lock — a frequency-REPRESENTATIVE battery of ordinary
// Lean 4 core code (generated neutrally, no gap-avoidance) measured 42/50 (84%)
// elaborating + kernel-checking. The 42 passing snippets are locked here as the
// everyday regression net. The 8 failures are recorded in the memory backlog:
// do-block instance non-reduction (Except throw/tryCatch), missing prelude
// `failure`/Membership-List, omega linear-nat routing, two recursive-def
// registration bugs (fuel-if-guard, two-arg recursion), Iff anon-ctor
// projection. Per-domain: defs/structures 10/10, lists/strings/arith 9/10,
// match/recursion 8/10, props/tactics 8/10, do/monads 7/10.
// ---------------------------------------------------------------------------

#[test]
fn test_r65_everyday_lock() {
    let locked: &[(&str, &str)] = &[
        ("ed1_defs_with_params", "def ed1_double (n : Nat) : Nat := 2 * n\ndef ed1_addThree (a b c : Nat) : Nat := a + b + c\ntheorem ed1_value : ed1_double 5 + ed1_addThree 1 2 3 = 16 := rfl"),
        ("ed2_structure_literal_field_access", "structure Ed2Point where\n  x : Nat\n  y : Nat\n\ndef ed2_p : Ed2Point := { x := 3, y := 7 }\ntheorem ed2_coords : ed2_p.x + ed2_p.y = 10 := rfl"),
        ("ed3_structure_update_syntax", "structure Ed3Config where\n  width : Nat\n  height : Nat\n  depth : Nat\n\ndef ed3_base : Ed3Config := ⟨10, 20, 30⟩\ndef ed3_updated : Ed3Config := { ed3_base with height := 25 }\ntheorem ed3_update : ed3_updated.width + ed3_updated.height = 35 := rfl"),
        ("ed4_enum_inductive_match", "inductive Ed4Color where\n  | red | green | blue\n\ndef ed4_toNat : Ed4Color → Nat\n  | .red => 0\n  | .green => 1\n  | .blue => 2\ntheorem ed4_match : ed4_toNat .green + ed4_toNat .blue = 3 := rfl"),
        ("ed5_class_instance_method", "class Ed5Area (α : Type) where\n  area : α → Nat\nstructure Ed5Rect where\n  w : Nat\n  h : Nat\ninstance : Ed5Area Ed5Rect where area r := r.w * r.h\ndef ed5_r : Ed5Rect := { w := 4, h := 6 }\ntheorem ed5_method : Ed5Area.area ed5_r = 24 := rfl"),
        ("ed6_abbrev", "abbrev Ed6Pair := Nat × Nat\ndef ed6_swap (p : Ed6Pair) : Ed6Pair := (p.2, p.1)\ntheorem ed6_swapped : ed6_swap (3, 8) = (8, 3) := rfl"),
        ("ed7_variable_section", "section\nvariable (n m : Nat)\ndef ed7_sumSq : Nat := n * n + m * m\ndef ed7_diff : Nat := n - m\nend\ntheorem ed7_values : ed7_sumSq 3 4 + ed7_diff 10 4 = 31 := rfl"),
        ("ed8_recursive_def", "def ed8_sumTo : Nat → Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + ed8_sumTo n\ntheorem ed8_recursion : ed8_sumTo 5 = 15 := rfl"),
        ("ed9_payload_inductive_decide", "inductive Ed9Shape where\n  | circle (r : Nat)\n  | square (s : Nat)\n\ndef ed9_perimeter : Ed9Shape → Nat\n  | .circle r => 6 * r\n  | .square s => 4 * s\ntheorem ed9_payload : ed9_perimeter (.square 5) = 20 := by decide"),
        ("ed10_ite_and_simp", "def ed10_maxOf (a b : Nat) : Nat := if a ≤ b then b else a\ntheorem ed10_concrete : ed10_maxOf 3 9 = 9 := rfl\ntheorem ed10_left (n : Nat) : ed10_maxOf 0 n = n := by simp [ed10_maxOf]"),
        ("ed1_doubleAll_list_map_recursion", "def ed1_doubleAll : List Nat → List Nat\n  | [] => []\n  | x :: xs => 2 * x :: ed1_doubleAll xs\n\ntheorem ed1_doubleAll_eval : ed1_doubleAll [1, 2, 3] = [2, 4, 6] := rfl"),
        ("ed2_keepPos_filter_with_if_guard", "def ed2_keepPos : List Int → List Int\n  | [] => []\n  | x :: xs => if x > 0 then x :: ed2_keepPos xs else ed2_keepPos xs\n\ntheorem ed2_keepPos_eval : ed2_keepPos [1, -2, 3, 0] = [1, 3] := rfl"),
        ("ed3_unwrapOr_option_match", "def ed3_unwrapOr : Option Nat → Nat → Nat\n  | some x, _ => x\n  | none, d => d\n\ntheorem ed3_unwrapOr_eval : ed3_unwrapOr (some 7) 0 = 7 := rfl"),
        ("ed4_addOpt_two_scrutinee_wildcard", "def ed4_addOpt : Option Nat → Option Nat → Option Nat\n  | some a, some b => some (a + b)\n  | _, _ => none\n\ntheorem ed4_addOpt_eval : ed4_addOpt (some 2) (some 3) = some 5 := rfl"),
        ("ed5_sumTo_nat_structural_recursion", "def ed5_sumTo : Nat → Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + ed5_sumTo n\n\ntheorem ed5_sumTo_eval : ed5_sumTo 4 = 10 := rfl"),
        ("ed6_secondD_nested_cons_pattern", "def ed6_secondD : List Nat → Nat\n  | _ :: y :: _ => y\n  | _ => 0\n\ntheorem ed6_secondD_eval : ed6_secondD [7, 8, 9] = 8 := rfl"),
        ("ed8_lookup_assoc_pair_pattern_getD", "def ed8_lookup : List (Nat × Nat) → Nat → Option Nat\n  | [], _ => none\n  | (k, v) :: rest, key => if k == key then some v else ed8_lookup rest key\n\ntheorem ed8_lookup_eval : (ed8_lookup [(1, 10), (2, 20)] 2).getD 0 = 20 := rfl"),
        ("ed9_allEven_bool_fold_recursion", "def ed9_allEven : List Nat → Bool\n  | [] => true\n  | x :: xs => x % 2 == 0 && ed9_allEven xs\n\ntheorem ed9_allEven_eval : ed9_allEven [2, 4, 6] = true := rfl"),
        ("edm1_option_do_bind_pure", "def edm1_addOpt (a b : Option Nat) : Option Nat := do\n  let x ← a\n  let y ← b\n  pure (x + y)\n\ntheorem edm1_val : edm1_addOpt (some 2) (some 3) = some 5 := rfl\ntheorem edm1_none : edm1_addOpt (some 2) none = none := rfl"),
        ("edm2_except_ok_error_paths", "def edm2_safeDiv (a b : Nat) : Except String Nat :=\n  if b = 0 then .error \"div by zero\" else .ok (a / b)\n\ntheorem edm2_ok : edm2_safeDiv 10 2 = .ok 5 := rfl\ntheorem edm2_err : edm2_safeDiv 1 0 = .error \"div by zero\" := rfl"),
        ("edm3_except_do_error_propagation", "def edm3_mulE (a b : Except String Nat) : Except String Nat := do\n  let x ← a\n  let y ← b\n  return x * y\n\ntheorem edm3_val : edm3_mulE (.ok 4) (.ok 5) = .ok 20 := rfl\ntheorem edm3_prop : edm3_mulE (.error \"e\") (.ok 5) = .error \"e\" := rfl"),
        ("edm4_id_run_let_mut", "def edm4_calc : Nat := Id.run do\n  let mut acc := 1\n  acc := acc + 4\n  acc := acc * 3\n  return acc\n\ntheorem edm4_val : edm4_calc = 15 := rfl"),
        ("edm5_early_return_if", "def edm5_clamp (n : Nat) : Nat := Id.run do\n  if n > 100 then\n    return 100\n  return n\n\ntheorem edm5_hi : edm5_clamp 250 = 100 := by decide\ntheorem edm5_lo : edm5_clamp 7 = 7 := by decide"),
        ("edm6_for_in_list_accumulator", "def edm6_sumList (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    s := s + x\n  return s\n\ntheorem edm6_val : edm6_sumList [1, 2, 3, 4] = 10 := rfl"),
        ("edm7_option_bind_chain", "def edm7_half (n : Nat) : Option Nat := if n % 2 = 0 then some (n / 2) else none\ndef edm7_quarter (n : Nat) : Option Nat := edm7_half n >>= edm7_half\ntheorem edm7_val : edm7_quarter 12 = some 3 := rfl\ntheorem edm7_none : edm7_quarter 6 = none := rfl"),
        ("ed1_list_literal_append_length", "def ed1_xs : List Nat := [1, 2, 3] ++ [4, 5]\n\ntheorem ed1_xs_eq : ed1_xs = [1, 2, 3, 4, 5] := rfl\n\ntheorem ed1_len : ed1_xs.length = 5 := rfl"),
        ("ed2_map_foldl", "def ed2_doubled : List Nat := [1, 2, 3].map (· * 2)\n\ndef ed2_total : Nat := ed2_doubled.foldl (· + ·) 0\n\ntheorem ed2_doubled_eq : ed2_doubled = [2, 4, 6] := rfl\n\ntheorem ed2_total_eq : ed2_total = 12 := rfl"),
        ("ed3_filter_reverse", "def ed3_evens : List Nat := ([5, 2, 8, 3, 6].filter (· % 2 == 0)).reverse\n\ntheorem ed3_evens_eq : ed3_evens = [6, 8, 2] := rfl\n\ntheorem ed3_evens_len : ed3_evens.length = 3 := rfl"),
        ("ed4_string_append_length", "def ed4_greet (name : String) : String := \"Hello, \" ++ name ++ \"!\"\n\ntheorem ed4_greet_lean : ed4_greet \"Lean\" = \"Hello, Lean!\" := rfl\n\ntheorem ed4_len : (ed4_greet \"Lean\").length = 12 := rfl"),
        ("ed5_nat_arith_pow_mod_div", "def ed5_calc : Nat := (2 ^ 5 + 7 * 3) % 10\n\ntheorem ed5_calc_eq : ed5_calc = 3 := rfl\n\ntheorem ed5_div_mod : 17 / 5 + 17 % 5 = 5 := rfl"),
        ("ed6_int_mixed_arith", "def ed6_balance : Int := -7 + 3 * 4 - 10\n\ntheorem ed6_balance_eq : ed6_balance = -5 := rfl\n\ntheorem ed6_mul_neg : (-3 : Int) * 4 = -12 := rfl"),
        ("ed7_comparisons_decide", "theorem ed7_lt : (3 : Nat) < 5 := by decide\n\ntheorem ed7_le : (10 : Nat) ≤ 10 := by decide\n\ntheorem ed7_beq : (4 + 4 == 8) = true := rfl\n\ntheorem ed7_int_lt : (-3 : Int) < 2 := by decide"),
        ("ed8_min_max_clamp", "def ed8_clamp (n : Nat) : Nat := min (max n 1) 10\n\ntheorem ed8_clamp_lo : ed8_clamp 0 = 1 := rfl\n\ntheorem ed8_clamp_mid : ed8_clamp 7 = 7 := rfl\n\ntheorem ed8_clamp_hi : ed8_clamp 99 = 10 := rfl"),
        ("ed10_string_interpolation_nat", "def ed10_report (n : Nat) : String := s!\"count = {n}\"\n\ntheorem ed10_report_eq : ed10_report 42 = \"count = 42\" := rfl"),
        ("ed1_rfl_def_eval", "def ed1_double (n : Nat) : Nat := 2 * n\ntheorem ed1_double_five : ed1_double 5 = 10 := rfl"),
        ("ed2_decide_conj", "theorem ed2_decide_conj : 7 * 6 = 42 ∧ 3 < 10 := by decide"),
        ("ed3_simp_arith_identity", "theorem ed3_simp_id (n m : Nat) : (n + 0) * 1 + m * 0 = n := by simp"),
        ("ed5_intro_apply_exact", "theorem ed5_comp (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by\n  intro hp\n  apply hqr\n  apply hpq\n  exact hp"),
        ("ed6_constructor_and_elim", "theorem ed6_and_swap (p q : Prop) (h : p ∧ q) : q ∧ p := by\n  constructor\n  · exact h.2\n  · exact h.1"),
        ("ed7_cases_or", "theorem ed7_or_swap (p q : Prop) (h : p ∨ q) : q ∨ p := by\n  cases h with\n  | inl hp => exact Or.inr hp\n  | inr hq => exact Or.inl hq"),
        ("ed9_exists_witness", "theorem ed9_exists_sq : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩"),
        ("ed10_calc_rw_hyp", "theorem ed10_calc (a b : Nat) (h1 : a = b) (h2 : b = 2) : a + 3 = 5 := by\n  calc a + 3 = b + 3 := by rw [h1]\n    _ = 2 + 3 := by rw [h2]\n    _ = 5 := rfl"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 42, "expected 42 locked everyday behaviors");
}

// ---------------------------------------------------------------------------
// Brick 78: named arguments on recursor/casesOn heads — `Nat.rec (motive := M)`.
// resolve_named_args previously failed LOUD (NamedArgBindingFailed) for any
// recursor head; binder names are now derived from the RecursorVal layout
// (params, motive(s), minors named by ctor short name, indices, major `t`).
// ---------------------------------------------------------------------------

#[test]
fn test_natrec_motive_named_arg() {
    let code = "def T2 : Nat → Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def f2r (n : Nat) : T2 n := Nat.rec (motive := T2) true (fun _ _ => (7 : Nat)) n\n\
        theorem natrec_dep : @Eq Nat (f2r 3) 7 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "Nat.rec (motive := T)");
}

#[test]
fn test_natrec_motive_named_arg_wrong_value_rejected() {
    let code = "def T3 : Nat → Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def f3r (n : Nat) : T3 n := Nat.rec (motive := T3) true (fun _ _ => (7 : Nat)) n\n\
        theorem natrec_wrong : @Eq Nat (f3r 3) 8 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value f3r 3 = 8 must be rejected"
    );
}

#[test]
fn test_cases_on_motive_named_arg() {
    let code = "def g2c (b : Bool) : Nat := Bool.casesOn (motive := fun _ => Nat) b 10 20\n\
        theorem gc1 : g2c false = 10 := rfl\n\
        theorem gc2 : g2c true = 20 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "Bool.casesOn (motive := ...)");
}

// ---------------------------------------------------------------------------
// Brick 79: `↑` prefix coercion binds to the next atom in ARGUMENT position.
// `f ↑x` previously juxtaposed as App(f, [↑, x]) → UnknownIdent("↑").
// ---------------------------------------------------------------------------

#[test]
fn test_uparrow_argument_position() {
    let code = "def bump2 (x : Int) : Int := x + 1\n\
        theorem up1 : bump2 ↑(3 : Nat) = 4 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "up-arrow in argument position");
}

#[test]
fn test_uparrow_head_position_regression() {
    let code = "theorem up2 : (↑(3 : Nat) + 4 : Int) = 7 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "up-arrow head position (R63 lock shape)",
    );
}

#[test]
fn test_uparrow_argument_wrong_value_rejected() {
    let code = "def bump3 (x : Int) : Int := x + 1\n\
        theorem up3 : bump3 ↑(3 : Nat) = 5 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value bump3 ↑3 = 5 must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Brick 80: dependent match return type (equation-style def). The equation-def
// normalizer peeled `def g : (b : Bool) → W b | …` into a synthetic `_x : Bool`
// binder while the residual return type still said `W b` — `b` dangled, got
// auto-bound as a FRESH fvar, and every dependent-motive consumer saw two
// distinct fvars for one parameter (MatchArmTypeMismatch on arm 2). The
// normalizer now lifts the binder under the DECLARED name (Lean-faithful) and
// renames the synthetic match scrutinee to match.
// ---------------------------------------------------------------------------

#[test]
fn test_dep_match_return_type_bool() {
    let code = "def W : Bool → Type\n  | true => Nat\n  | false => Bool\n\
        def gdep : (b : Bool) → W b\n  | true => (5 : Nat)\n  | false => false\n\
        theorem gd1 : @Eq Nat (gdep true) 5 := rfl\n\
        theorem gd2 : @Eq Bool (gdep false) false := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "dependent match return type (Bool)",
    );
}

#[test]
fn test_dep_match_return_type_wrong_value_rejected() {
    let code = "def W4 : Bool → Type\n  | true => Nat\n  | false => Bool\n\
        def gdep4 : (b : Bool) → W4 b\n  | true => (5 : Nat)\n  | false => false\n\
        theorem gd4 : @Eq Nat (gdep4 true) 6 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value gdep4 true = 6 must be rejected"
    );
}

#[test]
fn test_dep_match_succ_field_dependent() {
    let code = "def T5 : Nat → Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def h5 : (n : Nat) → T5 n\n  | 0 => true\n  | n+1 => (n : Nat)\n\
        theorem h5a : @Eq Nat (h5 3) 2 := rfl\n\
        theorem h5b : @Eq Bool (h5 0) true := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "dependent match succ field");
}

#[test]
fn test_dep_match_nondependent_regression() {
    // Non-dependent equation defs (Arrow + anonymous-Pi) must be unchanged.
    let code = "def nd : Bool → Nat\n  | true => 1\n  | false => 0\n\
        theorem nd1 : nd true = 1 := rfl\n\
        def nd2f : Nat → Nat\n  | 0 => 0\n  | n+1 => nd2f n + 2\n\
        theorem nd2a : nd2f 3 = 6 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "non-dependent regression");
}

// ---------------------------------------------------------------------------
// Bricks 81+82: multi-arg equation defs — variable rows in structural columns
// (Maranget variable rule via let-rebind) + declared Pi binder names threaded
// through peel_n_domains (multiarg form of the B80 name-drop fix).
// ---------------------------------------------------------------------------

#[test]
fn test_multiarg_equation_rec_var_row() {
    // `| 0, m => m` mixes a var with ctor heads in a structural column; the
    // whole def previously fell out of the normalizer and the self-call died
    // UnknownIdent.
    let code = "def ed10x : Nat → Nat → Nat\n  | 0, m => m\n  | n + 1, 0 => n + 1\n  | n + 1, m + 1 => ed10x n m + 1\n\
        theorem ed10a : ed10x 3 5 = 5 := rfl\n\
        theorem ed10b : ed10x 5 3 = 5 := rfl\n\
        theorem ed10c : ed10x 0 7 = 7 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "multiarg equation rec with var row",
    );
}

#[test]
fn test_multiarg_equation_rec_wrong_value_rejected() {
    let code = "def ed10y : Nat → Nat → Nat\n  | 0, m => m\n  | n + 1, 0 => n + 1\n  | n + 1, m + 1 => ed10y n m + 1\n\
        theorem ed10w : ed10y 3 5 = 6 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value ed10y 3 5 = 6 must be rejected"
    );
}

#[test]
fn test_multiarg_equation_regressions() {
    // Controls: 2-arg non-rec + 1-arg rec + all-structural 2-arg rec stay green.
    let code = "def f8 : Nat → Bool → Nat\n  | n, true => n\n  | _, false => 0\n\
        theorem f8a : f8 5 true = 5 := rfl\n\
        def len3 : Nat → Nat\n  | 0 => 0\n  | n + 1 => len3 n + 1\n\
        theorem len3a : len3 3 = 3 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "multiarg regressions");
}
#[test]
fn test_multiarg_dependent_declared_name() {
    // Declared Pi binder name (`n`) threads through the multiarg lift so the
    // dependent residual return type `T8 n` resolves to the lifted binder
    // (multiarg form of the B80 name-drop fix). Patterns are unambiguous
    // (0 / k+1); bare constructor idents (true/false) in patterns remain a
    // recorded follow-up (parsed as Var, need env-aware resolution).
    let code = "def T8 : Nat → Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def f9 : (n : Nat) → Nat → T8 n\n  | 0, _ => (true : Bool)\n  | k + 1, m => (k + m : Nat)\n\
        theorem f9a : @Eq Nat (f9 2 3) 4 := rfl\n\
        theorem f9b : @Eq Bool (f9 0 9) true := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "multiarg dependent declared name",
    );
}

#[test]
fn test_multiarg_nullary_ctor_ident_dependent() {
    // Brick 83: bare `true`/`false` ctor idents in multiarg columns previously
    // parsed as Var and mis-classified the column; with env-aware nullary-ctor
    // rewriting the dependent return type resolves per-branch.
    let code = "def W9 : Bool → Type\n  | true => Nat\n  | false => Bool\n\
        def f6 : (a : Nat) → (b : Bool) → W9 b\n  | a, true => (a : Nat)\n  | _, false => (true : Bool)\n\
        theorem f6a : @Eq Nat (f6 7 true) 7 := rfl\n\
        theorem f6b : @Eq Bool (f6 7 false) true := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "multiarg nullary ctor dependent",
    );
}

#[test]
fn test_multiarg_nullary_ctor_ident_wrong_value_rejected() {
    let code = "def W10 : Bool → Type\n  | true => Nat\n  | false => Bool\n\
        def f6w : (a : Nat) → (b : Bool) → W10 b\n  | a, true => (a : Nat)\n  | _, false => (true : Bool)\n\
        theorem f6wv : @Eq Nat (f6w 7 true) 8 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value f6w 7 true = 8 must be rejected"
    );
}

#[test]
fn test_b84_multiscrut_recursive_def_value() {
    // Brick 84: recursive def over a MULTI-SCRUTINEE `match a, b with`.
    // The parser packs the scrutinees into one right-nested `Prod.mk` tuple;
    // previously the tuple never matched the decreasing-arg ident, `use_rec`
    // never fired, and the self-call died UnknownIdent(ed7_log2).
    let code = "def ed7_log2 (fuel n : Nat) : Nat :=\n  match fuel, n with\n  | 0, _ => 0\n  | fuel + 1, n => if n <= 1 then 0 else 1 + ed7_log2 fuel (n / 2)\n\
        theorem ed7v : ed7_log2 10 8 = 3 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "b84 multi-scrutinee recursive");
}

#[test]
fn test_b84_multiscrut_recursive_wrong_value_rejected() {
    let code = "def ed7w_log2 (fuel n : Nat) : Nat :=\n  match fuel, n with\n  | 0, _ => 0\n  | fuel + 1, n => if n <= 1 then 0 else 1 + ed7w_log2 fuel (n / 2)\n\
        theorem ed7wv : ed7w_log2 10 8 = 4 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value ed7w_log2 10 8 = 4 must be rejected"
    );
}

#[test]
fn test_b84_multiscrut_three_scrutinee_recursive() {
    // 3-scrutinee recursive variant: the right-nested Prod spine unpacks to
    // three binder components; recursion decreases on the first. The
    // decreasing pattern var is FRESH (`k`): a pattern var that SHADOWS the
    // decreasing binder (`| a + 1, b, c => … f a b c`) fails identically in
    // the plain single-scrutinee form today (pre-existing 3-param limitation,
    // not a B84 regression) and stays out of scope here.
    let code = "def ed8_add3 (a b c : Nat) : Nat :=\n  match a, b, c with\n  | 0, b, c => b + c\n  | k + 1, b, c => 1 + ed8_add3 k b c\n\
        theorem ed8v : ed8_add3 2 3 4 = 9 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "b84 three-scrutinee recursive");
}

#[test]
fn test_b84_multiscrut_controls() {
    // Controls that MUST stay green (previously-working classes):
    // (a) NON-recursive multi-scrutinee match def — keeps the tuple-casesOn
    //     path (the B84 normalizer is engagement-gated on recursion);
    // (b) single-scrutinee recursive def — the existing `.rec` lowering.
    let code = "def mnr84 (a b : Nat) : Nat := match a, b with\n  | 0, m => m\n  | x, y => x + y\n\
        theorem mnr84a : mnr84 0 5 = 5 := rfl\n\
        theorem mnr84b : mnr84 2 3 = 5 := rfl\n\
        def lg4 (n : Nat) : Nat := match n with\n  | 0 => 0\n  | k + 1 => lg4 k + 1\n\
        theorem lg4a : lg4 3 = 3 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "b84 controls");
}

#[test]
fn test_b84_control_single_scrut_three_params() {
    // Control: the plain single-scrutinee 3-param recursive shape the B84
    // rewrite lowers INTO (fresh decreasing pattern var, two trailing
    // extra params) — must stay green independently of the rewrite.
    let code = "def ed8t (a b c : Nat) : Nat :=\n  match a with\n  | 0 => b + c\n  | k + 1 => 1 + ed8t k b c\n\
        theorem ed8tv : ed8t 2 3 4 = 9 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "b84 control single-scrut 3 params",
    );
}

// ---------------------------------------------------------------------------
// Brick 85: a failed `by omega` names omega, not the leaked linarith fallback.
// Brick 86: curried dependent match descopes loudly instead of silently
// dropping non-match-column pattern-variable bindings.
// ---------------------------------------------------------------------------

#[test]
fn test_omega_failure_names_omega_not_leaked_linarith() {
    // Brick 85: the omega pipeline's terminal fallback delegates to linarith
    // and previously propagated its error VERBATIM, so a failed `by omega`
    // reported `tactic: "linarith"` — a tactic the user never wrote. What
    // this test locks is that the failure names omega, with the fallback
    // recorded in the reason. (The original single-variable case-split goal
    // `n = 0 ∨ n = 1` now PROVES via the brick-87 lane, so the lock shape is
    // a two-variable disjunction — outside the b87 slice, still fallback-fed.)
    let code = "example (n m : Nat) (h : n \u{2264} 1) : n = 0 \u{2228} m = 0 := by omega\n";
    let (_, results) = elab_file_prelude(code);
    let err = results
        .iter()
        .find_map(|r| r.as_ref().err())
        .expect("two-variable disjunction omega goal should fail via the linarith fallback");
    let debug = format!("{err:?}");
    assert!(
        debug.contains("omega"),
        "failed `by omega` must name omega, got: {debug}"
    );
    assert!(
        debug.contains("linarith fallback"),
        "reason should record the linarith fallback, got: {debug}"
    );
    assert!(
        !debug.contains("tactic: \"linarith\""),
        "the leaked fallback tactic label must be gone, got: {debug}"
    );
}

// ---------------------------------------------------------------------------
// Brick 87: omega proves bounded case-split goals (`(h : n ≤ k) ⊢ n = 0 ∨ …
// ∨ n = k`) via a closed interval-descent term, kernel-re-checked.
// ---------------------------------------------------------------------------

#[test]
fn test_b87_omega_case_split() {
    // The everyday R65-family case split: compound `Or` goals were silently
    // dropped from omega's constraint system (hyps-only system is Sat) and
    // always fell to the failing linarith delegate. The b87 lane detects the
    // shape and proves it with a real kernel-checked Or.rec descent.
    let code = "theorem t87 (n : Nat) (h : n \u{2264} 1) : n = 0 \u{2228} n = 1 := by omega\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "b87 case split k=1");
    assert!(
        env.get_const(&Name::from_string("t87")).is_some(),
        "t87 should be registered"
    );
}

#[test]
fn test_b87_omega_case_split_wrong_rejected() {
    // Wrong disjunct set: the bound admits n = 1 but no disjunct states it —
    // the goal is FALSE and must be rejected (loud), never silently proved.
    let code = "theorem t87w (n : Nat) (h : n \u{2264} 1) : n = 0 \u{2228} n = 2 := by omega\n";
    let (env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false case-split goal must be rejected, got: {results:?}"
    );
    assert!(
        env.get_const(&Name::from_string("t87w")).is_none(),
        "t87w must not be registered"
    );
}

#[test]
fn test_b87_omega_case_split_k2_and_lt_bound() {
    // k = 2 (three disjuncts) plus the strict-bound variant `n < 3`
    // (≡ n ≤ 2), and disjuncts listed out of value order.
    let code = "theorem t87b (n : Nat) (h : n \u{2264} 2) : n = 0 \u{2228} n = 1 \u{2228} n = 2 := by omega\n\
        theorem t87c (n : Nat) (h : n < 3) : n = 2 \u{2228} n = 0 \u{2228} n = 1 := by omega\n";
    let (_, results) = elab_file_prelude(code);
    assert_all_ok(&results, "b87 case split k=2 + lt bound");
}

#[test]
fn test_b86_curried_dep_match_dropped_var_column_loud() {
    // Brick 86: the curried dependent-match lowering matches on ONE column
    // and used to silently discard pattern-variable bindings in the other
    // columns — a dropped `k` died as UnknownIdent far downstream. The drop
    // must be a loud descope at the source.
    //
    // MOVED (Brick 88): the original 2-arity `f7` shape now normalizes in the
    // multiarg equation path (per-row dependent-family refinement, see
    // `test_b88_dep_family_multiarg`) and never reaches the curried fallback.
    // The descope lock therefore moves to a still-descoped 3-arity dependent
    // variant — Brick 88 is gated to arity == 2, so this shape still routes
    // to the curried fallback and must keep failing LOUDLY, not by silently
    // dropping the `true`/`false`/`k`/`m` columns.
    let code = "def T9 : Nat \u{2192} Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def f8 : (n : Nat) \u{2192} T9 n \u{2192} Nat \u{2192} Nat\n  | 0, true, m => m\n  | 0, false, m => 0\n  | _+1, k, m => (k : Nat) + m\n";
    let (_, results) = elab_file_prelude(code);
    let err = results.iter().find_map(|r| r.as_ref().err()).expect(
        "f8 dropped-column shape should fail (multi-column dependent match beyond arity 2 is a future brick)",
    );
    let debug = format!("{err:?}");
    assert!(
        debug.contains("not bound by this lowering"),
        "dropped pattern variable must fail as a loud descope, got: {debug}"
    );
    assert!(
        !debug.contains("UnknownIdent(\"k\")") && !debug.contains("UnknownIdent(\"m\")"),
        "must not die as a silent downstream UnknownIdent, got: {debug}"
    );
}

#[test]
fn test_b88_dep_family_multiarg() {
    // Brick 88: dependent type-family second domain in a 2-arity equation def.
    // The per-row kernel-whnf probe refines `T9 0 → Bool` / `T9 (_+1) → Nat`,
    // rewrites each row's second-column leaf against ITS refined inductive,
    // and re-emits with the dependent domain in the return type so the
    // dependent-motive lane elaborates it. Kernel-checked end to end,
    // including rfl reduction through the emitted casesOn.
    let code = "def T9 : Nat \u{2192} Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def f7 : (n : Nat) \u{2192} T9 n \u{2192} Nat\n  | 0, true => 1\n  | 0, false => 0\n  | _+1, k => (k : Nat)\n\
        theorem f7a : f7 3 2 = 2 := rfl\n\
        theorem f7b : f7 0 true = 1 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "b88 dependent-family multiarg equation def");
    assert!(
        env.get_const(&Name::from_string("f7")).is_some(),
        "f7 should be registered"
    );
}

#[test]
fn test_b88_dep_family_wrong_value_rejected() {
    // Soundness twin: the same f7 must NOT prove a wrong equation. `f7 3 2`
    // reduces to 2, so `= 3` by rfl must be rejected loudly.
    let code = "def T9 : Nat \u{2192} Type\n  | 0 => Bool\n  | _+1 => Nat\n\
        def f7 : (n : Nat) \u{2192} T9 n \u{2192} Nat\n  | 0, true => 1\n  | 0, false => 0\n  | _+1, k => (k : Nat)\n\
        theorem f7w : f7 3 2 = 3 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert!(
        results
            .last()
            .expect("theorem f7w should have a result")
            .is_err(),
        "wrong-value rfl must be rejected, got: {:?}",
        results.last()
    );
    assert!(
        env.get_const(&Name::from_string("f7w")).is_none(),
        "f7w must not be registered"
    );
}

// ---------------------------------------------------------------------------
// Brick 89: shadowed decreasing pattern variable in single-scrutinee match
// recursion. `| a + 1 => 1 + f a b c` rebinds the PARAMETER name to the
// predecessor; the decreasing-arg detector now prefers the whole-body match
// scrutinee position, so the recursion context installs at the right slot.
// ---------------------------------------------------------------------------

#[test]
fn test_b89_shadowed_decreasing_two_param() {
    let code = "def lg2s (fuel n : Nat) : Nat :=\n  match fuel with\n  | 0 => n\n  | fuel + 1 => 1 + lg2s fuel n\n\
        theorem lg2sa : lg2s 2 5 = 7 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "2-param shadowed decreasing");
}

#[test]
fn test_b89_shadowed_decreasing_three_param() {
    let code = "def ed8s (a b c : Nat) : Nat :=\n  match a with\n  | 0 => b + c\n  | a + 1 => 1 + ed8s a b c\n\
        theorem ed8sa : ed8s 2 3 4 = 9 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "3-param shadowed decreasing");
}

#[test]
fn test_b89_shadowed_decreasing_wrong_value_rejected() {
    let code = "def ed8w (a b c : Nat) : Nat :=\n  match a with\n  | 0 => b + c\n  | a + 1 => 1 + ed8w a b c\n\
        theorem ed8wa : ed8w 2 3 4 = 10 := rfl\n";
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong-value ed8w 2 3 4 = 10 must be rejected"
    );
}

#[test]
fn test_b89_fresh_var_control() {
    let code = "def ed8f (a b c : Nat) : Nat :=\n  match a with\n  | 0 => b + c\n  | k + 1 => 1 + ed8f k b c\n\
        theorem ed8fa : ed8f 2 3 4 = 9 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "fresh-var control");
}

// ---------------------------------------------------------------------------
// Round-79 discovery lock — 21 verified behaviors from six fresh domains
// (structure-inheritance defaults, Char/String methods, Prop-decide chains,
// GADT-indexed reduce, mutual defs, let-in-type). The 33 failures are
// clustered + recorded in the memory backlog (structure default-override
// parser gap, Char/String method tier, decide-instance gaps, GADT pattern
// arity, mutual-def lowering, let-in-type ascription).
// ---------------------------------------------------------------------------

#[test]
fn test_r79_discovery_lock() {
    let locked: &[(&str, &str)] = &[
        ("sid_child_default_references_parent_field", "structure SIDPoint where\n  a : Nat := 2\nstructure SIDLine extends SIDPoint where\n  b : Nat := a + a\ntheorem sidParentRef : ({ a := 7 } : SIDLine).b = 14 := rfl"),
        ("sid_update_extended_struct_preserves_inherited", "structure SIDA where\n  p : Nat := 1\n  q : Nat := 2\nstructure SIDB extends SIDA where\n  r : Nat := 3\ndef sidB0 : SIDB := { p := 10 }\ntheorem sidUpdKeep : ({ sidB0 with r := 30 } : SIDB).p = 10 ∧ ({ sidB0 with q := 20 } : SIDB).r = 3 := ⟨rfl, rfl⟩"),
        ("sid_three_level_chain_defaults_each_level", "structure SIDL1 where\n  a : Nat := 1\nstructure SIDL2 extends SIDL1 where\n  b : Nat := a + 1\nstructure SIDL3 extends SIDL2 where\n  c : Nat := a + b\ntheorem sidChainDefault : ({} : SIDL3).c = 3 ∧ ({ a := 5 } : SIDL3).c = 11 := ⟨rfl, rfl⟩"),
        ("sid_multi_parent_extends_default_mixes_parents", "structure SIDLeft where\n  n : Nat := 1\nstructure SIDRight where\n  m : Nat := 2\nstructure SIDBoth extends SIDLeft, SIDRight where\n  s : Nat := n + m\ntheorem sidMultiParent : ({} : SIDBoth).s = 3 ∧ ({ m := 10 } : SIDBoth).s = 11 := ⟨rfl, rfl⟩"),
        ("sid_deep_update_grandparent_field", "structure SIDG1 where\n  g : Nat := 1\nstructure SIDG2 extends SIDG1 where\n  h : Nat := 2\nstructure SIDG3 extends SIDG2 where\n  k : Nat := 3\ndef sidG : SIDG3 := {}\ntheorem sidDeepUpdate : ({ sidG with g := 9 } : SIDG3).g = 9 ∧ ({ sidG with g := 9 } : SIDG3).h = 2 := ⟨rfl, rfl⟩"),
        ("charstr_ofnat_edges", "theorem charstr_ofnat_valid : Char.ofNat 65 = 'A' := rfl\ntheorem charstr_ofnat_surrogate : (Char.ofNat 55296).toNat = 0 := rfl\ntheorem charstr_tonat_utf8 : 'é'.toNat = 233 := rfl"),
        ("pdc-and-or-not-chain", "theorem pdcAndOrNotTrue :\n    decide ((2 = 2 ∧ ¬ (3 = 4)) ∨ 5 < 3) = true := rfl\ntheorem pdcAndOrNotFalse :\n    decide ((2 = 2 ∧ 3 = 4) ∨ ¬ (1 ≤ 4)) = false := rfl"),
        ("pdc-dite-compound-cond", "theorem pdcDiteOr : (dite (2 = 2 ∨ 3 = 5) (fun _ => 7) (fun _ => 9)) = 7 := rfl\ntheorem pdcDifSyntax : (if _h : 2 ≠ 3 ∧ 1 ≤ 1 then 1 else 0) = 1 := rfl\ntheorem pdcDiteNe : (dite (4 ≠ 4) (fun _ => 3) (fun _ => 5)) = 5 := rfl"),
        ("pdc-bool-decide-roundtrip", "theorem pdcRoundtrip : decide (decide (5 = 5) = true) = true := rfl\ntheorem pdcRoundtripNe : decide (decide (5 = 6) = false) = true := rfl\ntheorem pdcDecideAndBool : (decide (2 ≤ 3) && decide (¬ (4 < 2))) = true := rfl"),
        ("gadt_casesOn_motive_bang_index", "inductive GadtTag : Bool → Type where\n  | isT : GadtTag true\n  | isF : GadtTag false\ndef gadtTagFlip (t : GadtTag b) : GadtTag (!b) :=\n  GadtTag.casesOn (motive := fun b _ => GadtTag (!b)) t .isF .isT\ntheorem gadtTagFlip_t : gadtTagFlip GadtTag.isT = GadtTag.isF := rfl"),
        ("mutualdef-even-odd-literal-reduction", "mutual\ndef mutualdefIsEven : Nat → Bool | 0 => true | n+1 => mutualdefIsOdd n\ndef mutualdefIsOdd : Nat → Bool | 0 => false | n+1 => mutualdefIsEven n\nend\ntheorem mutualdefEvenOdd_lock : mutualdefIsEven 10 = true ∧ mutualdefIsOdd 7 = true := ⟨rfl, rfl⟩"),
        ("mutualdef-asymmetric-callgraph", "mutual\ndef mutualdefF : Nat → Nat | 0 => 1 | n+1 => mutualdefG n + mutualdefF n\ndef mutualdefG : Nat → Nat | 0 => 2 | n+1 => mutualdefF n\nend\ntheorem mutualdefFG_lock : mutualdefF 3 = 7 ∧ mutualdefG 2 = 3 := ⟨rfl, rfl⟩"),
        ("mutualdef-threeway-cycle", "mutual\ndef mutualdefRed : Nat → Nat | 0 => 0 | n+1 => mutualdefGreen n + 1\ndef mutualdefGreen : Nat → Nat | 0 => 1 | n+1 => mutualdefBlue n + 2\ndef mutualdefBlue : Nat → Nat | 0 => 2 | n+1 => mutualdefRed n + 3\nend\ntheorem mutualdefRGB_lock : mutualdefRed 3 = 6 ∧ mutualdefBlue 2 = 5 := ⟨rfl, rfl⟩"),
        ("letT_def_type_pi_under_let", "def letTfunTy : let T := Nat; T -> T := fun x => x + 2\ntheorem letTfunTy_eq : letTfunTy 3 = 5 := rfl"),
        ("letT_binder_type_let", "def letTbind (x : let T := Nat; T) : Nat := x + 3\ntheorem letTbind_eq : letTbind 4 = 7 := rfl"),
        ("letT_abbrev_chain_in_type", "abbrev letTA := Nat\nabbrev letTB := letTA\ndef letTbVal : letTB := 6\ntheorem letTbVal_eq : letTbVal + 1 = 7 := rfl"),
        ("letT_typelevel_fun_applied", "def letTapp : let F := fun (_ : Nat) => Nat; F 3 := 11\ntheorem letTapp_eq : letTapp = 11 := rfl"),
        ("letT_typelevel_match_under_let", "def letTsel (b : Bool) : Type := match b with | true => Nat | false => Bool\ndef letTselVal : let X := letTsel true; X := (5 : Nat)\ntheorem letTselVal_eq : letTselVal = (5 : Nat) := rfl"),
        ("letT_nested_dependent_lets_in_thm", "theorem letTnest : let a := 2; let b := a * 3; b = 6 := rfl"),
        ("letT_let_over_Type_universe", "def letTuniv : let T := Type; T := Nat\ntheorem letTuniv_eq : letTuniv = Nat := rfl"),
        ("letT_let_pi_argument_type", "def letTpi : (let T := Nat; T -> T) -> Nat := fun f => f 5\ntheorem letTpi_eq : letTpi (fun x => x + 1) = 6 := rfl"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 21, "expected 21 locked r79 behaviors");
}

// ---------------------------------------------------------------------------
// Brick 90: structure field-default OVERRIDE (`extends Base where x := 10`,
// a bare `name := value` re-default of an inherited field, Lean
// `structSimpleBinder` with no type ascription) + def-where struct-instance
// sugar (`def x : S where\n  f := v`). R79 cluster 1.
// ---------------------------------------------------------------------------

#[test]
fn test_b90_struct_default_override_value() {
    let code = "structure SIDBase where\n  x : Nat := 3\n  y : Nat := 5\n\
        structure SIDChild extends SIDBase where\n  x := 10\n  z : Nat := 1\n\
        theorem sidOverride : ({} : SIDChild).x = 10 \u{2227} ({} : SIDChild).y = 5 := \u{27e8}rfl, rfl\u{27e9}\n";
    assert_all_ok(&elab_file_prelude(code).1, "b90 default override value");
}

#[test]
fn test_b90_struct_default_override_wrong_value_rejected() {
    // Soundness twin: the override must actually take effect — the PARENT
    // default 3 must no longer be provable for `x` by rfl.
    let code = "structure SIDBase where\n  x : Nat := 3\n  y : Nat := 5\n\
        structure SIDChild extends SIDBase where\n  x := 10\n  z : Nat := 1\n\
        theorem sidOverrideW : ({} : SIDChild).x = 3 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert!(
        results
            .last()
            .expect("theorem sidOverrideW should have a result")
            .is_err(),
        "overridden default must reject the parent value by rfl, got: {:?}",
        results.last()
    );
    assert!(
        env.get_const(&Name::from_string("sidOverrideW")).is_none(),
        "sidOverrideW must not be registered"
    );
}

#[test]
fn test_b90_mid_level_override_propagates() {
    // The override lives on the MIDDLE structure; a grandchild default and a
    // grandchild literal must both see the overridden value.
    let code = "structure SIDCfg where\n  w : Nat := 2\n\
        structure SIDMid extends SIDCfg where\n  w := 8\n\
        structure SIDTop extends SIDMid where\n  v : Nat := w * w\n\
        theorem sidOverridePropagate : ({} : SIDTop).v = 64 \u{2227} ({} : SIDTop).w = 8 := \u{27e8}rfl, rfl\u{27e9}\n";
    assert_all_ok(&elab_file_prelude(code).1, "b90 mid-level override");
}

#[test]
fn test_b90_def_where_partial_fields() {
    // `def x : S where\n  f := v` struct-instance sugar, with the remaining
    // fields filled from defaults (including a default referencing the
    // supplied inherited field).
    let code = "structure SIDOpt where\n  lvl : Nat := 1\n  tag : Nat := 0\n\
        structure SIDOpts extends SIDOpt where\n  fast : Bool := lvl == 2\n\
        def sidO : SIDOpts where\n  lvl := 2\n\
        theorem sidWhereDefault : sidO.fast = true \u{2227} sidO.tag = 0 := \u{27e8}rfl, rfl\u{27e9}\n";
    assert_all_ok(&elab_file_prelude(code).1, "b90 def-where struct init");
}

#[test]
fn test_b90_override_unknown_field_loud() {
    // A bare `name := value` override of a name that is NOT an inherited
    // field must fail loudly at the structure declaration, never silently
    // succeed.
    let code = "structure OB where\n  a : Nat := 1\n\
        structure OC extends OB where\n  nosuch := 5\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "override of a non-inherited field must be rejected loudly, got: {results:?}"
    );
}

#[test]
fn test_b90_typed_default_control() {
    // Engagement gate: the pre-existing typed-field-with-default shape
    // (`q : Nat := p + 1`) must keep working unchanged alongside B90.
    let code = "structure TB where\n  p : Nat := 4\n\
        structure TC extends TB where\n  q : Nat := p + 1\n\
        theorem tc1 : ({} : TC).q = 5 := rfl\n";
    assert_all_ok(&elab_file_prelude(code).1, "b90 typed default control");
}

// ---------------------------------------------------------------------------
// B91: recursive match over an indexed family with implicit index fields.
// The ctor-ordered rec planner expands implicit ctor field patterns
// (`.cons a t` -> `[_, a, t]` for `cons : {n} -> α -> Vec α n -> Vec α (n+1)`)
// and the rec-arm elaboration re-normalizes; `expand_implicit_ctor_field_patterns`
// documented idempotence but rejected its own output, so EVERY recursive match
// over such a family died with ConstructorPatternArityMismatch. The idempotence
// arm accepts exactly the helper's own output shape (full arity + Wildcard at
// every implicit position); user patterns at implicit slots stay loud.
// ---------------------------------------------------------------------------

#[test]
fn test_b91_gadt_two_index_rec_match_value() {
    let src = r#"inductive GadtLE : Nat → Nat → Type where
  | refl : GadtLE n n
  | step : GadtLE m n → GadtLE m (n+1)
def gadtGap : GadtLE m n → Nat | .refl => 0 | .step h => gadtGap h + 1
theorem gadtGap_two : gadtGap (.step (.step (.refl : GadtLE 3 3))) = 2 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b91 two-index rec match value");
}

#[test]
fn test_b91_gadt_one_index_rec_len_value() {
    let src = r#"inductive GadtDVec (α : Type) : Nat → Type where
  | nil : GadtDVec α 0
  | cons : α → GadtDVec α n → GadtDVec α (n+1)
def gadtDLen : GadtDVec α n → Nat | .nil => 0 | .cons _ t => gadtDLen t + 1
theorem gadtDLen_two : gadtDLen (.cons 1 (.cons 2 .nil)) = 2 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b91 one-index rec len value");
}

#[test]
fn test_b91_gadt_wrong_value_rejected() {
    let src = r#"inductive GadtLE : Nat → Nat → Type where
  | refl : GadtLE n n
  | step : GadtLE m n → GadtLE m (n+1)
def gadtGap : GadtLE m n → Nat | .refl => 0 | .step h => gadtGap h + 1
theorem gadtGap_wrong : gadtGap (.step (.step (.refl : GadtLE 3 3))) = 3 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b91: wrong value 3 must be rejected (actual gap is 2)"
    );
}

#[test]
fn test_b91_pattern_at_implicit_slot_still_loud() {
    let src = r#"inductive GadtDVec (α : Type) : Nat → Type where
  | nil : GadtDVec α 0
  | cons : α → GadtDVec α n → GadtDVec α (n+1)
def bad : GadtDVec α n → Nat | .nil => 0 | .cons a b c => 0"#;
    let (_env, results) = elab_file_prelude(src);
    let err = format!(
        "{:?}",
        results
            .last()
            .expect("def decl present")
            .as_ref()
            .expect_err(
                "b91: binding pattern at the implicit index slot must stay a loud arity error"
            )
    );
    assert!(
        err.contains("ConstructorPatternArityMismatch"),
        "b91: expected ConstructorPatternArityMismatch, got: {err}"
    );
}

#[test]
fn test_b91_under_arity_still_loud() {
    let src = r#"inductive GadtDVec (α : Type) : Nat → Type where
  | nil : GadtDVec α 0
  | cons : α → GadtDVec α n → GadtDVec α (n+1)
def bad : GadtDVec α n → Nat | .nil => 0 | .cons a => 0"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("def decl present").is_err(),
        "b91: writing fewer patterns than explicit fields must stay loud"
    );
}

// ---------------------------------------------------------------------------
// B92: named-argument calls on structure/class projections. Projections are
// registered as ordinary definitions but never recorded binder names, so
// `Class.proj (α := T)` hit the no-recorded-binder-names LOUD descope. Every
// projection of a structure shares one binder row — the structure's binders
// then the receiver `self` — now recorded at registration.
// ---------------------------------------------------------------------------

#[test]
fn test_b92_class_projection_named_arg_value() {
    let src = r#"class B92C (α : Type) where
  val : Nat
instance : B92C Nat where
  val := 7
def b92get : Nat := B92C.val (α := Nat)
theorem b92get_eq : b92get = 7 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b92 class projection named arg");
}

#[test]
fn test_b92_structure_projection_named_self() {
    let src = r#"structure B92P where
  x : Nat
  y : Nat
def b92p : B92P := ⟨3, 5⟩
theorem b92p_x : B92P.x (self := b92p) = 3 := rfl
theorem b92p_y : B92P.y (self := b92p) = 5 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b92 structure projection named self");
}

#[test]
fn test_b92_wrong_value_rejected() {
    let src = r#"class B92C (α : Type) where
  val : Nat
instance : B92C Nat where
  val := 7
def b92get : Nat := B92C.val (α := Nat)
theorem b92get_wrong : b92get = 8 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b92: wrong value 8 must be rejected (val is 7)"
    );
}

#[test]
fn test_b92_unknown_named_arg_still_loud() {
    let src = r#"structure B92Q where
  x : Nat
def b92q : Nat := B92Q.x (nosuch := 3)"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("def decl present").is_err(),
        "b92: a named arg that matches no projection binder must stay loud"
    );
}

// ---------------------------------------------------------------------------
// B93: multi-accumulator `for` loops in the pure do lane (B23 extension).
// Several outer `let mut` accumulators pack into one right-nested `Prod`
// ForIn accumulator (sorted-name order); a body-local `let mut` threads
// per-iteration; a nested `for` lowers recursively through the same core.
// Single-accumulator loops keep the exact B23 term (engagement gate: the
// r82 do-loop locks doearly_sumbreak/oddskip/mixbc).
// ---------------------------------------------------------------------------

#[test]
fn test_b93_two_accumulators_value() {
    // Evens of range 6 are 0, 2, 4 → s = 6, c = 3 → 6 * 10 + 3 = 63.
    let src = r#"def doearlyTwoAcc : Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for i in List.range 6 do
    if i % 2 == 1 then
      continue
    s := s + i
    c := c + 1
  return s * 10 + c
theorem doearlyTwoAcc_eq : doearlyTwoAcc = 63 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b93 two accumulators value");
}

#[test]
fn test_b93_two_acc_wrong_value_rejected() {
    let src = r#"def doearlyTwoAccW : Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for i in List.range 6 do
    if i % 2 == 1 then
      continue
    s := s + i
    c := c + 1
  return s * 10 + c
theorem doearlyTwoAccW_eq : doearlyTwoAccW = 64 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b93: wrong value 64 must be rejected (actual value is 63)"
    );
}

#[test]
fn test_b93_outerskip_value() {
    // The r82 `doearly_outerskip` semantics: outer accumulator `total`,
    // body-local `let mut composite` probed by a nested `for` with `break`,
    // and a `continue` skip guard. Hand-check: 5 and 7 (not divisible by 2 or
    // 3) pass the composite skip; 6 and 9 are skipped → total = 5 + 7 = 12.
    //
    // Historical: this hoisted-break formulation predates B94 (which fixed
    // the else-less do-if branch truncation); the verbatim candidate is now
    // pinned by `test_b94_outerskip_verbatim_value`. Kept as an independent
    // shape (break-guard-first inner loop).
    let src = r#"def doearlyOuterSkip : Nat := Id.run do
  let mut total := 0
  for i in [5, 6, 7, 9] do
    let mut composite := false
    for d in [2, 3] do
      if composite then
        break
      if i % d == 0 then
        composite := true
    if composite then
      continue
    total := total + i
  return total

theorem doearlyOuterSkip_eq : doearlyOuterSkip = 12 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b93 outer accumulator + body-local skip");
}

#[test]
fn test_b94_outerskip_verbatim_value() {
    // The exact r82 `doearly_outerskip` candidate, VERBATIM: inner then-branch
    // `composite := true` followed by `break` at the same column. Previously
    // the else-less do-if backtrack re-parsed the branch as a single element
    // with the branch indent column dropped, so `break` was swallowed into the
    // application spine (`composite := (true break)`). Hand-check: 5 and 7
    // survive the composite skip; 6 and 9 are skipped -> total = 12.
    let src = "def doearlyOuterSkip : Nat := Id.run do\n  let mut total := 0\n  for i in [5, 6, 7, 9] do\n    let mut composite := false\n    for d in [2, 3] do\n      if i % d == 0 then\n        composite := true\n        break\n    if composite then\n      continue\n    total := total + i\n  return total\n\ntheorem doearlyOuterSkip_eq : doearlyOuterSkip = 12 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b94 verbatim outerskip value");
}

#[test]
fn test_b94_multi_stmt_then_no_else_skipped_value() {
    // Value-distinguishing pin of the B94 semantics fix: with a FALSE guard,
    // BOTH branch statements must be skipped. The old backtrack kept only
    // `x := 1` conditional and ran `x := x + 5` unconditionally, making the
    // WRONG value 5 provable here.
    let src = r#"def b94Skip : Nat := Id.run do
  let mut x := 0
  if 2 < 1 then
    x := 1
    x := x + 5
  return x
theorem b94Skip_eq : b94Skip = 0 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b94 false-guard multi-stmt then skipped");
}

#[test]
fn test_b94_multi_stmt_then_old_semantics_rejected() {
    // The exact value the pre-B94 backtracked semantics produced (5) must be
    // REJECTED now.
    let src = r#"def b94Skip : Nat := Id.run do
  let mut x := 0
  if 2 < 1 then
    x := 1
    x := x + 5
  return x
theorem b94Skip_wrong : b94Skip = 5 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b94: the old truncated-branch value 5 must no longer be provable"
    );
}

#[test]
fn test_b94_multi_stmt_then_taken_value() {
    // True-guard twin: both branch statements run -> 1 + 5 = 6.
    let src = r#"def b94Take : Nat := Id.run do
  let mut x := 0
  if 1 < 2 then
    x := 1
    x := x + 5
  return x
theorem b94Take_eq : b94Take = 6 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b94 true-guard multi-stmt then taken");
}

#[test]
fn test_b94_single_stmt_then_control() {
    // Engagement control: the everyday single-statement else-less then is
    // untouched.
    let src = r#"def b94One : Nat := Id.run do
  let mut x := 0
  if 1 < 2 then
    x := 3
  return x
theorem b94One_eq : b94One = 3 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b94 single-stmt then control");
}

#[test]
fn test_b93_three_accumulators_value() {
    // range 5 = 0..4: s = 10, c = 5, m = 4 → 10 * 100 + 5 * 10 + 4 = 1054.
    let src = r#"def doearlyThreeAcc : Nat := Id.run do
  let mut s := 0
  let mut c := 0
  let mut m := 0
  for i in List.range 5 do
    s := s + i
    c := c + 1
    if i > m then
      m := i
  return s * 100 + c * 10 + m
theorem doearlyThreeAcc_eq : doearlyThreeAcc = 1054 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b93 three accumulators value");
}

#[test]
fn test_b93_single_acc_control() {
    // Engagement control: a fresh single-accumulator loop stays on the exact
    // B23 path. 0 + 1 + 2 + 3 + 4 = 10, then i = 5 breaks.
    let src = r#"def b93SingleAcc : Nat := Id.run do
  let mut s := 0
  for i in List.range 7 do
    if i > 4 then
      break
    s := s + i
  return s
theorem b93SingleAcc_eq : b93SingleAcc = 10 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b93 single accumulator control");
}

#[test]
fn test_b93_break_with_two_accs() {
    // i = 0..3 accumulate (s = 6, c = 4); at i = 4 the guard s > 5 breaks
    // with the at-break values → 6 * 10 + 4 = 64.
    let src = r#"def b93BreakTwo : Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for i in List.range 10 do
    if s > 5 then
      break
    s := s + i
    c := c + 1
  return s * 10 + c
theorem b93BreakTwo_eq : b93BreakTwo = 64 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b93 break with two accumulators");
}

// ---------------------------------------------------------------------------
// Round-82 discovery lock — verified behaviors from six fresh domains
// (instance priority/default-instance, structure eta + anonymous-ctor depth,
// do early-return/break/continue, s! string interpolation, literal arithmetic
// in type positions, absurd/empty patterns). The 26 failures are clustered in
// the memory backlog: do-loop B23 limits (nested for, multi-accumulator,
// early return), instance-scoping silent-wrongs (local/scoped leak,
// priority := low ignored, default_instance on open mvar), Fin-bound
// arithmetic OfNat, nofun sugar, empty-match tier, interpolation escapes.
// ---------------------------------------------------------------------------

#[test]
fn test_r82_discovery_lock() {
    let locked: &[(&str, &str)] = &[
        ("doearly_sumbreak", "def doearlySumBreak : Nat := Id.run do\n  let mut s := 0\n  for i in List.range 10 do\n    if s > 6 then\n      break\n    s := s + i\n  return s\n\ntheorem doearlySumBreak_eq : doearlySumBreak = 10 := rfl"),
        ("doearly_oddskip", "def doearlyOddSkip : Nat := Id.run do\n  let mut s := 0\n  for i in List.range 8 do\n    if i % 2 == 0 then\n      continue\n    s := s + i\n  return s\n\ntheorem doearlyOddSkip_eq : doearlyOddSkip = 16 := rfl"),
        ("doearly_mixbc", "def doearlyMixBC : Nat := Id.run do\n  let mut s := 0\n  for i in List.range 12 do\n    if i % 2 == 1 then\n      continue\n    if i > 7 then\n      break\n    s := s + i\n  return s\n\ntheorem doearlyMixBC_eq : doearlyMixBC = 12 := rfl"),
        ("strinterp_natlit", "def strinterp_natlit (n : Nat) : String := s!\"{n}\"\n\ntheorem strinterp_natlit_val : strinterp_natlit 42 = \"42\" := rfl"),
        ("strinterp_arith", "def strinterp_arith : String := s!\"sum is {2 + 3}\"\n\ntheorem strinterp_arith_val : strinterp_arith = \"sum is 5\" := rfl"),
        ("strinterp_multihole", "def strinterp_multihole (a b : Nat) : String := s!\"{a}+{b}={a + b}\"\n\ntheorem strinterp_multihole_val : strinterp_multihole 2 3 = \"2+3=5\" := rfl"),
        ("strinterp_nested", "def strinterp_nested (n : Nat) : String := s!\"[{s!\"<{n}>\"}]\"\n\ntheorem strinterp_nested_val : strinterp_nested 7 = \"[<7>]\" := rfl"),
        ("strinterp_chain", "def strinterp_chain (n : Nat) : String := s!\"{n}\" ++ \"-\" ++ s!\"{n + 1}\"\n\ntheorem strinterp_chain_val : strinterp_chain 4 = \"4-5\" := rfl"),
        ("strinterp_strid", "def strinterp_strid (s : String) : String := s!\"({s})\"\n\ntheorem strinterp_strid_val : strinterp_strid \"hi\" = \"(hi)\" := rfl"),
        ("strinterp_append", "def strinterp_append : String := String.append (Nat.repr 12) (String.append \"-\" (toString false))\n\ntheorem strinterp_append_val : strinterp_append = \"12-false\" := rfl"),
        ("strinterp_boolop", "def strinterp_boolop : String := s!\"{true && false}!\"\n\ntheorem strinterp_boolop_val : strinterp_boolop = \"false!\" := rfl"),
        ("etaanon_nestedstruct", "structure EtaanonIn where\n  a : Nat\n  b : Nat\n\nstructure EtaanonOut where\n  inner : EtaanonIn\n  c : Nat\n\ndef etaanon_nested : EtaanonOut := ⟨⟨1, 2⟩, 3⟩\n\ntheorem etaanon_nested_val : etaanon_nested.inner.b + etaanon_nested.c = 5 := rfl"),
        ("etaanon_prodflat", "def etaanon_flat : Nat × Nat × Nat := ⟨1, 2, 3⟩\n\ntheorem etaanon_flat_mid : etaanon_flat.2.1 = 2 := rfl\n\ntheorem etaanon_flat_sum : etaanon_flat.1 + etaanon_flat.2.2 = 4 := rfl"),
        ("etaanon_mketa", "structure EtaanonPt where\n  x : Nat\n  y : Nat\n\ntheorem etaanon_mk_eta (s : EtaanonPt) : EtaanonPt.mk s.x s.y = s := rfl\n\ntheorem etaanon_mk_eta_val : (EtaanonPt.mk 5 7).y + (⟨1, 2⟩ : EtaanonPt).x = 8 := rfl"),
        ("etaanon_lamid", "theorem etaanon_lam_eta : (fun p : Nat × Nat => (⟨p.1, p.2⟩ : Nat × Nat)) = id := rfl\n\ntheorem etaanon_lam_eta_app : ((fun p : Nat × Nat => (⟨p.1, p.2⟩ : Nat × Nat)) ⟨3, 9⟩).2 = 9 := rfl"),
        ("etaanon_abbrevalias", "structure EtaanonBox where\n  val : Nat\n\nabbrev EtaanonBoxA := EtaanonBox\nabbrev EtaanonPairA := Nat × EtaanonBoxA\n\ndef etaanon_ab : EtaanonPairA := ⟨10, ⟨32⟩⟩\n\ntheorem etaanon_ab_sum : etaanon_ab.1 + etaanon_ab.2.val = 42 := rfl"),
        ("etaanon_existsand", "theorem etaanon_and_pair : 2 + 2 = 4 ∧ 3 * 3 = 9 := ⟨rfl, rfl⟩\n\ntheorem etaanon_exists_and : ∃ n : Nat, n + 3 = 7 ∧ n * 2 = 8 := ⟨4, rfl, rfl⟩"),
        ("etaanon_subtypeproj", "theorem etaanon_sub_lit : (⟨6, rfl⟩ : {n : Nat // n = 6}).val = 6 := rfl\n\ndef etaanon_subdef : {n : Nat // n + 1 = 8} := ⟨7, rfl⟩\n\ntheorem etaanon_subdef_val : etaanon_subdef.val * 2 = 14 := rfl"),
        ("etaanon_sigmadep", "def etaanon_dsig : (n : Nat) × { m : Nat // m = n } := ⟨5, 5, rfl⟩\n\ntheorem etaanon_dsig_val : etaanon_dsig.snd.val + etaanon_dsig.fst = 10 := rfl"),
        ("etaanon_uniteta", "structure EtaanonUnit\n\ndef etaanon_useUnit (_ : EtaanonUnit) : Nat := 11\n\ntheorem etaanon_unit_eta (u : EtaanonUnit) : u = ⟨⟩ := rfl\n\ntheorem etaanon_unit_app : etaanon_useUnit ⟨⟩ = 11 := rfl"),
        ("etaanon_deepeta", "structure EtaanonInner2 where\n  a : Nat\n  b : Nat\n\nstructure EtaanonOuter2 where\n  core : EtaanonInner2\n  c : Nat\n\ntheorem etaanon_deep_eta (s : EtaanonOuter2) : (⟨⟨s.core.a, s.core.b⟩, s.c⟩ : EtaanonOuter2) = s := rfl\n\ntheorem etaanon_deep_eta_val : (⟨⟨2, 3⟩, 4⟩ : EtaanonOuter2).core.b * 10 = 30 := rfl"),
        ("litintype_finmk_decide", "def litintypeSubBound : Fin (10 - 2) := ⟨5, by decide⟩\ntheorem litintypeSubBound_lt : 5 < 10 - 2 := by decide\ntheorem litintypeSubBound_val : litintypeSubBound.val = 5 := rfl"),
        ("litintype_abbrev_dim", "abbrev litintypeDim : Nat := 3 + 4\ndef litintypeInDim : Fin litintypeDim := ⟨6, Nat.lt_succ_self 6⟩\ntheorem litintypeInDim_val : litintypeInDim.val = 6 := rfl"),
        ("litintype_subtype_sq", "def litintypeSq : { n : Nat // n * n ≤ 20 } := ⟨4, by decide⟩\ntheorem litintypeSq_prop : litintypeSq.val * litintypeSq.val = 16 := rfl\ntheorem litintypeSq_val : litintypeSq.val = 4 := rfl"),
        ("litintype_uint8_wrap", "def litintypeWrapA : UInt8 := 200\ndef litintypeWrapSum : UInt8 := litintypeWrapA + 100\ntheorem litintypeWrapSum_eq : litintypeWrapSum = 44 := rfl"),
        ("litintype_uint32_mul", "def litintypeU32 : UInt32 := 1000 * 1000\ntheorem litintypeU32_toNat : litintypeU32.toNat = 1000000 := rfl\ntheorem litintypeU32_eq : litintypeU32 = 1000000 := rfl"),
        ("litintype_def_bound", "def litintypeMkBound : Nat := 3 * 3 - 1\ndef litintypeMk : Fin litintypeMkBound := ⟨2 + 2, by decide⟩\ntheorem litintypeMk_val : litintypeMk.val = 4 := rfl"),
        ("litintype_subtype_eqpred", "def litintypeExact : { n : Nat // n + 3 = 10 } := ⟨7, rfl⟩\ndef litintypeExactVal : Nat := litintypeExact.val - 2\ntheorem litintypeExactVal_eq : litintypeExactVal = 5 := rfl"),
        ("instprio_prio_beats_recency", "class InstprioTagA (α : Type) where\n  tag : Nat\ninstance (priority := high) instprioA_hi : InstprioTagA Nat where tag := 2\ninstance instprioA_lo : InstprioTagA Nat where tag := 1\ndef instprio_tagA : Nat := InstprioTagA.tag (α := Nat)\ntheorem instprio_tagA_eq : instprio_tagA = 2 := rfl"),
        ("instprio_attr_numeric_prio", "class InstprioAttrC (α : Type) where\n  n : Nat\n@[reducible] def instprioAttrHi : InstprioAttrC Nat := ⟨3⟩\n@[reducible] def instprioAttrLo : InstprioAttrC Nat := ⟨4⟩\nattribute [instance 2000] instprioAttrHi\nattribute [instance] instprioAttrLo\ndef instprio_attrN : Nat := InstprioAttrC.n (α := Nat)\ntheorem instprio_attrN_eq : instprio_attrN = 3 := rfl"),
        ("instprio_default_instance_prio_order", "class InstprioDp (α : Type) where\n  w : Nat\n@[default_instance 100] instance instprioDpNat : InstprioDp Nat where w := 5\n@[default_instance 200] instance instprioDpBool : InstprioDp Bool where w := 6\ndef instprio_dpGet {α : Type} [InstprioDp α] : Nat := InstprioDp.w (α := α)\ndef instprio_dpVal : Nat := instprio_dpGet\ntheorem instprio_dpVal_eq : instprio_dpVal = 6 := rfl"),
        ("absurdmatch_sumempty", "def absurdmatch_sumEmpty : Sum Empty Nat → Nat\n  | .inl e => nomatch e\n  | .inr n => n + 5\n\ntheorem absurdmatch_sumEmpty_eq : absurdmatch_sumEmpty (.inr 2) = 7 := rfl"),
        ("absurdmatch_diteabsurd", "def absurdmatch_diteAbs (n : Nat) : Nat :=\n  if h : n = n then n * 2 else absurd rfl h\n\ntheorem absurdmatch_diteAbs_eq : absurdmatch_diteAbs 6 = 12 := rfl"),
        ("absurdmatch_vacfalse", "def absurdmatch_base : Nat := 2\n\ntheorem absurdmatch_vacuous (h : False) : absurdmatch_base = 5 := nomatch h\n\ntheorem absurdmatch_base_eq : absurdmatch_base = 2 := rfl"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 34, "expected 34 locked r82 behaviors");
}

// ---------------------------------------------------------------------------
// B95: user-defined OfNat instances + computed type-argument bounds. The
// kernel prelude ships the OfNat constant without registering the class, so
// the elaborator's instance table never seeded it: the literal Step-1 search
// was dead and every user OfNat instance was unreachable. Seeded in
// init_instances_from_env; additionally the literal path normalizes the
// expected type's ARGUMENTS (whnf leaves application args untouched), so a
// computed bound (`B95Box (2+3)`) matches a ground instance head.
// ---------------------------------------------------------------------------

#[test]
fn test_b95_user_ofnat_computed_bound_value() {
    let src = r#"structure B95Box (n : Nat) where
  val : Nat
instance : OfNat (B95Box 5) 3 where
  ofNat := ⟨3⟩
def b95 : B95Box (2+3) := 3
theorem b95_val : b95.val = 3 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b95 computed-bound user OfNat value");
}

#[test]
fn test_b95_user_ofnat_plain_bound_value() {
    let src = r#"structure B95Pl (n : Nat) where
  val : Nat
instance : OfNat (B95Pl 5) 3 where
  ofNat := ⟨3⟩
def b95p : B95Pl 5 := 3
theorem b95p_val : b95p.val = 3 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b95 plain-bound user OfNat value");
}

#[test]
fn test_b95_user_ofnat_mul_bound_value() {
    let src = r#"structure B95M (n : Nat) where
  val : Nat
instance : OfNat (B95M 8) 6 where
  ofNat := ⟨6⟩
def b95m : B95M (2*4) := 6
theorem b95m_val : b95m.val = 6 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b95 mul-bound user OfNat value");
}

#[test]
fn test_b95_wrong_value_rejected() {
    let src = r#"structure B95Box (n : Nat) where
  val : Nat
instance : OfNat (B95Box 5) 3 where
  ofNat := ⟨3⟩
def b95 : B95Box (2+3) := 3
theorem b95_wrong : b95.val = 4 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b95: wrong value 4 must be rejected (val is 3)"
    );
}

#[test]
fn test_b95_unmatched_literal_still_loud() {
    // No instance covers the literal 7 -> the def must still fail loud, not
    // silently accept a raw Nat.
    let src = r#"structure B95Box (n : Nat) where
  val : Nat
instance : OfNat (B95Box 5) 3 where
  ofNat := ⟨3⟩
def b95bad : B95Box 5 := 7"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("def decl present").is_err(),
        "b95: a literal with no matching OfNat instance must stay loud"
    );
}

// ---------------------------------------------------------------------------
// B96: early `return` inside `for` bodies — Option-tunneling accumulator.
// A `for` body containing `return e` threads `Option R` (R = the do-block
// result type) through the ForIn accumulator: `return e` lowers to
// `ForInStep.done (some e ⊗ muts)`, fall-through/`continue` to
// `yield (none ⊗ muts)`, `break` to `done (none ⊗ muts)`; after the loop the
// Option component is case-split (`some r → pure r`, `none → rest`). A
// nested loop's return tunnels through the ENCLOSING loop's Option slot too.
// No-return bodies keep their byte-identical B23/B93 lowerings (engagement
// gate: b93/b94 tests + the r82 lock + the fresh controls below).
// ---------------------------------------------------------------------------

#[test]
fn test_b96_return_in_for_value() {
    // T1: x = 0, 1, 2 → at x = 2 the guard fires and returns 7.
    let src = "def drc : Nat := Id.run do\n  for x in List.range 4 do\n    if x == 2 then\n      return 7\n  return 0\n\ntheorem drc_eq : drc = 7 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b96 return-in-for value");
}

#[test]
fn test_b96_return_in_for_wrong_value_rejected() {
    // Wrong-value twin: the post-loop `return 0` is DEAD (the return fires at
    // x = 2), so `drc = 0` must be rejected.
    let src = "def drc : Nat := Id.run do\n  for x in List.range 4 do\n    if x == 2 then\n      return 7\n  return 0\n\ntheorem drc_wrong : drc = 0 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b96: the fall-through value 0 must be rejected (the loop returns 7)"
    );
}

#[test]
fn test_b96_literal_list_nested_if_return_value() {
    // T2: first x > 5 with x % 3 == 0 is 9 → return 18.
    let src = "def dnir : Nat := Id.run do\n  for x in [3, 9, 4, 12, 7] do\n    if x > 5 then\n      if x % 3 == 0 then\n        return x * 2\n  return 0\n\ntheorem dnir_eq : dnir = 18 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b96 literal list + nested ifs return value");
}

#[test]
fn test_b96_nested_for_return_tunnels_value() {
    // T3: the INNER loop's return must tunnel through the OUTER loop too.
    // First i * j == 6 in lexicographic order is (2, 3) → 23.
    let src = "def dnr : Nat := Id.run do\n  for i in List.range 5 do\n    for j in List.range 5 do\n      if i * j == 6 then\n        return i * 10 + j\n  return 99\n\ntheorem dnr_eq : dnr = 23 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b96 nested-for return tunnels value");
}

#[test]
fn test_b96_mut_acc_with_return_value() {
    // T4 (r82 doearly_accret): s runs 0, 1, 3, 6, 10, 15 — first s > 10 is at
    // i = 5 → return 15 (hand-verified).
    let src = "def doearlyAccRet : Nat := Id.run do\n  let mut s := 0\n  for i in List.range 20 do\n    s := s + i\n    if s > 10 then\n      return s\n  return 0\n\ntheorem doearlyAccRet_eq : doearlyAccRet = 15 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b96 mut accumulator + return value");
}

#[test]
fn test_b96_no_return_control() {
    // Engagement controls: fresh no-return loops (mut single-acc, mut
    // two-acc, and break-guard) stay green on their unchanged B23/B93
    // lowerings.
    let src = r#"def b96CtlMut : Nat := Id.run do
  let mut t := 0
  for i in List.range 4 do
    t := t + i * 2
  return t
theorem b96CtlMut_eq : b96CtlMut = 12 := rfl
def b96CtlTwo : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for i in List.range 3 do
    a := a + i
    b := b * 2
  return a * 10 + b
theorem b96CtlTwo_eq : b96CtlTwo = 38 := rfl
def b96CtlBreak : Nat := Id.run do
  let mut s := 0
  for i in List.range 9 do
    if i > 3 then
      break
    s := s + i
  return s
theorem b96CtlBreak_eq : b96CtlBreak = 6 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b96 no-return engagement controls");
}

#[test]
fn test_b96_break_still_works() {
    // break + return coexisting in one body. First def: break fires first
    // (x = 2) → fall through to 7. Second def: return fires first (x = 2)
    // → 102.
    let src = "def b96BreakThenRet : Nat := Id.run do\n  for x in List.range 10 do\n    if x == 2 then\n      break\n    if x == 5 then\n      return x + 100\n  return 7\n\ntheorem b96BreakThenRet_eq : b96BreakThenRet = 7 := rfl\n\ndef b96RetThenBreak : Nat := Id.run do\n  for x in List.range 10 do\n    if x == 2 then\n      return x + 100\n    if x == 5 then\n      break\n  return 7\n\ntheorem b96RetThenBreak_eq : b96RetThenBreak = 102 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b96 break and return coexisting");
}

// ---------------------------------------------------------------------------
// Round-87 discovery lock — verified behaviors from six fresh domains
// (deriving Ord chains, Array literals, String/Char literal matching, nested
// with-update sugar, universe-polymorphic defs, let rec). Notably ALL
// String/Char literal-match and nested with-update candidates pass. The 24
// failures are clustered in the memory backlog: Array METHOD tier
// (co-tenant), let-rec match-decrease detection (in-lane, queued), deriving
// Hashable builder (in-lane derive, queued), universe-poly mixed bag.
// ---------------------------------------------------------------------------

#[test]
fn test_r87_discovery_lock() {
    let locked: &[(&str, &str)] = &[
        ("arrlit_size", "def arrlitBase : Array Nat := #[3, 1, 4, 1, 5]\n\ntheorem arrlit_size_val : arrlitBase.size = 5 := rfl"),
        ("withupd_nested_sugar", "structure WithupdPt where\n  x : Nat\n  y : Nat\nstructure WithupdBox where\n  pos : WithupdPt\n  tag : Nat\ndef withupd_b0 : WithupdBox := { pos := { x := 1, y := 2 }, tag := 3 }\ndef withupd_b1 : WithupdBox := { withupd_b0 with pos.x := 10 }\ntheorem withupd_nested_sugar :\n    (withupd_b1.pos.x, withupd_b1.pos.y, withupd_b1.tag) = (10, 2, 3) := rfl"),
        ("withupd_selfref", "structure WithupdCtr where\n  count : Nat\n  step : Nat\ndef withupd_bump (c : WithupdCtr) : WithupdCtr :=\n  { c with count := c.count + c.step }\ntheorem withupd_selfref :\n    (withupd_bump { count := 4, step := 3 }).count = 7 := rfl"),
        ("withupd_chain", "structure WithupdPr where\n  a : Nat\n  b : Nat\ndef withupd_p0 : WithupdPr := { a := 0, b := 0 }\ndef withupd_p1 : WithupdPr := { { withupd_p0 with a := 1 } with b := 2 }\ntheorem withupd_chain : (withupd_p1.a, withupd_p1.b) = (1, 2) := rfl"),
        ("withupd_chain_override", "structure WithupdOv where\n  a : Nat\n  b : Nat\ndef withupd_o0 : WithupdOv := { a := 1, b := 6 }\ndef withupd_o1 : WithupdOv := { { withupd_o0 with a := 2 } with a := 5 }\ntheorem withupd_chain_override : (withupd_o1.a, withupd_o1.b) = (5, 6) := rfl"),
        ("withupd_ext_parent", "structure WithupdBase where\n  tag : Nat\n  ver : Nat\nstructure WithupdExt extends WithupdBase where\n  extra : Nat\ndef withupd_e0 : WithupdExt := { tag := 1, ver := 2, extra := 3 }\ndef withupd_e1 : WithupdExt := { withupd_e0 with tag := 9 }\ntheorem withupd_ext_parent :\n    (withupd_e1.tag, withupd_e1.ver, withupd_e1.extra) = (9, 2, 3) := rfl"),
        ("withupd_ext_parentobj", "structure WithupdCore where\n  n : Nat\nstructure WithupdWrap extends WithupdCore where\n  m : Nat\ndef withupd_w0 : WithupdWrap := { n := 1, m := 2 }\ndef withupd_w1 : WithupdWrap := { withupd_w0 with toWithupdCore := { n := 7 } }\ntheorem withupd_ext_parentobj : (withupd_w1.n, withupd_w1.m) = (7, 2) := rfl"),
        ("withupd_nested_selfref", "structure WithupdCell where\n  v : Nat\nstructure WithupdGrid where\n  cell : WithupdCell\n  cnt : Nat\ndef withupd_g0 : WithupdGrid := { cell := { v := 6 }, cnt := 1 }\ndef withupd_g1 : WithupdGrid := { withupd_g0 with cell.v := withupd_g0.cell.v * 2 }\ntheorem withupd_nested_selfref :\n    (withupd_g1.cell.v, withupd_g1.cnt) = (12, 1) := rfl"),
        ("withupd_mixed_multi", "structure WithupdSub where\n  p : Nat\n  q : Nat\nstructure WithupdTop where\n  sub : WithupdSub\n  r : Nat\ndef withupd_t0 : WithupdTop := { sub := { p := 1, q := 2 }, r := 3 }\ndef withupd_t1 : WithupdTop := { withupd_t0 with sub.p := 8, r := 9 }\ntheorem withupd_mixed_multi :\n    (withupd_t1.sub.p, withupd_t1.sub.q, withupd_t1.r) = (8, 2, 9) := rfl"),
        ("withupd_twin_nested", "structure WithupdXY where\n  x : Nat\n  y : Nat\nstructure WithupdFrame where\n  pt : WithupdXY\n  key : Nat\ndef withupd_f0 : WithupdFrame := { pt := { x := 1, y := 1 }, key := 4 }\ndef withupd_f1 : WithupdFrame := { withupd_f0 with pt.x := 5, pt.y := 6 }\ntheorem withupd_twin_nested :\n    (withupd_f1.pt.x, withupd_f1.pt.y, withupd_f1.key) = (5, 6, 4) := rfl"),
        ("withupd_deep3", "structure WithupdL3 where\n  c : Nat\n  d : Nat\nstructure WithupdL2 where\n  b : WithupdL3\nstructure WithupdL1 where\n  a : WithupdL2\n  top : Nat\ndef withupd_d0 : WithupdL1 := { a := { b := { c := 1, d := 2 } }, top := 3 }\ndef withupd_d1 : WithupdL1 := { withupd_d0 with a.b.c := 42 }\ntheorem withupd_deep3 :\n    (withupd_d1.a.b.c, withupd_d1.a.b.d, withupd_d1.top) = (42, 2, 3) := rfl"),
        ("strmatch_lit_scrutinee", "def strmatch_litPick : Nat :=\n  match \"foo\" with\n  | \"foo\" => 1\n  | _ => 2\n\ntheorem strmatch_litPick_eq : strmatch_litPick = 1 := rfl"),
        ("strmatch_char_arms", "def strmatch_charCode (c : Char) : Nat :=\n  match c with\n  | 'a' => 10\n  | 'b' => 20\n  | _ => 0\n\ntheorem strmatch_charCode_b : strmatch_charCode 'b' = 20 := rfl\ntheorem strmatch_charCode_z : strmatch_charCode 'z' = 0 := rfl"),
        ("strmatch_multiarm_fallback", "def strmatch_color (s : String) : Nat :=\n  match s with\n  | \"red\" => 1\n  | \"green\" => 2\n  | \"blue\" => 3\n  | _ => 0\n\ntheorem strmatch_color_mid : strmatch_color \"green\" = 2 := rfl\ntheorem strmatch_color_fall : strmatch_color \"teal\" = 0 := rfl"),
        ("strmatch_nested_arm", "def strmatch_nestedPick (s : String) : Nat :=\n  match s with\n  | \"on\" => (match \"hi\" with | \"hi\" => 5 | _ => 6)\n  | _ => 7\n\ntheorem strmatch_nestedPick_on : strmatch_nestedPick \"on\" = 5 := rfl\ntheorem strmatch_nestedPick_off : strmatch_nestedPick \"off\" = 7 := rfl"),
        ("strmatch_if_guard", "def strmatch_guardPick (s : String) : Nat :=\n  match s with\n  | \"no\" => 0\n  | _ => if s = \"yes\" then 1 else 2\n\ntheorem strmatch_guardPick_yes : strmatch_guardPick \"yes\" = 1 := rfl\ntheorem strmatch_guardPick_other : strmatch_guardPick \"hm\" = 2 := rfl"),
        ("strmatch_length_literal", "def strmatch_lenOf (s : String) : Nat :=\n  match s with\n  | \"hi\" => \"hello\".length\n  | _ => \"no\".length\n\ntheorem strmatch_lenOf_hit : strmatch_lenOf \"hi\" = 5 := rfl\ntheorem strmatch_lenOf_miss : strmatch_lenOf \"zz\" = 2 := rfl"),
        ("strmatch_append_scrutinee", "def strmatch_appendPick : Nat :=\n  match \"ab\" ++ \"cd\" with\n  | \"abcd\" => 11\n  | _ => 22\n\ntheorem strmatch_appendPick_eq : strmatch_appendPick = 11 := rfl"),
        ("strmatch_string_result", "def strmatch_swap (s : String) : String :=\n  match s with\n  | \"yin\" => \"yang\"\n  | \"yang\" => \"yin\"\n  | _ => s\n\ntheorem strmatch_swap_eq : strmatch_swap \"yang\" = \"yin\" := rfl\ntheorem strmatch_swap_id : strmatch_swap \"zen\" = \"zen\" := rfl"),
        ("strmatch_empty_pattern", "def strmatch_emptyPick (s : String) : Nat :=\n  match s with\n  | \"\" => 7\n  | _ => 8\n\ntheorem strmatch_emptyPick_nil : strmatch_emptyPick \"\" = 7 := rfl\ntheorem strmatch_emptyPick_q : strmatch_emptyPick \"q\" = 8 := rfl"),
        ("strmatch_def_compose", "def strmatch_innerPick (s : String) : Nat :=\n  match s with\n  | \"one\" => 1\n  | _ => 0\n\ndef strmatch_outerPick (s : String) : Nat :=\n  match s with\n  | \"go\" => strmatch_innerPick \"one\"\n  | _ => strmatch_innerPick s\n\ntheorem strmatch_outerPick_go : strmatch_outerPick \"go\" = 1 := rfl\ntheorem strmatch_outerPick_two : strmatch_outerPick \"two\" = 0 := rfl"),
        ("letrec_two_indep", "def letrecSumLen (xs : List Nat) : Nat :=\n  let rec total (ys : List Nat) : Nat :=\n    match ys with\n    | [] => 0\n    | y :: rest => y + total rest\n  let rec len (ys : List Nat) : Nat :=\n    match ys with\n    | [] => 0\n    | _ :: rest => len rest + 1\n  total xs + len xs\n\ntheorem letrec_sumlen_eq : letrecSumLen [4, 5, 6] = 18 := rfl"),
        ("letrec_capture", "def letrecAddBase (base : Nat) (xs : List Nat) : Nat :=\n  let rec go (ys : List Nat) : Nat :=\n    match ys with\n    | [] => 0\n    | y :: rest => y + base + go rest\n  go xs\n\ntheorem letrec_addbase_eq : letrecAddBase 10 [1, 2, 3] = 36 := rfl"),
        ("letrec_maplist", "def letrecDoubleAll (xs : List Nat) : List Nat :=\n  let rec go (ys : List Nat) : List Nat :=\n    match ys with\n    | [] => []\n    | y :: rest => 2 * y :: go rest\n  go xs\n\ntheorem letrec_doubleall_eq : letrecDoubleAll [1, 2, 3] = [2, 4, 6] := rfl"),
        ("letrec_accrev", "def letrecRev (xs : List Nat) : List Nat :=\n  let rec go (ys acc : List Nat) : List Nat :=\n    match ys with\n    | [] => acc\n    | y :: rest => go rest (y :: acc)\n  go xs []\n\ntheorem letrec_rev_eq : letrecRev [1, 2, 3] = [3, 2, 1] := rfl"),
        ("letrec_letbind", "def letrecSquareLen : Nat :=\n  let rec len (xs : List Nat) : Nat :=\n    match xs with\n    | [] => 0\n    | _ :: rest => len rest + 1\n  let a := len [7, 8, 9]\n  a * a\n\ntheorem letrec_squarelen_eq : letrecSquareLen = 9 := rfl"),
        ("unipoly_sort_id_prop", "def unipolySid.{u} (α : Sort u) (a : α) : α := a\ndef unipolyEight : Nat := unipolySid Nat 8\ndef unipolyPrf : unipolyEight = 8 := unipolySid (unipolyEight = 8) rfl\ntheorem unipoly_sid_t : unipolyEight = 8 := rfl"),
        ("unipoly_dep_sort_family", "def unipolyPi.{u} (β : Nat → Sort u) (f : (n : Nat) → β n) : β 2 := f 2\ntheorem unipoly_pi_t : unipolyPi (fun _ => Nat) (fun n => n + n) = 4 := rfl"),
        ("derord_enum_basic", "inductive DerordColor\n  | red | green | blue\nderiving Ord\n\ntheorem derord_color_eq : compare DerordColor.green DerordColor.green = Ordering.eq := rfl\n\ntheorem derord_color_gt : compare DerordColor.blue DerordColor.red = Ordering.gt := rfl\n"),
        ("derord_struct_lex3", "structure DerordTriple where\n  a : Nat\n  b : Nat\n  c : Nat\nderiving Ord\n\ntheorem derord_triple_lex : compare (DerordTriple.mk 1 5 2) (DerordTriple.mk 1 5 9) = Ordering.lt := rfl\n"),
        ("derord_sum_payload", "inductive DerordShape\n  | circle (r : Nat)\n  | square (side : Nat)\nderiving Ord\n\ntheorem derord_shape_ctor_order : compare (DerordShape.square 1) (DerordShape.circle 99) = Ordering.gt := rfl\n\ntheorem derord_shape_payload : compare (DerordShape.square 2) (DerordShape.square 5) = Ordering.lt := rfl\n"),
        ("derord_bool_field", "structure DerordFlag where\n  active : Bool\n  level : Nat\nderiving Ord\n\ntheorem derord_flag_bool_first : compare (DerordFlag.mk false 9) (DerordFlag.mk true 0) = Ordering.lt := rfl\n"),
        ("derord_minmax_chain", "def derordClamp (lo hi x : Nat) : Nat :=\n  min hi (max lo x)\n\ntheorem derord_clamp_high : derordClamp 2 7 9 = 7 := rfl\n\ntheorem derord_clamp_mid : derordClamp 2 7 4 = 4 := rfl\n"),
        ("derord_pick_match", "def derordMaxOfCompare (a b : Nat) : Nat :=\n  match compare a b with\n  | Ordering.lt => b\n  | _ => a\n\ntheorem derord_max_of_compare : derordMaxOfCompare 3 8 = 8 := rfl\n"),
        ("derord_enum_in_struct", "inductive DerordRank\n  | bronze | silver | gold\nderiving Ord\n\nstructure DerordPlayer where\n  rank : DerordRank\n  score : Nat\nderiving Ord\n\ntheorem derord_player_rank_first : compare (DerordPlayer.mk DerordRank.silver 99) (DerordPlayer.mk DerordRank.gold 0) = Ordering.lt := rfl\n"),
        ("derord_nested_struct", "structure DerordInner where\n  v : Nat\nderiving Ord\n\nstructure DerordOuter where\n  core : DerordInner\n  tag : Nat\nderiving Ord\n\ntheorem derord_outer_tie_break : compare (DerordOuter.mk (DerordInner.mk 3) 1) (DerordOuter.mk (DerordInner.mk 3) 4) = Ordering.lt := rfl\n"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 36, "expected 36 locked r87 behaviors");
}

// ---------------------------------------------------------------------------
// B97: `let rec` match-decrease structural detection — shadowed rebind.
// The let-rec lift already routes through the shared B89 detection
// (whole-body-match-scrutinee preference), but its extra name-based
// "passes the parameter unchanged" bail rejected the SHADOWED-REBIND shape
// (`let rec go (k : Nat) := match k with | 0 => 0 | k + 1 => go k`): the
// self-call's argument NAME equals the parameter, yet it is the rebound,
// one-step-smaller pattern variable. The bail is now skipped exactly when
// the whole body matches on the chosen parameter AND some arm's pattern
// rebinds that name (shared `whole_body_match_rebinds_param`). Routing
// only — the `.rec` lowering substitutes IHs solely for genuinely smaller
// components and the kernel re-checks; already-detected shapes (fresh
// pattern-var names — the r87 letrec locks) lower byte-identically, and
// genuinely non-decreasing `let rec`s still fail LOUD.
// ---------------------------------------------------------------------------

#[test]
fn test_b97_letrec_basic_value() {
    // r87 letrec_basic (hand-verified): go 3 = ((0+2)+2)+2 = 6.
    let src = "def letrecDouble (n : Nat) : Nat :=\n  let rec go (k : Nat) : Nat :=\n    match k with\n    | 0 => 0\n    | k + 1 => go k + 2\n  go n\n\ntheorem letrec_double_eq : letrecDouble 3 = 6 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b97 letrec_basic value");
}

#[test]
fn test_b97_letrec_basic_wrong_value_rejected() {
    // Wrong-value twin: letrecDouble 3 = 6, so 7 must be rejected.
    let src = "def letrecDouble (n : Nat) : Nat :=\n  let rec go (k : Nat) : Nat :=\n    match k with\n    | 0 => 0\n    | k + 1 => go k + 2\n  go n\n\ntheorem letrec_double_wrong : letrecDouble 3 = 7 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b97: wrong value 7 must be rejected (letrecDouble 3 = 6)"
    );
}

#[test]
fn test_b97_letrec_lit_twice_value() {
    // r87 letrec_lit_twice (hand-verified): tri 3 + tri 4 = 6 + 10 = 16.
    let src = "def letrecTriangles : Nat :=\n  let rec tri (k : Nat) : Nat :=\n    match k with\n    | 0 => 0\n    | k + 1 => (k + 1) + tri k\n  tri 3 + tri 4\n\ntheorem letrec_triangles_eq : letrecTriangles = 16 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b97 letrec_lit_twice value");
}

#[test]
fn test_b97_letrec_chain_value() {
    // r87 letrec_chain (hand-verified): dbl k = 2k;
    // sumDbl 3 = 6 + 4 + 2 + 0 = 12.
    let src = "def letrecChain (n : Nat) : Nat :=\n  let rec dbl (k : Nat) : Nat :=\n    match k with\n    | 0 => 0\n    | k + 1 => dbl k + 2\n  let rec sumDbl (k : Nat) : Nat :=\n    match k with\n    | 0 => 0\n    | k + 1 => dbl (k + 1) + sumDbl k\n  sumDbl n\n\ntheorem letrec_chain_eq : letrecChain 3 = 12 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b97 letrec_chain value");
}

#[test]
fn test_b97_letrec_bool_value() {
    // r87 letrec_bool (hand-verified): go 5 = ! applied 5 times to true
    // = false.
    let src = "def letrecParity (n : Nat) : Bool :=\n  let rec go (k : Nat) : Bool :=\n    match k with\n    | 0 => true\n    | k + 1 => !(go k)\n  go n\n\ntheorem letrec_parity_eq : letrecParity 5 = false := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b97 letrec_bool value");
}

#[test]
fn test_b97_letrec_secondarg_value() {
    // r87 letrec_secondarg (hand-verified): mulAdd 5 3 = 5 + 5 + 5 + 0 = 15.
    // The decreasing parameter is the SECOND one (k, position 1).
    let src = "def letrecMul : Nat :=\n  let rec mulAdd (b k : Nat) : Nat :=\n    match k with\n    | 0 => 0\n    | k + 1 => b + mulAdd b k\n  mulAdd 5 3\n\ntheorem letrec_mul_eq : letrecMul = 15 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b97 letrec_secondarg value");
}

#[test]
fn test_b97_letrec_fresh_name_control() {
    // Engagement control: an ALREADY-working let-rec shape (pattern var name
    // differs from the parameter — the r87 letrec_capture/maplist class)
    // stays green on its unchanged path. Hand-verified: 2 * 3 * 4 * 1 = 24.
    let src = "def b97CtlProd (xs : List Nat) : Nat :=\n  let rec go (ys : List Nat) : Nat :=\n    match ys with\n    | [] => 1\n    | y :: rest => y * go rest\n  go xs\n\ntheorem b97CtlProd_eq : b97CtlProd [2, 3, 4] = 24 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b97 fresh-pattern-name control");
}

#[test]
fn test_b97_letrec_nondecreasing_no_match_still_loud() {
    // A genuinely non-decreasing let rec with NO whole-body match must keep
    // the typed loud error: `bad n` passes `n` through unchanged.
    let src = "def b97Bad : Nat :=\n  let rec bad (n : Nat) : Nat := bad n\n  bad 3";
    let (_env, results) = elab_file_prelude(src);
    match results.first().expect("def decl present") {
        Err(crate::ElabError::WhereLetRecUnsupported { name, .. }) => {
            assert_eq!(name, "bad", "error should name the let rec binder");
        }
        Err(other) => panic!("expected WhereLetRecUnsupported, got {other:?}"),
        Ok(_) => panic!("non-decreasing let rec `bad n` must NOT elaborate"),
    }
}

#[test]
fn test_b97_letrec_nondecreasing_under_match_still_loud() {
    // Whole-body match on `n`, but the arm does NOT rebind `n` and the call
    // passes the OUTER `n` unchanged — no arm rebinds the parameter, so the
    // unchanged-parameter bail still fires: typed loud error preserved.
    let src = "def b97BadMatch : Nat :=\n  let rec bad (n : Nat) : Nat :=\n    match n with\n    | 0 => 0\n    | k + 1 => bad n\n  bad 3";
    let (_env, results) = elab_file_prelude(src);
    match results.first().expect("def decl present") {
        Err(crate::ElabError::WhereLetRecUnsupported { name, .. }) => {
            assert_eq!(name, "bad", "error should name the let rec binder");
        }
        Err(other) => panic!("expected WhereLetRecUnsupported, got {other:?}"),
        Ok(_) => panic!("non-decreasing let rec `bad n` under match must NOT elaborate"),
    }
}

#[test]
fn test_b97_letrec_mixed_arm_nondecreasing_still_loud() {
    // Evil twin: one arm rebinds `n` (engaging the B97 skip), but the actual
    // self-call sits in the ZERO arm and passes the OUTER `n` unchanged —
    // `bad 0` would loop forever. The lift may be ATTEMPTED, but no IH exists
    // for `n` in that arm, so elaboration must still fail LOUD (never a
    // silently-registered wrong value).
    let src = "def b97BadMixed : Nat :=\n  let rec bad (n : Nat) : Nat :=\n    match n with\n    | 0 => bad n\n    | n + 1 => n\n  bad 3";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.first().expect("def decl present").is_err(),
        "b97: non-decreasing self-call in a non-rebinding arm must fail loud"
    );
}

// ---------------------------------------------------------------------------
// B98: `deriving Hashable` — enum ctor-index hash + structural field-fold.
// Clean's kernel `Hashable` is Nat-valued (`hash : α → Nat`, no `mixHash` —
// a pre-existing divergence from Lean's UInt64 class), so the derived
// instances use the documented deterministic Nat formula
//   hash (Cᵢ f₁ … fₖ) = ((i * 31 + hash f₁) * 31 + …) * 31 + hash fₖ
// (ctor index i as seed; field hashes via each field's own `Hashable`
// instance). Tests never pin CROSS-value hash constants; only hash-equality
// on definitionally-equal values — except the explicitly-marked
// formula-pinning check of Clean's own defined behavior.
// ---------------------------------------------------------------------------

#[test]
fn test_b98_enum_hash_value() {
    // r87 derord_hash_mirror verbatim: `hash (derordMirror .east)` must be
    // defeq to `hash .west` (mirror reduces east ↦ west; the derived enum
    // hash is applied to definitionally-equal values on both sides).
    let src = "inductive DerordDir\n  | north | south | east | west\nderiving Hashable\n\ndef derordMirror : DerordDir \u{2192} DerordDir\n  | .north => .south\n  | .south => .north\n  | .east => .west\n  | .west => .east\n\ntheorem derord_hash_mirror : hash (derordMirror DerordDir.east) = hash DerordDir.west := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b98 enum hash mirror value");
}

#[test]
fn test_b98_struct_hash_refl() {
    // r87 derord_ord_hash_multi verbatim: multi-deriving `Ord, Hashable` on a
    // structure. The Ord compare theorem is the working control; the hash
    // theorem is same-value-only (never a cross-value constant).
    let src = "structure DerordTag where\n  id : Nat\n  ver : Nat\nderiving Ord, Hashable\n\ntheorem derord_tag_hash_refl : hash (DerordTag.mk 3 4) = hash (DerordTag.mk 3 4) := rfl\n\ntheorem derord_tag_compare : compare (DerordTag.mk 3 4) (DerordTag.mk 3 5) = Ordering.lt := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b98 struct hash refl + ord control");
}

#[test]
fn test_b98_nested_struct_hash() {
    // A structure whose field is itself a derived-Hashable ENUM: the struct
    // builder must resolve the field's derived `Hashable DerordRankH`
    // instance (registered by the earlier deriving clause) — mirror of the
    // r87 `derord_enum_in_struct` Ord lock, for Hashable.
    let src = "inductive DerordRankH\n  | bronze | silver | gold\nderiving Hashable\n\nstructure DerordPlayerH where\n  rank : DerordRankH\n  score : Nat\nderiving Hashable\n\ntheorem derord_player_hash_refl : hash (DerordPlayerH.mk DerordRankH.silver 9) = hash (DerordPlayerH.mk DerordRankH.silver 9) := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b98 nested struct hash refl");
}

#[test]
fn test_b98_hash_instance_resolves() {
    // A def whose body synthesizes `[Hashable DerordDirH]` on the derived
    // type; the theorem equates it with the direct call (same value only).
    // The final theorem PINS Clean's own documented formula (`hash cᵢ = i`
    // for a field-less ctor — north is ctor 0). This is formula-pinning of
    // Clean's defined behavior, NOT Lean fidelity (Lean's UInt64 hashes
    // differ).
    let src = "inductive DerordDirH\n  | north | south | east | west\nderiving Hashable\n\ndef derordDirHash (d : DerordDirH) : Nat := hash d\n\ntheorem derord_dir_hash_same : derordDirHash DerordDirH.east = hash DerordDirH.east := rfl\n\ntheorem derord_dir_hash_pin : hash DerordDirH.north = 0 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b98 hash instance resolves in def");
}

#[test]
fn test_b98_unsupported_shape_still_loud() {
    // Descoped shapes must keep LOUD typed errors (never a silent stub):
    // (a) recursive inductive, (b) parametric structure.
    let recursive = "inductive DerordTreeH\n  | leaf\n  | node (l : DerordTreeH) (r : DerordTreeH)\nderiving Hashable\n";
    let (_env, results) = elab_file_prelude(recursive);
    match results.first().expect("inductive decl present") {
        Err(crate::ElabError::Unsupported { feature }) => {
            assert!(
                feature.contains("Hashable") && feature.contains("DerordTreeH"),
                "recursive descope must name Hashable and the type, got: {feature}"
            );
        }
        other => panic!("recursive deriving Hashable must fail loud, got {other:?}"),
    }

    let parametric =
        "structure DerordBoxH (\u{3b1} : Type) where\n  val : \u{3b1}\nderiving Hashable\n";
    let (_env, results) = elab_file_prelude(parametric);
    match results.first().expect("structure decl present") {
        Err(crate::ElabError::Unsupported { feature }) => {
            assert!(
                feature.contains("Hashable") && feature.contains("DerordBoxH"),
                "parametric descope must name Hashable and the type, got: {feature}"
            );
        }
        other => panic!("parametric deriving Hashable must fail loud, got {other:?}"),
    }
}

#[test]
fn test_b98_ord_derive_control() {
    // Engagement control: a fresh Ord-only derive (enum + struct) stays green
    // on its unchanged path.
    let src = "inductive DerordCtl\n  | low | mid | high\nderiving Ord\n\nstructure DerordCtlPair where\n  x : Nat\n  y : Nat\nderiving Ord\n\ntheorem derord_ctl_enum : compare DerordCtl.low DerordCtl.high = Ordering.lt := rfl\n\ntheorem derord_ctl_pair : compare (DerordCtlPair.mk 1 2) (DerordCtlPair.mk 1 3) = Ordering.lt := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b98 ord-only derive control");
}

// ---------------------------------------------------------------------------
// B99: instance priority alignment + local/scoped instance scoping — the
// four wrong-VALUE-provable instance-scoping repros from R82 cluster 2
// (r82 instprio_low_loses_recency / instprio_default_instance_mvar /
// instprio_local_section_shadow / instprio_scoped_open_in).
//
// (a) `(priority := low)` must LOSE to an earlier unannotated instance:
//     Lean's default priority is 1000 (low = 100, high = 10000), so an
//     unannotated instance strictly out-prioritizes a `low` one. Clean's
//     elaborator default was 100 — a TIE with `low` — and the Lean-faithful
//     most-recent-first tie-break then let the newer low-priority instance
//     win (5 provable where Lean proves 4).
// (b) `@[default_instance]` must drive open-metavariable defaulting: for a
//     goal `C ?α` whose carrier no use-site pins, Lean picks the
//     highest-priority `@[default_instance]` entry for `C` (here `Bool`,
//     v = 4); Clean resolved the open goal against the plain instance
//     table (3 provable where Lean proves 4).
// (c) `local instance` must DIE at `end` of its section (9 provable outside
//     the section where Lean proves 5).
// (d) `scoped instance` must be visible only when its namespace is open
//     (2 provable without `open` where Lean proves 1).
// ---------------------------------------------------------------------------

#[test]
fn test_b99_low_prio_loses_to_default_value() {
    // r82 instprio_low_loses_recency verbatim: the earlier unannotated
    // instance (default priority 1000) beats the newer `(priority := low)`
    // (100) one, so the tag is 4.
    let src = "class InstprioTagJ (α : Type) where\n  tag : Nat\ninstance instprioJfirst : InstprioTagJ Nat where tag := 4\ninstance (priority := low) instprioJsecond : InstprioTagJ Nat where tag := 5\ndef instprio_tagJ : Nat := InstprioTagJ.tag (α := Nat)\ntheorem instprio_tagJ_eq : instprio_tagJ = 4 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b99 low-priority loses to default value");
}

#[test]
fn test_b99_low_prio_wrong_value_rejected() {
    // Wrong-value twin: the OLD silent-wrong proved tag = 5 (the newer
    // low-priority instance won the 100-vs-100 tie by recency). Must be
    // rejected now that default priority is 1000.
    let src = "class InstprioTagJ (α : Type) where\n  tag : Nat\ninstance instprioJfirst : InstprioTagJ Nat where tag := 4\ninstance (priority := low) instprioJsecond : InstprioTagJ Nat where tag := 5\ndef instprio_tagJ : Nat := InstprioTagJ.tag (α := Nat)\ntheorem instprio_tagJ_wrong : instprio_tagJ = 5 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b99: old wrong value 5 must be rejected (Lean proves instprio_tagJ = 4)"
    );
}

#[test]
fn test_b99_default_instance_open_mvar_value() {
    // r82 instprio_default_instance_mvar verbatim: `instprio_dfKnown` pins
    // α := Nat (v = 3); `instprio_dfOpen` leaves α open, so the
    // @[default_instance] entry (Bool, v = 4) must drive the defaulting.
    let src = "class InstprioDf (α : Type) where\n  v : Nat\ninstance instprioDfNat : InstprioDf Nat where v := 3\n@[default_instance] instance instprioDfBool : InstprioDf Bool where v := 4\ndef instprio_dfGet {α : Type} [InstprioDf α] : Nat := InstprioDf.v (α := α)\ndef instprio_dfKnown : Nat := instprio_dfGet (α := Nat)\ndef instprio_dfOpen : Nat := instprio_dfGet\ntheorem instprio_dfKnown_eq : instprio_dfKnown = 3 := rfl\ntheorem instprio_dfOpen_eq : instprio_dfOpen = 4 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b99 default_instance open-mvar value");
}

#[test]
fn test_b99_default_instance_open_mvar_wrong_rejected() {
    // Wrong-value twin: the OLD silent-wrong proved dfOpen = 3 (the plain
    // instance table resolved the open goal, ignoring @[default_instance]).
    let src = "class InstprioDf (α : Type) where\n  v : Nat\ninstance instprioDfNat : InstprioDf Nat where v := 3\n@[default_instance] instance instprioDfBool : InstprioDf Bool where v := 4\ndef instprio_dfGet {α : Type} [InstprioDf α] : Nat := InstprioDf.v (α := α)\ndef instprio_dfOpen : Nat := instprio_dfGet\ntheorem instprio_dfOpen_wrong : instprio_dfOpen = 3 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b99: old wrong value 3 must be rejected (Lean proves instprio_dfOpen = 4)"
    );
}

#[test]
fn test_b99_local_instance_section_value() {
    // r82 instprio_local_section_shadow verbatim: inside the section the
    // `local instance` shadow (9) wins by recency; after `end` it is dead
    // and the global instance (5) resolves again.
    let src = "class InstprioLoc (α : Type) where\n  v : Nat\ninstance instprioLocGlobal : InstprioLoc Nat where v := 5\nsection\nlocal instance instprioLocShadow : InstprioLoc Nat where v := 9\ndef instprio_inside : Nat := InstprioLoc.v (α := Nat)\nend\ndef instprio_outside : Nat := InstprioLoc.v (α := Nat)\ntheorem instprio_inside_eq : instprio_inside = 9 := rfl\ntheorem instprio_outside_eq : instprio_outside = 5 := rfl";
    let (_env, results) = elab_file_prelude(src);
    for r in &results {
        if let Ok(ElabResult::Multiple(inner)) = r {
            for item in inner {
                assert!(
                    !matches!(item, ElabResult::Failed { .. }),
                    "b99 local-instance section: inner decl failed: {item:?}"
                );
            }
        }
    }
    assert_all_ok(&results, "b99 local instance section value");
}

#[test]
fn test_b99_local_instance_leak_rejected() {
    // Wrong-value twin: the OLD silent-wrong let the `local instance` leak
    // past `end`, proving outside = 9.
    let src = "class InstprioLoc (α : Type) where\n  v : Nat\ninstance instprioLocGlobal : InstprioLoc Nat where v := 5\nsection\nlocal instance instprioLocShadow : InstprioLoc Nat where v := 9\nend\ndef instprio_outside : Nat := InstprioLoc.v (α := Nat)\ntheorem instprio_outside_wrong : instprio_outside = 9 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b99: local instance must not leak past section end (Lean proves 5, not 9)"
    );
}

#[test]
fn test_b99_scoped_instance_open_value() {
    // r82 instprio_scoped_open_in verbatim: the scoped instance is invisible
    // without `open` (plain = 1) and visible under `open ... in` (opened = 2).
    let src = "class InstprioSc (α : Type) where\n  s : Nat\ninstance instprioScGlobal : InstprioSc Nat where s := 1\nnamespace InstprioScope\nscoped instance instprioScLocal : InstprioSc Nat where s := 2\nend InstprioScope\ndef instprio_plain : Nat := InstprioSc.s (α := Nat)\nopen InstprioScope in\ndef instprio_opened : Nat := InstprioSc.s (α := Nat)\ntheorem instprio_plain_eq : instprio_plain = 1 := rfl\ntheorem instprio_opened_eq : instprio_opened = 2 := rfl";
    let (_env, results) = elab_file_prelude(src);
    for r in &results {
        if let Ok(ElabResult::Multiple(inner)) = r {
            for item in inner {
                assert!(
                    !matches!(item, ElabResult::Failed { .. }),
                    "b99 scoped-instance open: inner decl failed: {item:?}"
                );
            }
        }
    }
    assert_all_ok(&results, "b99 scoped instance open value");
}

#[test]
fn test_b99_scoped_instance_unopened_rejected() {
    // Wrong-value twin: the OLD silent-wrong registered the scoped instance
    // globally, proving plain = 2 without any `open`.
    let src = "class InstprioSc (α : Type) where\n  s : Nat\ninstance instprioScGlobal : InstprioSc Nat where s := 1\nnamespace InstprioScope\nscoped instance instprioScLocal : InstprioSc Nat where s := 2\nend InstprioScope\ndef instprio_plain : Nat := InstprioSc.s (α := Nat)\ntheorem instprio_plain_wrong : instprio_plain = 2 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b99: scoped instance must be invisible without open (Lean proves 1, not 2)"
    );
}

#[test]
fn test_b99_plain_recency_tie_control() {
    // Engagement control (tie-break): two UNANNOTATED instances still tie at
    // the (now 1000) default priority, and the Lean-faithful
    // most-recent-first tie-break keeps the NEWER one winning.
    let src = "class B99TieCtl (α : Type) where\n  t : Nat\ninstance b99TieFirst : B99TieCtl Nat where t := 1\ninstance b99TieSecond : B99TieCtl Nat where t := 2\ndef b99_tie : Nat := B99TieCtl.t (α := Nat)\ntheorem b99_tie_eq : b99_tie = 2 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b99 plain recency tie control");
}

#[test]
fn test_b99_explicit_prio_still_dominates_control() {
    // Engagement control (priority still dominates recency): an explicit
    // high-priority instance beats a newer unannotated (1000) one, and an
    // explicit numeric 2000 beats the 1000 default.
    let src = "class B99HiCtl (α : Type) where\n  h : Nat\ninstance (priority := high) b99HiOld : B99HiCtl Nat where h := 7\ninstance b99HiNew : B99HiCtl Nat where h := 8\ndef b99_hi : Nat := B99HiCtl.h (α := Nat)\ntheorem b99_hi_eq : b99_hi = 7 := rfl\nclass B99NumCtl (α : Type) where\n  m : Nat\ninstance (priority := 2000) b99NumOld : B99NumCtl Nat where m := 3\ninstance b99NumNew : B99NumCtl Nat where m := 4\ndef b99_num : Nat := B99NumCtl.m (α := Nat)\ntheorem b99_num_eq : b99_num = 3 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b99 explicit priority dominates control");
}

#[test]
fn test_b99_nonscoped_instance_unchanged_control() {
    // Engagement control (scoping): a PLAIN instance declared inside a
    // section / namespace stays globally visible after the block ends —
    // only `local` / `scoped` modifiers gate visibility.
    let src = "class B99PlainCtl (α : Type) where\n  p : Nat\nsection\ninstance b99PlainSec : B99PlainCtl Nat where p := 6\nend\nnamespace B99PlainNs\ninstance b99PlainNsInst : B99PlainCtl Bool where p := 7\nend B99PlainNs\ndef b99_plain_nat : Nat := B99PlainCtl.p (α := Nat)\ndef b99_plain_bool : Nat := B99PlainCtl.p (α := Bool)\ntheorem b99_plain_nat_eq : b99_plain_nat = 6 := rfl\ntheorem b99_plain_bool_eq : b99_plain_bool = 7 := rfl";
    let (_env, results) = elab_file_prelude(src);
    for r in &results {
        if let Ok(ElabResult::Multiple(inner)) = r {
            for item in inner {
                assert!(
                    !matches!(item, ElabResult::Failed { .. }),
                    "b99 non-scoped control: inner decl failed: {item:?}"
                );
            }
        }
    }
    assert_all_ok(&results, "b99 non-scoped instance unchanged control");
}

// ---------------------------------------------------------------------------
// Round-90 discovery lock — verified behaviors from six fresh domains
// (pattern guards + if-let, fold chains, Option/Except chains, dependent if,
// section variables, custom notation precedence). The 22 failures are
// clustered in the memory backlog: notation-precedence mis-grouping (in-lane,
// potential silent-wrong family), if-let shadowing UnknownFVar (name-shadowing
// theme), section-variable subset inclusion, dependent-if proof-witness
// shapes, and the Nat.fold/Nat.repeat + Option.elim/Except.map co-tenant
// method tiers.
// ---------------------------------------------------------------------------

#[test]
fn test_r90_discovery_lock() {
    let locked: &[(&str, &str)] = &[
        ("sectvar_named_section", "section SectVarBasic\nvariable (n : Nat)\ndef sectvar_double : Nat := n + n\ndef sectvar_triple : Nat := n + n + n\nend SectVarBasic\n\ntheorem sectvar_double_triple : sectvar_double 4 + sectvar_triple 2 = 14 := rfl"),
        ("sectvar_implicit_alpha", "section\nvariable {α : Type}\ndef sectvar_idfun (a : α) : α := a\ndef sectvar_pairup (a b : α) : α × α := (a, b)\nend\n\ntheorem sectvar_pair_id : sectvar_pairup (sectvar_idfun 3) 5 = (3, 5) := rfl"),
        ("sectvar_nested_sections", "section\nvariable (n : Nat)\nsection\nvariable (m : Nat)\ndef sectvar_inner : Nat := n * m\nend\ndef sectvar_outer : Nat := n + 1\nend\n\ntheorem sectvar_nested : sectvar_inner 3 4 + sectvar_outer 5 = 18 := rfl"),
        ("sectvar_toplevel_var", "variable (k : Nat)\ndef sectvar_topA : Nat := k + 2\ndef sectvar_topB : Nat := k * k\n\ntheorem sectvar_toplevel : sectvar_topA 5 + sectvar_topB 3 = 16 := rfl"),
        ("sectvar_universe_decl", "section\nuniverse u\nvariable {α : Type u}\ndef sectvar_firstOf (a b : α) : α := a\nend\n\ntheorem sectvar_universe : sectvar_firstOf 3 8 = 3 := rfl"),
        ("sectvar_transitive_incl", "section\nvariable {α : Type} (p : α × α)\ndef sectvar_swapPair : α × α := (p.2, p.1)\nend\n\ntheorem sectvar_swap : sectvar_swapPair (1, 2) = (2, 1) := rfl"),
        ("sectvar_rescope_name", "section\nvariable (n : Nat)\ndef sectvar_addTwo : Nat := n + 2\nend\nsection\nvariable (n : Bool)\ndef sectvar_notN : Bool := !n\nend\n\ntheorem sectvar_rescope : (sectvar_addTwo 3, sectvar_notN true) = (5, false) := rfl"),
        ("sectvar_interleaved", "section\nvariable (a : Nat)\ndef sectvar_incA : Nat := a + 1\nvariable (b : Nat)\ndef sectvar_addAB : Nat := a + b\ntheorem sectvar_incA_spec : sectvar_incA a = a + 1 := rfl\nend\n\ntheorem sectvar_interleave : sectvar_incA 4 + sectvar_addAB 2 3 = 10 := rfl"),
        ("patguard_iflet_basic", "def patguard_iflet_basic (o : Option Nat) : Nat :=\n  if let some x := o then x + 1 else 0\n\ntheorem patguard_iflet_basic_eq :\n    patguard_iflet_basic (some 4) * 10 + patguard_iflet_basic none = 50 := rfl"),
        ("patguard_iflet_chain", "def patguard_iflet_chain (o : Option (Option Nat)) : Nat :=\n  if let some (some x) := o then x * 2\n  else if let some none := o then 7\n  else 1\n\ntheorem patguard_iflet_chain_eq :\n    patguard_iflet_chain (some (some 3)) * 100 + patguard_iflet_chain (some none) * 10\n      + patguard_iflet_chain none = 671 := rfl"),
        ("patguard_arm_guard", "def patguard_arm_guard : List Nat → Nat\n  | a :: b :: _ => if a ≤ b then a else b\n  | a :: _ => a + 10\n  | [] => 99\n\ntheorem patguard_arm_guard_eq :\n    patguard_arm_guard [5, 2] * 1000 + patguard_arm_guard [4] * 10 + patguard_arm_guard [] = 2239 := rfl"),
        ("patguard_iflet_pair", "def patguard_iflet_pair (p : Nat × Nat) : Nat :=\n  if let (0, y) := p then y + 5 else p.1\n\ntheorem patguard_iflet_pair_eq :\n    patguard_iflet_pair (0, 3) * 10 + patguard_iflet_pair (2, 3) = 82 := rfl"),
        ("patguard_dite_arm", "def patguard_dite_arm (o : Option Nat) : Nat :=\n  match o with\n  | some n => if _h : n > 2 then n - 2 else n + 2\n  | none => 0\n\ntheorem patguard_dite_arm_eq :\n    patguard_dite_arm (some 7) * 100 + patguard_dite_arm (some 1) * 10 + patguard_dite_arm none = 530 := rfl"),
        ("patguard_nested_iflet", "def patguard_nested_iflet (a b : Option Nat) : Nat :=\n  if let some x := a then\n    if let some y := b then x + y else x\n  else 0\n\ntheorem patguard_nested_iflet_eq :\n    patguard_nested_iflet (some 2) (some 3) * 100 + patguard_nested_iflet (some 2) none * 10\n      + patguard_nested_iflet none (some 3) = 520 := rfl"),
        ("patguard_bool_scrutinee", "def patguard_bool_scrutinee (n : Nat) : Nat :=\n  match n % 2 == 0, n with\n  | true, m => m / 2\n  | false, m => 3 * m + 1\n\ntheorem patguard_bool_scrutinee_eq :\n    patguard_bool_scrutinee 6 * 100 + patguard_bool_scrutinee 5 = 316 := rfl"),
        ("patguard_iflet_custom", "inductive PatguardShape where\n  | circle (r : Nat)\n  | rect (w h : Nat)\n\ndef patguard_area (s : PatguardShape) : Nat :=\n  if let PatguardShape.rect w h := s then w * h else 0\n\ntheorem patguard_area_eq :\n    patguard_area (PatguardShape.rect 3 4) * 10 + patguard_area (PatguardShape.circle 5) = 120 := rfl"),
        ("patguard_iflet_subexpr", "def patguard_iflet_subexpr (o : Option Nat) : Nat :=\n  10 * (if let some x := o then x else 7) + 1\n\ntheorem patguard_iflet_subexpr_eq :\n    patguard_iflet_subexpr (some 3) * 1000 + patguard_iflet_subexpr none = 31071 := rfl"),
        ("optbind_mapchain", "def optbind_mapChain : Nat :=\n  (((some 3).map (· + 1)).map (· * 2)).getD 0\n\ntheorem optbind_mapChain_eq : optbind_mapChain = 8 := rfl"),
        ("optbind_halfbind", "def optbind_half (n : Nat) : Option Nat :=\n  if n % 2 = 0 then some (n / 2) else none\n\ndef optbind_halfTwice : Option Nat :=\n  ((some 12).bind optbind_half).bind optbind_half\n\ndef optbind_halfStuck : Option Nat :=\n  ((some 6).bind optbind_half).bind optbind_half\n\ntheorem optbind_half_eq : optbind_halfTwice.getD 0 + optbind_halfStuck.getD 7 = 10 := rfl"),
        ("optbind_orelse", "def optbind_firstHit : Option Nat :=\n  none <|> some 5 <|> some 9\n\ndef optbind_pick (n : Nat) : Option Nat :=\n  if n < 3 then some (n * 10) else none\n\ndef optbind_fallback : Nat :=\n  (optbind_pick 5 <|> optbind_pick 2).getD 0\n\ntheorem optbind_firstHit_eq : optbind_firstHit = some 5 := rfl\n\ntheorem optbind_fallback_eq : optbind_fallback = 20 := rfl"),
        ("optbind_joinbind", "def optbind_nested : Option (Option Nat) :=\n  some (some 6)\n\ndef optbind_flat : Option Nat :=\n  (optbind_nested.bind id).map (· + 1)\n\ndef optbind_flatNone : Option Nat :=\n  ((some (none : Option Nat)).bind id).map (· + 1)\n\ntheorem optbind_flat_eq : optbind_flat.getD 0 + optbind_flatNone.getD 3 = 10 := rfl"),
        ("optbind_safediv", "def optbind_safeDiv (a b : Nat) : Option Nat :=\n  if b = 0 then none else some (a / b)\n\ndef optbind_go : Nat :=\n  ((optbind_safeDiv 20 2).bind (optbind_safeDiv 100)).getD 99\n\ndef optbind_stuck : Nat :=\n  ((optbind_safeDiv 20 0).bind (optbind_safeDiv 100)).getD 99\n\ntheorem optbind_safeDiv_eq : optbind_go + optbind_stuck = 109 := rfl"),
        ("optbind_pipe", "def optbind_pipe : Option Nat :=\n  some 5\n    |>.map (· * 4)\n    |>.bind (fun n => if n ≤ 20 then some (n - 3) else none)\n    |>.map (· + 1)\n\ntheorem optbind_pipe_eq : optbind_pipe = some 18 := rfl"),
        ("notprec_infixl_chain", "def notprec_step (a b : Nat) : Nat := a * 2 + b\n\ninfixl:65 \" ⊞ \" => notprec_step\n\ntheorem notprec_infixl_chain : 3 ⊞ 4 ⊞ 5 = 25 := rfl\n"),
        ("notprec_infixr_chain", "def notprec_cut (a b : Nat) : Nat := a - b\n\ninfixr:65 \" ⊖ \" => notprec_cut\n\ntheorem notprec_infixr_chain : 10 ⊖ 3 ⊖ 2 = 9 := rfl\n"),
        ("notprec_prefix_tight", "def notprec_sq (a : Nat) : Nat := a * a\n\nprefix:100 \"△\" => notprec_sq\n\ntheorem notprec_prefix_tight : △3 + △5 = 34 := rfl\n"),
        ("notprec_postfix_star", "def notprec_bump (a : Nat) : Nat := a + 2\n\npostfix:max \"‼\" => notprec_bump\n\ntheorem notprec_postfix_star : 5‼ * 3 = 21 := rfl\n"),
        ("notprec_plus_mix", "def notprec_avg (a b : Nat) : Nat := (a + b) / 2\n\ninfixl:70 \" ⋄ \" => notprec_avg\n\ntheorem notprec_plus_mix : 1 + 8 ⋄ 4 = 7 := rfl\n"),
        ("depif_dite_explicit", "def depifCap (n : Nat) (h : n ≤ 6) : Nat := 6 - n\n\ndef depifDiteBasic (n : Nat) : Nat :=\n  dite (n ≤ 6) (fun h => depifCap n h) (fun _ => 99)\n\ntheorem depif_dite_basic_val : depifDiteBasic 2 = 4 := rfl"),
        ("depif_le_helper", "def depifGuarded (n : Nat) (h : n ≤ 9) : Nat := n + 1\n\ndef depifUseLe (n : Nat) : Nat :=\n  if h : n ≤ 9 then depifGuarded n h else 0\n\ntheorem depif_use_le_val : depifUseLe 7 = 8 := rfl"),
        ("depif_else_neg", "def depifNonzero (n : Nat) (h : ¬ n = 0) : Nat := n * 3\n\ndef depifElseUse (n : Nat) : Nat :=\n  if h : n = 0 then 1 else depifNonzero n h\n\ntheorem depif_else_use_val : depifElseUse 4 = 12 := rfl"),
        ("depif_else_absurd", "def depifAbsurd (n : Nat) : Nat :=\n  if h : n < n + 1 then n * 2 else absurd (Nat.lt_succ_self n) h\n\ntheorem depif_absurd_val : depifAbsurd 5 = 10 := rfl"),
        ("depif_eq_helper", "def depifTag (n : Nat) (h : n = 3) : Nat := n + n\n\ndef depifEqUse (n : Nat) : Nat :=\n  if h : n = 3 then depifTag n h else 0\n\ntheorem depif_eq_use_val : depifEqUse 3 = 6 := rfl"),
        ("depif_nested_both", "def depifBetween (n : Nat) (hl : 2 ≤ n) (hu : n ≤ 8) : Nat := (n - 2) + (8 - n)\n\ndef depifNestedUse (n : Nat) : Nat :=\n  if hl : 2 ≤ n then\n    if hu : n ≤ 8 then depifBetween n hl hu else 0\n  else 1\n\ntheorem depif_nested_use_val : depifNestedUse 5 = 6 := rfl"),
        ("depif_and_proj", "def depifNeed (a b : Nat) (h : a < b) : Nat := b - a\n\ndef depifPair (n : Nat) : Nat :=\n  if h : 0 < n ∧ n < 10 then depifNeed 0 n h.left + depifNeed n 10 h.right else 0\n\ntheorem depif_pair_val : depifPair 4 = 10 := rfl"),
        ("natfold_subfold", "def natfold_subR : Nat := [10, 4, 3].foldr (· - ·) 20\ndef natfold_subL : Nat := [10, 4, 3].foldl (· - ·) 20\n\ntheorem natfold_subR_val : natfold_subR = 6 := rfl\ntheorem natfold_subL_val : natfold_subL = 3 := rfl"),
        ("natfold_gluecons", "def natfold_glue : List Nat := [1, 2].foldr (· :: ·) [7, 8]\n\ntheorem natfold_glue_val : natfold_glue = [1, 2, 7, 8] := rfl"),
        ("natfold_rangesum", "def natfold_rangeSum : Nat := (List.range 6).foldl (· + ·) 0\n\ntheorem natfold_rangeSum_val : natfold_rangeSum = 15 := rfl"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 38, "expected 38 locked r90 behaviors");
}

// ---------------------------------------------------------------------------
// B100 Brick A — custom notation precedence: user-declared `infixl`/`infixr`/
// `prefix` levels must group against BUILTIN operator levels (Lean: `+` = 65,
// `*` = 70) and against each other by their declared `:N`, not by a fixed
// "tighter than every builtin binary" slot. Each repro pins REAL Lean's
// grouping via a value theorem — the old mis-grouping elaborated SILENTLY to a
// wrong value.
// ---------------------------------------------------------------------------

#[test]
fn test_b100_notprec_two_levels_value() {
    // r90 notprec_two_levels verbatim: ⊠ (70) binds tighter than ⊹ (60), so
    // `2 ⊹ 3 ⊠ 4` = `2 ⊹ (3 ⊠ 4)` = padd 2 12 = 15 (NOT `(2 ⊹ 3) ⊠ 4` = 24).
    let src = "def notprec_padd (a b : Nat) : Nat := a + b + 1\ndef notprec_pmul (a b : Nat) : Nat := a * b\n\ninfixl:60 \" ⊹ \" => notprec_padd\ninfixl:70 \" ⊠ \" => notprec_pmul\n\ntheorem notprec_two_levels : 2 ⊹ 3 ⊠ 4 = 15 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 two custom levels group by declared prec");
}

#[test]
fn test_b100_notprec_two_levels_wrong_grouping_rejected() {
    // Wrong-grouping twin: the OLD silent-wrong left-fold proved
    // `(2 ⊹ 3) ⊠ 4` = 24. Must be rejected (Lean proves 15).
    let src = "def notprec_padd (a b : Nat) : Nat := a + b + 1\ndef notprec_pmul (a b : Nat) : Nat := a * b\n\ninfixl:60 \" ⊹ \" => notprec_padd\ninfixl:70 \" ⊠ \" => notprec_pmul\n\ntheorem notprec_two_levels_wrong : 2 ⊹ 3 ⊠ 4 = 24 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b100: old wrong grouping value 24 must be rejected (Lean proves 15)"
    );
}

#[test]
fn test_b100_notprec_star_mix_value() {
    // r90 notprec_star_mix verbatim: ⧳ (60) is LOOSER than builtin `*` (70),
    // so `2 ⧳ 3 * 4` = `2 ⧳ (3 * 4)` = 2 + 12*12 = 146.
    let src = "def notprec_wide (a b : Nat) : Nat := a + b * b\n\ninfixl:60 \" ⧳ \" => notprec_wide\n\ntheorem notprec_star_mix : 2 ⧳ 3 * 4 = 146 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 custom looser than builtin *");
}

#[test]
fn test_b100_notprec_prefix_loose_value() {
    // r90 notprec_prefix_loose verbatim: prefix:60 parses its operand at
    // level 60, which INCLUDES `*` (70): `∿ 3 * 4` = `∿(3 * 4)` = 100-12 = 88.
    let src = "def notprec_flip (a : Nat) : Nat := 100 - a\n\nprefix:60 \"∿\" => notprec_flip\n\ntheorem notprec_prefix_loose : ∿ 3 * 4 = 88 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 loose prefix operand swallows *");
}

#[test]
fn test_b100_notprec_combo_value() {
    // r90 notprec_combo verbatim: levels + = 65 < ⊛ = 67 < * = 70 < ⊘ = 73.
    // `1 + 2 ⊛ 3 ⊘ 4 * 5` = `1 + (2 ⊛ ((3 ⊘ 4) * 5))` = 1 + f 2 55 = 112.
    let src = "def notprec_f (a b : Nat) : Nat := a * b + 1\ndef notprec_g (a b : Nat) : Nat := a + b * 2\n\ninfixl:67 \" ⊛ \" => notprec_f\ninfixr:73 \" ⊘ \" => notprec_g\n\ntheorem notprec_combo : 1 + 2 ⊛ 3 ⊘ 4 * 5 = 112 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 custom/builtin combo grouping");
}

#[test]
fn test_b100_notprec_multihole_value() {
    // r90 notprec_multihole verbatim: closed multi-hole `notation` with
    // literal separators must parse and beta-reduce the template.
    let src = "def notprec_digits (a b c : Nat) : Nat := a * 100 + b * 10 + c\n\nnotation:max \"⟪\" a \", \" b \", \" c \"⟫\" => notprec_digits a b c\n\ntheorem notprec_multihole : ⟪1, 2, 3⟫ = 123 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 closed multi-hole notation");
}

#[test]
fn test_b100_notprec_same_level_infixl_control() {
    // Engagement control (fresh names, not the r90 lock's ⊞): equal-level
    // infixl still folds LEFT: `3 ⨟ 4 ⨟ 5` = step (step 3 4) 5 = 25.
    let src = "def b100_lstep (a b : Nat) : Nat := a * 2 + b\n\ninfixl:70 \" ⨟ \" => b100_lstep\n\ntheorem b100_lassoc : 3 ⨟ 4 ⨟ 5 = 25 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 same-level infixl control");
}

#[test]
fn test_b100_notprec_same_level_infixr_control() {
    // Engagement control (fresh names, not the r90 lock's ⊖): equal-level
    // infixr still nests RIGHT: `10 ⨠ 3 ⨠ 2` = cut 10 (cut 3 2) = 9.
    let src = "def b100_rcut (a b : Nat) : Nat := a - b\n\ninfixr:70 \" ⨠ \" => b100_rcut\n\ntheorem b100_rassoc : 10 ⨠ 3 ⨠ 2 = 9 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 same-level infixr control");
}

#[test]
fn test_b104_temporal_relation_low_band_value() {
    // Trust's canonical temporal relations occupy the lower infix band:
    // `~>` at 50 binds tighter than `⊨` at 45. Thus `1 ⊨ 2 ~> 3` is
    // `sat 1 (leads 2 3)` = 123, not `leads (sat 1 2) 3` = 1023.
    let src = "def b104_leads (a b : Nat) : Nat := a * 10 + b\ndef b104_sat (a b : Nat) : Nat := a * 100 + b\n\ninfixl:50 \" ~> \" => b104_leads\ninfixl:45 \" ⊨ \" => b104_sat\n\ntheorem b104_temporal_relations : (1 ⊨ 2 ~> 3) = 123 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b104 temporal relation low precedence band");
}

#[test]
fn test_b104_temporal_relation_wrong_grouping_rejected() {
    let src = "def b104_leads (a b : Nat) : Nat := a * 10 + b\ndef b104_sat (a b : Nat) : Nat := a * 100 + b\n\ninfixl:50 \" ~> \" => b104_leads\ninfixl:45 \" ⊨ \" => b104_sat\n\ntheorem b104_temporal_relations_wrong : (1 ⊨ 2 ~> 3) = 1023 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b104: low-band relations must not use the old left-to-right grouping"
    );
}

// ---------------------------------------------------------------------------
// B100 Brick B — if-let pattern variable shadowing an outer binder: the
// pattern var may reuse an outer binder's name; the THEN branch sees the
// pattern var, the ELSE branch sees the OUTER binder (Lean scoping).
// ---------------------------------------------------------------------------

#[test]
fn test_b100_iflet_shadow_value() {
    // r90 patguard_shadow verbatim: pattern `some n` shadows param `n` in the
    // then-branch only; the else-branch `n` is the OUTER param.
    // 9 (some 4) → 4*2 = 8; 9 none → 9; 8*10 + 9 = 89.
    let src = "def patguard_shadow (n : Nat) (o : Option Nat) : Nat :=\n  if let some n := o then n * 2 else n\n\ntheorem patguard_shadow_eq :\n    patguard_shadow 9 (some 4) * 10 + patguard_shadow 9 none = 89 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 if-let pattern var shadows outer binder");
}

#[test]
fn test_b100_iflet_shadow_wrong_value_rejected() {
    // Wrong-value twin: if the then-branch `n` wrongly resolved to the OUTER
    // param (9), the value would be 9*2*10 + 9 = 189. Must be rejected.
    let src = "def patguard_shadow (n : Nat) (o : Option Nat) : Nat :=\n  if let some n := o then n * 2 else n\n\ntheorem patguard_shadow_wrong :\n    patguard_shadow 9 (some 4) * 10 + patguard_shadow 9 none = 189 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b100: outer-binder capture value 189 must be rejected (Lean proves 89)"
    );
}

#[test]
fn test_b100_iflet_nonshadow_control() {
    // Engagement control: distinct pattern-var name, same semantics.
    let src = "def b100_noshadow (n : Nat) (o : Option Nat) : Nat :=\n  if let some m := o then m * 2 else n\n\ntheorem b100_noshadow_eq :\n    b100_noshadow 9 (some 4) * 10 + b100_noshadow 9 none = 89 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 non-shadow if-let control");
}

#[test]
fn test_b100_iflet_shadow_else_absent_control() {
    // Engagement control: shadowing pattern var with the outer binder UNUSED
    // in the else-branch. 9 (some 4) → 4; 9 none → 0; 4*10 + 0 = 40.
    let src = "def b100_shadow_noelse (n : Nat) (o : Option Nat) : Nat :=\n  if let some n := o then n else 0\n\ntheorem b100_shadow_noelse_eq :\n    b100_shadow_noelse 9 (some 4) * 10 + b100_shadow_noelse 9 none = 40 := rfl";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b100 shadow with unused-else control");
}

// ---------------------------------------------------------------------------
// Round-92 everyday-Lean measurement lock. A fresh 50-program battery was
// generated with NO avoid-list (honest sampling of everyday code, including
// known-broken areas): 39/50 = 78% passed on this tree; the passing set is
// locked here. The 11 failures (memory backlog R92): user Add-instance +
// bridging, equation-style let rec parse, simp arithmetic-identity coverage,
// apply-unification fvar bug, while-loop rung, and co-tenant method tiers.
// ---------------------------------------------------------------------------

#[test]
fn test_r92_everyday_lock() {
    let locked: &[(&str, &str)] = &[
        ("ev_defs_params_compose", "def ev_defs_double (n : Nat) : Nat := 2 * n\n\ndef ev_defs_addThen (a b : Nat) : Nat := ev_defs_double (a + b)\n\ntheorem ev_defs_addThen_pin : ev_defs_addThen 3 4 = 14 := rfl\n"),
        ("ev_defs_struct_literal_projection", "structure ev_defs_Point where\n  x : Nat\n  y : Nat\n\ndef ev_defs_origin : ev_defs_Point := { x := 0, y := 0 }\n\ndef ev_defs_p1 : ev_defs_Point := ⟨3, 4⟩\n\ntheorem ev_defs_p1_pin : ev_defs_p1.x + ev_defs_origin.y = 3 := rfl\n"),
        ("ev_defs_struct_update", "structure ev_defs_Score where\n  home : Nat\n  away : Nat\n\ndef ev_defs_start : ev_defs_Score := { home := 0, away := 0 }\n\ndef ev_defs_homeGoal (s : ev_defs_Score) : ev_defs_Score :=\n  { s with home := s.home + 1 }\n\ntheorem ev_defs_two_goals :\n    (ev_defs_homeGoal (ev_defs_homeGoal ev_defs_start)).home = 2 := rfl\n"),
        ("ev_defs_abbrev_alias", "abbrev ev_defs_Cents := Nat\n\ndef ev_defs_price : ev_defs_Cents := 1999\n\ndef ev_defs_withTax (p : ev_defs_Cents) : ev_defs_Cents := p + p / 10\n\ntheorem ev_defs_withTax_pin : ev_defs_withTax ev_defs_price = 2198 := rfl\n"),
        ("ev_defs_implicits_higher_order", "def ev_defs_swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)\n\ndef ev_defs_twice {α : Type} (f : α → α) (a : α) : α := f (f a)\n\ntheorem ev_defs_swap_swap : ev_defs_swap (ev_defs_swap (1, true)) = (1, true) := rfl\n\ntheorem ev_defs_twice_pin : ev_defs_twice (· + 3) 4 = 10 := rfl\n"),
        ("ev_defs_class_instance", "structure ev_defs_Rect where\n  w : Nat\n  h : Nat\n\nclass ev_defs_HasArea (α : Type) where\n  area : α → Nat\n\ninstance : ev_defs_HasArea ev_defs_Rect where\n  area r := r.w * r.h\n\ntheorem ev_defs_rect_area :\n    ev_defs_HasArea.area { w := 3, h := 5 : ev_defs_Rect } = 15 := rfl\n"),
        ("ev_defs_dot_call_methods", "structure ev_defs_Circle where\n  radius : Nat\n\ndef ev_defs_Circle.diameter (c : ev_defs_Circle) : Nat := 2 * c.radius\n\ndef ev_defs_Circle.scaled (c : ev_defs_Circle) (k : Nat) : ev_defs_Circle :=\n  { c with radius := k * c.radius }\n\ntheorem ev_defs_circle_pin :\n    ((⟨5⟩ : ev_defs_Circle).scaled 3).diameter = 30 := rfl\n"),
        ("ev_defs_default_fields", "structure ev_defs_Config where\n  verbose : Bool := false\n  retries : Nat := 3\n  label : String := \"job\"\n\ndef ev_defs_default : ev_defs_Config := {}\n\ndef ev_defs_noisy : ev_defs_Config := { verbose := true, retries := 5 }\n\ntheorem ev_defs_config_pin : ev_defs_default.retries + ev_defs_noisy.retries = 8 := rfl\n"),
        ("ev_defs_match_literals", "def ev_defs_describe (n : Nat) : String :=\n  match n with\n  | 0 => \"zero\"\n  | 1 => \"one\"\n  | _ => \"many\"\n\ntheorem ev_defs_describe_pin : ev_defs_describe 7 = \"many\" := rfl\n"),
        ("ev_data_filter_map_pipeline", "def ev_data_scores : List Nat := [3, 8, 5, 12, 7]\n\ndef ev_data_bigDoubled : List Nat :=\n  (ev_data_scores.filter (· > 4)).map (· * 2)\n\ntheorem ev_data_bigDoubled_eq : ev_data_bigDoubled = [16, 10, 24, 14] := rfl\n"),
        ("ev_data_option_lookup", "def ev_data_colorCode : String → Option Nat\n  | \"red\" => some 1\n  | \"green\" => some 2\n  | \"blue\" => some 3\n  | _ => none\n\ntheorem ev_data_colorCode_green : ev_data_colorCode \"green\" = some 2 := rfl\n\ntheorem ev_data_colorCode_missing : (ev_data_colorCode \"pink\").getD 0 = 0 := rfl\n"),
        ("ev_data_foldl_average", "def ev_data_total (xs : List Nat) : Nat :=\n  xs.foldl (· + ·) 0\n\ndef ev_data_average (xs : List Nat) : Nat :=\n  ev_data_total xs / xs.length\n\ntheorem ev_data_average_eq : ev_data_average [2, 4, 6, 8] = 5 := rfl\n"),
        ("ev_data_string_building", "def ev_data_greet (name : String) : String :=\n  \"Hello, \" ++ name ++ \"!\"\n\ntheorem ev_data_greet_lean : ev_data_greet \"Lean\" = \"Hello, Lean!\" := rfl\n\ntheorem ev_data_greet_length : (ev_data_greet \"ab\").length = 10 := rfl\n"),
        ("ev_data_recursive_evens", "def ev_data_evens : List Nat → List Nat\n  | [] => []\n  | x :: xs => if x % 2 == 0 then x :: ev_data_evens xs else ev_data_evens xs\n\ntheorem ev_data_evens_eq : ev_data_evens [1, 2, 3, 4, 6, 7] = [2, 4, 6] := rfl\n"),
        ("ev_data_option_bind_chain", "def ev_data_half? (n : Nat) : Option Nat :=\n  if n % 2 == 0 then some (n / 2) else none\n\ndef ev_data_quarter? (n : Nat) : Option Nat :=\n  ev_data_half? n >>= ev_data_half?\n\ntheorem ev_data_quarter_12 : ev_data_quarter? 12 = some 3 := rfl\n\ntheorem ev_data_quarter_6 : ev_data_quarter? 6 = none := rfl\n"),
        ("ev_data_struct_field_map", "structure ev_data_Point where\n  x : Nat\n  y : Nat\n\ndef ev_data_pts : List ev_data_Point := [⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩]\n\ndef ev_data_xs : List Nat := ev_data_pts.map (·.x)\n\ntheorem ev_data_xs_eq : ev_data_xs = [1, 3, 5] := rfl\n"),
        ("ev_data_zip_pairs", "def ev_data_pairs : List (Nat × String) :=\n  [1, 2, 3].zip [\"one\", \"two\", \"three\"]\n\ntheorem ev_data_pairs_snd : ev_data_pairs.map (·.2) = [\"one\", \"two\", \"three\"] := rfl\n\ntheorem ev_data_pairs_len : ev_data_pairs.length = 3 := rfl\n"),
        ("ev_rec_factorial", "def ev_rec_factorial : Nat → Nat\n  | 0 => 1\n  | n + 1 => (n + 1) * ev_rec_factorial n\n\ntheorem ev_rec_factorial_five : ev_rec_factorial 5 = 120 := rfl\n"),
        ("ev_rec_sum_match", "def ev_rec_sum (xs : List Nat) : Nat :=\n  match xs with\n  | [] => 0\n  | x :: rest => x + ev_rec_sum rest\n\ntheorem ev_rec_sum_pin : ev_rec_sum [3, 1, 4, 1, 5] = 14 := rfl\n"),
        ("ev_rec_helper_double_all", "def ev_rec_double : Nat → Nat\n  | 0 => 0\n  | n + 1 => ev_rec_double n + 2\n\ndef ev_rec_doubleAll : List Nat → List Nat\n  | [] => []\n  | x :: xs => ev_rec_double x :: ev_rec_doubleAll xs\n\ntheorem ev_rec_doubleAll_pin : ev_rec_doubleAll [1, 2, 3] = [2, 4, 6] := rfl\n"),
        ("ev_rec_parity_two_step", "def ev_rec_isEven : Nat → Bool\n  | 0 => true\n  | 1 => false\n  | n + 2 => ev_rec_isEven n\n\ntheorem ev_rec_isEven_pin : ev_rec_isEven 7 = false := rfl\n"),
        ("ev_rec_acc_reverse", "def ev_rec_revAcc : List Nat → List Nat → List Nat\n  | [], acc => acc\n  | x :: xs, acc => ev_rec_revAcc xs (x :: acc)\n\ndef ev_rec_rev (xs : List Nat) : List Nat := ev_rec_revAcc xs []\n\ntheorem ev_rec_rev_pin : ev_rec_rev [1, 2, 3, 4] = [4, 3, 2, 1] := rfl\n"),
        ("ev_rec_length_induction", "def ev_rec_len : List Nat → Nat\n  | [] => 0\n  | _ :: xs => ev_rec_len xs + 1\n\ntheorem ev_rec_len_eq_length (xs : List Nat) : ev_rec_len xs = xs.length := by\n  induction xs with\n  | nil => rfl\n  | cons _ xs ih => simp [ev_rec_len, ih]\n"),
        ("ev_rec_fib", "def ev_rec_fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => ev_rec_fib n + ev_rec_fib (n + 1)\n\ntheorem ev_rec_fib_pin : ev_rec_fib 10 = 55 := rfl\n"),
        ("ev_rec_filter_if_guard", "def ev_rec_keepBig : List Nat → List Nat\n  | [] => []\n  | x :: xs => if x ≥ 10 then x :: ev_rec_keepBig xs else ev_rec_keepBig xs\n\ntheorem ev_rec_keepBig_pin : ev_rec_keepBig [3, 12, 7, 25, 10] = [12, 25, 10] := by\n  decide\n"),
        ("ev_proof_double_rfl_value", "def ev_proof_double (n : Nat) : Nat := n + n\n\ntheorem ev_proof_double_21 : ev_proof_double 21 = 42 := rfl\n"),
        ("ev_proof_decide_arith_conj", "theorem ev_proof_pow_mod : 2 ^ 6 = 64 ∧ 100 % 7 = 2 := by decide\n"),
        ("ev_proof_bool_cases_demorgan", "theorem ev_proof_demorgan (a b : Bool) : (!(a && b)) = (!a || !b) := by\n  cases a <;> cases b <;> rfl\n"),
        ("ev_proof_option_cases_getD", "def ev_proof_orZero (o : Option Nat) : Nat :=\n  match o with\n  | some n => n\n  | none => 0\n\ntheorem ev_proof_orZero_eq_getD (o : Option Nat) : ev_proof_orZero o = o.getD 0 := by\n  cases o <;> rfl\n"),
        ("ev_proof_exact_add_comm", "theorem ev_proof_flip_sum (a b : Nat) : a + b = b + a := by\n  exact Nat.add_comm a b\n"),
        ("ev_proof_ite_string_rfl", "def ev_proof_classify (n : Nat) : String :=\n  if n < 10 then \"small\" else \"big\"\n\ntheorem ev_proof_classify_three : ev_proof_classify 3 = \"small\" := rfl\n"),
        ("ev_flow_sum_to", "def ev_flow_sum_to (n : Nat) : Nat := Id.run do\n  let mut acc := 0\n  for i in List.range n do\n    acc := acc + (i + 1)\n  return acc\n\ntheorem ev_flow_sum_to_five : ev_flow_sum_to 5 = 15 := rfl"),
        ("ev_flow_first_even", "def ev_flow_first_even (xs : List Nat) : Nat := Id.run do\n  for x in xs do\n    if x % 2 == 0 then\n      return x\n  return 0\n\ntheorem ev_flow_first_even_spec : ev_flow_first_even [3, 7, 8, 5] = 8 := rfl"),
        ("ev_flow_classify", "def ev_flow_classify (score : Nat) : String :=\n  if score ≥ 90 then \"A\"\n  else if score ≥ 80 then \"B\"\n  else if score ≥ 70 then \"C\"\n  else \"F\"\n\ntheorem ev_flow_classify_85 : ev_flow_classify 85 = \"B\" := rfl"),
        ("ev_flow_pair_rule", "def ev_flow_pair_rule : Nat × Nat → Nat\n  | (0, y) => y\n  | (x, 0) => x\n  | (x, y) => x * y\n\ntheorem ev_flow_pair_rule_mul : ev_flow_pair_rule (3, 4) = 12 := rfl"),
        ("ev_flow_unwrap_or", "def ev_flow_unwrap_or (o : Option Nat) (d : Nat) : Nat :=\n  if let some x := o then x + 1 else d\n\ntheorem ev_flow_unwrap_or_some : ev_flow_unwrap_or (some 9) 0 = 10 := rfl"),
        ("ev_flow_count_evens", "def ev_flow_count_evens (xs : List Nat) : Nat := Id.run do\n  let mut n := 0\n  for x in xs do\n    if x % 2 == 0 then\n      n := n + 1\n  return n\n\ntheorem ev_flow_count_evens_spec : ev_flow_count_evens [1, 2, 4, 7, 10] = 3 := rfl"),
        ("ev_flow_second_or", "def ev_flow_second_or (xs : List Nat) : Nat :=\n  match xs with\n  | [] => 0\n  | [x] => x\n  | _ :: y :: _ => y\n\ntheorem ev_flow_second_or_spec : ev_flow_second_or [5, 9, 1] = 9 := rfl"),
        ("ev_flow_sum_until_zero", "def ev_flow_sum_until_zero (xs : List Nat) : Nat := Id.run do\n  let mut acc := 0\n  for x in xs do\n    if x == 0 then\n      break\n    acc := acc + x\n  return acc\n\ntheorem ev_flow_sum_until_zero_spec : ev_flow_sum_until_zero [4, 6, 0, 100] = 10 := rfl"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 39, "expected 39 locked r92 behaviors");
}

// ---------------------------------------------------------------------------
// B101 Brick A — user `Add`/`Mul`/`Sub`/`Div` instances must be reachable
// through their operators: `+` builds an `HAdd α α α` goal, and Lean core's
// `instHAdd [Add α] : HAdd α α α` bridge makes a user `Add X` instance
// satisfy it (same pattern for HMul/HSub/HDiv).
// ---------------------------------------------------------------------------

#[test]
fn test_b101_add_instance_operator() {
    // r92 fresh_ev_defs_add_instance_operator verbatim: ⟨1,2⟩ + ⟨3,4⟩ = ⟨4,6⟩,
    // so .x = 4.
    let src = "structure ev_defs_Vec2 where\n  x : Int\n  y : Int\n\ninstance : Add ev_defs_Vec2 where\n  add a b := ⟨a.x + b.x, a.y + b.y⟩\n\ndef ev_defs_v1 : ev_defs_Vec2 := ⟨1, 2⟩\ndef ev_defs_v2 : ev_defs_Vec2 := ⟨3, 4⟩\n\ntheorem ev_defs_vadd_pin : (ev_defs_v1 + ev_defs_v2).x = 4 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 user Add instance through `+`");
}

#[test]
fn test_b101_add_instance_operator_wrong_value_rejected() {
    // Wrong-value twin: (⟨1,2⟩ + ⟨3,4⟩).x = 4, so 5 must be rejected.
    let src = "structure ev_defs_Vec2 where\n  x : Int\n  y : Int\n\ninstance : Add ev_defs_Vec2 where\n  add a b := ⟨a.x + b.x, a.y + b.y⟩\n\ndef ev_defs_v1 : ev_defs_Vec2 := ⟨1, 2⟩\ndef ev_defs_v2 : ev_defs_Vec2 := ⟨3, 4⟩\n\ntheorem ev_defs_vadd_wrong : (ev_defs_v1 + ev_defs_v2).x = 5 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b101: wrong sum component 5 must be rejected (Lean proves 4)"
    );
}

#[test]
fn test_b101_mul_instance_operator() {
    // Mul sibling, hand-computed: ⟨2,3⟩ * ⟨4,5⟩ componentwise = ⟨8,15⟩, .x = 8.
    let src = "structure b101_MVec where\n  x : Nat\n  y : Nat\n\ninstance : Mul b101_MVec where\n  mul a b := ⟨a.x * b.x, a.y * b.y⟩\n\ndef b101_m1 : b101_MVec := ⟨2, 3⟩\ndef b101_m2 : b101_MVec := ⟨4, 5⟩\n\ntheorem b101_vmul_pin : (b101_m1 * b101_m2).x = 8 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 user Mul instance through `*`");
}

#[test]
fn test_b101_sub_instance_operator() {
    // Sub sibling, hand-computed: ⟨5,7⟩ - ⟨2,3⟩ = ⟨3,4⟩, .x = 3.
    let src = "structure b101_SVec where\n  x : Int\n  y : Int\n\ninstance : Sub b101_SVec where\n  sub a b := ⟨a.x - b.x, a.y - b.y⟩\n\ndef b101_s1 : b101_SVec := ⟨5, 7⟩\ndef b101_s2 : b101_SVec := ⟨2, 3⟩\n\ntheorem b101_vsub_pin : (b101_s1 - b101_s2).x = 3 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 user Sub instance through `-`");
}

#[test]
fn test_b101_div_instance_operator_descoped_loud() {
    // DESCOPED sibling (B101, co-tenant): the homogeneous `Div` CLASS is
    // absent from `Environment::with_prelude` — kernel `init_div` exists
    // (clean-kernel/src/env/algebra_hetero.rs) but `init_prelude_algebra`
    // never calls it — so `instance : Div b101_DVec` cannot even elaborate,
    // and no honest `instHDiv [Div α] : HDiv α α α` bridge value can name
    // `Div.div`. Registering the class is kernel-prelude (co-tenant) work;
    // this test pins that the gap stays LOUD (the instance decl errors)
    // until that lands, at which point the seed's guard opens and this pin
    // should flip to the green sibling shape.
    let src = "structure b101_DVec where\n  x : Nat\n  y : Nat\n\ninstance : Div b101_DVec where\n  div a b := ⟨a.x / b.x, a.y / b.y⟩\n\ndef b101_d1 : b101_DVec := ⟨12, 9⟩\ndef b101_d2 : b101_DVec := ⟨4, 3⟩\n\ntheorem b101_vdiv_pin : (b101_d1 / b101_d2).x = 3 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.iter().any(|r| r.is_err()),
        "b101: user Div instance is a descoped co-tenant gap (no prelude `Div` class); \
         it must fail LOUD, not silently succeed — if this now passes, land the \
         instHDiv bridge sibling and flip this pin to the green shape"
    );
}

#[test]
fn test_b101_builtin_nat_add_control() {
    // Engagement gate: builtin Nat `+` stays byte-identical — resolves via the
    // directly-registered instHAddNat, untouched by the Add→HAdd bridge.
    let src = "def b101_natsum (a b : Nat) : Nat := a + b\n\ntheorem b101_natsum_pin : b101_natsum 20 22 = 42 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 builtin Nat `+` control");
}

#[test]
fn test_b101_user_hadd_hetero_direct() {
    // FLIPPED by B104 (was `..._descoped_loud`): the binop% heterogeneous
    // fallback landed. The homogenizer still TRIES the homogeneous pin first
    // (`idx == 0` → `pin_hetero_binop_slots([β, γ], α)` pins `?β := b101_Sec`),
    // operand 2 `(⟨2⟩ : b101_Min)` mismatches, and the one-shot fallback
    // retries with the slots unpinned so `HAdd b101_Sec b101_Min ?γ`
    // synthesizes directly against the user instance (Lean's binop%
    // try-homogeneous-then-heterogeneous behavior). Hand-computed value pin:
    // ⟨30⟩ + ⟨2⟩ = ⟨30 + 60*2⟩ = ⟨150⟩.
    let src = "structure b101_Sec where\n  s : Nat\n\nstructure b101_Min where\n  m : Nat\n\ninstance : HAdd b101_Sec b101_Min b101_Sec where\n  hAdd a b := ⟨a.s + 60 * b.m⟩\n\ntheorem b101_hetero_pin :\n    ((⟨30⟩ : b101_Sec) + (⟨2⟩ : b101_Min)).s = 150 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 heterogeneous user HAdd through `+` (B104)");
}

#[test]
fn test_b101_neg_instance_operator() {
    // Neg sibling: no bridge involved — unary `-` goes through `Neg.neg`
    // directly and the kernel prelude registers `Neg` as a class, so a user
    // `Neg X` instance is reachable through `-x`. ⟨3, 5⟩ negates to
    // ⟨-3, -5⟩; (-n1).x + 3 = 0.
    let src = "structure b101_NVec where\n  x : Int\n  y : Int\n\ninstance : Neg b101_NVec where\n  neg a := ⟨-a.x, -a.y⟩\n\ndef b101_n1 : b101_NVec := ⟨3, 5⟩\n\ntheorem b101_vneg_pin : (-b101_n1).x + 3 = 0 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 user Neg instance through unary `-`");
}

// ---------------------------------------------------------------------------
// B101 Brick B — equation-style `let rec` (`| pat => body` arms instead of
// `:= expr`), mirroring the top-level def equation form and lowering to the
// same shape as `:= match`.
// ---------------------------------------------------------------------------

#[test]
fn test_b101_letrec_equation_countdown() {
    // r92 fresh_ev_rec_letrec_countdown verbatim; hand-verified:
    // countdown 4 = 4 :: 3 :: 2 :: 1 :: [].
    let src = "def ev_rec_countdown (n : Nat) : List Nat :=\n  let rec go : Nat → List Nat\n    | 0 => []\n    | k + 1 => (k + 1) :: go k\n  go n\n\ntheorem ev_rec_countdown_pin : ev_rec_countdown 4 = [4, 3, 2, 1] := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 equation-style let rec countdown");
}

#[test]
fn test_b101_letrec_equation_list_decrease() {
    // Two-arm equation let rec with a different (structural List) decrease.
    let src = "def b101_sumList (xs : List Nat) : Nat :=\n  let rec go : List Nat → Nat\n    | [] => 0\n    | x :: rest => x + go rest\n  go xs\n\ntheorem b101_sumList_pin : b101_sumList [3, 4, 5] = 12 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 equation-style let rec over List");
}

#[test]
fn test_b101_letrec_equation_wrong_value_rejected() {
    // Wrong-value twin: countdown 4 = [4,3,2,1]; the reversed list must be
    // rejected.
    let src = "def ev_rec_countdown (n : Nat) : List Nat :=\n  let rec go : Nat → List Nat\n    | 0 => []\n    | k + 1 => (k + 1) :: go k\n  go n\n\ntheorem ev_rec_countdown_wrong : ev_rec_countdown 4 = [1, 2, 3, 4] := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b101: reversed countdown must be rejected (Lean proves [4, 3, 2, 1])"
    );
}

#[test]
fn test_b101_letrec_assign_form_control() {
    // Engagement gate: `:=`-form let rec stays byte-identical — same function
    // written with an explicit binder and `:= match`.
    let src = "def b101_countdown_ctrl (n : Nat) : List Nat :=\n  let rec go (k : Nat) : List Nat :=\n    match k with\n    | 0 => []\n    | j + 1 => (j + 1) :: go j\n  go n\n\ntheorem b101_countdown_ctrl_pin : b101_countdown_ctrl 4 = [4, 3, 2, 1] := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b101 `:=`-form let rec control");
}

// ---------------------------------------------------------------------------
// B102 Brick A — `apply` with a PARTIALLY-APPLIED lemma (`apply f h`, an
// application, not a bare const) must not leak an argument metavariable
// (encoded as a high-bit FVar) into the closing proof term.
// ---------------------------------------------------------------------------

#[test]
fn test_b102_apply_partial_le_trans() {
    // R92 fresh repro verbatim: apply of `Nat.le_trans hab` (lemma applied to
    // a hypothesis) then exact for the remaining premise.
    let src = "theorem ev_proof_le_chain (a b c : Nat) (hab : a \u{2264} b) (hbc : b \u{2264} c) : a \u{2264} c := by\n  apply Nat.le_trans hab\n  exact hbc\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b102 apply partially-applied Nat.le_trans");
}

#[test]
fn test_b102_apply_bare_le_trans_control() {
    // Engagement gate: bare-const `apply Nat.le_trans` + two exacts stays green.
    let src = "theorem b102_le_chain_bare (a b c : Nat) (hab : a \u{2264} b) (hbc : b \u{2264} c) : a \u{2264} c := by\n  apply Nat.le_trans\n  exact hab\n  exact hbc\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b102 bare apply Nat.le_trans control");
}

#[test]
fn test_b102_apply_partial_le_of_lt() {
    // Second partially-applied shape, Trans-free: Nat.le_of_lt is a
    // single-premise lemma, so `apply Nat.le_of_lt h` closes the goal
    // outright (h supplies the only premise).
    let src = "theorem b102_le_of_lt (a b : Nat) (h : a < b) : a \u{2264} b := by\n  apply Nat.le_of_lt h\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b102 apply partially-applied Nat.le_of_lt");
}

#[test]
fn test_b102_apply_partial_wrong_lemma_rejected() {
    // NEGATIVE (soundness): applying a partially-applied lemma whose
    // conclusion cannot prove the goal must stay a loud failure — here the
    // hypotheses chain a ≤ b ≤ c but the goal claims c ≤ a.
    let src = "theorem b102_le_chain_wrong (a b c : Nat) (hab : a \u{2264} b) (hbc : b \u{2264} c) : c \u{2264} a := by\n  apply Nat.le_trans hab\n  exact hbc\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b102: `apply Nat.le_trans hab` against goal c \u{2264} a must be rejected"
    );
}

// ---------------------------------------------------------------------------
// B102 Brick B — default simp set must close everyday arithmetic identities
// (add_zero / zero_add / mul_one / one_mul) and the simp [defName, ih]
// induction step.
// ---------------------------------------------------------------------------

#[test]
fn test_b102_simp_arith_identities() {
    // R92 fresh repro verbatim: (a + 0) * 1 + (0 + b) = a + b by simp.
    let src = "theorem ev_proof_tidy (a b : Nat) : (a + 0) * 1 + (0 + b) = a + b := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b102 simp add_zero/mul_one/zero_add identities");
}

#[test]
fn test_b102_simp_mul_one_only() {
    // Narrow variant: a single mul_one rewrite.
    let src = "theorem b102_tidy_mul_one (a : Nat) : a * 1 = a := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b102 simp mul_one-only variant");
}

#[test]
fn test_b102_simp_stepcount_induction() {
    // R92 fresh repro verbatim: induction with simp [defName, ih] in the
    // succ arm (needs unfold-by-name + hypothesis-as-rewrite + add_zero-family
    // normalization to close `stepCount k + 1 = k + 1` after ih rewrite).
    let src = "def ev_proof_stepCount : Nat \u{2192} Nat\n  | 0 => 0\n  | n + 1 => ev_proof_stepCount n + 1\ntheorem ev_proof_stepCount_id (n : Nat) : ev_proof_stepCount n = n := by\n  induction n with\n  | zero => rfl\n  | succ k ih => simp [ev_proof_stepCount, ih]\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b102 simp [defName, ih] induction step");
}

#[test]
fn test_b102_simp_unprovable_goal_rejected() {
    // NEGATIVE (soundness): simp on a false arithmetic identity must NOT
    // silently prove it — a + 0 = a + 1 is false at every a.
    let src = "theorem b102_tidy_wrong (a : Nat) : a + 0 = a + 1 := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b102: simp must not prove the false identity a + 0 = a + 1"
    );
}

// ---------------------------------------------------------------------------
// B103 Brick A — abs_cases binder-scope fix (tactic-internal meta minted under
// a binder must not capture an out-of-scope binder-local). The corpus-level
// companion pins an abs-shape VALUE theorem (Int.natAbs-free abs via if-neg).
// ---------------------------------------------------------------------------

#[test]
fn test_b103_abs_if_neg_value_pin() {
    // Hand-verified: -3 >= 0 is false, so the else branch fires: -(-3) = 3.
    let src = "def b103_myAbs (x : Int) : Int := if x \u{2265} 0 then x else -x\n\ntheorem b103_abs_neg3 : b103_myAbs (-3) = 3 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b103 if-neg abs value theorem");
}

#[test]
fn test_b103_abs_if_neg_wrong_value_rejected() {
    // NEGATIVE (soundness): the wrong abs value must stay unprovable —
    // b103_myAbs (-3) evaluates to 3, never -3.
    let src = "def b103_myAbs (x : Int) : Int := if x \u{2265} 0 then x else -x\n\ntheorem b103_abs_neg3_wrong : b103_myAbs (-3) = -3 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b103: wrong abs value (-3) must be rejected (b103_myAbs (-3) = 3)"
    );
}

// ---------------------------------------------------------------------------
// B103 Brick B — remaining WHNF-rotted simp identity siblings migrate to
// SimpIndexMode::Unindexed (B102 follow-up): Nat.mul_zero / Nat.zero_mul /
// Nat.sub_zero / Nat.sub_self (+ verified-existing siblings Nat.zero_sub /
// Nat.sub_one).
// ---------------------------------------------------------------------------

#[test]
fn test_b103_simp_mul_zero() {
    let src = "theorem b103_mul_zero (a : Nat) : a * 0 = 0 := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b103 simp mul_zero identity");
}

#[test]
fn test_b103_simp_zero_mul() {
    let src = "theorem b103_zero_mul (a : Nat) : 0 * a = 0 := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b103 simp zero_mul identity");
}

#[test]
fn test_b103_simp_sub_zero() {
    let src = "theorem b103_sub_zero (a : Nat) : a - 0 = a := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b103 simp sub_zero identity");
}

#[test]
fn test_b103_simp_sub_self() {
    let src = "theorem b103_sub_self (a : Nat) : a - a = 0 := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b103 simp sub_self identity");
}

#[test]
fn test_b103_simp_combined_identities() {
    // Hand-verified: (a - a) + (b * 0) + (0 * c) + (d - 0)
    //              = ((0 + 0) + 0) + d = d.
    let src = "theorem b103_combined (a b c d : Nat) : (a - a) + (b * 0) + (0 * c) + (d - 0) = d := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b103 simp combined identity goal");
}

#[test]
fn test_b103_simp_wrong_sub_identity_rejected() {
    // NEGATIVE (soundness): simp must not prove the false identity
    // a - 0 = a + 1 (false at every a).
    let src = "theorem b103_sub_wrong (a : Nat) : a - 0 = a + 1 := by simp\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b103: simp must not prove the false identity a - 0 = a + 1"
    );
}

// ---------------------------------------------------------------------------
// B104 Brick A — wlog binder-scope cure (same disease B103 fixed in
// abs_cases: parallel branch fvars vs the positional scope model; the cure is
// ONE shared fvar + abstract_fvar, wlog.rs). The corpus companion proves an
// em-shaped theorem whose two branches each USE their branch hypothesis —
// exactly the parallel-binder shape the old two-fvar code rejected with
// "captures out-of-scope local FVarId(1) at binder depth 1".
// ---------------------------------------------------------------------------

#[test]
fn test_b104_wlog_em_value() {
    // Both branch binders reference the shared hypothesis fvar: branch 1 uses
    // `h : P`, branch 2 uses `h_neg_h : P → False` (wlog's h_neg_{name}).
    let src = "theorem b104_wlog_em (P : Prop) : P \u{2228} (P \u{2192} False) := by\n  wlog h P\n  \u{00b7} exact Or.inl h\n  \u{00b7} exact Or.inr h_neg_h\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b104 wlog em-split value theorem");
}

// ---------------------------------------------------------------------------
// B104 Brick B — binop% heterogeneous fallback (B101-discovered). The
// homogenizer pins `?β` onto operand-1's type after the first operand; a
// genuinely heterogeneous user instance (`HAdd b104_Sec b104_Min b104_Sec`)
// then fails TypeMismatch on operand 2. Lean's binop% tries homogeneous
// first, then falls back to genuine heterogeneous elaboration. The fallback
// only fires where elaboration previously FAILED — homogeneous paths are
// byte-identical (controls below).
// ---------------------------------------------------------------------------

#[test]
fn test_b104_hetero_hadd_fallback_value() {
    // Hand-computed: ⟨30⟩ + ⟨2⟩ = ⟨30 + 60*2⟩ = ⟨150⟩.
    let src = "structure b104_Sec where\n  s : Nat\n\nstructure b104_Min where\n  m : Nat\n\ninstance : HAdd b104_Sec b104_Min b104_Sec where\n  hAdd a b := \u{27e8}a.s + 60 * b.m\u{27e9}\n\ntheorem b104_hetero_pin :\n    ((\u{27e8}30\u{27e9} : b104_Sec) + (\u{27e8}2\u{27e9} : b104_Min)).s = 150 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b104 heterogeneous HAdd fallback value theorem");
}

#[test]
fn test_b104_hetero_hadd_wrong_value_rejected() {
    // NEGATIVE (soundness): the fallback must not prove a wrong value —
    // ⟨30⟩ + ⟨2⟩ computes to ⟨150⟩, never ⟨151⟩.
    let src = "structure b104_Sec where\n  s : Nat\n\nstructure b104_Min where\n  m : Nat\n\ninstance : HAdd b104_Sec b104_Min b104_Sec where\n  hAdd a b := \u{27e8}a.s + 60 * b.m\u{27e9}\n\ntheorem b104_hetero_wrong :\n    ((\u{27e8}30\u{27e9} : b104_Sec) + (\u{27e8}2\u{27e9} : b104_Min)).s = 151 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b104: wrong heterogeneous sum value (151) must be rejected (actual 150)"
    );
}

#[test]
fn test_b104_hetero_type_incorrect_mix_stays_loud() {
    // NEGATIVE (soundness): a mix with NO instance in either direction must
    // stay a loud elaboration error — the fallback synthesizes
    // `HAdd b104_Min b104_Sec ?γ`, which has no instance (only Sec+Min is
    // registered).
    let src = "structure b104_Sec where\n  s : Nat\n\nstructure b104_Min where\n  m : Nat\n\ninstance : HAdd b104_Sec b104_Min b104_Sec where\n  hAdd a b := \u{27e8}a.s + 60 * b.m\u{27e9}\n\ndef b104_bad := (\u{27e8}2\u{27e9} : b104_Min) + (\u{27e8}30\u{27e9} : b104_Sec)\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("def decl present").is_err(),
        "b104: Min + Sec has no HAdd instance and must fail loud"
    );
}

#[test]
fn test_b104_homogeneous_user_add_control() {
    // ENGAGEMENT GATE: the homogeneous user Add-bridge path stays green (and
    // byte-identical — the pin path succeeds, so the fallback never fires)
    // even with a heterogeneous instance ALSO in scope.
    let src = "structure b104_Sec where\n  s : Nat\n\nstructure b104_Min where\n  m : Nat\n\ninstance : Add b104_Sec where\n  add a b := \u{27e8}a.s + b.s\u{27e9}\n\ninstance : HAdd b104_Sec b104_Min b104_Sec where\n  hAdd a b := \u{27e8}a.s + 60 * b.m\u{27e9}\n\ntheorem b104_homog_pin :\n    ((\u{27e8}20\u{27e9} : b104_Sec) + (\u{27e8}22\u{27e9} : b104_Sec)).s = 42 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b104 homogeneous user Add control");
}

#[test]
fn test_b104_builtin_nat_add_control() {
    // ENGAGEMENT GATE: builtin Nat `+` stays byte-identical (pin path).
    let src = "def b104_natsum (a b : Nat) : Nat := a + b\n\ntheorem b104_natsum_pin : b104_natsum 20 22 = 42 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b104 builtin Nat `+` control");
}

#[test]
fn test_b104_wlog_wrong_goal_rejected() {
    // NEGATIVE (soundness): wlog only case-splits — it must not let the
    // branch hypothesis `h : Q` (or `h_neg_h : Q → False`) prove an unrelated
    // goal P.
    let src = "theorem b104_wlog_wrong (P Q : Prop) : P := by\n  wlog h Q\n  \u{00b7} exact h\n  \u{00b7} exact h_neg_h\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem decl present").is_err(),
        "b104: wlog branch hypothesis of Q must not prove an unrelated goal P"
    );
}

// ---------------------------------------------------------------------------
// Round-97 discovery lock — verified behaviors from six fresh domains (calc
// blocks, have/show/suffices, rw tactic, List recursion, Subtype, namespaces).
// Best sweep rate yet: rw 10/10, listrec 9/10, namespaces 8/10, calc core
// 7/10. The 14 failures are clustered in the memory backlog: the have/show
// cluster (anonymous have does not bind `this`, show-from + have-pattern
// term-mode parse arms), qualified Nat.zero/succ pattern exhaustiveness bug,
// the Nat.le_succ/succ_pos co-tenant lemma tier, and calc Trans-instance mix.
// ---------------------------------------------------------------------------

#[test]
fn test_r97_discovery_lock() {
    let locked: &[(&str, &str)] = &[
        ("subtypes_mk_decide_val", "def subtypes_seven : {n : Nat // n > 5} := ⟨7, by decide⟩\n\ntheorem subtypes_seven_val : subtypes_seven.val = 7 := rfl"),
        ("subtypes_property_projection", "def subtypes_even : {n : Nat // n % 2 = 0} := ⟨12, rfl⟩\n\ntheorem subtypes_even_prop : subtypes_even.val % 2 = 0 :=\n  subtypes_even.property"),
        ("subtypes_fn_arg_ne_pred", "def subtypes_pred (x : {n : Nat // n ≠ 0}) : Nat := x.val - 1\n\ntheorem subtypes_pred_five : subtypes_pred ⟨5, by decide⟩ = 4 := rfl"),
        ("subtypes_struct_field", "structure subtypes_Slot where\n  idx : {n : Nat // n < 8}\n\ndef subtypes_slot : subtypes_Slot := { idx := ⟨5, by decide⟩ }\n\ntheorem subtypes_slot_val : subtypes_slot.idx.val = 5 := rfl"),
        ("subtypes_let_pattern", "def subtypes_unpack (x : {n : Nat // n ≥ 2}) : Nat :=\n  let ⟨v, _⟩ := x\n  v * v\n\ntheorem subtypes_unpack_val : subtypes_unpack ⟨3, by decide⟩ = 9 := rfl"),
        ("subtypes_two_vals_arith", "def subtypes_a : {n : Nat // n > 1} := ⟨4, by decide⟩\ndef subtypes_b : {n : Nat // n > 2} := ⟨5, by decide⟩\n\ntheorem subtypes_sum : subtypes_a.val + subtypes_b.val = 9 := rfl"),
        ("subtypes_fun_lambda_pattern", "def subtypes_getInc : {n : Nat // n < 50} → Nat :=\n  fun ⟨v, _⟩ => v + 1\n\ntheorem subtypes_getInc_val : subtypes_getInc ⟨10, by decide⟩ = 11 := rfl"),
        ("calcblk_two_step_literal", "theorem calcblk_two_step_literal : 2 + 3 = 6 - 1 :=\n  calc 2 + 3 = 5 := rfl\n    _ = 6 - 1 := rfl"),
        ("calcblk_hyp_chain", "theorem calcblk_hyp_chain (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=\n  calc a = b := h1\n    _ = c := h2"),
        ("calcblk_simp_identity_steps", "theorem calcblk_simp_identity_steps (n : Nat) : (n + 0) * 1 = n :=\n  calc (n + 0) * 1 = n * 1 := by simp\n    _ = n := by simp"),
        ("calcblk_tactic_position", "theorem calcblk_tactic_position (n : Nat) : 1 * n + 0 = n := by\n  calc 1 * n + 0 = 1 * n := by simp\n    _ = n := by simp"),
        ("calcblk_underscore_head", "theorem calcblk_underscore_head (n : Nat) : n + 0 + 0 = n := by\n  calc _ = n + 0 := Nat.add_zero (n + 0)\n    _ = n := Nat.add_zero n"),
        ("calcblk_single_step", "theorem calcblk_single_step : (7 : Nat) * 3 = 21 :=\n  calc (7 : Nat) * 3 = 21 := rfl"),
        ("calcblk_rw_steps", "theorem calcblk_rw_steps (a b : Nat) (h : a = b) : a + a = b + b :=\n  calc a + a = b + a := by rw [h]\n    _ = b + b := by rw [h]"),
        ("listrec2_map_acc_rev", "def listrec2_revAcc : List Nat → List Nat → List Nat\n  | [], acc => acc\n  | x :: xs, acc => listrec2_revAcc xs (x :: acc)\n\ndef listrec2_mapAcc (f : Nat → Nat) : List Nat → List Nat → List Nat\n  | [], acc => listrec2_revAcc acc []\n  | x :: xs, acc => listrec2_mapAcc f xs (f x :: acc)\n\ntheorem listrec2_mapAcc_pin :\n    listrec2_mapAcc (fun n => n * 2) [1, 2, 3] [] = [2, 4, 6] := rfl"),
        ("listrec2_filter_acc", "def listrec2_frev : List Nat → List Nat → List Nat\n  | [], acc => acc\n  | x :: xs, acc => listrec2_frev xs (x :: acc)\n\ndef listrec2_filterAcc (p : Nat → Bool) : List Nat → List Nat → List Nat\n  | [], acc => listrec2_frev acc []\n  | x :: xs, acc => listrec2_filterAcc p xs (if p x then x :: acc else acc)\n\ntheorem listrec2_filterAcc_pin :\n    listrec2_filterAcc (fun n => n % 2 == 0) [1, 2, 3, 4, 5, 6] [] = [2, 4, 6] := rfl"),
        ("listrec2_pair_explicit", "def listrec2_pairUp : List Nat → List Nat → List (Nat × Nat)\n  | x :: xs, y :: ys => (x, y) :: listrec2_pairUp xs ys\n  | _, _ => []\n\ntheorem listrec2_pairUp_pin :\n    listrec2_pairUp [1, 2, 3] [4, 5, 6, 7] = [(1, 4), (2, 5), (3, 6)] := rfl"),
        ("listrec2_rev_acc_involution", "def listrec2_rev : List Nat → List Nat → List Nat\n  | [], acc => acc\n  | x :: xs, acc => listrec2_rev xs (x :: acc)\n\ntheorem listrec2_rev_twice_pin :\n    listrec2_rev (listrec2_rev [1, 2, 3, 4] []) [] = [1, 2, 3, 4] := rfl"),
        ("listrec2_sum_left_right_agree", "def listrec2_sumR : List Nat → Nat\n  | [] => 0\n  | x :: xs => x + listrec2_sumR xs\n\ndef listrec2_sumL : List Nat → Nat → Nat\n  | [], acc => acc\n  | x :: xs, acc => listrec2_sumL xs (acc + x)\n\ntheorem listrec2_sum_agree :\n    listrec2_sumL [5, 8, 13] 0 = listrec2_sumR [5, 8, 13] := rfl"),
        ("listrec2_is_prefix", "def listrec2_isPrefix : List Nat → List Nat → Bool\n  | [], _ => true\n  | _ :: _, [] => false\n  | x :: xs, y :: ys => x == y && listrec2_isPrefix xs ys\n\ntheorem listrec2_isPrefix_yes : listrec2_isPrefix [1, 2] [1, 2, 3] = true := rfl\n\ntheorem listrec2_isPrefix_no : listrec2_isPrefix [3, 1] [3, 2, 1] = false := rfl"),
        ("listrec2_common_prefix", "def listrec2_commonPrefix : List Nat → List Nat → List Nat\n  | x :: xs, y :: ys =>\n    if x == y then x :: listrec2_commonPrefix xs ys else []\n  | _, _ => []\n\ntheorem listrec2_commonPrefix_pin :\n    listrec2_commonPrefix [7, 8, 9, 4] [7, 8, 1, 4] = [7, 8] := rfl"),
        ("listrec2_unzip_pairs", "def listrec2_unzip : List (Nat × Nat) → List Nat × List Nat\n  | [] => ([], [])\n  | (a, b) :: ps =>\n    let r := listrec2_unzip ps\n    (a :: r.1, b :: r.2)\n\ntheorem listrec2_unzip_pin :\n    listrec2_unzip [(1, 4), (2, 5), (3, 6)] = ([1, 2, 3], [4, 5, 6]) := rfl"),
        ("listrec2_len_map_invariant", "def listrec2_dub : List Nat → List Nat\n  | [] => []\n  | x :: xs => x * 2 :: listrec2_dub xs\n\ndef listrec2_count : List Nat → Nat\n  | [] => 0\n  | _ :: xs => Nat.succ (listrec2_count xs)\n\ntheorem listrec2_count_dub :\n    listrec2_count (listrec2_dub [4, 5, 6]) = listrec2_count [4, 5, 6] := by decide"),
        ("rwtac_add_zero_rfl_close", "theorem rwtac_add_zero_rfl_close (n : Nat) : n + 0 = n := by\n  rw [Nat.add_zero]"),
        ("rwtac_multi_in_one", "theorem rwtac_multi_in_one (a b : Nat) : (a + 0) * (1 * b) = a * b := by\n  rw [Nat.add_zero, Nat.one_mul]"),
        ("rwtac_at_hyp", "theorem rwtac_at_hyp (a b : Nat) (h : a + 0 = b) : a = b := by\n  rw [Nat.add_zero] at h\n  exact h"),
        ("rwtac_rev_arrow_goal", "theorem rwtac_rev_arrow_goal (a b : Nat) (h : a + 0 = b) : a = b := by\n  rw [← Nat.add_zero a]\n  exact h"),
        ("rwtac_comm_rfl_close", "theorem rwtac_comm_rfl_close (a b : Nat) : a + b = b + a := by\n  rw [Nat.add_comm]"),
        ("rwtac_hyp_rules_chain", "theorem rwtac_hyp_rules_chain (a b c : Nat) (h1 : a = b) (h2 : b + c = 0) : a + c = 0 := by\n  rw [h1, h2]"),
        ("rwtac_rev_at_hyp", "theorem rwtac_rev_at_hyp (a b c : Nat) (h : a = b) (h2 : b + c = c + b) : a + c = c + a := by\n  rw [← h] at h2\n  exact h2"),
        ("rwtac_lt_goal", "theorem rwtac_lt_goal (a b : Nat) (h : a < b) : a + 0 < b := by\n  rw [Nat.add_zero]\n  exact h"),
        ("rwtac_all_occurrences", "theorem rwtac_all_occurrences (a : Nat) : (a + 0) * 1 = 1 * (a + 0) := by\n  rw [Nat.add_zero, Nat.mul_one, Nat.one_mul]"),
        ("rwtac_at_hyp_and_goal", "theorem rwtac_at_hyp_and_goal (a b : Nat) (h : a + 0 = b) : a + 0 = b := by\n  rw [Nat.add_zero] at h ⊢\n  exact h"),
        ("namesp_basic_qualified", "namespace namesp_Geo\ndef namesp_area (w h : Nat) : Nat := w * h\ntheorem namesp_area_3_4 : namesp_area 3 4 = 12 := rfl\nend namesp_Geo\n\ntheorem namesp_basic_qualified : namesp_Geo.namesp_area 3 4 = 12 := namesp_Geo.namesp_area_3_4"),
        ("namesp_nested_blocks", "namespace namesp_Outer\nnamespace namesp_Inner\ndef namesp_val : Nat := 21\nend namesp_Inner\ndef namesp_twice : Nat := namesp_Inner.namesp_val * 2\nend namesp_Outer\n\ntheorem namesp_nested_blocks : namesp_Outer.namesp_twice = 42 := rfl"),
        ("namesp_open_unqualified", "namespace namesp_Sh\ndef namesp_base : Nat := 7\ndef namesp_off : Nat := 3\nend namesp_Sh\n\nopen namesp_Sh\n\ntheorem namesp_open_unqualified : namesp_base + namesp_off = 10 := rfl"),
        ("namesp_open_in_scope", "namespace namesp_K\ndef namesp_k : Nat := 9\nend namesp_K\n\nopen namesp_K in\ntheorem namesp_open_in_first : namesp_k = 9 := rfl\n\ntheorem namesp_open_in_scope : namesp_K.namesp_k + 1 = 10 := rfl"),
        ("namesp_protected_open", "namespace namesp_P\nprotected def namesp_secret : Nat := 11\ndef namesp_plain : Nat := namesp_P.namesp_secret - 7\nend namesp_P\n\nopen namesp_P\n\ntheorem namesp_protected_open : namesp_P.namesp_secret + namesp_plain = 15 := rfl"),
        ("namesp_root_shadow", "def namesp_level : Nat := 1\n\nnamespace namesp_D\ndef namesp_level : Nat := 2\ndef namesp_both : Nat := namesp_level + _root_.namesp_level\nend namesp_D\n\ntheorem namesp_root_shadow : namesp_D.namesp_both = 3 := rfl"),
        ("namesp_dotname_reopen", "def namesp_M.namesp_first : Nat := 10\n\nnamespace namesp_M\ndef namesp_second : Nat := namesp_first + 5\nend namesp_M\n\ntheorem namesp_dotname_reopen : namesp_M.namesp_second = 15 := rfl"),
        ("namesp_open_multi", "namespace namesp_W.namesp_X\ndef namesp_deep : Nat := 30\nend namesp_W.namesp_X\n\nnamespace namesp_Z\ndef namesp_shallow : Nat := 12\nend namesp_Z\n\nopen namesp_W.namesp_X namesp_Z in\ntheorem namesp_open_multi : namesp_deep + namesp_shallow = 42 := rfl"),
        ("haveshow_have_by_rhs", "theorem haveshow_have_by_rhs (a b : Nat) : a + b = b + a := by\n  have h : a + b = b + a := by exact Nat.add_comm a b\n  exact h"),
        ("haveshow_show_unfold_def", "def haveshow_double (n : Nat) : Nat := n + n\n\ntheorem haveshow_show_unfold_def : haveshow_double 3 = 6 := by\n  show 3 + 3 = 6\n  rfl"),
        ("haveshow_suffices_from_tactic", "theorem haveshow_suffices_from_tactic (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  suffices h : q from And.intro hp h\n  exact hq"),
        ("haveshow_nested_have_symm", "theorem haveshow_nested_have_symm (a : Nat) : a + 2 = a + 1 + 1 := by\n  have h : a + 2 = a + 1 + 1 := by\n    have h2 : a + 1 + 1 = a + 2 := rfl\n    exact h2.symm\n  exact h"),
        ("haveshow_suffices_term_mode", "theorem haveshow_suffices_term_mode (p q : Prop) (hp : p) (hq : q) : q ∧ p :=\n  suffices h : p ∧ q from And.intro h.2 h.1\n  And.intro hp hq"),
    ];
    for (name, code) in locked {
        let (_env, results) = elab_file_prelude(code);
        assert_all_ok(&results, name);
    }
    assert_eq!(locked.len(), 46, "expected 46 locked r97 behaviors");
}

// ---------------------------------------------------------------------------
// B105: anonymous tactic-mode `have : T := e` binds the hypothesis under
// `this` (Lean's haveIdLhs default), so a following `exact this` resolves.
// Previously it defaulted to `h`, leaving `this` unbound. Term-mode `have`
// already bound `this`; this aligns the tactic lane.
// ---------------------------------------------------------------------------

#[test]
fn test_b105_tactic_anon_have_binds_this() {
    let src = r#"theorem b105Tac (n : Nat) : n * 1 = n := by
  have h := Nat.mul_one n
  have : n * 1 = n := h
  exact this"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b105 anonymous tactic have binds this");
}

#[test]
fn test_b105_named_have_does_not_bind_this() {
    // A NAMED have must NOT leak `this`; referencing `this` stays unbound.
    let src = r#"theorem b105Named (n : Nat) : n * 1 = n := by
  have h : n * 1 = n := Nat.mul_one n
  exact this"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem present").is_err(),
        "b105: a named have must not bind `this`"
    );
}

#[test]
fn test_b105_anon_have_nested_this_shadows() {
    // The inner anonymous have's `this` shadows the outer.
    let src = r#"theorem b105Shadow (a b : Nat) : b + 0 = b := by
  have : a + 0 = a := Nat.add_zero a
  have : b + 0 = b := Nat.add_zero b
  exact this"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b105 nested anonymous have this shadows");
}

#[test]
fn test_b105_show_from_as_have_body() {
    // `show T from e` as the implicit body of a chained term-mode `have`.
    let src = r#"theorem b105ShowFrom (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  have h1 : p := hp
  have h2 : q := hq
  show p ∧ q from And.intro h1 h2"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b105 show-from as have body");
}

#[test]
fn test_b105_suffices_from_as_have_body() {
    // `suffices` as the implicit body of a chained `have`.
    let src = r#"theorem b105SufBody (p q : Prop) (hp : p) (hq : q) : q ∧ p :=
  have h1 : p := hp
  suffices h : q from And.intro h h1
  hq"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b105 suffices as have body");
}

#[test]
fn test_b105_show_from_wrong_proof_rejected() {
    // Soundness: a show-from whose proof term does not prove the ascribed type
    // stays loud.
    let src = r#"theorem b105ShowWrong (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  have h1 : p := hp
  show p ∧ q from hp"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem present").is_err(),
        "b105: show-from with a non-proof must stay loud"
    );
}

// ---------------------------------------------------------------------------
// B106: term-mode `have ⟨a, b⟩ := e; body` anonymous-constructor destructuring
// (Lean's `have`-with-pattern), lowered to `match e with | ⟨a,b⟩ => body`.
// Previously the term-mode have parsed only an identifier and ParseErrored.
// ---------------------------------------------------------------------------

#[test]
fn test_b106_have_pattern_value() {
    // Value-distinguishing: destructure a Prod and use both components.
    let src = r#"def b106P : Nat × Nat := (3, 4)
theorem b106V : (have ⟨a, b⟩ := b106P
                 a * 10 + b) = 34 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b106 have-pattern prod value");
}

#[test]
fn test_b106_have_pattern_wrong_value_rejected() {
    let src = r#"def b106P2 : Nat × Nat := (3, 4)
theorem b106W : (have ⟨a, b⟩ := b106P2
                 a * 10 + b) = 35 := rfl"#;
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem present").is_err(),
        "b106: wrong value 35 must be rejected (a*10+b = 34)"
    );
}

#[test]
fn test_b106_named_have_still_works() {
    // Engagement control: the ordinary named have is unchanged.
    let src = r#"theorem b106N (n : Nat) : n * 1 = n :=
  have h : n * 1 = n := Nat.mul_one n
  h"#;
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b106 named have control");
}

#[test]
fn test_r100_everyday_lock() {
    // R100 strategic re-measure (fresh independent no-avoid battery,
    // 5-agent gen 2026-07-20): the 38 everyday snippets that
    // parse -> elaborate -> kernel-verify clean today. Pins them
    // against regression. Full sweep 38/63 = 60.3%; the failing 25
    // are tracked in the R100 backlog (deriving Repr x6, omega/linarith
    // x4, recursive dot-notation x3, simp-set x2, prelude consts x2,
    // do/coe/array/rw tail x8).
    let passing: &[(&str, &str)] = &[
        (
            "logic_and-comm-impl",
            r####"theorem and_comm_impl (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.2, h.1⟩
"####,
        ),
        (
            "logic_or-comm-cases",
            r####"theorem or_comm_impl (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq
"####,
        ),
        (
            "logic_and-self-iff",
            r####"theorem and_self_iff_self (p : Prop) : (p ∧ p) ↔ p := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h⟩
"####,
        ),
        (
            "logic_exists-intro-term",
            r####"theorem exists_sum_six : ∃ n : Nat, n + n = 6 := ⟨3, rfl⟩
"####,
        ),
        (
            "logic_exists-elim-cases",
            r####"theorem exists_relabel (p : Nat → Prop) (h : ∃ n, p n) : ∃ m, p m := by
  cases h with
  | intro w hw => exact ⟨w, hw⟩
"####,
        ),
        (
            "logic_excluded-middle-bycases",
            r####"theorem em_via_bycases (p : Prop) : p ∨ ¬p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h
"####,
        ),
        (
            "logic_eq-trans-calc",
            r####"theorem eq_trans_calc (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2
"####,
        ),
        (
            "logic_modus-ponens-suffices",
            r####"theorem modus_ponens_suffices (p q : Prop) (h : p → q) (hp : p) : q := by
  suffices hq : p by exact h hq
  exact hp
"####,
        ),
        (
            "logic_and-distrib-or",
            r####"theorem and_distrib_or (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  cases h.2 with
  | inl hq => exact Or.inl ⟨h.1, hq⟩
  | inr hr => exact Or.inr ⟨h.1, hr⟩
"####,
        ),
        (
            "logic_forall-and-distrib",
            r####"theorem forall_and_distrib (α : Type) (p q : α → Prop) :
    (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := by
  intro h
  exact ⟨fun x => (h x).1, fun x => (h x).2⟩
"####,
        ),
        (
            "logic_chain-have-show",
            r####"theorem chain_have (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  have hq : q := hpq hp
  show r
  exact hqr hq
"####,
        ),
        (
            "class_color-tostring-deriving",
            r####"inductive Color where
  | red
  | green
  | blue
  deriving Repr, BEq, DecidableEq

instance : ToString Color where
  toString
    | .red => "red"
    | .green => "green"
    | .blue => "blue"

example : toString Color.green = "green" := rfl"####,
        ),
        (
            "class_monoid-user-class",
            r####"class Monoid' (α : Type) where
  one : α
  mul : α → α → α

instance : Monoid' Nat where
  one := 1
  mul := Nat.mul

example : Monoid'.mul (Monoid'.one : Nat) 5 = 5 := rfl"####,
        ),
        (
            "class_vec2-custom-beq",
            r####"structure Vec2 where
  x : Int
  y : Int

instance : BEq Vec2 where
  beq a b := a.x == b.x && a.y == b.y

example : ((⟨1, 2⟩ : Vec2) == ⟨1, 2⟩) = true := rfl"####,
        ),
        (
            "class_suit-decidableeq-decide",
            r####"inductive Suit where
  | hearts | diamonds | clubs | spades
  deriving DecidableEq, Repr

example : Suit.hearts ≠ Suit.spades := by decide

example : (if Suit.clubs = Suit.clubs then 1 else 0) = 1 := by decide"####,
        ),
        (
            "class_named-bool-instance",
            r####"class Named (α : Type) where
  name : α → String

instance : Named Bool where
  name b := if b then "yes" else "no"

example : Named.name true = "yes" := rfl"####,
        ),
        (
            "class_priority-rank-def",
            r####"inductive Priority where
  | low | medium | high
  deriving Repr, DecidableEq

def Priority.rank : Priority → Nat
  | .low => 0
  | .medium => 1
  | .high => 2

example : Priority.medium.rank < Priority.high.rank := by decide"####,
        ),
        (
            "data_map-length",
            r####"theorem data_map_length {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]
"####,
        ),
        (
            "data_addopt-do",
            r####"def data_addOpt (a b : Option Nat) : Option Nat := do
  let x ← a
  let y ← b
  pure (x + y)

theorem data_addOpt_some (a b : Nat) :
    data_addOpt (some a) (some b) = some (a + b) := rfl
"####,
        ),
        (
            "data_safediv-except",
            r####"def data_safeDiv (a b : Nat) : Except String Nat :=
  if b = 0 then Except.error "div by zero" else Except.ok (a / b)

theorem data_safeDiv_ok : data_safeDiv 10 2 = Except.ok 5 := rfl

theorem data_safeDiv_err : data_safeDiv 10 0 = Except.error "div by zero" := rfl
"####,
        ),
        (
            "data_concat-foldr",
            r####"def data_concat {α : Type} (xss : List (List α)) : List α :=
  xss.foldr (· ++ ·) []

theorem data_concat_nil {α : Type} : data_concat ([] : List (List α)) = [] := rfl

theorem data_concat_cons {α : Type} (xs : List α) (xss : List (List α)) :
    data_concat (xs :: xss) = xs ++ data_concat xss := rfl
"####,
        ),
        (
            "data_headopt-map",
            r####"def data_headOpt {α : Type} : List α → Option α
  | [] => none
  | x :: _ => some x

theorem data_headOpt_map {α β : Type} (f : α → β) (xs : List α) :
    (data_headOpt xs).map f = data_headOpt (xs.map f) := by
  cases xs with
  | nil => rfl
  | cons x xs => rfl
"####,
        ),
        (
            "data_vec2-add-instance",
            r####"structure data_Vec2 where
  a : Int
  b : Int

instance : Add data_Vec2 where
  add u v := ⟨u.a + v.a, u.b + v.b⟩

theorem data_Vec2_add_comm (u v : data_Vec2) :
    (u + v).a = (v + u).a := by
  show u.a + v.a = v.a + u.a
  exact Int.add_comm u.a v.a
"####,
        ),
        (
            "arith-zero-add-induction",
            r####"theorem arith_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"####,
        ),
        (
            "arith-iseven-match-rfl",
            r####"def arith_isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => arith_isEven n

theorem arith_isEven_four : arith_isEven 4 = true := rfl
"####,
        ),
        (
            "arith-two-dvd-six-witness",
            r####"theorem arith_two_dvd_six : 2 ∣ 6 := ⟨3, rfl⟩
"####,
        ),
        (
            "arith-calc-nat-comm",
            r####"theorem arith_calc (a b c : Nat) : (a + b) + c = c + (b + a) := by
  calc (a + b) + c = c + (a + b) := by rw [Nat.add_comm (a + b) c]
    _ = c + (b + a) := by rw [Nat.add_comm a b]
"####,
        ),
        (
            "arith-safediv-option-do",
            r####"def arith_safeDiv (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

def arith_compute : Option Nat := do
  let x ← arith_safeDiv 10 2
  let y ← arith_safeDiv x 0
  pure (x + y)

theorem arith_compute_none : arith_compute = none := rfl
"####,
        ),
        (
            "arith-le-trans-omega",
            r####"theorem arith_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  omega
"####,
        ),
        (
            "arith-sign-inductive-toint",
            r####"inductive arith_Sign where
  | neg
  | zero
  | pos

def arith_toInt : arith_Sign → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

theorem arith_toInt_pos : arith_toInt .pos = 1 := rfl
"####,
        ),
        (
            "arith-fib-where-rfl",
            r####"def arith_fib (n : Nat) : Nat := go n 0 1
where
  go : Nat → Nat → Nat → Nat
    | 0, a, _ => a
    | n + 1, a, b => go n b (a + b)

theorem arith_fib_five : arith_fib 5 = 5 := rfl
"####,
        ),
        (
            "mixed_expr_eval_rfl",
            r####"inductive Expr where
  | num : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

def Expr.eval : Expr → Nat
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

example : (Expr.add (Expr.num 2) (Expr.mul (Expr.num 3) (Expr.num 4))).eval = 14 := rfl
"####,
        ),
        (
            "mixed_where_tail_recursion",
            r####"def sumTo (n : Nat) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc => go n (acc + n + 1)

example : sumTo 5 = 15 := rfl
"####,
        ),
        (
            "mixed_mutual_even_odd",
            r####"mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

example : (isEven 6 && isOdd 5) = true := rfl
"####,
        ),
        (
            "mixed_anon_ctor_exists_and",
            r####"theorem exists_add_one (n : Nat) : ∃ m, m = n + 1 := ⟨n + 1, rfl⟩

theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

example : ∃ n : Nat, n + n = 6 := ⟨3, rfl⟩
"####,
        ),
        (
            "mixed_calc_chain_nat",
            r####"theorem calc_example (a b : Nat) (h1 : a = b) (h2 : b = 5) : a + 1 = 6 := by
  calc a + 1 = b + 1 := by rw [h1]
    _ = 5 + 1 := by rw [h2]
    _ = 6 := rfl
"####,
        ),
        (
            "mixed_except_do_safediv",
            r####"def safeDiv (a b : Nat) : Except String Nat :=
  if b = 0 then Except.error "div by zero" else Except.ok (a / b)

def compute : Except String Nat := do
  let x ← safeDiv 10 2
  let y ← safeDiv x 0
  pure (x + y)

example : compute = Except.error "div by zero" := rfl
"####,
        ),
        (
            "mixed_natrec_double",
            r####"def double (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2) n

example : double 4 = 8 := rfl

example : double 0 = 0 := rfl
"####,
        ),
    ];
    let mut failures: Vec<String> = Vec::new();
    for (name, code) in passing {
        let decls = match parse_file(code) {
            Ok(d) => d,
            Err(e) => {
                failures.push(format!("{name}: ParseError({e:?})"));
                continue;
            }
        };
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        for (i, decl) in decls.iter().enumerate() {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            if let Err(e) =
                elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            {
                failures.push(format!("{name}: decl#{i} {e:?}"));
                break;
            }
        }
    }
    assert!(
        failures.is_empty(),
        "R100 everyday lock regressed:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// B107 — `deriving Repr` for structures.
//
// The #1 everyday gap from the R100 no-avoid re-measure (6 of 25 failures):
// `structure … deriving Repr` used to bail with a hard `Unsupported`. The
// structure derive path now emits a minimal-but-type-correct `Repr` instance
// against Clean's String-valued `Repr` (`reprPrec : α → Nat → String`),
// mirroring the shipped inductive-Repr bootstrap. These pin the behavior end
// to end (parse → elaborate → genuine kernel registration).
// ---------------------------------------------------------------------------

#[test]
fn test_b107_deriving_repr_struct_kernel_checks() {
    // Value-distinguishing: deriving Repr no longer blocks the everyday
    // pattern, and a downstream theorem that USES the struct reduces to the
    // real value (3 + 4 = 7) under kernel `rfl`.
    let code = r####"structure Point where
  x : Nat
  y : Nat
  deriving Repr

def Point.norm1 (p : Point) : Nat := p.x + p.y

theorem point_norm1_val : Point.norm1 ⟨3, 4⟩ = 7 := rfl
"####;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "struct deriving Repr + downstream rfl theorem");
    // Genuine kernel registration: `register_derived_instance` adds the
    // instance as a kernel-checked `Declaration::Definition`, so the constant
    // only exists if its value type-checked as `Repr Point`.
    assert!(
        env.get_const(&Name::from_string("instPointRepr")).is_some(),
        "deriving Repr must register a kernel-checked `Repr Point` instance"
    );
}

#[test]
fn test_b107_deriving_repr_parametric_struct() {
    // Parametric: synthesizes `[Repr α] → [Repr β] → Repr (Pair α β)`; the
    // instance value + type are kernel-checked at registration.
    let code = r####"structure Pair (α : Type) (β : Type) where
  fst : α
  snd : β
  deriving Repr
"####;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "parametric struct deriving Repr");
    assert!(
        env.get_const(&Name::from_string("instPairRepr")).is_some(),
        "parametric deriving Repr must register `[Repr α] → [Repr β] → Repr (Pair α β)`"
    );
}

#[test]
fn test_b107_deriving_repr_nonrepr_field_fails_loud() {
    // Fail-loud negative: a field whose type has NO `Repr` instance (a bare
    // function `Nat → Nat`) must make deriving fail rather than silently mint a
    // bogus instance — exactly like Lean, which requires every field to be Repr.
    let code = r####"structure HasFn where
  f : Nat → Nat
  deriving Repr
"####;
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(std::result::Result::is_err),
        "deriving Repr on a struct with a non-representable field must fail loud, got: {results:?}"
    );
}

#[test]
fn test_b107_deriving_repr_mixed_with_beq_decidable() {
    // Mixed everyday shape: `deriving Repr, BEq, DecidableEq` on one struct
    // plus a downstream `==` reduction — the family the R100 failures
    // (`mixed_point_struct_decidable`, `class_*-add-decide`,
    // `class_pair-generic-beq`) exercise. Repr must coexist with the other
    // derives and all three must kernel-register.
    let code = r####"structure Point where
  x : Nat
  y : Nat
  deriving Repr, BEq, DecidableEq

example : ((⟨1, 2⟩ : Point) == ⟨1, 2⟩) = true := rfl
"####;
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(
        &results,
        "struct deriving Repr, BEq, DecidableEq + `==` rfl",
    );
    assert!(
        env.get_const(&Name::from_string("instPointRepr")).is_some(),
        "combined deriving must still register the Repr instance"
    );
}

// ---------------------------------------------------------------------------
// B108: term-mode anonymous-constructor `⟨…⟩` patterns in `have`/`let`/`match`
// remap the parser's `Prod.mk` placeholder to the scrutinee's real single
// constructor (And.intro / Exists.intro / Subtype.mk / Sigma.mk / a user
// structure's ctor) based on the whnf head — mirroring the tactic-lane rintro
// classification. B106 lowers term `have ⟨a,b⟩ := e` to a single-arm
// `match e with | ⟨a,b⟩ => …`, so all three surface forms route through the
// same match-arm remap (`remap_anonymous_tuple_ctor` /
// `remap_anon_tuple_to_structure` in elab_match/match_arms.rs + helpers.rs).
// These tests pin the R99-filed everyday shapes (have/let/match ⟨⟩ over And/
// Exists/Subtype/Sigma/user-struct) against regression; every positive is
// value-distinguishing (the built term must kernel-check, not merely elaborate)
// and the negatives must fail loud (is_err), never silently accept.
// ---------------------------------------------------------------------------

#[test]
fn test_b108_have_anon_and_swap() {
    // Value-distinguishing: `⟨hp, hq⟩` over `p ∧ q` then rebuild the swapped
    // conjunction. The theorem `p ∧ q → q ∧ p` only kernel-checks if hp/hq
    // bind the correct And.intro fields.
    let src = "theorem b108AndSwap (p q : Prop) (h : p ∧ q) : q ∧ p :=\n  have ⟨hp, hq⟩ := h\n  ⟨hq, hp⟩\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b108 have ⟨⟩ over And, swapped rebuild");
}

#[test]
fn test_b108_have_anon_and_order_sensitive() {
    // Order-sensitive discriminators: proving `p` from the FIRST binder and `q`
    // from the SECOND. A wrong (swapped) remap would flip which goal each closes,
    // so both directions passing pins the field order of the And.intro remap.
    let first = "theorem b108AndFst (p q : Prop) (h : p ∧ q) : p :=\n  have ⟨hp, hq⟩ := h\n  hp\n";
    let second = "theorem b108AndSnd (p q : Prop) (h : p ∧ q) : q :=\n  have ⟨hp, hq⟩ := h\n  hq\n";
    let (_e1, r1) = elab_file_prelude(first);
    assert_all_ok(&r1, "b108 have ⟨hp,hq⟩ first-field proves p");
    let (_e2, r2) = elab_file_prelude(second);
    assert_all_ok(&r2, "b108 have ⟨hp,hq⟩ second-field proves q");
}

#[test]
fn test_b108_have_anon_nested_and() {
    // Nested `⟨hp, hq, hr⟩` over `p ∧ (q ∧ r)`: the right-nested Prod.mk spine
    // must peel through the inner And too, binding the deepest field.
    let src = "theorem b108Nested (p q r : Prop) (h : p ∧ (q ∧ r)) : r :=\n  have ⟨hp, hq, hr⟩ := h\n  hr\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b108 nested have ⟨_,_,_⟩ over p ∧ (q ∧ r)");
}

#[test]
fn test_b108_have_anon_exists() {
    // Exists.intro remap: bind witness + proof, reuse both to reprove the
    // existential. Value-distinguishing via the `= 5` proof carried through.
    let src = "theorem b108Exists (h : ∃ n : Nat, n = 5) : ∃ m : Nat, m = 5 :=\n  have ⟨w, hw⟩ := h\n  ⟨w, hw⟩\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b108 have ⟨w,hw⟩ over ∃, rebuild");
}

#[test]
fn test_b108_have_anon_subtype_all_forms() {
    // Subtype.mk remap over `{n : Nat // n > 0}` in all three surface forms —
    // the gap hits have / let / match identically, so pin all three.
    let have_form = "def b108SubHave (s : {n : Nat // n > 0}) : Nat :=\n  have ⟨v, hv⟩ := s\n  v\n";
    let let_form = "def b108SubLet (s : {n : Nat // n > 0}) : Nat :=\n  let ⟨v, hv⟩ := s\n  v\n";
    let match_form =
        "def b108SubMatch (s : {n : Nat // n > 0}) : Nat :=\n  match s with\n  | ⟨v, hv⟩ => v\n";
    for (label, src) in [
        ("have", have_form),
        ("let", let_form),
        ("match", match_form),
    ] {
        let (_env, results) = elab_file_prelude(src);
        assert_all_ok(&results, &format!("b108 {label} ⟨v,hv⟩ over Subtype"));
    }
}

#[test]
fn test_b108_anon_sigma() {
    // Sigma.mk remap over a dependent `Σ n : Nat, Fin n`.
    let src = "def b108Sigma (s : Σ n : Nat, Fin n) : Nat :=\n  have ⟨n, f⟩ := s\n  n\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b108 have ⟨n,f⟩ over Sigma");
}

#[test]
fn test_b108_anon_user_structure() {
    // A user single-constructor `structure`: the anonymous pattern remaps to its
    // sole constructor via the field-name table (mirrors the tactic-side
    // `get_structure_field_names` classification). Value-distinguishing via x+y.
    let src = "structure B108Pair where\n  a : Nat\n  b : Nat\n\ndef b108UserStruct (p : B108Pair) : Nat :=\n  have ⟨x, y⟩ := p\n  x * 10 + y\n\nexample : b108UserStruct ⟨3, 4⟩ = 34 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b108 have ⟨x,y⟩ over user structure + rfl");
}

#[test]
fn test_b108_genuine_prod_regression() {
    // Regression guard: a genuine `Prod` scrutinee keeps its Prod.mk path and
    // reduces to the right components (a=3, b=4 -> 34). The remap must not
    // disturb real tuples.
    let src = "def b108Prod (x : Nat × Nat) : Nat :=\n  have ⟨a, b⟩ := x\n  a * 10 + b\n\nexample : b108Prod (3, 4) = 34 := rfl\n";
    let (_env, results) = elab_file_prelude(src);
    assert_all_ok(&results, "b108 genuine Prod tuple still destructures");
}

#[test]
fn test_b108_wrong_arity_rejected() {
    // Fail-loud negative: `⟨a, b, c⟩` over a 2-field `And` has no third field to
    // bind; the elaborator must return Err, never a silent success that would let
    // an over-long pattern close the goal.
    let src = "theorem b108BadArity (p q : Prop) (h : p ∧ q) : q :=\n  have ⟨a, b, c⟩ := h\n  b\n";
    let (_env, results) = elab_file_prelude(src);
    assert!(
        results.last().expect("theorem present").is_err(),
        "b108: over-long ⟨a,b,c⟩ on a 2-field And must be rejected loud"
    );
}

#[test]
fn test_b108_pattern_lambda_prop_scrutinees() {
    // The pattern-lambda `fun ⟨a, b⟩ => …` form shares the same anonymous-ctor
    // remap over Prop/Subtype scrutinees (And.intro / Exists.intro / Subtype.mk),
    // with a genuine Prod as the regression guard.
    let cases: &[(&str, &str)] = &[
        (
            "and",
            "theorem b108PlAnd (p q : Prop) : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩\n",
        ),
        (
            "exists",
            "theorem b108PlEx (p : Nat → Prop) : (∃ x, p x) → (∃ y, p y) := fun ⟨w, hw⟩ => ⟨w, hw⟩\n",
        ),
        (
            "subtype",
            "def b108PlSub : {n : Nat // n > 0} → Nat := fun ⟨v, hv⟩ => v\n",
        ),
        (
            "prod",
            "def b108PlProd : Nat × Nat → Nat := fun ⟨a, b⟩ => a * 10 + b\n",
        ),
    ];
    for (label, src) in cases {
        let (_env, results) = elab_file_prelude(src);
        assert_all_ok(&results, &format!("b108 pattern-lambda ⟨⟩ over {label}"));
    }
}

#[test]
fn test_b108_omega_ofnat_two_mul() {
    // `n + n = 2 * n` — Lean elaborates the `2` as `OfNat.ofNat Nat 2 _`, so
    // omega's Nat linear closer must peel `OfNat` to see the `2 * n`
    // coefficient. Before the peel it read `2 * n` as a non-linear product and
    // reported "could not extract linear constraints". Kernel-re-checked: the
    // omega-closed proof passes close_goal.
    let code = "theorem t_omega_2mul (n : Nat) : n + n = 2 * n := by omega\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "omega n + n = 2 * n");
    assert!(
        env.get_const(&Name::from_string("t_omega_2mul")).is_some(),
        "t_omega_2mul should register"
    );
}

#[test]
fn test_b108_omega_ofnat_exists_witness() {
    // `∃ k, n + n = 2 * k` with witness `n` reduces to `n + n = 2 * n`, closed
    // by omega once the `OfNat` literal `2` is peeled.
    let code = "theorem t_omega_exists (n : Nat) : ∃ k, n + n = 2 * k := ⟨n, by omega⟩\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "omega exists 2*k witness");
    assert!(
        env.get_const(&Name::from_string("t_omega_exists"))
            .is_some(),
        "t_omega_exists should register"
    );
}

#[test]
fn test_b108_omega_ofnat_false_goal_rejected() {
    // SOUNDNESS: the `OfNat` peel must NOT let omega close a FALSE coefficient
    // goal. `n + n = 3 * n` holds only at n = 0; with `3 * n` now linearized to
    // coefficient 3, the decision gate sees 2*n vs 3*n differ and must fail
    // closed (never a spurious `proved`).
    let code = "theorem t_omega_false (n : Nat) : n + n = 3 * n := by omega\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "omega MUST reject the false goal n + n = 3 * n, got: {results:?}"
    );
}

#[test]
fn test_b109_wlog_colon_closes() {
    // Lean 4 `wlog h : P` now parses (dedicated parser arm mirroring by_cases)
    // and elaborates: `super::wlog` produces two goals (the assumption branch
    // `h : a ≤ b` and the negated branch), both closed by omega here. Before the
    // parser arm, `wlog h : a ≤ b` failed with MissingArgument (the generic
    // arg parser stopped at `:`, passing < 2 args to the wlog handler).
    // Value-distinguishing: the whole proof is kernel-re-checked on register.
    let code = "theorem wlog_ok (a b : Nat) : a + b = b + a := by\n  wlog h : a \u{2264} b\n  \u{b7} omega\n  \u{b7} omega\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "wlog h : P closes");
    assert!(
        env.get_const(&Name::from_string("wlog_ok")).is_some(),
        "wlog_ok theorem should register"
    );
}

#[test]
fn test_b109_wlog_no_ident_rejected() {
    // SOUNDNESS/robustness: `wlog : P` with no hypothesis identifier must fail
    // loud (the parser arm requires `<ident> : <prop>`), never silently succeed.
    let code = "example (a b : Nat) : a + b = b + a := by wlog : a \u{2264} b\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "wlog with no identifier must be rejected, got: {results:?}"
    );
}

#[test]
fn test_b109_wlog_unsolved_rejected() {
    // SOUNDNESS: `wlog h : P` opens TWO goals; discharging only one must leave
    // the proof with an unsolved goal (never a silent success).
    let code = "theorem wlog_bad (a b : Nat) : a + b = b + a := by\n  wlog h : a \u{2264} b\n  \u{b7} omega\n";
    let (_env, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "wlog leaving one goal unsolved must be rejected, got: {results:?}"
    );
}

#[test]
fn test_b110_int_lt_succ_omega() {
    // Int linear arithmetic: `a < b + 1` from `h : a ≤ b`. B110 combines the
    // app_spine FM parser fix (so `b + 1` over Int is extracted, not dropped)
    // with an Int weakening prover: `Int.lt a c` is def `Int.le (a+1) c`, so
    // `@Int.add_le_add_right a b h 1 : Int.le (a+1)(b+1)` is def-eq to the goal.
    // Value-distinguishing: the built proof is kernel-re-checked by close_goal.
    let code = "theorem b110_ilt (a b : Int) (h : a ≤ b) : a < b + 1 := by omega\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int a < b + 1 by omega");
    assert!(env.get_const(&Name::from_string("b110_ilt")).is_some());
}

#[test]
fn test_b110_int_lt_succ_linarith() {
    let code = "theorem b110_ilt_lin (a b : Int) (h : a ≤ b) : a < b + 1 := by linarith\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int a < b + 1 by linarith");
    assert!(env.get_const(&Name::from_string("b110_ilt_lin")).is_some());
}

#[test]
fn test_b110_int_false_goal_rejected() {
    // SOUNDNESS: `a > b` from `a ≤ b` is false — must NOT close.
    let code = "example (a b : Int) (h : a ≤ b) : a > b := by omega\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false Int a > b must be rejected: {results:?}"
    );
}

#[test]
fn test_b110_int_wrong_lhs_rejected() {
    // SOUNDNESS: `b < a + 1` from `a ≤ b` holds only at a = b — must NOT close
    // (the weakening prover only fires when the goal LHS matches the hyp LHS).
    let code = "example (a b : Int) (h : a ≤ b) : b < a + 1 := by omega\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false Int b < a + 1 must be rejected: {results:?}"
    );
}

#[test]
fn test_b110_natsub_still_rejected() {
    // SOUNDNESS: the app_spine parser must keep the Nat.sub truncation guard —
    // `a - b + b = a` is false over truncated Nat and must NOT close.
    let code = "example (a b : Nat) : a - b + b = a := by omega\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false Nat.sub goal must be rejected: {results:?}"
    );
}

#[test]
fn test_b111_int_le_succ_omega() {
    // B111 extends the Int weakening prover to the non-strict shape `a ≤ b + 1`
    // from `h : a ≤ b`, proved by `Int.le_trans a b (b+1) h (Int.le_self_add_one b)`
    // (both lemmas registered in the kernel prelude). Value-distinguishing: the
    // built proof is kernel-re-checked by close_goal.
    let code = "theorem b111_ile (a b : Int) (h : a ≤ b) : a ≤ b + 1 := by omega\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int a ≤ b + 1 by omega");
    assert!(env.get_const(&Name::from_string("b111_ile")).is_some());
}

#[test]
fn test_b111_int_le_succ_linarith() {
    let code = "theorem b111_ile_lin (a b : Int) (h : a ≤ b) : a ≤ b + 1 := by linarith\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int a ≤ b + 1 by linarith");
    assert!(env.get_const(&Name::from_string("b111_ile_lin")).is_some());
}

#[test]
fn test_b111_int_le_identity_still_closes() {
    // REGRESSION GUARD: the identity goal `a ≤ b` must STILL close via the raw
    // hypothesis — the new le-weakening returns None on it (RHS is not `b + 1`),
    // so it must not shadow the raw-hyp closer.
    let code = "theorem b111_ile_id (a b : Int) (h : a ≤ b) : a ≤ b := by omega\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int identity a ≤ b by omega");
    assert!(env.get_const(&Name::from_string("b111_ile_id")).is_some());
}

#[test]
fn test_b111_int_le_false_rejected() {
    // SOUNDNESS: `a ≤ b - 2` from `a ≤ b` is false (fails at a = b) — must NOT close.
    let code = "example (a b : Int) (h : a ≤ b) : a ≤ b - 2 := by omega\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false Int a ≤ b - 2 must be rejected: {results:?}"
    );
}

#[test]
fn test_b111_int_le_wrong_lhs_rejected() {
    // SOUNDNESS: `b ≤ a + 1` from `a ≤ b` holds only at a = b — must NOT close
    // (the weakening prover only fires when the goal LHS matches the hyp LHS).
    let code = "example (a b : Int) (h : a ≤ b) : b ≤ a + 1 := by omega\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false Int b ≤ a + 1 must be rejected: {results:?}"
    );
}

#[test]
fn test_b112_calc_le_lt_nat() {
    // B112: calc mixed-relation `a ≤ b < c ⊢ a < c` over Nat. The carrier-qualified
    // Nat.lt_of_le_of_lt has EXPLICIT endpoint binders (a b c), which the implicit-only
    // apply_lemma_to_proofs cannot fill; try_apply_explicit_endpoints supplies them.
    let code = "theorem b112_lelt (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c := by\n  calc a ≤ b := h1\n    _ < c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a ≤ b < c");
    assert!(env.get_const(&Name::from_string("b112_lelt")).is_some());
}

#[test]
fn test_b112_calc_le_lt_int() {
    let code = "theorem b112_lelt_int (a b c : Int) (h1 : a ≤ b) (h2 : b < c) : a < c := by\n  calc a ≤ b := h1\n    _ < c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a ≤ b < c");
    assert!(env.get_const(&Name::from_string("b112_lelt_int")).is_some());
}

#[test]
fn test_b112_calc_homog_le_regression() {
    // REGRESSION GUARD: homogeneous `a ≤ b ≤ c ⊢ a ≤ c` (implicit-endpoint
    // Nat.le_trans) must STILL close via the existing implicit path.
    let code = "theorem b112_lele (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by\n  calc a ≤ b := h1\n    _ ≤ c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a ≤ b ≤ c regression");
    assert!(env.get_const(&Name::from_string("b112_lele")).is_some());
}

#[test]
fn test_b112_calc_mix_false_rejected() {
    // SOUNDNESS: the chain `a ≤ b < c` proves `a < c`; a false goal `c < a`
    // must NOT be closed by it.
    let code = "example (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : c < a := by\n  calc a ≤ b := h1\n    _ < c := h2\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false calc goal c < a must be rejected: {results:?}"
    );
}

#[test]
fn test_b113_calc_lt_le_int() {
    // B113 (test-only): the B112 explicit-endpoint calc fix ALSO closes the
    // `lt` + `le` mixed shape `a < b ≤ c ⊢ a < c` over Int, because with_prelude
    // registers Int.lt_of_lt_of_le (env/mod.rs). This locks that capability in.
    let code = "theorem b113_ltle_int (a b c : Int) (h1 : a < b) (h2 : b ≤ c) : a < c := by\n  calc a < b := h1\n    _ ≤ c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a < b ≤ c");
    assert!(env.get_const(&Name::from_string("b113_ltle_int")).is_some());
}

#[test]
fn test_b113_calc_lt_le_int_false_rejected() {
    // SOUNDNESS: the chain `a < b ≤ c` proves `a < c`; a false goal `c < a`
    // must NOT be closed by it.
    let code = "example (a b c : Int) (h1 : a < b) (h2 : b ≤ c) : c < a := by\n  calc a < b := h1\n    _ ≤ c := h2\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false calc goal c < a must be rejected: {results:?}"
    );
}

#[test]
fn test_b114_calc_le_eq_nat() {
    let code = "theorem b114_leeq_n (a b c : Nat) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by\n  calc a ≤ b := h1\n    _ = c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a ≤ b = c");
    assert!(env.get_const(&Name::from_string("b114_leeq_n")).is_some());
}

#[test]
fn test_b114_calc_le_eq_int() {
    let code = "theorem b114_leeq_i (a b c : Int) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by\n  calc a ≤ b := h1\n    _ = c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a ≤ b = c");
    assert!(env.get_const(&Name::from_string("b114_leeq_i")).is_some());
}

#[test]
fn test_b114_calc_eq_lt_nat() {
    let code = "theorem b114_eqlt_n (a b c : Nat) (h1 : a = b) (h2 : b < c) : a < c := by\n  calc a = b := h1\n    _ < c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a = b < c");
    assert!(env.get_const(&Name::from_string("b114_eqlt_n")).is_some());
}

#[test]
fn test_b114_calc_eq_lt_int() {
    let code = "theorem b114_eqlt_i (a b c : Int) (h1 : a = b) (h2 : b < c) : a < c := by\n  calc a = b := h1\n    _ < c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a = b < c");
    assert!(env.get_const(&Name::from_string("b114_eqlt_i")).is_some());
}

#[test]
fn test_b114_calc_lt_eq_int() {
    let code = "theorem b114_lteq_i (a b c : Int) (h1 : a < b) (h2 : b = c) : a < c := by\n  calc a < b := h1\n    _ = c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a < b = c");
    assert!(env.get_const(&Name::from_string("b114_lteq_i")).is_some());
}

#[test]
fn test_b114_calc_eq_lt_false_rejected() {
    // SOUNDNESS: chain `a = b < c` proves `a < c`; false goal `c < a` must NOT close.
    let code = "example (a b c : Int) (h1 : a = b) (h2 : b < c) : c < a := by\n  calc a = b := h1\n    _ < c := h2\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false calc goal c < a must be rejected: {results:?}"
    );
}

#[test]
fn test_b114_calc_eq_eq_regression() {
    // REGRESSION GUARD: homogeneous Eq.trans `a = b = c ⊢ a = c` must still close.
    let code = "theorem b114_eqeq (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := h1\n    _ = c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a = b = c regression");
    assert!(env.get_const(&Name::from_string("b114_eqeq")).is_some());
}

#[test]
fn test_b115_calc_eq_le_int() {
    // B115: the eq-subst calc path now returns a SURFACE result type, so it
    // recognizes result_rel = Eq cases (`a = b ≤ c ⊢ a ≤ c`) and threads into
    // following steps (multi-step chains). Over Int.
    let code = "theorem b115_eqle_i (a b c : Int) (h1 : a = b) (h2 : b ≤ c) : a ≤ c := by\n  calc a = b := h1\n    _ ≤ c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a = b ≤ c");
    assert!(env.get_const(&Name::from_string("b115_eqle_i")).is_some());
}

#[test]
fn test_b115_calc_eq_le_nat() {
    let code = "theorem b115_eqle_n (a b c : Nat) (h1 : a = b) (h2 : b ≤ c) : a ≤ c := by\n  calc a = b := h1\n    _ ≤ c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a = b ≤ c");
    assert!(env.get_const(&Name::from_string("b115_eqle_n")).is_some());
}

#[test]
fn test_b115_calc_lt_eq_nat() {
    let code = "theorem b115_lteq_n (a b c : Nat) (h1 : a < b) (h2 : b = c) : a < c := by\n  calc a < b := h1\n    _ = c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a < b = c");
    assert!(env.get_const(&Name::from_string("b115_lteq_n")).is_some());
}

#[test]
fn test_b115_calc_ge_eq_int() {
    // GE + Eq: `a ≥ b = c ⊢ a ≥ c` — match_goal_rel recognizes the surface GE.ge.
    let code = "theorem b115_geeq_i (a b c : Int) (h1 : a ≥ b) (h2 : b = c) : a ≥ c := by\n  calc a ≥ b := h1\n    _ = c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a ≥ b = c");
    assert!(env.get_const(&Name::from_string("b115_geeq_i")).is_some());
}

#[test]
fn test_b115_calc_3step_eq_le_lt() {
    // Multi-step chain `a = b ≤ c < d ⊢ a < d`: the eq-subst step now returns a
    // surface `a ≤ c`, which threads into the following `< d` step. This is the
    // capability the whnf'd type blocked before B115.
    let code = "theorem b115_3s (a b c d : Int) (h1 : a = b) (h2 : b ≤ c) (h3 : c < d) : a < d := by\n  calc a = b := h1\n    _ ≤ c := h2\n    _ < d := h3\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Int calc a = b ≤ c < d");
    assert!(env.get_const(&Name::from_string("b115_3s")).is_some());
}

#[test]
fn test_b115_calc_eq_le_false_rejected() {
    // SOUNDNESS: `a = b ≤ c` proves `a ≤ c`; false goal `c ≤ a` (holds only at
    // a = b = c) must NOT close.
    let code = "example (a b c : Int) (h1 : a = b) (h2 : b ≤ c) : c ≤ a := by\n  calc a = b := h1\n    _ ≤ c := h2\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false calc goal c ≤ a must be rejected: {results:?}"
    );
}

#[test]
fn test_b115_calc_3step_false_rejected() {
    // SOUNDNESS: the 3-step chain proves `a < d`; false goal `d < a` must NOT close.
    let code = "example (a b c d : Int) (h1 : a = b) (h2 : b ≤ c) (h3 : c < d) : d < a := by\n  calc a = b := h1\n    _ ≤ c := h2\n    _ < d := h3\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false 3-step goal d < a must be rejected: {results:?}"
    );
}

#[test]
fn test_b116_calc_lt_le_nat() {
    // B116: `a < b ≤ c ⊢ a < c` over Nat. Nat has no registered Nat.lt_of_lt_of_le,
    // but Nat.lt a b is definitionally Nat.le (a+1) b, so le_trans composes it:
    // le_trans (h1 : le (a+1) b) (h2 : le b c) : le (a+1) c ≡ a < c. mk_calc_trans
    // now tries le_trans as a fallback for the (Lt, Le) rule.
    let code = "theorem b116_ltle_n (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by\n  calc a < b := h1\n    _ ≤ c := h2\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "Nat calc a < b ≤ c");
    assert!(env.get_const(&Name::from_string("b116_ltle_n")).is_some());
}

#[test]
fn test_b116_calc_lt_le_nat_false_rejected() {
    // SOUNDNESS: `a < b ≤ c` proves `a < c`; false goal `c < a` must NOT close.
    let code = "example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : c < a := by\n  calc a < b := h1\n    _ ≤ c := h2\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "false Nat calc goal c < a must be rejected: {results:?}"
    );
}

#[test]
fn test_b117_nested_ctor_match() {
    // B117: nested constructor patterns whose arms share an outer ctor now
    // compile. `some (some n)` and `some none` are merged into a nested inner
    // match on the Option field via the column-split rescue; the fix resolves the
    // inner ctor's short name (`some`) to `Option.some` so its field-type
    // metadata lookup succeeds.
    let code = "def f117 : Option (Option Nat) → Nat\n  | some (some n) => n\n  | some none => 0\n  | none => 0\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested some (some n) match");
    assert!(env.get_const(&Name::from_string("f117")).is_some());
}

#[test]
fn test_b117_nested_ctor_computes() {
    // VALUE: the compiled nested match actually reduces (kernel rfl on each arm).
    let code = "def f117b : Option (Option Nat) → Nat\n  | some (some n) => n\n  | some none => 0\n  | none => 0\n\ntheorem f117b_a : f117b (some (some 5)) = 5 := rfl\ntheorem f117b_b : f117b (some none) = 0 := rfl\ntheorem f117b_c : f117b none = 0 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested match computes via rfl");
    assert!(env.get_const(&Name::from_string("f117b_a")).is_some());
}

#[test]
fn test_b117_nested_non_exhaustive_rejected() {
    // SOUNDNESS/EXHAUSTIVENESS: a genuinely non-exhaustive nested match — missing
    // the `some none` case — must STILL be rejected. The fix must not weaken the
    // exhaustiveness checker into accepting incomplete matches.
    let code = "def f117c : Option (Option Nat) → Nat\n  | some (some n) => n\n  | none => 0\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "non-exhaustive nested match (missing some none) must be rejected: {results:?}"
    );
}

#[test]
fn test_b117_nested_ctor_wildcard_still_works() {
    // REGRESSION: nested pattern + a catch-all wildcard arm still compiles.
    let code = "def f117d : Option (Option Nat) → Nat\n  | some (some n) => n\n  | _ => 0\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "nested + wildcard");
    assert!(env.get_const(&Name::from_string("f117d")).is_some());
}

#[test]
fn test_b118_infix_single() {
    // B118: non-associative `infix` notation. `infix:65 " ⊗⊗ " => Nat.add` then
    // `2 ⊗⊗ 3` now parses and elaborates (fresh non-builtin symbol).
    let code = "infix:65 \" ⊗⊗ \" => Nat.add\n\ndef b118_f : Nat := 2 ⊗⊗ 3\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "infix single application");
    assert!(env.get_const(&Name::from_string("b118_f")).is_some());
}

#[test]
fn test_b118_infix_computes() {
    // VALUE: the infix application reduces (kernel rfl).
    let code = "infix:65 \" ⊗⊗ \" => Nat.add\n\ntheorem b118_c : (2 ⊗⊗ 3) = 5 := rfl\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "infix computes via rfl");
    assert!(env.get_const(&Name::from_string("b118_c")).is_some());
}

#[test]
fn test_b118_infix_low_band() {
    // The low precedence band (45-50) also handles infix.
    let code = "infix:50 \" ⊗⊗ \" => Nat.add\n\ndef b118_lb : Nat := 2 ⊗⊗ 3\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "infix low band");
    assert!(env.get_const(&Name::from_string("b118_lb")).is_some());
}

#[test]
fn test_b118_infix_chain_rejected() {
    // FAITHFULNESS: `infix` is NON-associative — `2 ⊗⊗ 3 ⊗⊗ 4` must be rejected
    // (Lean requires explicit parentheses). NOT silently left-associated.
    let code = "infix:65 \" ⊗⊗ \" => Nat.add\n\ndef b118_bad : Nat := 2 ⊗⊗ 3 ⊗⊗ 4\n";
    let (_e, results) = elab_file_prelude(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "non-assoc infix chaining must be rejected: {results:?}"
    );
}

#[test]
fn test_b118_infixl_regression() {
    // REGRESSION: infixl still left-associates and chains.
    let code = "infixl:65 \" ⊗⊗ \" => Nat.add\n\ndef b118_il : Nat := 2 ⊗⊗ 3 ⊗⊗ 4\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "infixl still works + chains");
    assert!(env.get_const(&Name::from_string("b118_il")).is_some());
}

#[test]
fn test_b118_infixr_regression() {
    // REGRESSION: infixr still right-associates and chains.
    let code = "infixr:65 \" ⊗⊗ \" => Nat.mul\n\ndef b118_ir : Nat := 2 ⊗⊗ 3 ⊗⊗ 4\n";
    let (env, results) = elab_file_prelude(code);
    assert_all_ok(&results, "infixr still works + chains");
    assert!(env.get_const(&Name::from_string("b118_ir")).is_some());
}

#[test]
fn test_do_for_list_mut_kernel_computes() {
    // LOCK: do-notation `let mut` + `for x in <list> do` accumulator must desugar
    // (ForIn over List) AND kernel-reduce, so `rfl` closes on the computed value.
    // This capability had ZERO corpus coverage before this lock. The distinct
    // results (6 / 60 / 0 / 24) guard against a stub returning a constant, and the
    // mixed `+`/`*` bodies + the empty-list base case guard loop-body substitution
    // and the fold's initial value.
    let code = r#"
def fSum : Nat := Id.run do
  let mut s := 0
  for i in [1,2,3] do
    s := s + i
  return s
def fSum2 : Nat := Id.run do
  let mut s := 0
  for i in [10,20,30] do
    s := s + i
  return s
def fEmpty : Nat := Id.run do
  let mut s := 0
  for i in ([] : List Nat) do
    s := s + i
  return s
def fProd : Nat := Id.run do
  let mut s := 1
  for i in [2,3,4] do
    s := s * i
  return s
theorem dfl_sum : fSum = 6 := rfl
theorem dfl_sum2 : fSum2 = 60 := rfl
theorem dfl_empty : fEmpty = 0 := rfl
theorem dfl_prod : fProd = 24 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "do/for-over-list mut kernel-computes",
    );
}

#[test]
fn test_do_for_list_mut_wrong_value_rejected() {
    // SOUNDNESS: the loop genuinely computes, so a wrong accumulator target must be
    // rejected by the kernel — never accepted by a lax `do`/`for` stub.
    let code = r#"
def fSum : Nat := Id.run do
  let mut s := 0
  for i in [1,2,3] do
    s := s + i
  return s
theorem dfl_wrong : fSum = 7 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong for-loop sum (fSum = 7) must be rejected"
    );
}

#[test]
fn test_b119_macro_command_computes() {
    // B119: the one-line `macro "kw" args : cat => rhs` command (application form)
    // must register usable syntax whose use site `kw args` expands AND kernel-reduces,
    // so rfl closes on the computed value. Previously register_macro keyed the macro
    // under a kind the use site never has (`app("kw")` vs `app_kind()`), so `kw args`
    // stayed an unresolved ident. Distinct results (10 / 42 / 8) guard against a stub.
    let code = r#"
macro "twice" x:term : term => `($x + $x)
macro "addup" x:term y:term : term => `($x + $y + 1)
def m1 : Nat := twice 5
def m2 : Nat := twice 21
def m3 : Nat := addup 3 4
theorem b119_a : m1 = 10 := rfl
theorem b119_b : m2 = 42 := rfl
theorem b119_c : m3 = 8 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "macro command application form computes",
    );
}

#[test]
fn test_b119_macro_command_wrong_value_rejected() {
    // SOUNDNESS: the macro genuinely expands and computes, so a wrong target must be
    // rejected by the kernel — never accepted by a lax registration.
    let code = r#"
macro "twice" x:term : term => `($x + $x)
def m1 : Nat := twice 5
theorem b119_wrong : m1 = 11 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong macro expansion (twice 5 = 11) must be rejected"
    );
}

#[test]
fn test_b119_macro_rules_still_works_regression() {
    // The two-step syntax + macro_rules path (which already worked) must remain intact
    // after rerouting the one-line `macro` command's registration.
    let code = r#"
syntax "dbl" term : term
macro_rules | `(dbl $x) => `($x * 2)
def m4 : Nat := dbl 7
theorem b119_reg : m4 = 14 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "macro_rules regression after B119",
    );
}

#[test]
fn test_b120_array_foldl_computes() {
    // B120: Array.foldl registered in the kernel prelude (clean-kernel data.rs
    // init_array), defined compositionally as List.foldl ∘ Array.data. Dot-notation
    // `as.foldl f init` now expands AND kernel-reduces. Distinct results (6/60/24)
    // + mixed +/* bodies guard against a stub; List.foldl regression unaffected.
    let code = r#"
def s1 : Nat := #[1,2,3].foldl (· + ·) 0
def s2 : Nat := #[10,20,30].foldl (· + ·) 0
def s3 : Nat := #[2,3,4].foldl (· * ·) 1
def s4 : Nat := (#[] : Array Nat).foldl (· + ·) 0
theorem b120_f1 : s1 = 6 := rfl
theorem b120_f2 : s2 = 60 := rfl
theorem b120_f3 : s3 = 24 := rfl
theorem b120_f4 : s4 = 0 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "Array.foldl dot-notation kernel-computes",
    );
}

#[test]
fn test_b120_array_foldl_wrong_value_rejected() {
    // SOUNDNESS: the fold genuinely computes, so a wrong target must be rejected.
    let code = r#"
def s1 : Nat := #[1,2,3].foldl (· + ·) 0
theorem b120_fw : s1 = 7 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Array.foldl sum (= 7) must be rejected"
    );
}

#[test]
fn test_b120_array_map_computes() {
    // B120: Array.map = Array.mk ∘ (List.map f) ∘ Array.data. `as.map f` expands and
    // the resulting Array reduces so rfl closes on the mapped array literal.
    let code = r#"
def a1 : Array Nat := #[1,2,3].map (· + 1)
def a2 : Array Nat := #[1,2,3].map (· * 2)
theorem b120_m1 : a1 = #[2,3,4] := rfl
theorem b120_m2 : a2 = #[2,4,6] := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "Array.map dot-notation kernel-computes",
    );
}

#[test]
fn test_b120_array_map_wrong_value_rejected() {
    // SOUNDNESS: a wrong mapped array must be rejected.
    let code = r#"
def a1 : Array Nat := #[1,2,3].map (· + 1)
theorem b120_mw : a1 = #[2,3,5] := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Array.map result must be rejected"
    );
}

#[test]
fn test_b121_array_push_computes() {
    // B121: Array.push = Array.mk (Array.data as ++ [a]) registered in the kernel
    // prelude (clean-kernel data.rs init_array, guarded on List.append). `as.push a`
    // expands and kernel-reduces so rfl closes on the extended array literal.
    let code = r#"
def a1 : Array Nat := #[1,2].push 3
def a2 : Array Nat := (#[] : Array Nat).push 5
def a3 : Array Nat := (#[7].push 8).push 9
theorem b121_p1 : a1 = #[1,2,3] := rfl
theorem b121_p2 : a2 = #[5] := rfl
theorem b121_p3 : a3 = #[7,8,9] := rfl
theorem b121_p4 : a1.size = 3 := rfl
"#;
    assert_all_ok(&elab_file_prelude(code).1, "Array.push kernel-computes");
}

#[test]
fn test_b121_array_push_wrong_value_rejected() {
    // SOUNDNESS: a wrong pushed array must be rejected.
    let code = r#"
def a1 : Array Nat := #[1,2].push 3
theorem b121_pw : a1 = #[1,2,4] := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Array.push result must be rejected"
    );
}

#[test]
fn test_b121_array_foldr_computes() {
    // B121: Array.foldr = List.foldr ∘ Array.data. The `foldr (·::·) []` case is
    // ORDER-distinguishing: a genuine right-fold yields [1,2,3] (foldl would reverse
    // to [3,2,1]), so it guards fold direction, not just the summed value.
    let code = r#"
def s1 : Nat := #[1,2,3].foldr (· + ·) 0
def l1 : List Nat := #[1,2,3].foldr (fun x acc => x :: acc) []
def e1 : Nat := (#[] : Array Nat).foldr (· + ·) 0
theorem b121_f1 : s1 = 6 := rfl
theorem b121_f2 : l1 = [1,2,3] := rfl
theorem b121_f3 : e1 = 0 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "Array.foldr kernel-computes (order-preserving)",
    );
}

#[test]
fn test_b121_array_foldr_wrong_value_rejected() {
    // SOUNDNESS: a wrong fold result must be rejected.
    let code = r#"
def s1 : Nat := #[1,2,3].foldr (· + ·) 0
theorem b121_fw : s1 = 7 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Array.foldr result must be rejected"
    );
}

#[test]
fn test_b122_fin_literal_computes() {
    // B122: instOfNatFin (kernel prelude, clean-kernel data.rs) makes a numeric
    // literal at type `Fin (n+1)` elaborate via OfNat → Fin.ofNat, which reduces
    // `i % (n+1)`. Instance synthesis matches `Fin 5` against `Fin (Nat.succ ?n)`,
    // and the value kernel-reduces so rfl closes on the modular result. The
    // wrap case (7 : Fin 3 → 1) is value-distinguishing: it proves genuine
    // `i % (n+1)`, not a truncation or a stuck literal.
    let code = r#"
def a : Fin 5 := 3
def b : Fin 5 := 0
def c : Fin 3 := 7
def d : Fin 10 := 2
theorem b122_a : a.val = 3 := rfl
theorem b122_b : b.val = 0 := rfl
theorem b122_c : c.val = 1 := rfl
theorem b122_d : d.val = 2 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "Fin numeric literal elaborates + kernel-computes",
    );
}

#[test]
fn test_b122_fin_literal_wrong_value_rejected() {
    // SOUNDNESS: the Fin literal genuinely computes its residue, so a wrong .val
    // must be rejected by the kernel.
    let code = r#"
def a : Fin 5 := 3
theorem b122_w : a.val = 4 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Fin-literal value (a.val = 4) must be rejected"
    );
}

#[test]
fn test_b123_getd_computes() {
    // B123: List.getD / Array.getD registered in the kernel prelude (clean-kernel
    // data.rs init_array) — the TOTAL index-with-default (no Inhabited), built from
    // List.rec into a Nat→α step function with an inner Nat.rec. Dot-notation
    // `xs.getD i d` expands and kernel-reduces: in-bounds returns the element,
    // out-of-bounds (index past the end, and empty list) returns the fallback.
    let code = r#"
def a1 : Nat := #[10,20,30].getD 1 0
def a2 : Nat := #[10,20,30].getD 0 0
def a3 : Nat := #[10,20].getD 5 99
def l1 : Nat := [10,20,30].getD 2 0
def l2 : Nat := ([] : List Nat).getD 3 7
theorem b123_a1 : a1 = 20 := rfl
theorem b123_a2 : a2 = 10 := rfl
theorem b123_a3 : a3 = 99 := rfl
theorem b123_l1 : l1 = 30 := rfl
theorem b123_l2 : l2 = 7 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "List.getD / Array.getD kernel-compute",
    );
}

#[test]
fn test_b123_getd_wrong_value_rejected() {
    // SOUNDNESS: getD genuinely computes the indexed element, so a wrong target
    // must be rejected by the kernel.
    let code = r#"
def a1 : Nat := #[10,20,30].getD 1 0
theorem b123_w : a1 = 21 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Array.getD value (a1 = 21) must be rejected"
    );
}

#[test]
fn test_b124_get_bang_computes() {
    // B124: List.get! / Array.get! (kernel prelude, clean-kernel data.rs init_array) —
    // the Inhabited-defaulted partial index accessors: get! = getD with the fallback
    // supplied by the Inhabited instance. `xs.get! i` kernel-reduces; out-of-bounds
    // (and empty) return `default` (0 for Nat), which is value-distinguishing against
    // any stub that would panic or return a wrong element.
    let code = r#"
def a1 : Nat := #[10,20,30].get! 1
def a2 : Nat := #[10,20,30].get! 0
def a3 : Nat := #[10,20].get! 5
def l1 : Nat := [10,20,30].get! 2
def l2 : Nat := ([] : List Nat).get! 3
theorem b124_a1 : a1 = 20 := rfl
theorem b124_a2 : a2 = 10 := rfl
theorem b124_a3 : a3 = 0 := rfl
theorem b124_l1 : l1 = 30 := rfl
theorem b124_l2 : l2 = 0 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "List.get! / Array.get! kernel-compute",
    );
}

#[test]
fn test_b124_get_bang_wrong_value_rejected() {
    // SOUNDNESS: get! genuinely computes the indexed element, so a wrong target
    // must be rejected by the kernel.
    let code = r#"
def a1 : Nat := #[10,20,30].get! 1
theorem b124_w : a1 = 21 := rfl
"#;
    assert!(
        elab_file_prelude(code).1.iter().any(|r| r.is_err()),
        "wrong Array.get! value (a1 = 21) must be rejected"
    );
}

#[test]
fn test_b125_bitvec_literal_elaborates() {
    // B125: instOfNatBitVec + BitVec.ofNat (kernel prelude, clean-kernel
    // data_types_bitvec.rs register_bitvec_of_nat) make a numeric literal at type
    // `BitVec w` elaborate via OfNat instance synthesis, exactly like `Fin`.
    // Before this brick there was NO OfNat-BitVec instance, so `(n : BitVec w)`
    // failed instance synthesis outright. The instance omits any succ-constraint
    // (2^w > 0 for all w), so `BitVec 0` literals also elaborate.
    let code = r#"
def x : BitVec 8 := 5
def y : BitVec 8 := 200
def w2 : BitVec 2 := 5
def z0 : BitVec 8 := 0
def b0 : BitVec 0 := 5
def b1 : BitVec 1 := 3
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "BitVec numeric literals elaborate via OfNat instance synthesis",
    );
}

#[test]
fn test_b125_bitvec_ofnat_computes() {
    // B125: the registered `BitVec.ofNat w n` genuinely kernel-reduces to the
    // wrapped residue `n % 2^w` (via BitVec.ofNatLT + a Nat.pow_le_pow_right
    // positivity witness). The wrap cases (5 : BitVec 2 → 1) are
    // value-distinguishing: they prove genuine `n % 2^w`, not a truncation or a
    // stuck literal. Both the direct `BitVec.ofNat` spelling and the fully
    // instance-synthesised `@OfNat.ofNat (BitVec w) i (@instOfNatBitVec w i)`
    // spelling reduce identically.
    let code = r#"
theorem b125_c1 : (BitVec.ofNat 8 5).toNat = 5 := rfl
theorem b125_c2 : (BitVec.ofNat 8 200).toNat = 200 := rfl
theorem b125_c3 : (BitVec.ofNat 2 5).toNat = 1 := rfl
theorem b125_c4 : (BitVec.ofNat 0 5).toNat = 0 := rfl
theorem b125_c5 : (@OfNat.ofNat (BitVec 8) 5 (@instOfNatBitVec 8 5)).toNat = 5 := rfl
theorem b125_c6 : (@OfNat.ofNat (BitVec 2) 5 (@instOfNatBitVec 2 5)).toNat = 1 := rfl
"#;
    assert_all_ok(
        &elab_file_prelude(code).1,
        "BitVec.ofNat / instOfNatBitVec literal kernel-compute (incl. wrap)",
    );
}

#[test]
fn test_b125_bitvec_ofnat_wrong_value_rejected() {
    // SOUNDNESS: BitVec.ofNat genuinely computes `n % 2^w`, so a wrong .toNat
    // target — including asserting the un-wrapped value (5) instead of the wrapped
    // residue (1) at width 2 — must be rejected by the kernel.
    for code in [
        "theorem bad : (BitVec.ofNat 8 5).toNat = 6 := rfl",
        "theorem bad : (BitVec.ofNat 2 5).toNat = 5 := rfl",
        "theorem bad : (@OfNat.ofNat (BitVec 8) 5 (@instOfNatBitVec 8 5)).toNat = 6 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong BitVec-literal value must be rejected: {code}",
        );
    }
}

#[test]
fn test_b125_bitvec_literal_const_indirection_gap() {
    // HONEST GAP (loud, NOT silent-wrong): a `def`-const whose value is the
    // OfNat-wrapped literal `@OfNat.ofNat (BitVec w) i (@instOfNatBitVec w i)`
    // does NOT currently whnf-reduce when it is the deeply-nested major of the
    // `Fin.rec` inside `BitVec.toNat` (i.e. `x.toNat = 5 := rfl` for
    // `def x : BitVec 8 := 5`). The IDENTICAL inline term reduces
    // (test_b125_bitvec_ofnat_computes b125_c5), and the `Fin` analogue
    // `def xf : Fin 5 := 3; xf.val = 3 := rfl` reduces (B122) — the difference is
    // a lazy-delta / recursor-major whnf limitation in the kernel reducer, not a
    // registration defect. Directly-`BitVec.ofNat` consts DO reduce through
    // `.toNat` (see below), isolating the gap to the extra OfNat-projection layer.
    //
    // This is the exact analogue of the USize sibling's documented honest gap
    // (register_usize_of_nat: `(USize.ofNat 42).toNat = 42 := rfl` does not
    // reduce). It is a LOUD completeness gap: the rfl is REJECTED, never a
    // silently-accepted wrong value. This test pins the current behaviour so a
    // future reducer improvement that closes it is caught and the story updated.
    let gap = "def x : BitVec 8 := 5\ntheorem t : x.toNat = 5 := rfl";
    assert!(
        elab_file_prelude(gap).1.iter().any(|r| r.is_err()),
        "const-indirection BitVec-literal .toNat rfl is a known LOUD whnf gap (rejected, not silent)",
    );
    // But the direct-`BitVec.ofNat` const DOES reduce through `.toNat`, proving
    // the value machinery is sound and the gap is purely the OfNat-projection
    // layer under the const.
    let direct = "def bx : BitVec 8 := BitVec.ofNat 8 5\ntheorem t : bx.toNat = 5 := rfl";
    assert_all_ok(
        &elab_file_prelude(direct).1,
        "direct BitVec.ofNat const reduces through .toNat",
    );
}

#[test]
fn test_omega_nat_sub_eq_zero_of_le() {
    // omega Nat truncated-subtraction lane (omega_tactic/nat_sub.rs): the
    // everyday truncation fact `a - b = 0` when a hypothesis states `a ≤ b`.
    // Nat subtraction is truncated, which the linear (Fourier-Motzkin) relaxation
    // cannot express without a case-split, so this family always fell through to
    // the failing linarith delegate. The proof is the proven prelude lemma
    // `Nat.ulpRound.sub_eq_zero_of_le a b h`, re-checked by close_goal.
    let code = "\
theorem s1 (a b : Nat) (h : a ≤ b) : a - b = 0 := by omega\n\
theorem s2 (a : Nat) (h : a ≤ a) : a - a = 0 := by omega\n\
theorem s3 (n : Nat) (h : n ≤ 5) : n - 5 = 0 := by omega\n\
theorem s4 (a : Nat) : a - a = 0 := by omega\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "omega proves a - b = 0 from a ≤ b (Nat truncation)",
    );
}

#[test]
fn test_omega_nat_sub_eq_zero_soundness() {
    // SOUNDNESS: the lane fires only when a hypothesis genuinely bounds
    // `a ≤ b`; every shape below is FALSE (or unprovable) and MUST be rejected —
    // the closed proof term is re-checked by close_goal, so a wrong match cannot
    // slip through. Covers: no bounding hypothesis, the wrong-direction bound
    // `b ≤ a` (from which `a - b = 0` does NOT follow), and a false target value.
    for code in [
        "theorem bad (a b : Nat) : a - b = 0 := by omega",
        "theorem bad (a b : Nat) (h : b ≤ a) : a - b = 0 := by omega",
        "theorem bad (a b : Nat) (h : a ≤ b) : a - b = 1 := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "unsound Nat-sub goal must be rejected: {code}",
        );
    }
}

#[test]
fn test_r137_array_literal_as_argument_parses() {
    // R137: `#[...]` array literals now parse as application ARGUMENTS
    // (clean-parser grammar/expr_app.rs atom_expr_can_start_at). Before this fix
    // the app-argument loop stopped at `#` (Hash was excluded from atom-start to
    // keep `#check`/`#eval` commands out of argument position), so `Array.size
    // #[1,2,3]` left `Array.size` un-applied and surfaced as a misleading
    // universe `Array {u} fvar → Nat` TypeMismatch. List literals `[..]` were
    // always accepted; this closes the array-literal parity gap. Covers size,
    // foldl, map, push, and the empty array in argument position.
    let code = "\
def s1 : Nat := Array.size #[1, 2, 3]\n\
def s2 : Nat := Array.foldl (· + ·) 0 #[1, 2, 3]\n\
def s3 : Array Nat := Array.map (· + 1) #[1, 2, 3]\n\
def s4 : Array Nat := Array.push #[1, 2] 3\n\
def s5 : Nat := Array.size (#[] : Array Nat)\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "#[..] array literals parse as application arguments",
    );
}

#[test]
fn test_r137_array_literal_as_argument_computes() {
    // The explicitly-applied Array functions kernel-COMPUTE once the `#[..]`
    // argument parses — proving the fix restores a genuine application spine, not
    // just a parse. Value-distinguishing (size=3, sum=6, not truncated/stuck).
    let code = "\
theorem c1 : Array.size #[1, 2, 3] = 3 := rfl\n\
theorem c2 : Array.foldl (· + ·) 0 #[1, 2, 3] = 6 := rfl\n\
theorem c3 : Array.size (#[] : Array Nat) = 0 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "explicitly-applied Array functions on #[..] kernel-compute",
    );
}

#[test]
fn test_r137_array_literal_as_argument_soundness() {
    // SOUNDNESS: the application genuinely computes, so a wrong result must be
    // rejected by the kernel — the fix restores real evaluation, not a stub.
    for code in [
        "theorem bad : Array.size #[1, 2, 3] = 4 := rfl",
        "theorem bad : Array.foldl (· + ·) 0 #[1, 2, 3] = 7 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong explicitly-applied Array value must be rejected: {code}",
        );
    }
}
#[test]
fn test_omega_nat_sub_eq_zero_of_lt() {
    // R138: extends the omega Nat truncated-subtraction lane
    // (omega_tactic/nat_sub.rs) to a strict `a < b` hypothesis — weakened to the
    // `a ≤ b` the truncation lemma needs via the proven, axiom-clean
    // `Nat.le_of_lt`. Same fail-closed + close_goal backstop as the `≤` case.
    let code = "\
theorem l1 (a b : Nat) (h : a < b) : a - b = 0 := by omega\n\
theorem l2 (a : Nat) (h : a < a + 1) : a - (a + 1) = 0 := by omega\n\
theorem l3 (n : Nat) (h : n < 5) : n - 5 = 0 := by omega\n\
theorem l4 (h : (0 : Nat) < 1) : (0 : Nat) - 1 = 0 := by omega\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "omega proves a - b = 0 from a < b (Nat truncation, weakened via Nat.le_of_lt)",
    );
}

#[test]
fn test_omega_nat_sub_eq_zero_of_lt_soundness() {
    // SOUNDNESS: a strict bound in the WRONG direction (`b < a`) does NOT prove
    // `a - b = 0`, and a false target must be rejected — close_goal is the
    // backstop, so a spurious `<`-match cannot slip through.
    for code in [
        "theorem bad (a b : Nat) (h : b < a) : a - b = 0 := by omega",
        "theorem bad (a b : Nat) (h : a < b) : a - b = 1 := by omega",
        "theorem bad : (1 : Nat) - 0 = 0 := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "unsound Nat-sub `<` goal must be rejected: {code}",
        );
    }
}

#[test]
fn test_omega_nat_sub_add_cancel() {
    // R139: dual truncation lane (omega_tactic/nat_sub.rs try_nat_sub_add_cancel)
    // — `a - b + b = a` from a hypothesis `b ≤ a` (or `b < a`), via the proven
    // axiom-clean `Nat.ulpRound.sub_add_cancel`, close_goal-rechecked, fail-closed.
    let code = "\
theorem s1 (a b : Nat) (h : b ≤ a) : a - b + b = a := by omega\n\
theorem s2 (a b : Nat) (h : b < a) : a - b + b = a := by omega\n\
theorem s3 (a : Nat) (h : 3 ≤ a) : a - 3 + 3 = a := by omega\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "omega proves a - b + b = a from b ≤ a (Nat truncation dual)",
    );
}

#[test]
fn test_omega_nat_sub_add_cancel_soundness() {
    // SOUNDNESS: `a - b + b = a` needs `b ≤ a`; without it (or with the wrong
    // direction `a ≤ b`, which gives `a - b = 0` so the sum is `b ≠ a`), and for
    // a false target, the goal must be rejected — close_goal is the backstop.
    for code in [
        "theorem bad (a b : Nat) : a - b + b = a := by omega",
        "theorem bad (a b : Nat) (h : a ≤ b) : a - b + b = a := by omega",
        "theorem bad (a b : Nat) (h : b ≤ a) : a - b + b = a + 1 := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "unsound Nat sub-add-cancel goal must be rejected: {code}",
        );
    }
}

#[test]
fn test_r140_array_getelem_index() {
    // R140: the `GetElem (Array α) Nat α` instance
    // (Array.instGetElemNatLtSize, clean-kernel data_getelem_list.rs) — it was
    // MISSING, so `arr[i]` had no instance: `valid` stayed a metavariable, the
    // bounds goal was never ground, and the unsolved index proof surfaced at
    // add_decl as "contains free variables". Now `arr[i]` elaborates end-to-end
    // (bounds discharged by the get_elem_tactic analog) and kernel-COMPUTES.
    let code = "\
def a1 : Nat := #[10, 20, 30][1]\n\
def a2 : Nat := #[10, 20, 30][0]'(by decide)\n\
def f (as : Array Nat) (h : 0 < as.size) : Nat := as[0]\n\
theorem c1 : #[10, 20, 30][1] = 20 := rfl\n\
theorem c2 : #[10, 20, 30][0] = 10 := rfl\n\
theorem c3 : #[10, 20, 30][2] = 30 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "Array xs[i] elaborates + kernel-computes via the GetElem instance",
    );
}

#[test]
fn test_r140_array_getelem_soundness() {
    // SOUNDNESS: the bounds proof is real (get_elem_tactic analog + kernel
    // re-check), so an out-of-bounds index (no valid proof) and a wrong computed
    // value must both be rejected — never a silent out-of-bounds read.
    for code in [
        "def x : Nat := #[10, 20][5]",
        "theorem t : #[10, 20, 30][1] = 21 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "unsound Array index must be rejected: {code}",
        );
    }
}

#[test]
fn test_r141_array_getelem_opt() {
    // R141: the `GetElem? (Array α) Nat α` instance (Array.instGetElem?NatLtSize,
    // clean-kernel data_getelem_list.rs) — the R140 sibling, so `arr[i]!` and
    // `arr[i]?` resolve + kernel-compute on Arrays. getElem?/getElem! thread
    // through the List carrier via Array.data (List.get? eta-expanded).
    let code = "\
theorem b1 : #[10, 20, 30][1]! = 20 := rfl\n\
theorem b2 : #[10, 20, 30][0]! = 10 := rfl\n\
theorem o1 : #[10, 20, 30][1]? = some 20 := rfl\n\
theorem o2 : #[10, 20, 30][2]? = some 30 := rfl\n\
theorem oob_bang : #[10, 20][5]! = 0 := rfl\n\
theorem oob_opt : (#[10, 20][5]? : Option Nat) = none := rfl\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "Array arr[i]! and arr[i]? elaborate + kernel-compute via GetElem?",
    );
}

#[test]
fn test_r141_array_getelem_opt_soundness() {
    // SOUNDNESS: getElem!/getElem? genuinely compute (real value / some / none),
    // so wrong targets — a wrong bang value, a wrong some, and an out-of-bounds
    // getElem? claimed to be `some` — must all be rejected by the kernel.
    for code in [
        "theorem bad : #[10, 20, 30][1]! = 21 := rfl",
        "theorem bad : #[10, 20, 30][1]? = some 21 := rfl",
        "theorem bad : (#[10, 20][5]? : Option Nat) = some 0 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "unsound Array getElem?/getElem! goal must be rejected: {code}",
        );
    }
}

#[test]
fn test_r142_membership_elaborates() {
    // R142: the `Membership` instances (List.instMembership etc, clean-kernel
    // data_types_collections.rs / set_theory.rs / finset / multiset) were
    // registered as Definitions but never in the instance registry, so `a ∈ l`
    // failed instance synthesis (FailedToSynthesizeInstance "Membership Nat
    // (List Nat)"). Now `a ∈ l` elaborates as a Prop and membership hypotheses
    // are usable. (`by decide` on membership needs a separate Decidable-mem
    // instance — a documented follow-up.)
    let code = "\
def p : Prop := 2 ∈ [1, 2, 3]\n\
def q (a : Nat) (l : List Nat) : Prop := a ∈ l\n\
def r (a : Nat) (l : List Nat) : Prop := a ∉ l\n\
theorem use_hyp (a : Nat) (l : List Nat) (h : a ∈ l) : a ∈ l := h\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "a ∈ l elaborates as a Prop and membership hypotheses are usable",
    );
}

#[test]
fn test_r142_membership_soundness() {
    // SOUNDNESS: `∈` is a real proposition (Membership.mem over List.Mem), so a
    // proof of the wrong membership must be rejected — the instance being
    // registered must not let a mismatched proof through the kernel.
    for code in [
        // h proves a ∈ l, goal is b ∈ l — distinct proposition.
        "theorem bad (a b : Nat) (l : List Nat) (h : a ∈ l) : b ∈ l := h",
        // h proves a ∈ l, goal is a ∉ l — negation, distinct.
        "theorem bad (a : Nat) (l : List Nat) (h : a ∈ l) : a ∉ l := h",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong membership proof must be rejected: {code}",
        );
    }
}

#[test]
fn test_r143_array_forin_elaborates() {
    // R143: the pure mutating-`do` `for` lane (elab_do_mut.rs, B23/B93/B96)
    // hard-restricted the collection to `List α`, rejecting `for x in (arr :
    // Array α)` LOUD. Since `Array` wraps `List` (`Array.mk (data : List α)`)
    // and the lane lowers to an inlined `List.rec` fold over a `List α` *term*
    // (never a synthesized `ForIn` instance), iterating an array is exactly
    // iterating its backing list `Array.data α arr` — an elaborator-only fix,
    // no new kernel instance. Both a literal `#[..]` and a variable `Array`
    // now elaborate, and the literal loop COMPUTES to the correct value.
    let code = "\
def sumA : Id Nat := do\n  let mut s := 0\n  for x in #[1, 2, 3] do\n    s := s + x\n  return s\n\
def sumVar (l : Array Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in l do\n    s := s + x\n  return s\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`for x in (arr : Array α)` elaborates in the pure mutating-do lane",
    );

    // Value pin: the array loop reduces to the same total as the list loop.
    // `1 + 2 + 3 = 6`, checked by the kernel via `rfl` (the `Array.data`
    // projection reduces on the literal `Array.mk (cons-chain)`, so the
    // inlined `List.rec` fold computes end-to-end).
    let pin = "theorem t : (Id.run do\n  let mut s := 0\n  for x in #[1, 2, 3] do\n    s := s + x\n  return s) = 6 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(pin).1,
        "array `for` loop computes the correct total (= 6) by rfl",
    );
}

#[test]
fn test_r143_array_forin_soundness() {
    // SOUNDNESS (value-distinguishing): the array loop must compute the RIGHT
    // value — a `rfl` pin to the WRONG total must be rejected by the kernel,
    // and a body that does not type-check must be rejected. If the desugaring
    // silently dropped or mis-iterated elements the wrong-total pin would go
    // through; it must not.
    for code in [
        // The true total is 6; pinning to 7 must fail (kernel reduces the
        // fold to 6 and 6 = 7 is not `rfl`).
        "theorem bad : (Id.run do\n  let mut s := 0\n  for x in #[1, 2, 3] do\n    s := s + x\n  return s) = 7 := rfl",
        // Pinning to 5 (dropping the last element) must also fail.
        "theorem bad : (Id.run do\n  let mut s := 0\n  for x in #[1, 2, 3] do\n    s := s + x\n  return s) = 5 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong array-for total must be rejected: {code}",
        );
    }
}

#[test]
fn test_r144_string_forin_elaborates() {
    // R144: extends R143 — the pure mutating-`do` `for` lane (elab_do_mut.rs)
    // now also iterates `String`. `String` is a non-polymorphic structure
    // (`String.mk (data : List Char)`, projection `String.data s : List Char`,
    // element `Char`), so — exactly as `Array` — `for c in s` feeds the backing
    // list `String.data s` to the same inlined `List.rec` fold. Its collection
    // type is a bare `Const("String")`, not an `App`. Both a variable `String`
    // and a literal `"abc"` now elaborate, and the literal loop COMPUTES
    // (the `String.data` projection reduces on the string literal).
    let code = "\
def cnt (s : String) : Nat := Id.run do\n  let mut n := 0\n  for c in s do\n    n := n + 1\n  return n\n\
def cntabc : Nat := Id.run do\n  let mut n := 0\n  for c in \"abc\" do\n    n := n + 1\n  return n\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`for c in (s : String)` elaborates in the pure mutating-do lane",
    );

    // Value pin: iterating `"abc"` and counting reaches 3, checked by the
    // kernel via `rfl` (the `String.data` projection reduces on the literal,
    // so the inlined `List.rec` fold computes end-to-end).
    let pin = "theorem t : (Id.run do\n  let mut n := 0\n  for c in \"abc\" do\n    n := n + 1\n  return n) = 3 := rfl\n";
    assert_all_ok(
        &elab_file_prelude(pin).1,
        "string `for` loop computes the correct char count (= 3) by rfl",
    );
}

#[test]
fn test_r144_string_forin_soundness() {
    // SOUNDNESS (value-distinguishing): the string loop must compute the RIGHT
    // count — a `rfl` pin to the WRONG char count must be rejected. `"abc"` has
    // 3 characters; pinning to 4 (or 2) must fail (the kernel reduces the fold
    // to 3). If the desugaring dropped or duplicated a char the wrong-count pin
    // would slip through; it must not.
    for code in [
        "theorem bad : (Id.run do\n  let mut n := 0\n  for c in \"abc\" do\n    n := n + 1\n  return n) = 4 := rfl",
        "theorem bad : (Id.run do\n  let mut n := 0\n  for c in \"abc\" do\n    n := n + 1\n  return n) = 2 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong string-for char count must be rejected: {code}",
        );
    }
}

#[test]
fn test_r145_array_tolist_elaborates() {
    // R145: `Array.toList : {α} → Array α → List α` — the modern Lean 4
    // accessor for an array's backing list (an alias for `Array.data`, which
    // upstream renamed to `toList`). It was unregistered, so dot-notation
    // `a.toList` failed LOUD with `UnknownProjectionField` (Array's only field
    // is `data`, and the namespace-function fallback — the same path that
    // resolves `a.size`/`a.push` — found nothing). Registered in the kernel
    // prelude (data.rs::init_array) as `fun {α} a => Array.data α a`, reducible
    // and axiom-free. Now both `a.toList` and `Array.toList a` elaborate, and a
    // literal reduces through the `Array.data` projection.
    let code = "\
def f (a : Array Nat) : List Nat := a.toList\n\
def g (a : Array Nat) : List Nat := Array.toList a\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`a.toList` and `Array.toList a` elaborate for a variable Array",
    );

    // Value pins: a literal array's toList reduces to the backing list, checked
    // by the kernel via `rfl`. The empty array yields `[]`; the toList also
    // composes with the R143 array `for` loop (both reduce to the same list).
    for pin in [
        "theorem t : (#[1, 2, 3] : Array Nat).toList = [1, 2, 3] := rfl\n",
        "theorem t : (#[] : Array Nat).toList = [] := rfl\n",
        "theorem t : (Id.run do\n  let mut s := 0\n  for x in (#[1, 2, 3] : Array Nat).toList do\n    s := s + x\n  return s) = 6 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Array.toList reduces to the backing list and computes by rfl",
        );
    }
}

#[test]
fn test_r145_array_tolist_soundness() {
    // SOUNDNESS (value-distinguishing): `Array.toList` must reduce to the RIGHT
    // list — a `rfl` pin to a WRONG list must be rejected by the kernel. If the
    // alias were mis-wired (e.g. dropped or reordered elements) a wrong-list pin
    // would slip through; it must not.
    for code in [
        // #[1,2,3].toList is [1,2,3]; pinning to a truncation or extension fails.
        "theorem bad : (#[1, 2, 3] : Array Nat).toList = [1, 2] := rfl",
        "theorem bad : (#[1, 2, 3] : Array Nat).toList = [1, 2, 3, 4] := rfl",
        "theorem bad : (#[1, 2, 3] : Array Nat).toList = [3, 2, 1] := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Array.toList result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r146_conversion_accessors_elaborate() {
    // R146: two more missing conversion accessors (the R145 Array.toList class).
    // `String.toList : String → List Char := fun s => String.data s` (alias of
    // the String.data projection) — `s.toList` had failed with
    // UnknownProjectionField. `List.toArray : {α} → List α → Array α :=
    // fun {α} l => Array.mk α l` (wraps a list in the Array constructor) —
    // `l.toArray` had failed with UnknownIdent. Both reducible + axiom-free,
    // registered in the kernel prelude. Now they elaborate and literals reduce.
    let code = "\
def f (s : String) : List Char := s.toList\n\
def g (l : List Nat) : Array Nat := l.toArray\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`s.toList` and `l.toArray` elaborate for variable String/List",
    );

    // Value pins: literals reduce through String.data / Array.mk, so lengths
    // compute by rfl; and the conversions round-trip
    // (`l.toArray.toList = l`, both reducing through their projections).
    for pin in [
        "theorem t : \"abc\".toList.length = 3 := rfl\n",
        "theorem t : [1, 2, 3].toArray.size = 3 := rfl\n",
        "theorem t : [1, 2, 3].toArray.toList = [1, 2, 3] := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "String.toList / List.toArray reduce and compute by rfl",
        );
    }
}

#[test]
fn test_r146_conversion_accessors_soundness() {
    // SOUNDNESS (value-distinguishing): the aliases must reduce to the RIGHT
    // values — a `rfl` pin to a WRONG length/element must be rejected. "abc"
    // has 3 chars; [1,2,3].toArray has size 3; a mis-wired alias would let a
    // wrong pin through — it must not.
    for code in [
        "theorem bad : \"abc\".toList.length = 4 := rfl",
        "theorem bad : [1, 2, 3].toArray.size = 4 := rfl",
        "theorem bad : [1, 2, 3].toArray.toList = [1, 2] := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong conversion-accessor result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r147_array_back_elaborates() {
    // R147: `Array.back : {α} → [Inhabited α] → Array α → α` — the last element
    // of an array (the Inhabited default on empty). Registered in the kernel
    // prelude as `Array.get! a (Array.size a - 1)` over the already-registered
    // Array.get! / Array.size (a thin reducible wrapper, zero axioms). Without
    // it, `a.back` failed LOUD with UnknownIdent (dot notation's
    // namespace-function fallback — the path that resolves a.size/a.toList —
    // had no Array.back). Now `a.back` and `Array.back a` elaborate, and on a
    // literal array the whole chain reduces (size → n, Nat.sub n 1, get! (n-1)).
    let code = "\
def f (a : Array Nat) : Nat := a.back\n\
def g (a : Array Nat) : Nat := Array.back a\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`a.back` and `Array.back a` elaborate for a variable Array",
    );

    // Value pins: the last element of a literal array computes by rfl.
    for pin in [
        "theorem t : #[1, 2, 3].back = 3 := rfl\n",
        "theorem t : #[5].back = 5 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Array.back of a literal reduces to the last element by rfl",
        );
    }
}

#[test]
fn test_r147_array_back_soundness() {
    // SOUNDNESS (value-distinguishing): `Array.back` must reduce to the LAST
    // element — a `rfl` pin to a non-last element must be rejected. #[1,2,3].back
    // is 3; pinning to 2 (the second element) or 1 (the first) must fail, or a
    // mis-wired index (e.g. size instead of size-1) would slip through.
    for code in [
        "theorem bad : #[1, 2, 3].back = 2 := rfl",
        "theorem bad : #[1, 2, 3].back = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Array.back result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r148_array_mkempty_elaborates() {
    // R148: Lean 4's `Array.mkEmpty (capacity : Nat) : Array α` builds an empty
    // array — the capacity is only a runtime preallocation hint, so the logical
    // value is `#[]` for any capacity. Registered in the kernel prelude as a
    // reducible axiom-free wrapper `fun _c => Array.mk List.nil` (ignores the
    // Nat). Without it `Array.mkEmpty n` failed LOUD with UnknownIdent.
    // (Probed this round: omega already handles Nat-sub / case-splits / mul-by-
    // const soundly; its real remaining gap is `%`/`/`, which is a separate
    // medium effort — see the ROUND 148 backlog note.)
    let code = "\
def f : Array Nat := Array.mkEmpty 8\n\
def g (n : Nat) : Array Nat := Array.mkEmpty n\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`Array.mkEmpty n` elaborates for a literal and variable capacity",
    );

    // Value pins: the result is empty regardless of the capacity argument.
    for pin in [
        "theorem t : (Array.mkEmpty 8 : Array Nat).size = 0 := rfl\n",
        "theorem t : (Array.mkEmpty 0 : Array Nat).toList = [] := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Array.mkEmpty is empty (size 0 / toList []) by rfl",
        );
    }
}

#[test]
fn test_r148_array_mkempty_soundness() {
    // SOUNDNESS (value-distinguishing): Array.mkEmpty must be EMPTY — a `rfl`
    // pin claiming a nonzero size (or a non-empty backing list) must be
    // rejected. If the wrapper mis-used its capacity argument as a length, the
    // wrong-size pin would slip through; it must not.
    for code in [
        "theorem bad : (Array.mkEmpty 8 : Array Nat).size = 8 := rfl",
        "theorem bad : (Array.mkEmpty 1 : Array Nat).size = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "Array.mkEmpty must be empty; wrong-size pin must be rejected: {code}",
        );
    }
}

#[test]
fn test_r149_list_headd_elaborates() {
    // R149: `List.headD : {α} → List α → α → α` — the head of a list, or the
    // default on the empty list. Registered in the kernel prelude as a simple
    // `List.rec` fold (motive `fun _ => α`: nil ↦ default, cons hd _ _ ↦ hd),
    // reducible + axiom-free. Without it, `l.headD d` failed LOUD with
    // UnknownIdent (dot notation's namespace-function fallback had no
    // List.headD). (Probed this round: List range/append/map/filter/foldl/
    // reverse/++, Option.getD, Nat pow, Int-cast all already work; the fresh
    // gaps were List.headD [landed here] and List.getLast! [follow-up].)
    let code = "\
def f (l : List Nat) : Nat := l.headD 0\n\
def g (l : List Nat) : Nat := List.headD l 0\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.headD d` and `List.headD l d` elaborate for a variable list",
    );

    // Value pins: cons picks the head, nil picks the default — both compute.
    for pin in [
        "theorem t : [1, 2, 3].headD 0 = 1 := rfl\n",
        "theorem t : ([] : List Nat).headD 7 = 7 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.headD reduces (cons → head, nil → default) by rfl",
        );
    }
}

#[test]
fn test_r149_list_headd_soundness() {
    // SOUNDNESS (value-distinguishing, both recursor cases): `headD` must return
    // the head on a cons and the default on nil — a `rfl` pin to the wrong value
    // in either case must be rejected. If the fold picked the wrong element (or
    // swapped the nil/cons cases) a wrong pin would slip through; it must not.
    for code in [
        "theorem bad : [1, 2, 3].headD 0 = 2 := rfl",
        "theorem bad : ([] : List Nat).headD 7 = 0 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.headD result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r150_list_head_opt_elaborates() {
    // R150: `List.head? : {α} → List α → Option α` — the head of a list as an
    // Option (none on the empty list). Registered in the kernel prelude as a
    // simple `List.rec` fold (motive `fun _ => Option α`: nil ↦ Option.none,
    // cons hd _ _ ↦ Option.some hd), reducible + axiom-free (no native reducer
    // to coexist with, unlike List.getLast!). Without it, `l.head?` failed LOUD
    // with UnknownIdent. (Probed this round: List getLast!/take/drop/sum/head!/
    // getLastD are also absent — take/drop need recursion, getLast! collides
    // with a native reducer; head? is the cleanest — follow-ups noted.)
    let code = "\
def f (l : List Nat) : Option Nat := l.head?\n\
def g (l : List Nat) : Option Nat := List.head? l\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.head?` and `List.head? l` elaborate for a variable list",
    );

    // Value pins: cons → some head, nil → none — both compute.
    for pin in [
        "theorem t : [1, 2, 3].head? = some 1 := rfl\n",
        "theorem t : ([] : List Nat).head? = none := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.head? reduces (cons → some head, nil → none) by rfl",
        );
    }
}

#[test]
fn test_r150_list_head_opt_soundness() {
    // SOUNDNESS (value-distinguishing, both recursor cases): `head?` must give
    // `some head` on a cons and `none` on nil — a `rfl` pin to the wrong Option
    // in either case must be rejected. If the fold picked the wrong element or
    // swapped the nil/cons cases (e.g. `some` on nil) a wrong pin would slip
    // through; it must not.
    for code in [
        "theorem bad : [1, 2, 3].head? = some 2 := rfl",
        "theorem bad : ([] : List Nat).head? = some 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.head? result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r151_list_getlastd_elaborates() {
    // R151: `List.getLastD : {α} → List α → α → α` — the last element of a list,
    // or the default on the empty list. Registered in the kernel prelude as a
    // COMPOSITION of the already-registered List.headD (R149) and List.reverse:
    // `List.getLastD l d := List.headD (List.reverse l) d`. Reducible +
    // axiom-free, no Inhabited, no native reducer (unlike List.getLast!, which
    // is why this is the clean sibling). Without it, `l.getLastD d` failed LOUD
    // with UnknownIdent. The reverse∘headD chain reduces end-to-end on literals.
    let code = "\
def f (l : List Nat) : Nat := l.getLastD 0\n\
def g (l : List Nat) : Nat := List.getLastD l 0\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.getLastD d` and `List.getLastD l d` elaborate for a variable list",
    );

    // Value pins: cons picks the last element, nil picks the default — both
    // compute through the List.reverse then List.headD reduction chain.
    for pin in [
        "theorem t : [1, 2, 3].getLastD 0 = 3 := rfl\n",
        "theorem t : [5].getLastD 0 = 5 := rfl\n",
        "theorem t : ([] : List Nat).getLastD 7 = 7 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.getLastD reduces (cons → last, nil → default) by rfl",
        );
    }
}

#[test]
fn test_r151_list_getlastd_soundness() {
    // SOUNDNESS (value-distinguishing, both cases): `getLastD` must give the
    // LAST element on a cons and the default on nil — a `rfl` pin to the wrong
    // value in either case must be rejected. #[1,2,3].getLastD is 3 (not 2, the
    // second element, nor a reverse/head mixup); [].getLastD 7 is 7. A mis-wired
    // reverse∘headD composition would let a wrong pin through; it must not.
    for code in [
        "theorem bad : [1, 2, 3].getLastD 0 = 2 := rfl",
        "theorem bad : [1, 2, 3].getLastD 0 = 1 := rfl",
        "theorem bad : ([] : List Nat).getLastD 7 = 0 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.getLastD result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r152_list_getlast_opt_elaborates() {
    // R152: `List.getLast? : {α} → List α → Option α` — the last element of a
    // list as an Option (none on empty). The Option-valued sibling of R151
    // List.getLastD, composed from the already-registered List.head? (R150) and
    // List.reverse: `List.getLast? l := List.head? (List.reverse l)`. Reducible
    // + axiom-free, no Inhabited, no native reducer. Without it, `l.getLast?`
    // failed LOUD with UnknownIdent. The reverse∘head? chain reduces end-to-end.
    let code = "\
def f (l : List Nat) : Option Nat := l.getLast?\n\
def g (l : List Nat) : Option Nat := List.getLast? l\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.getLast?` and `List.getLast? l` elaborate for a variable list",
    );

    // Value pins: cons → some last, nil → none — both compute through the
    // List.reverse then List.head? reduction chain.
    for pin in [
        "theorem t : [1, 2, 3].getLast? = some 3 := rfl\n",
        "theorem t : [5].getLast? = some 5 := rfl\n",
        "theorem t : ([] : List Nat).getLast? = none := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.getLast? reduces (cons → some last, nil → none) by rfl",
        );
    }
}

#[test]
fn test_r152_list_getlast_opt_soundness() {
    // SOUNDNESS (value-distinguishing, both cases): `getLast?` must give
    // `some last` on a cons and `none` on nil — a `rfl` pin to the wrong Option
    // in either case must be rejected. #[1,2,3].getLast? is some 3 (not some 2,
    // the second element, nor a reverse/head mixup); [].getLast? is none. A
    // mis-wired reverse∘head? composition would let a wrong pin through.
    for code in [
        "theorem bad : [1, 2, 3].getLast? = some 2 := rfl",
        "theorem bad : [1, 2, 3].getLast? = some 1 := rfl",
        "theorem bad : ([] : List Nat).getLast? = some 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.getLast? result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r153_list_head_bang_elaborates() {
    // R153: `List.head! : {α} → [Inhabited α] → List α → α` — the head of a list,
    // or the Inhabited default on the empty list. Registered in the kernel
    // prelude via the already-registered List.headD: `List.head! l := List.headD
    // l (Inhabited.default)` (Inhabited / Inhabited.default at Level::succ u, an
    // InstImplicit binder — the Array.back-style Inhabited threading). Reducible
    // + axiom-free, no native reducer. Without it, `l.head!` failed LOUD with
    // UnknownIdent. Both List.rec cases reduce (cons → head, nil → default).
    let code = "\
def f (l : List Nat) : Nat := l.head!\n\
def g (l : List Nat) : Nat := List.head! l\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.head!` and `List.head! l` elaborate for a variable list",
    );

    // Value pins: cons picks the head; the empty list reduces to the Inhabited
    // default (0 for Nat, via instInhabitedNat) — both compute by rfl.
    for pin in [
        "theorem t : [1, 2, 3].head! = 1 := rfl\n",
        "theorem t : [5].head! = 5 := rfl\n",
        "theorem t : ([] : List Nat).head! = 0 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.head! reduces (cons → head, nil → Inhabited.default) by rfl",
        );
    }
}

#[test]
fn test_r153_list_head_bang_soundness() {
    // SOUNDNESS (value-distinguishing): `head!` must return the actual head on a
    // cons and the Inhabited default on nil — a `rfl` pin to the wrong value in
    // either case must be rejected. [1,2,3].head! is 1 (not 2); [].head! is 0
    // (the Nat default, not 1). A mis-threaded Inhabited or wrong-element fold
    // would let a wrong pin through; it must not.
    for code in [
        "theorem bad : [1, 2, 3].head! = 2 := rfl",
        "theorem bad : ([] : List Nat).head! = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.head! result must be rejected: {code}",
        );
    }
}

#[test]
fn test_r154_function_comp_elaborates() {
    // R154: `Function.comp : {α : Sort u} → {β : Sort v} → {δ : Sort w} →
    // (β → δ) → (α → β) → α → δ := fun f g x => f (g x)` — core function
    // composition, registered as a reducible axiom-free kernel-prelude Def
    // mirroring Lean core. Clean desugars the `∘` notation and the partially
    // applied `(f ∘ g) x` forms at the surface, but the fully named, fully
    // applied `Function.comp f g x` (and a bare `Function.comp` by name) fell
    // through to UnknownIdent. Now every arity resolves through ordinary
    // application + kernel reduction.
    let code = "\
def c1 (f : Nat → Nat) (g : Nat → Nat) : Nat → Nat := Function.comp f g\n\
def c2 : Nat := Function.comp Nat.succ Nat.succ 0\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`Function.comp f g` and `Function.comp f g x` elaborate",
    );

    // Value pins: comp f g x = f (g x); order matters. The `∘` notation stays
    // defeq to the named form. All reduce by rfl.
    for pin in [
        "theorem t : Function.comp Nat.succ Nat.succ 0 = 2 := rfl\n",
        "theorem t : (Function.comp Nat.succ Nat.succ) 5 = 7 := rfl\n",
        "theorem t : Function.comp (fun n => n + 1) (fun n => n * 2) 3 = 7 := rfl\n",
        "theorem t : (Nat.succ ∘ Nat.succ) 0 = 2 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Function.comp reduces (f (g x)) by rfl; ∘ stays defeq",
        );
    }
}

#[test]
fn test_r154_function_comp_soundness() {
    // SOUNDNESS (value-distinguishing): comp must compute f (g x), in that
    // order. `Function.comp Nat.succ Nat.succ 0` is 2 (not 3, not 1); and the
    // composition order is f-after-g — `comp (·+1) (·*2) 3` is (3*2)+1 = 7, NOT
    // the swapped-order (3+1)*2 = 8. A wrong reduction or a flipped f/g order
    // must be rejected by the kernel.
    for code in [
        "theorem bad : Function.comp Nat.succ Nat.succ 0 = 3 := rfl",
        "theorem bad : Function.comp Nat.succ Nat.succ 0 = 1 := rfl",
        "theorem bad : Function.comp (fun n => n + 1) (fun n => n * 2) 3 = 8 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Function.comp result / order must be rejected: {code}",
        );
    }
}

#[test]
fn test_r155_flip_elaborates() {
    // R155: `flip : {α : Sort u} → {β : Sort v} → {γ : Sort w} →
    // (α → β → γ) → β → α → γ := fun f b a => f a b` — the core argument-flip
    // combinator, registered as a reducible axiom-free kernel-prelude Def
    // mirroring Function.comp / Lean core. Clean desugars only the partial
    // `flip g` form at the surface; the fully named, fully applied
    // `flip f b a` (and a bare `flip` by name) fell through to UnknownIdent.
    // Now every arity resolves through ordinary application + kernel reduction.
    let code = "\
def h (f : Nat → Nat → Nat) : Nat → Nat → Nat := flip f\n\
def k : Nat := flip Nat.sub 1 5\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`flip f` and `flip Nat.sub 1 5` elaborate",
    );

    // Value pins: flip f b a = f a b, so `flip Nat.sub 1 5 = Nat.sub 5 1 = 4`.
    // A user lambda flips the same way. Both reduce by rfl.
    for pin in [
        "theorem t : flip Nat.sub 1 5 = 4 := rfl\n",
        "theorem t : flip (fun a b => a - b) 1 5 = 4 := rfl\n",
    ] {
        assert_all_ok(&elab_file_prelude(pin).1, "flip reduces (f a b) by rfl");
    }
}

#[test]
fn test_r155_flip_soundness() {
    // SOUNDNESS (value-distinguishing / order): flip must swap the two
    // arguments — `flip Nat.sub 1 5` is `Nat.sub 5 1 = 4`, NOT the un-flipped
    // `Nat.sub 1 5 = 0` (which would slip through a no-op / identity mistake),
    // and not any other value. The 0 pin is the crucial one: it catches a flip
    // that failed to actually flip.
    for code in [
        "theorem bad : flip Nat.sub 1 5 = 0 := rfl",
        "theorem bad : flip Nat.sub 1 5 = 6 := rfl",
        "theorem bad : flip Nat.sub 1 5 = 2 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong flip result / order must be rejected: {code}",
        );
    }
}

#[test]
fn test_r156_function_const_elaborates() {
    // R156: `Function.const : {α : Sort u} → (β : Sort v) → α → β → α :=
    // fun {α} β a => fun _ => a` — the core constant function (β explicit, the
    // domain of the ignored argument), registered as a reducible axiom-free
    // kernel-prelude Def mirroring Function.comp / flip / Lean core. Clean
    // desugars only the one/two-argument forms at the surface; the fully named,
    // fully applied `Function.const β a x` (and a bare `Function.const` by name)
    // fell through to UnknownIdent. Now every arity resolves through ordinary
    // application + kernel reduction.
    let code = "\
def c (a : Nat) : Bool → Nat := Function.const Bool a\n\
def d : Nat := Function.const Bool 5 true\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`Function.const Bool a` and `Function.const Bool 5 true` elaborate",
    );

    // Value pins: `Function.const β a x = a` (the trailing β-typed argument is
    // ignored). The parenthesised applied form stays defeq. All reduce by rfl.
    for pin in [
        "theorem t : Function.const Bool 5 true = 5 := rfl\n",
        "theorem t : Function.const Nat 7 0 = 7 := rfl\n",
        "theorem t : (Function.const Bool 5) true = 5 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Function.const reduces (ignores its last arg, returns a) by rfl",
        );
    }
}

#[test]
fn test_r156_function_const_soundness() {
    // SOUNDNESS (value-distinguishing): `Function.const β a x` must return `a`,
    // never the ignored argument `x`. `Function.const Nat 7 9` is 7 (not 9), and
    // `Function.const Bool 5 true` is 5 (not 6). A const that returned its last
    // argument, or the wrong value, must be rejected by the kernel.
    for code in [
        "theorem bad : Function.const Bool 5 true = 6 := rfl",
        "theorem bad : Function.const Nat 7 9 = 9 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Function.const result (returning the ignored arg) must be rejected: {code}",
        );
    }
}
#[test]
fn test_r158_nat_mod_div_literal_reduces() {
    // R158: real elaborated Nat `%` / `/` goals carry the homogeneous instances
    // `instHModNat` / `instHDivNat` (which wrap `Nat.mod` / `Nat.div`), but the
    // native HMod/HDiv reducers only recognized the olean triple-Nat instances,
    // so `HMod.hMod .. instHModNat 7 3` stalled in whnf and neither `rfl` nor
    // `omega` could close `7 % 3 = 1`. The reducers now also delegate the
    // homogeneous instances to `Nat.mod` / `Nat.div` (faithful def-unfolding,
    // mirroring the existing `instHAddNat` arm). Literal `%` / `/` now reduce.
    for pin in [
        "theorem t : (7 : Nat) % 3 = 1 := rfl\n",
        "theorem t : (10 : Nat) % 4 = 2 := rfl\n",
        "theorem t : (6 : Nat) % 3 = 0 := rfl\n",
        "theorem t : (10 : Nat) / 3 = 3 := rfl\n",
        "theorem t : (9 : Nat) / 3 = 3 := rfl\n",
        "theorem t : (5 : Nat) / 1 = 5 := rfl\n",
        // omega closes them too (its opening reduce_eq now sees through %/÷).
        "theorem t : (7 : Nat) % 3 = 1 := by omega\n",
        "theorem t : (10 : Nat) / 3 = 3 := by omega\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "literal Nat %/÷ reduces (via instHModNat/instHDivNat → Nat.mod/Nat.div)",
        );
    }
}

#[test]
fn test_r158_nat_mod_div_soundness() {
    // SOUNDNESS (value-distinguishing, and CRITICAL because the native reducer
    // is trusted / not re-checked): the reducer must compute the TRUE Nat
    // mod/div value — 7 % 3 is 1 (not 2, not 0), 10 / 3 is 3 (not 4). A wrong
    // `rfl` pin in either direction must be rejected by the kernel, proving the
    // native reduction agrees with the structural Nat.mod/Nat.div semantics.
    for code in [
        "theorem bad : (7 : Nat) % 3 = 2 := rfl",
        "theorem bad : (7 : Nat) % 3 = 0 := rfl",
        "theorem bad : (10 : Nat) / 3 = 4 := rfl",
        "theorem bad : (10 : Nat) / 3 = 2 := rfl",
        // omega must also reject the false div/mod goals (fail-closed).
        "theorem bad : (7 : Nat) % 3 = 2 := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Nat %/÷ value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r159_omega_mod_lt() {
    // R159: omega now proves the modulo bound `a % k < k` when `0 < k` is in
    // context, via a new nat_div_mod lane emitting the proven Nat.mod_lt lemma
    // (re-checked by close_goal). Previously the mod atom was dropped by the
    // linear relaxation and the goal fell through to the failing linarith
    // delegate. Symbolic and literal-with-hypothesis divisors both work.
    for pin in [
        "theorem t (n k : Nat) (h : 0 < k) : n % k < k := by omega\n",
        "theorem t (a b : Nat) (hb : 0 < b) : a % b < b := by omega\n",
        "theorem t (n : Nat) (h : 0 < 3) : n % 3 < 3 := by omega\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "omega proves a % k < k from a 0 < k hypothesis",
        );
    }
}

#[test]
fn test_r159_omega_mod_lt_soundness() {
    // SOUNDNESS (fail-closed): the lane must fire ONLY on the real bound with a
    // genuine 0 < k. Without the hypothesis, `n % k < k` is FALSE (k = 0 gives
    // 0 % 0 = 0, not < 0) and omega must reject it. And a wrong-shape goal
    // (`n % k = 0`) must not be closed by this lane. Every reconstruction is
    // kernel-re-checked, so a spurious match fails closed.
    for code in [
        "theorem bad (n k : Nat) : n % k < k := by omega",
        "theorem bad (n k : Nat) (h : 0 < k) : n % k = 0 := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "omega must reject the unsound / wrong-shape mod goal: {code}",
        );
    }
}

#[test]
fn test_r160_omega_div_add_mod() {
    // R160: omega now proves the Euclidean division identity
    // (a / k) * k + a % k = a, via a new nat_div_mod lane emitting the proven
    // Nat.div_add_mod lemma (re-checked by close_goal, no side condition).
    // Previously the div/mod atoms were dropped by the linear relaxation and the
    // goal fell through to the failing linarith delegate.
    for pin in [
        "theorem t (a k : Nat) : (a / k) * k + a % k = a := by omega\n",
        "theorem t (m n : Nat) : (m / n) * n + m % n = m := by omega\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "omega proves the Euclidean division identity via Nat.div_add_mod",
        );
    }
}

#[test]
fn test_r160_omega_div_add_mod_soundness() {
    // SOUNDNESS (fail-closed): the lane must emit Nat.div_add_mod ONLY for the
    // true identity. A wrong RHS (`= a + 1`) or a wrong RHS entirely (`= k`) is
    // FALSE and must be rejected — close_goal re-checks the reconstructed term,
    // so a spurious match cannot slip through.
    for code in [
        "theorem bad (a k : Nat) : (a / k) * k + a % k = a + 1 := by omega",
        "theorem bad (a k : Nat) : (a / k) * k + a % k = k := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "omega must reject the false div/mod identity: {code}",
        );
    }
}

#[test]
fn test_r161_omega_mod_lt_literal() {
    // R161: omega now proves n % k < k for a positive LITERAL divisor with no
    // hypothesis — the mod-bound lane synthesizes the 0 < k side proof as
    // Nat.zero_lt_succ (k-1) (def-eq to 0 < k), feeding Nat.mod_lt. This closes
    // the common n % 3 < 3 that R159 (hypothesis-only) could not.
    for pin in [
        "theorem t (n : Nat) : n % 3 < 3 := by omega\n",
        "theorem t (n : Nat) : n % 7 < 7 := by omega\n",
        "theorem t (n : Nat) : n % 1 < 1 := by omega\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "omega proves n % k < k for a positive literal k",
        );
    }
}

#[test]
fn test_r161_omega_mod_lt_literal_soundness() {
    // SOUNDNESS (fail-closed): the synthesized 0 < k must be genuine. A tighter
    // false bound `n % 3 < 2` is FALSE (n % 3 can be 2) and must be rejected. And
    // `n % 0 < 0` is FALSE (n % 0 = n, never < 0); k = 0 makes synth_pos_lit
    // return None so the lane disengages and omega correctly fails. close_goal
    // re-checks every reconstructed term.
    for code in [
        "theorem bad (n : Nat) : n % 3 < 2 := by omega",
        "theorem bad (n : Nat) : n % 0 < 0 := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "omega must reject the false literal mod bound: {code}",
        );
    }
}

#[test]
fn test_r162_option_is_some_none_elaborates() {
    // R162: Option.isSome / Option.isNone — Bool-valued Option predicates,
    // registered as reducible axiom-free Option.rec folds. Both `o.isSome` and
    // `o.isNone` had failed UnknownIdent. Now they elaborate and reduce in both
    // recursor cases (some → true/false, none → false/true) by rfl.
    let code = "\
def a (o : Option Nat) : Bool := o.isSome\n\
def b (o : Option Nat) : Bool := o.isNone\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`o.isSome` and `o.isNone` elaborate for a variable Option",
    );
    for pin in [
        "theorem t : (some 5).isSome = true := rfl\n",
        "theorem t : (none : Option Nat).isSome = false := rfl\n",
        "theorem t : (some 5).isNone = false := rfl\n",
        "theorem t : (none : Option Nat).isNone = true := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Option.isSome/isNone reduce (some/none cases) by rfl",
        );
    }
}

#[test]
fn test_r162_option_is_some_none_soundness() {
    // SOUNDNESS (value-distinguishing across BOTH recursor arms): isSome is true
    // exactly on `some`, isNone is true exactly on `none`. A rfl pin to the
    // wrong Bool in any of the four (predicate × constructor) cases must be
    // rejected — a swapped none/some fold cannot slip through.
    for code in [
        "theorem bad : (some 5).isSome = false := rfl",
        "theorem bad : (none : Option Nat).isSome = true := rfl",
        "theorem bad : (some 5).isNone = true := rfl",
        "theorem bad : (none : Option Nat).isNone = false := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Option.isSome/isNone value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r163_bool_to_nat_elaborates() {
    // R163: Bool.toNat — the Bool→Nat coercion, registered as a reducible
    // axiom-free Bool.rec fold (false ↦ 0, true ↦ 1). `(b : Bool).toNat` had
    // failed UnknownIdent. Now it elaborates and reduces in both cases by rfl.
    let code = "def f (b : Bool) : Nat := b.toNat\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`b.toNat` elaborates for a variable Bool",
    );
    for pin in [
        "theorem t : (true : Bool).toNat = 1 := rfl\n",
        "theorem t : (false : Bool).toNat = 0 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Bool.toNat reduces (true ↦ 1, false ↦ 0) by rfl",
        );
    }
}

#[test]
fn test_r163_bool_to_nat_soundness() {
    // SOUNDNESS (value-distinguishing across both recursor arms): toNat maps
    // true to 1 and false to 0 — the reverse (true ↦ 0, false ↦ 1) is what a
    // swapped minor-premise order would give, and must be rejected.
    for code in [
        "theorem bad : (true : Bool).toNat = 0 := rfl",
        "theorem bad : (false : Bool).toNat = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Bool.toNat value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r164_option_orelse_elaborates() {
    // R164: Option.orElse — the fallback combinator, registered as a reducible
    // axiom-free Option.rec fold. The second argument is a THUNK
    // (`Unit → Option α`), forced only in the `none` case: `some a` keeps `a`,
    // `none` runs the thunk. `o.orElse (fun _ => …)` had failed UnknownIdent.
    let code = "def f (o : Option Nat) : Option Nat := o.orElse (fun _ => some 9)\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`o.orElse thunk` elaborates for a variable Option",
    );
    for pin in [
        "theorem t : (some 5).orElse (fun _ => some 9) = some 5 := rfl\n",
        "theorem t : (none : Option Nat).orElse (fun _ => some 9) = some 9 := rfl\n",
        "theorem t : (none : Option Nat).orElse (fun _ => none) = none := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Option.orElse reduces (some keeps value, none forces thunk) by rfl",
        );
    }
}

#[test]
fn test_r164_option_orelse_soundness() {
    // SOUNDNESS (value-distinguishing across both recursor arms): on `some a`
    // the fallback thunk is NEVER forced (`some 5` stays `some 5`, not the
    // thunk's `some 9`); on `none` the result is exactly the thunk's value
    // (`some 9`, not `none`). A rfl pin to the wrong branch value must be
    // rejected — a swapped none/some fold or an eagerly-forced thunk cannot
    // slip through.
    for code in [
        "theorem bad : (some 5).orElse (fun _ => some 9) = some 9 := rfl",
        "theorem bad : (none : Option Nat).orElse (fun _ => some 9) = none := rfl",
        "theorem bad : (some 5).orElse (fun _ => some 9) = some 14 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Option.orElse value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r165_prod_map_elaborates() {
    // R165: Prod.map — map a function over each component of a pair, registered
    // as a reducible axiom-free projection fold: `Prod.map f g p = (f p.1, g p.2)`.
    // `p.map f g` / `Prod.map f g p` had failed (missing const). Now it
    // elaborates and reduces both components by rfl.
    let code = "def f (p : Nat × Nat) : Nat × Nat := p.map (fun a => a + 10) (fun b => b + 20)\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`p.map f g` elaborates for a variable pair",
    );
    for pin in [
        "theorem t : Prod.map (fun (a : Nat) => a + 10) (fun (b : Nat) => b + 20) ((3, 4) : Nat × Nat) = (13, 24) := rfl\n",
        "theorem t : (((3, 4) : Nat × Nat).map (fun (a : Nat) => a + 10) (fun (b : Nat) => b + 20)) = (13, 24) := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Prod.map reduces (f on .1, g on .2) by rfl",
        );
    }
}

#[test]
fn test_r165_prod_map_soundness() {
    // SOUNDNESS (value-distinguishing across BOTH components + projection order):
    // with f = (·+10), g = (·+20) on (3, 4) the only correct result is (13, 24).
    // Wrong-fst, wrong-snd, and swapped-projection (f on .2, g on .1 → (14, 23))
    // rfl pins must all be rejected.
    for code in [
        "theorem bad : Prod.map (fun (a : Nat) => a + 10) (fun (b : Nat) => b + 20) ((3, 4) : Nat × Nat) = (14, 24) := rfl",
        "theorem bad : Prod.map (fun (a : Nat) => a + 10) (fun (b : Nat) => b + 20) ((3, 4) : Nat × Nat) = (13, 25) := rfl",
        "theorem bad : Prod.map (fun (a : Nat) => a + 10) (fun (b : Nat) => b + 20) ((3, 4) : Nat × Nat) = (14, 23) := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Prod.map value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r166_option_filter_elaborates() {
    // R166: Option.filter — keep `some a` iff `p a`, registered as a reducible
    // axiom-free Option.rec fold whose some-case nests a Bool.rec testing `p a`
    // (false ↦ none, true ↦ some a). `o.filter p` had failed UnknownIdent.
    let code = "def f (o : Option Nat) : Option Nat := o.filter (fun n => Nat.ble 3 n)\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`o.filter p` elaborates for a variable Option",
    );
    for pin in [
        // 3 ≤ 5 → true → keep
        "theorem t : (some 5).filter (fun n => Nat.ble 3 n) = some 5 := rfl\n",
        // 3 ≤ 2 → false → drop
        "theorem t : (some 2).filter (fun n => Nat.ble 3 n) = none := rfl\n",
        // none stays none (never touches the predicate)
        "theorem t : (none : Option Nat).filter (fun n => Nat.ble 3 n) = none := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "Option.filter reduces (keep-on-true, drop-on-false, none↦none) by rfl",
        );
    }
}

#[test]
fn test_r166_option_filter_soundness() {
    // SOUNDNESS (value-distinguishing across the some/none arms AND both Bool
    // branches of the nested test): a passing element is kept unchanged, a
    // failing one becomes none, and none is untouched. Wrong-branch rfl pins —
    // including a swapped Bool minor order (keep-on-false / drop-on-true) — must
    // be rejected.
    for code in [
        "theorem bad : (some 2).filter (fun n => Nat.ble 3 n) = some 2 := rfl",
        "theorem bad : (some 5).filter (fun n => Nat.ble 3 n) = none := rfl",
        "theorem bad : (none : Option Nat).filter (fun n => Nat.ble 3 n) = some 5 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong Option.filter value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r169_list_head_i_elaborates() {
    // R169: List.headI — head of a list, or the Inhabited default on `[]`,
    // registered as a reducible axiom-free `List.headD l default` fold (the same
    // body as List.head!). `l.headI` had failed UnknownIdent. (Kernel Def gated
    // via the corpus here — env::data was blocked by a co-tenant kernel-test
    // compile breakage; the corpus builds with_prelude and kernel-re-checks the
    // reductions below.)
    let code = "def f (l : List Nat) : Nat := l.headI\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.headI` elaborates for a variable List",
    );
    for pin in [
        "theorem t : [7, 8, 9].headI = 7 := rfl\n",
        "theorem t : ([] : List Nat).headI = 0 := rfl\n",
        "theorem t : [42].headI = 42 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.headI reduces (head on cons, default on nil) by rfl",
        );
    }
}

#[test]
fn test_r169_list_head_i_soundness() {
    // SOUNDNESS (value-distinguishing across the cons/nil arms): headI returns
    // the FIRST element on a non-empty list (not the second, not the default)
    // and the Inhabited default (0 for Nat) on the empty list. Wrong-value rfl
    // pins must be rejected by the kernel.
    for code in [
        "theorem bad : [7, 8, 9].headI = 8 := rfl",
        "theorem bad : [7, 8, 9].headI = 0 := rfl",
        "theorem bad : ([] : List Nat).headI = 7 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.headI value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r170_list_contains_elaborates() {
    // R170: List.contains — `as.contains a` is `true` iff some element BEq-equals
    // `a`, registered as a reducible axiom-free `List.rec`→Bool fold whose cons
    // test is `a == hd` via the `[BEq α]` instance (same shape as List.any, but
    // comparing the fixed query element rather than a predicate). `l.contains a`
    // had failed UnknownIdent. (Kernel Def gated via the corpus — env::data was
    // blocked by a co-tenant kernel-test compile breakage.)
    let code = "def f (l : List Nat) (a : Nat) : Bool := l.contains a\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.contains a` elaborates for variable List/element",
    );
    for pin in [
        "theorem t : [1, 2, 3].contains 2 = true := rfl\n",
        "theorem t : [1, 2, 3].contains 5 = false := rfl\n",
        "theorem t : ([] : List Nat).contains 1 = false := rfl\n",
        "theorem t : [7].contains 7 = true := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.contains reduces (member↦true, non-member↦false, nil↦false) by rfl",
        );
    }
}

#[test]
fn test_r170_list_contains_soundness() {
    // SOUNDNESS (value-distinguishing): contains is true EXACTLY on membership —
    // `2` is in `[1,2,3]` (must not be false), `5` is not (must not be true),
    // and nothing is in `[]`. Wrong-value rfl pins must be rejected by the kernel.
    for code in [
        "theorem bad : [1, 2, 3].contains 2 = false := rfl",
        "theorem bad : [1, 2, 3].contains 5 = true := rfl",
        "theorem bad : ([] : List Nat).contains 1 = true := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.contains value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r171_list_count_elaborates() {
    // R171: List.count — number of elements BEq-equal to `a`, registered as a
    // reducible axiom-free `List.rec`→Nat fold reusing the R163 `Bool.toNat`
    // (`Nat.add (Bool.toNat (hd == a)) ih`, base Nat.zero). `l.count a` had
    // failed UnknownIdent. (Kernel Def gated via the corpus — env::data was
    // blocked by a co-tenant kernel-test compile breakage.)
    let code = "def f (l : List Nat) (a : Nat) : Nat := l.count a\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.count a` elaborates for variable List/element",
    );
    for pin in [
        "theorem t : [1, 2, 2, 3].count 2 = 2 := rfl\n",
        "theorem t : [1, 2, 3].count 5 = 0 := rfl\n",
        "theorem t : ([] : List Nat).count 1 = 0 := rfl\n",
        "theorem t : [2, 2, 2].count 2 = 3 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.count reduces (counts BEq-matches; 0 on nil/non-member) by rfl",
        );
    }
}

#[test]
fn test_r171_list_count_soundness() {
    // SOUNDNESS (value-distinguishing): the count is the EXACT number of matches
    // — `2` occurs twice in `[1,2,2,3]` (not once), `5` occurs zero times in
    // `[1,2,3]` (not one), and nothing occurs in `[]`. Wrong-count rfl pins must
    // be rejected by the kernel.
    for code in [
        "theorem bad : [1, 2, 2, 3].count 2 = 1 := rfl",
        "theorem bad : [1, 2, 3].count 5 = 1 := rfl",
        "theorem bad : ([] : List Nat).count 1 = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.count value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r172_list_elem_elaborates() {
    // R172: List.elem — `true` iff some element BEq-equals the query `a` (the
    // primitive List.contains delegates to), registered as a reducible axiom-free
    // List.rec→Bool fold `Bool.or (a == hd) ih` with the query `a` as the FIRST
    // explicit arg. `l.elem a` / `List.elem a l` had failed UnknownIdent.
    // (Kernel Def gated via the corpus — env::data blocked by a co-tenant
    // kernel-test compile breakage.)
    let code = "def f (l : List Nat) (a : Nat) : Bool := l.elem a\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.elem a` elaborates for variable List/element",
    );
    for pin in [
        "theorem t : List.elem 2 [1, 2, 3] = true := rfl\n",
        "theorem t : [1, 2, 3].elem 2 = true := rfl\n",
        "theorem t : [1, 2, 3].elem 5 = false := rfl\n",
        "theorem t : ([] : List Nat).elem 1 = false := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.elem reduces (member↦true, non-member↦false, nil↦false) by rfl",
        );
    }
}

#[test]
fn test_r172_list_elem_soundness() {
    // SOUNDNESS (value-distinguishing): elem is true EXACTLY on membership — `2`
    // is in `[1,2,3]` (not false), `5` is not (not true), nothing is in `[]`.
    // Wrong-value rfl pins must be rejected by the kernel.
    for code in [
        "theorem bad : [1, 2, 3].elem 2 = false := rfl",
        "theorem bad : [1, 2, 3].elem 5 = true := rfl",
        "theorem bad : ([] : List Nat).elem 1 = true := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.elem value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r173_list_index_of_elaborates() {
    // R173: List.indexOf — 0-based position of the first BEq-match, or the list
    // length if none. Registered as a reducible axiom-free List.rec→Nat fold
    // (cons `if hd == a then 0 else Nat.succ ih` via Bool.rec, base Nat.zero).
    // `l.indexOf a` had failed UnknownIdent. (Kernel Def gated via the corpus —
    // env::data blocked by a co-tenant kernel-test compile breakage.)
    let code = "def f (l : List Nat) (a : Nat) : Nat := l.indexOf a\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.indexOf a` elaborates for variable List/element",
    );
    for pin in [
        "theorem t : [10, 20, 30].indexOf 20 = 1 := rfl\n",
        "theorem t : [10, 20, 30].indexOf 10 = 0 := rfl\n",
        "theorem t : [10, 20, 30].indexOf 99 = 3 := rfl\n",
        "theorem t : ([] : List Nat).indexOf 1 = 0 := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.indexOf reduces (first-match position; length if absent) by rfl",
        );
    }
}

#[test]
fn test_r173_list_index_of_soundness() {
    // SOUNDNESS (value-distinguishing): the position is EXACT — `20` is at index
    // 1 (not 0), an absent `99` yields the length 3 (not 0), and `10` is at 0
    // (not 1). Wrong-position rfl pins must be rejected by the kernel.
    for code in [
        "theorem bad : [10, 20, 30].indexOf 20 = 0 := rfl",
        "theorem bad : [10, 20, 30].indexOf 99 = 0 := rfl",
        "theorem bad : [10, 20, 30].indexOf 10 = 1 := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.indexOf value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r174_list_drop_elaborates() {
    // R174: List.drop — drop the first `n` elements, registered as a reducible
    // axiom-free `Nat.rec`-into-`(List α → List α)` fold (drop 0 ↦ id, drop (k+1)
    // ↦ ih ∘ tail), all fundamental primitives. `l.drop n` had failed
    // UnknownIdent. (Kernel Def gated via the corpus — env::data blocked by a
    // co-tenant kernel-test compile breakage.)
    let code = "def f (l : List Nat) : List Nat := l.drop 2\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.drop n` elaborates for a variable List",
    );
    for pin in [
        "theorem t : [10, 20, 30].drop 2 = [30] := rfl\n",
        "theorem t : [10, 20, 30].drop 0 = [10, 20, 30] := rfl\n",
        "theorem t : [10, 20, 30].drop 5 = [] := rfl\n",
        "theorem t : [10, 20, 30].drop 1 = [20, 30] := rfl\n",
        "theorem t : ([] : List Nat).drop 3 = [] := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.drop reduces (drops n heads; empty past the end) by rfl",
        );
    }
}

#[test]
fn test_r174_list_drop_soundness() {
    // SOUNDNESS (value-distinguishing): dropping 2 of [10,20,30] leaves exactly
    // [30] (not [20,30]), dropping 0 leaves the whole list, and dropping past the
    // end leaves []. Wrong-tail rfl pins must be rejected by the kernel.
    for code in [
        "theorem bad : [10, 20, 30].drop 2 = [20, 30] := rfl",
        "theorem bad : [10, 20, 30].drop 0 = [20, 30] := rfl",
        "theorem bad : [10, 20, 30].drop 5 = [10] := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.drop value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r175_list_take_elaborates() {
    // R175: List.take — keep the first `n` elements, registered as a reducible
    // axiom-free `Nat.rec`-into-`(List α → List α)` fold (take 0 ↦ [], take (k+1)
    // ↦ λ x => match x with [] => [] | a::l => a :: ih l), all fundamental
    // primitives. `l.take n` had failed UnknownIdent. (Kernel Def gated via the
    // corpus — env::data blocked by a co-tenant kernel-test compile breakage.)
    let code = "def f (l : List Nat) : List Nat := l.take 2\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.take n` elaborates for a variable List",
    );
    for pin in [
        "theorem t : [10, 20, 30].take 2 = [10, 20] := rfl\n",
        "theorem t : [10, 20, 30].take 0 = [] := rfl\n",
        "theorem t : [10, 20, 30].take 5 = [10, 20, 30] := rfl\n",
        "theorem t : [10, 20, 30].take 1 = [10] := rfl\n",
        "theorem t : ([] : List Nat).take 3 = [] := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.take reduces (keeps n heads; whole list past the end) by rfl",
        );
    }
}

#[test]
fn test_r175_list_take_soundness() {
    // SOUNDNESS (value-distinguishing): taking 2 of [10,20,30] keeps exactly
    // [10,20] (not [20,30]), taking 0 keeps [], and taking past the end keeps the
    // whole list. Wrong-prefix rfl pins must be rejected by the kernel.
    for code in [
        "theorem bad : [10, 20, 30].take 2 = [20, 30] := rfl",
        "theorem bad : [10, 20, 30].take 0 = [10] := rfl",
        "theorem bad : [10, 20, 30].take 5 = [10, 20] := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.take value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r176_list_filtermap_elaborates() {
    // R176: List.filterMap — map each element to an Option and keep the `some`s,
    // registered as a reducible axiom-free `List.rec` fold over `List α` (Type u)
    // into the motive `λ _ => List β` (Type v), with a nested `Option.rec` on
    // `f hd` in the cons case (none ↦ drop, some b ↦ b :: ih). `List.rec.{succ v,
    // u}` outer, `Option.rec.{succ v, v}` inner, two universe params. `l.filterMap
    // f` had failed UnknownIdent. (Kernel Def gated via the corpus — env::data
    // blocked by a co-tenant kernel-test compile breakage.)
    let code = "def f (l : List Nat) : List Nat := l.filterMap (fun n => some (n + 1))\n";
    assert_all_ok(
        &elab_file_prelude(code).1,
        "`l.filterMap f` elaborates for a variable List",
    );
    for pin in [
        // always-some ⇒ pure map (pins order + the per-element transform)
        "theorem t : [1, 2, 3].filterMap (fun n => some (n + 10)) = [11, 12, 13] := rfl\n",
        // empty list ⇒ empty
        "theorem t : ([] : List Nat).filterMap (fun n => some n) = [] := rfl\n",
        // all-none ⇒ every element dropped
        "theorem t : [1, 2].filterMap (fun _ => (none : Option Nat)) = [] := rfl\n",
        // mixed: keep+transform only n ≥ 3 (1,2 dropped; 3↦13, 4↦14)
        "theorem t : [1, 2, 3, 4].filterMap (fun n => if Nat.ble 3 n then some (n + 10) else none) = [13, 14] := rfl\n",
    ] {
        assert_all_ok(
            &elab_file_prelude(pin).1,
            "List.filterMap reduces (keeps/transforms the some-mapped elements) by rfl",
        );
    }
}

#[test]
fn test_r176_list_filtermap_soundness() {
    // SOUNDNESS (value-distinguishing): filterMap threads the transform through in
    // order, drops exactly the `none`-mapped elements, and preserves length only
    // for all-some. Wrong-value rfl pins must be rejected by the kernel. (All use
    // always-some / all-none forms so any failure is a genuine value mismatch, not
    // an elaboration gap.)
    for code in [
        "theorem bad : [1, 2, 3].filterMap (fun n => some (n + 10)) = [11, 12] := rfl",
        "theorem bad : [1, 2, 3].filterMap (fun n => some (n + 10)) = [12, 13, 14] := rfl",
        "theorem bad : [1, 2].filterMap (fun _ => (none : Option Nat)) = [1, 2] := rfl",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "wrong List.filterMap value must be rejected: {code}",
        );
    }
}

#[test]
fn test_r177_omega_add_sub_cancel_proves() {
    // R177: omega Nat-sub lane — the add-commuted truncation shape
    // `b + (a - b) = a` given `b ≤ a` (or `b < a`). The existing `sub_add_cancel`
    // lane only spelled `(a - b) + b = a`; the sibling commutes via the proven
    // axiom-clean `Nat.add_comm` and chains with `Eq.trans`, kernel-re-checked by
    // `close_goal`. (clean-elab lane; corpus-gated — env::data co-tenant-blocked.)
    for code in [
        // the new orientation, from a `≤` hypothesis
        "theorem t (a b : Nat) (h : b ≤ a) : b + (a - b) = a := by omega",
        // from a `<` hypothesis (weakened via Nat.le_of_lt)
        "theorem t (a b : Nat) (h : b < a) : b + (a - b) = a := by omega",
        // concrete subtrahend
        "theorem t (n : Nat) (h : 3 ≤ n) : 3 + (n - 3) = n := by omega",
        // the ORIGINAL orientation must still work (no regression to sub_add_cancel)
        "theorem t (a b : Nat) (h : b ≤ a) : a - b + b = a := by omega",
    ] {
        assert_all_ok(
            &elab_file_prelude(code).1,
            "omega proves the add-commuted Nat truncation `b + (a - b) = a`",
        );
    }
}

#[test]
fn test_r177_omega_add_sub_cancel_soundness() {
    // SOUNDNESS: the lane fires ONLY on `b + (a - b) = a` with a matching
    // `b ≤ a` / `b < a` hypothesis, and every synthesized term is kernel-re-checked
    // — so it must NOT prove any of these false / unwarranted goals. Each isolates
    // one guard: missing hypothesis, wrong RHS, wrong left-addend (add_l ≠ b), and
    // wrong hypothesis direction.
    for code in [
        // no hypothesis: false whenever b > a
        "theorem bad (a b : Nat) : b + (a - b) = a := by omega",
        // off-by-one RHS
        "theorem bad (a b : Nat) (h : b ≤ a) : b + (a - b) = a + 1 := by omega",
        // left addend is `a`, not the subtrahend `b` (a + (a - b) = a ⇒ a ≤ b, not given)
        "theorem bad (a b : Nat) (h : b ≤ a) : a + (a - b) = a := by omega",
        // hypothesis is the wrong direction (a ≤ b): false unless a = b
        "theorem bad (a b : Nat) (h : a ≤ b) : b + (a - b) = a := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "omega must NOT prove the false/unwarranted goal: {code}",
        );
    }
}

#[test]
fn test_r178_omega_add_sub_cancel_left_proves() {
    // R178: omega Nat-sub lane — the UNCONDITIONAL left-cancellation
    // `(a + b) - a = b` (holds for all a, b; no hypothesis). Nat truncation makes
    // it true but the linear relaxation drops the `- a` atom, so it fell through
    // to the failing linarith delegate. `try_nat_add_sub_cancel_left` closes it
    // with the single proven, axiom-clean term
    // `@Nat.ulpRound.add_sub_cancel_left a b`, kernel-re-checked by `close_goal`.
    // (clean-elab lane; corpus-gated.)
    for code in [
        "theorem t (a b : Nat) : a + b - a = b := by omega",
        "theorem t (x y : Nat) : x + y - x = y := by omega",
        // concrete left addend
        "theorem t (n : Nat) : 3 + n - 3 = n := by omega",
        // the right-cancellation sibling `(a + b) - b = a` must still work too
        "theorem t (a b : Nat) : a + b - b = a := by omega",
    ] {
        assert_all_ok(
            &elab_file_prelude(code).1,
            "omega proves the unconditional Nat left-cancellation `(a + b) - a = b`",
        );
    }
}

#[test]
fn test_r178_omega_add_sub_cancel_left_soundness() {
    // SOUNDNESS: the lane fires ONLY on `(a + b) - a = b` (subtracted term = left
    // addend, RHS = right addend); every term is kernel-re-checked — so it must
    // NOT prove any of these false / unwarranted goals. Each isolates one guard:
    // wrong RHS (= a not b), the right-cancel shape mis-stated (= b not a),
    // off-by-one, and a subtracted term that is neither addend.
    for code in [
        "theorem bad (a b : Nat) : a + b - a = a := by omega",
        "theorem bad (a b : Nat) : a + b - b = b := by omega",
        "theorem bad (a b : Nat) : a + b - a = b + 1 := by omega",
        "theorem bad (a b c : Nat) : a + b - c = b := by omega",
    ] {
        assert!(
            elab_file_prelude(code).1.iter().any(|r| r.is_err()),
            "omega must NOT prove the false/unwarranted goal: {code}",
        );
    }
}

/// `elab ... : term` must stay registered for LATER declarations in the file.
///
/// `ElabCtx` is rebuilt per declaration, and `user_term_elabs` lived only on
/// that context, so a term elaborator was registered and then dropped before
/// the next declaration could call it — `def v : Nat := myone` failed with
/// `UnknownIdentWithSuggestions { name: "myone", .. }`. It is now persisted
/// through `FileContext`, exactly like the tactic registry and macro context.
#[test]
fn test_b203_user_term_elab_persists_across_declarations() {
    let code = r#"
elab "myone" : term => Nat.succ Nat.zero
def v : Nat := myone
theorem v_is_one : v = 1 := rfl
def w : Nat := myone + myone
"#;
    let results = elab_file_prelude(code).1;
    assert_all_ok(&results, "user term elaborator across declarations");
}

/// The elaborator must produce the real term, not a placeholder that merely
/// type-checks: `v_is_one` closes by `rfl`, which only holds if `myone`
/// elaborated to `Nat.succ Nat.zero`.
#[test]
fn test_b203_user_term_elab_produces_the_declared_body() {
    let code = r#"
elab "mytwo" : term => Nat.succ (Nat.succ Nat.zero)
theorem mytwo_is_two : mytwo = 2 := rfl
"#;
    let results = elab_file_prelude(code).1;
    assert_all_ok(&results, "user term elaborator body fidelity");
}
