// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Recursion staging R0 — the refusal for a self-reference must carry the
//! fix, with options (v7/D3), never a name-distance guess.
//!
//! THE DEFECT (measured 2026-08-20, Trust superproject
//! `crates/trust-clean-origin/tests/recursion_boundary_probes.rs`): the §1
//! demo `def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)`
//! died `UnknownIdentWithSuggestions { name: "gcd" }` and the suggestion
//! machinery offered **`Quotient.ind`** — a nearest-theorem-name guess that
//! is actively misleading, because `gcd` is not a typo: it is the name being
//! defined, i.e. a recursive definition whose form no lowering accepted.
//!
//! These tests pin the honest refusal on every seam that produced the bad
//! one, each paired with a control that must keep going the other way, so
//! none can be passed by a checker that simply refuses more:
//!
//! * a self-reference refusal NAMES the definition and the recursion
//!   fragment (structural; WF via a `termination_by` measure naming ONE
//!   parameter) and carries the three options — never "nearest theorem names";
//!
//! **The fragment MOVED on 2026-08-22 (R3), and two rows here moved with it.**
//! A `termination_by` whose measure names one parameter now lowers at ANY
//! arity, so the dite spelling of `gcd` ADMITS and the Bool-test spelling
//! refuses at its real defect (an `ite` binds no hypothesis, so nothing bounds
//! `b` away from zero) instead of at the name. Both rows are re-pinned below
//! rather than deleted: this file's job is to state where the boundary IS, and
//! a refusal file whose fragment description has gone stale is exactly the
//! misleading diagnostic it was written to remove.
//! * a genuine typo KEEPS the name-distance suggestions (the new refusal
//!   must not swallow ordinary unknown identifiers);
//! * the admitting recursion paths (structural equation form, phase-1 WF)
//!   still admit — the change is diagnostic-only, fail-closed identical;
//! * in a header-first batch, a reference to a same-batch declaration whose
//!   header FAILED collection points at that sibling declaration (the
//!   adjacent case), while an ordinary forward reference stays accepted.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Sequentially elaborate `source` one declaration at a time — the island
/// session's `check` lane — returning every error and the final environment.
fn check_sequential(source: &str) -> (Environment, Vec<ElabError>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut errors = Vec::new();
    let decls = parse_file(source).expect("fixture must parse");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context_and_warning(
            &mut env,
            &processed,
            &mut file_ctx,
        ) {
            Ok(registered) => {
                let mut leaves = Vec::new();
                registered.result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    if let ElabResult::Failed { error, .. } = leaf {
                        errors.push((**error).clone());
                    }
                }
            }
            Err(error) => errors.push(error),
        }
    }
    (env, errors)
}

/// Header-first batch elaboration — the island session's `check_all` lane.
fn check_batch(source: &str) -> (Environment, bool, String) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    (env, outcome.committed, outcome.render_rejections())
}

/// The refusal must be recursion-aware: name the definition, state the
/// supported fragment, and carry the three options — and it must NOT be a
/// name-distance suggestion list.
fn assert_recursion_refusal(error: &ElabError, decl: &str, params: usize) {
    match error {
        ElabError::RecursionOutsideFragment {
            name,
            decl: found_decl,
            params: found_params,
            ..
        } => {
            assert_eq!(name, decl, "the refusal must carry the ident as written");
            assert_eq!(found_decl, decl, "the refusal must name the definition");
            assert_eq!(
                *found_params, params,
                "the refusal must state the measured parameter count \
                 (post equation-form normalization)"
            );
        }
        other => panic!(
            "expected the recursion-aware refusal for `{decl}`, got: {other:?}\n\
             display: {other}"
        ),
    }
    let message = error.to_string();
    for needle in [
        "the name being defined",
        "structural recursion",
        "termination_by",
        "(1)",
        "(2)",
        "(3)",
        "proof position",
    ] {
        assert!(
            message.contains(needle),
            "the refusal must carry the fix with options (v7/D3); missing \
             `{needle}` in:\n{message}"
        );
    }
    assert!(
        !message.contains("nearest theorem"),
        "a self-reference is not a typo: name-distance suggestions are the \
         defect this refusal replaces:\n{message}"
    );
}

// ══════════ the §1 demo shape: if-then-else self-call, two parameters ══════════

/// MUST REFUSE, recursion-aware. This exact source used to die
/// `UnknownIdentWithSuggestions { name: "gcd" }` offering `Quotient.ind`.
/// Fail-closed is untouched: the batch still refuses and registers nothing —
/// only the refusal text changed.
#[test]
fn test_gcd_self_reference_refuses_with_the_fragment_not_a_theorem_guess() {
    let (env, errors) =
        check_sequential("def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)\n");
    assert!(
        env.get_const(&Name::from_string("gcd")).is_none(),
        "`gcd` must not register: the diagnostic change may not widen the fragment"
    );
    assert_eq!(errors.len(), 1, "exactly one refusal, got: {errors:?}");
    assert_recursion_refusal(&errors[0], "gcd", 2);
}

/// MUST REFUSE, recursion-aware — equation form. The parameter count in the
/// refusal must be the NORMALIZED one (the surface decl writes no binders;
/// `normalize_equation_def` lifts two).
#[test]
fn test_equation_form_self_reference_gets_the_same_refusal() {
    let (env, errors) =
        check_sequential("def gcd3 : Nat -> Nat -> Nat\n| a, 0 => a\n| a, b => gcd3 b (a % b)\n");
    assert!(env.get_const(&Name::from_string("gcd3")).is_none());
    assert_eq!(errors.len(), 1, "exactly one refusal, got: {errors:?}");
    assert_recursion_refusal(&errors[0], "gcd3", 2);
}

/// **R4, the pin FLIPPED (2026-08-22).** The VERBATIM Bool-test spelling with
/// `termination_by b` now ADMITS.
///
/// Its history in this file is worth keeping, because both earlier verdicts
/// were correct when written and neither is the current one:
///
/// * **at R0** — refused at the NAME (`RecursionOutsideFragment`), because
///   routing never reached the well-founded lowering at all;
/// * **at R3** — refused at the DECREASE. An explicit `termination_by` naming a
///   different parameter than the structural auto-detector picked now wins, so
///   `gcd2` reached the lowering, which accepted the wider signature and then
///   refused where the real defect was: `if b == 0 then …` is a non-dependent
///   `ite`, so its else branch bound NO hypothesis and nothing in scope bounded
///   `b` away from zero;
/// * **at R4** — ADMITTED. The lowering normalizes that `ite` into the
///   dependent `dite` (a DEFINITIONAL rewrite — both are reducible and unfold
///   to the same `Decidable.casesOn`), which binds `¬((b == 0) = true)` at the
///   call site; the discharge cascade turns that into `0 < b` through the
///   axiom-free `of_not_decide_eq_true` + `Nat.pos_of_ne_zero`, which is
///   exactly `Nat.mod_lt`'s side condition.
///
/// Pinned HERE, in the refusal file, for the same reason R3 pinned `gcd4`
/// here: this row is the boundary of the fragment these diagnostics describe,
/// and the two must move together or the diagnostics start lying. The
/// end-to-end evidence (kernel check, axiom closure, `gcd 12 18 = 6`) is
/// `r4_gcd_bool_spelling_e2e.rs`.
#[test]
fn test_bool_test_gcd_with_termination_by_now_admits() {
    let (env, errors) = check_sequential(
        "def gcd2 (a b : Nat) : Nat := if b == 0 then a else gcd2 b (a % b)\ntermination_by b\n",
    );
    assert!(
        errors.is_empty(),
        "R4: the verbatim Bool-test spelling must admit, got: {errors:?}"
    );
    assert!(
        env.get_const(&Name::from_string("gcd2")).is_some(),
        "`gcd2` must register"
    );
}

/// CONTROL for the row above — the fragment moved, fail-closed did NOT. A
/// Bool-tested recursion whose measured argument does not actually decrease is
/// still refused AT THE DECREASE, with the same shape of message R3 pinned.
/// Without this, "the Bool spelling admits" would be indistinguishable from
/// "the Bool-test lane stopped checking".
///
/// The shape is chosen to reach the well-founded lowering rather than die at
/// routing: the call's parameter-0 argument is the bare identifier `b`, which
/// the structural auto-detector reads as "parameter 0 decreases", while
/// `termination_by b` names parameter 1 — the declaration wins (R3), the
/// lowering runs, and the obligation `Nat.lt (a + 1) b` is the thing that
/// cannot be discharged. (Measured: with the parameters the other way round it
/// is refused one layer earlier, `RecursionOutsideFragment`, which is a
/// different — also fail-closed — story and not what this control is about.)
#[test]
fn test_a_bool_test_without_a_real_decrease_still_refuses_at_the_decrease() {
    let (env, errors) = check_sequential(
        "def spin2 (a b : Nat) : Nat := if b == 0 then a else spin2 b (a + 1)\n\
         termination_by b\n",
    );
    assert!(
        env.get_const(&Name::from_string("spin2")).is_none(),
        "fail-closed: an undischargeable decrease registers nothing"
    );
    assert_eq!(errors.len(), 1, "exactly one refusal, got: {errors:?}");
    let ElabError::Unsupported { feature } = &errors[0] else {
        panic!("must fail closed as `Unsupported`, got: {:?}", errors[0]);
    };
    assert!(
        feature.contains("termination_by") && feature.contains("spin2"),
        "the refusal must name the construct and the declaration: {feature}"
    );
    assert!(
        feature.contains("no decreasing proof was found"),
        "and it must say WHAT failed — the decrease, not the name: {feature}"
    );
    assert!(
        !feature.contains("nearest theorem"),
        "still never a name-distance guess: {feature}"
    );
}

/// The `UInt64` spelling has NO `termination_by`, so nothing names its
/// recursion parameter and it stays outside the fragment with the R0
/// recursion-aware refusal. (Its measure would also not be `Nat`-valued.)
#[test]
fn test_the_uint64_gcd_spelling_gets_the_same_refusal() {
    let (env, errors) = check_sequential(
        "def gcd64 (a b : UInt64) : UInt64 := if b == 0 then a else gcd64 b (a % b)\n",
    );
    assert!(env.get_const(&Name::from_string("gcd64")).is_none());
    assert_eq!(errors.len(), 1, "exactly one refusal, got: {errors:?}");
    assert_recursion_refusal(&errors[0], "gcd64", 2);
}

/// **R3, the pin FLIPPED (2026-08-22).** The dite spelling with
/// `termination_by b` — the "passing class's spelling" the recursion boundary
/// probes named — now ADMITS: two parameters, a one-parameter measure, and a
/// decrease discharged by the axiom-free `Nat.mod_lt`.
///
/// It is pinned HERE, in the refusal file, deliberately: this row is the
/// boundary of the fragment those refusals describe, and the two must move
/// together or the diagnostics start lying. The dedicated end-to-end evidence
/// (kernel check, axiom closure, `gcd 12 18 = 6`) is `r3_gcd_wf_e2e.rs`.
#[test]
fn test_the_dite_gcd_spelling_now_admits() {
    let (env, errors) = check_sequential(
        "def gcd4 (a b : Nat) : Nat := if h : 0 < b then gcd4 b (a % b) else a\n\
         termination_by b\n",
    );
    assert!(
        errors.is_empty(),
        "R3: the dite spelling of `gcd` must admit, got: {errors:?}"
    );
    assert!(
        env.get_const(&Name::from_string("gcd4")).is_some(),
        "`gcd4` must register"
    );
}

// ═════════════════ controls: what must NOT change ═════════════════

/// CONTROL — a genuine typo is not a self-reference: the ordinary
/// unknown-identifier diagnostics (name-distance suggestions included) must
/// survive, or the new refusal has swallowed the case it does not own.
#[test]
fn test_a_genuine_typo_keeps_the_ordinary_unknown_ident_diagnostics() {
    let (env, errors) = check_sequential("def uses_typo (n : Nat) : Nat := succc n\n");
    assert!(env.get_const(&Name::from_string("uses_typo")).is_none());
    assert_eq!(errors.len(), 1, "exactly one refusal, got: {errors:?}");
    assert!(
        matches!(
            errors[0],
            ElabError::UnknownIdent(_) | ElabError::UnknownIdentWithSuggestions { .. }
        ),
        "a typo'd ident that is NOT the declaration's name must keep the \
         ordinary diagnostic, got: {:?}",
        errors[0]
    );
    assert!(
        !errors[0].to_string().contains("the name being defined"),
        "the recursion refusal fired on a non-self identifier:\n{}",
        errors[0]
    );
}

/// CONTROL — a missing dotted identifier is not a self-reference merely
/// because its namespace prefix is the declaration currently being defined.
/// `elab_proj` must try the complete written name after the base `diagPrefix`
/// receives the recursion-aware unknown-identifier diagnostic. The deliberately
/// distant suffix has no nearby theorem, so the complete-name diagnostic is a
/// bare `UnknownIdent`; correctness must not depend on a suggestion payload.
#[test]
fn test_missing_dotted_name_is_not_self_reference_to_its_prefix() {
    let distant_suffix = "z".repeat(128);
    let missing_name = format!("diagPrefix.{distant_suffix}");
    let source = format!("def diagPrefix : Nat := {missing_name}\n");
    let (env, errors) = check_sequential(&source);
    assert!(
        env.get_const(&Name::from_string("diagPrefix")).is_none(),
        "the invalid definition must remain fail-closed"
    );
    assert_eq!(errors.len(), 1, "exactly one refusal, got: {errors:?}");
    match &errors[0] {
        ElabError::UnknownIdent(name) => assert_eq!(
            name, &missing_name,
            "the diagnostic must preserve the complete identifier as written"
        ),
        other => panic!(
            "the dotted identifier is not a self-reference to its prefix; got: {other:?}\n\
             display: {other}"
        ),
    }
}

/// CONTROL — the admitting recursion paths still admit. The change is
/// diagnostic-only: structural equation-form recursion and phase-1
/// single-parameter WF recursion were in the fragment before and must stay.
#[test]
fn test_the_admitting_recursion_paths_still_admit() {
    // Structural: equation form over Nat, lowered through `Nat.rec`.
    let (env, errors) =
        check_sequential("def tozero : Nat -> Nat\n| 0 => 0\n| n + 1 => tozero n\n");
    assert!(
        errors.is_empty(),
        "structural equation-form recursion must still admit: {errors:?}"
    );
    assert!(
        env.get_const(&Name::from_string("tozero")).is_some(),
        "`tozero` must register"
    );

    // Phase-1 WF: one parameter, Nat measure, cascade-dischargeable decrease.
    let (env, errors) = check_sequential(
        "def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0\n\
         termination_by n\n",
    );
    assert!(
        errors.is_empty(),
        "phase-1 well-founded recursion must still admit: {errors:?}"
    );
    assert!(
        env.get_const(&Name::from_string("countdownSum")).is_some(),
        "`countdownSum` must register"
    );
}

// ══════ the adjacent case: a same-batch sibling whose header failed ══════

/// MUST REFUSE, sibling-aware. `lead` references `helper`, declared in the
/// same batch, whose own signature does not elaborate (`NoSuchType` — with
/// `autoImplicit false` it cannot silently become a binder), so `helper`
/// staged no header. The refusal at `lead`'s use site must point at the
/// SIBLING declaration and its repair — not offer nearest theorem names.
#[test]
fn test_batch_reference_to_a_failed_header_names_the_sibling_declaration() {
    let (env, committed, rejections) = check_batch(
        "set_option autoImplicit false\n\
         def lead (n : Nat) : Nat := helper n\n\
         def helper (n : Nat) : NoSuchType := helper n\n",
    );
    assert!(!committed, "a failed sibling header must refuse the batch");
    for name in ["lead", "helper"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` reached the environment from a REFUSED batch"
        );
    }
    let lead_refusal = rejections
        .split("\n\n")
        .find(|r| r.contains("`lead`"))
        .unwrap_or_else(|| panic!("no refusal names `lead`:\n{rejections}"));
    for needle in [
        "matches `helper`, declared in this same batch",
        "no forward-resolvable header",
        "repair `helper`",
    ] {
        assert!(
            lead_refusal.contains(needle),
            "the refusal must point at the sibling declaration and its fix \
             (v7/D3); missing `{needle}` in:\n{lead_refusal}"
        );
    }
    assert!(
        !lead_refusal.contains("nearest theorem"),
        "a same-batch sibling is not a typo: name-distance suggestions are \
         the defect this refusal replaces:\n{lead_refusal}"
    );
    // `helper`'s OWN refusal is about `NoSuchType` — a genuine unknown name —
    // and must KEEP the ordinary diagnostics (the sibling-aware refusal must
    // not swallow it).
    let helper_refusal = rejections
        .split("\n\n")
        .find(|r| r.contains("`helper` did not elaborate"))
        .unwrap_or_else(|| panic!("no refusal names `helper`:\n{rejections}"));
    assert!(
        helper_refusal.contains("NoSuchType"),
        "`helper`'s own refusal must stay about its actual defect, the \
         unknown `NoSuchType`:\n{helper_refusal}"
    );
}

/// CONTROL — the same-batch sibling diagnostic also belongs to the failed
/// BASE identifier, not to every dotted name beginning with that spelling.
/// Here `batchPrefix` has no header, but the authored use is the distinct name
/// `batchPrefix.<distant suffix>`; the complete bare-unknown diagnostic must
/// win without relying on a nearby-theorem suggestion.
#[test]
fn test_missing_dotted_name_is_not_failed_same_batch_prefix() {
    let distant_suffix = "z".repeat(128);
    let missing_name = format!("batchPrefix.{distant_suffix}");
    let source = format!(
        "set_option autoImplicit false\n\
         def lead : Nat := {missing_name}\n\
         def batchPrefix : NoSuchType := 0\n"
    );
    let (env, committed, rejections) = check_batch(&source);
    assert!(!committed, "the invalid batch must remain fail-closed");
    for name in ["lead", "batchPrefix"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` reached the environment from a refused atomic batch"
        );
    }
    let lead_refusal = rejections
        .split("\n\n")
        .find(|rejection| rejection.contains("`lead`"))
        .unwrap_or_else(|| panic!("no refusal names `lead`:\n{rejections}"));
    assert!(
        lead_refusal.contains(&format!("Unknown identifier: {missing_name}")),
        "the refusal must preserve the complete identifier as written:\n{lead_refusal}"
    );
    assert!(
        !lead_refusal.contains("matches `batchPrefix`, declared in this same batch"),
        "a diagnostic for the base prefix swallowed the complete dotted name:\n{lead_refusal}"
    );
}

/// CONTROL — a plain forward reference (the sibling's header DOES stage) is
/// exactly what header-first checking exists to accept; the sibling-aware
/// refusal must not fire on it.
#[test]
fn test_batch_forward_reference_with_a_good_header_is_still_accepted() {
    let (env, committed, rejections) = check_batch(
        "set_option autoImplicit false\n\
         def lead (n : Nat) : Nat := helper n\n\
         def helper (n : Nat) : Nat := n\n",
    );
    assert!(
        committed,
        "REJECTED a forward reference whose sibling staged a header: {rejections}"
    );
    for name in ["lead", "helper"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` must be registered"
        );
    }
}

/// CONTROL — the refusal must not LEAK past its own declaration. `stale`
/// refuses as a self-reference and registers nothing; the next declaration
/// then names `stale`, which is now simply an identifier that is not in scope
/// and is not the name being defined there. If the subject survived the first
/// declaration, `after` would be told it is recursive, which it is not.
#[test]
fn test_the_recursion_refusal_does_not_leak_into_the_next_declaration() {
    let (env, errors) = check_sequential(
        "def stale (a b : Nat) : Nat := if b == 0 then a else stale b (a % b)\n\
         def after (n : Nat) : Nat := stale n n\n",
    );
    for name in ["stale", "after"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` must not register"
        );
    }
    assert_eq!(errors.len(), 2, "one refusal each, got: {errors:?}");
    assert_recursion_refusal(&errors[0], "stale", 2);
    assert!(
        matches!(
            errors[1],
            ElabError::UnknownIdent(_) | ElabError::UnknownIdentWithSuggestions { .. }
        ),
        "`after` names an identifier that is not in scope and is not the name \
         being defined; the subject leaked from the previous declaration: {:?}",
        errors[1]
    );
}
