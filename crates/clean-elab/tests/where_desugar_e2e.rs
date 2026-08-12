// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `where`-clause desugaring — end-to-end (parse → elaborate → kernel-check).
//!
//! Audit row d04 (docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md §1/§2.7/§5): the
//! `where` path was the audit's only "registers-anyway" case — a helper decl
//! silently lowered to a synthetic `sorry`, so the parent registered
//! axiom-tainted (`sorryAx`). That fallback is ELIMINATED:
//!
//! - Common shapes lower to real kernel values (plain `let` for non-recursive
//!   helpers, the structural-recursion lift for self-recursive ones), and the
//!   parent's transitive axiom closure is EMPTY.
//! - Every unsupported shape FAILS LOUD with a typed `ElabError`
//!   (`WhereLetRecUnsupported`) naming `where` and the offending shape —
//!   mutual (cyclic) helper groups, duplicate helper names, non-structural
//!   recursion, zero-parameter self-reference.
//!
//! Lean ground truth: `where` decls are `letRecDecl`s
//! (`Lean/Parser/Term.lean:701-703 whereDecls`) expanded to a leading
//! `let rec` group (`Lean/Elab/Binders.lean:472-476 expandWhereDecls`) whose
//! names are mutually visible and which see the parent's binders
//! (`Lean/Elab/MutualDef.lean:332-397`, `Lean/Elab/LetRec.lean:87/110/140`).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::{parse_file, SurfaceDecl};

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Transitive axiom closure of a registered declaration (empty = proof-grade).
fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(ToString::to_string)
        .collect()
}

fn assert_empty_closure(env: &Environment, name: &str) {
    let closure = axiom_closure(env, name);
    assert!(
        closure.is_empty(),
        "{name} must have an EMPTY transitive axiom closure (no sorryAx, no stubs), got {closure:?}"
    );
}

/// Assert `source` fails loud somewhere in parse/elab/kernel and that the
/// failure text mentions every fragment in `must_mention`.
fn expect_rejected(source: &str, what: &str, must_mention: &[&str]) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => {
            for fragment in must_mention {
                assert!(
                    e.contains(fragment),
                    "{what}: rejection must mention {fragment:?}; got: {e}"
                );
            }
            e
        }
    }
}

// =========================================================================
// 1. POSITIVE — common `where` shapes lower to real values, no axiom taint
// =========================================================================

/// The exact d04 audit probe: non-recursive helper. Pre-fix this REGISTERED
/// with `sorry axioms: 1`; now it registers clean and computes.
#[test]
fn test_where_simple_helper_registers_clean_d04() {
    let env = elaborate_module(
        "def f (n : Nat) : Nat := g n where g (m : Nat) : Nat := m + 1\n\
         theorem f_val : f 3 = 4 := rfl\n",
    )
    .expect("d04 probe: simple where helper should elaborate and kernel-check");
    assert_empty_closure(&env, "f");
    assert_empty_closure(&env, "f_val");
}

/// Helper reads the parent's binder `n` (Lean: where decls see the parent's
/// binders because the generated `let rec` sits inside them —
/// Lean/Elab/MutualDef.lean:332-397).
#[test]
fn test_where_helper_captures_parent_params() {
    let env = elaborate_module(
        "def pc (n : Nat) : Nat := h 1 where h (m : Nat) : Nat := m + n\n\
         theorem pc_val : pc 5 = 6 := rfl\n",
    )
    .expect("where helper referencing parent params should elaborate");
    assert_empty_closure(&env, "pc");
    assert_empty_closure(&env, "pc_val");
}

/// Multiple where decls; the later helper references the earlier one and the
/// body uses both.
#[test]
fn test_where_multiple_decls_with_cross_reference() {
    let env = elaborate_module(
        "def f3 (n : Nat) : Nat := a n + b n where a (m : Nat) : Nat := m + 1\n  \
         b (m : Nat) : Nat := a m + 1\n\
         theorem f3_val : f3 1 = 5 := rfl\n",
    )
    .expect("multiple where decls should elaborate");
    assert_empty_closure(&env, "f3");
    assert_empty_closure(&env, "f3_val");
}

/// FORWARD reference: `a` uses `b`, which is defined after it. Lean's where
/// decls form one mutually visible `let rec` group
/// (Lean/Elab/Binders.lean:475, Lean/Elab/LetRec.lean:87), so source order
/// must not matter for acyclic groups — the desugar topologically reorders.
#[test]
fn test_where_forward_reference_reorders() {
    let env = elaborate_module(
        "def fw (n : Nat) : Nat := a n where a (m : Nat) : Nat := b m\n  \
         b (m : Nat) : Nat := m + 1\n\
         theorem fw_val : fw 3 = 4 := rfl\n",
    )
    .expect("forward-referencing where decls should reorder and elaborate");
    assert_empty_closure(&env, "fw");
    assert_empty_closure(&env, "fw_val");
}

/// Zero-parameter helper with an explicit type ascription.
#[test]
fn test_where_zero_param_helper_with_type_ascription() {
    let env = elaborate_module(
        "def z2 : Nat := c + 1 where c : Nat := 41\n\
         theorem z2_val : z2 = 42 := rfl\n",
    )
    .expect("zero-param ascribed where helper should elaborate");
    assert_empty_closure(&env, "z2");
    assert_empty_closure(&env, "z2_val");
}

/// Helper with parameters but NO return-type annotation (inferred).
#[test]
fn test_where_helper_without_return_annotation() {
    let env = elaborate_module(
        "def nr (n : Nat) : Nat := g n where g (m : Nat) := m + 1\n\
         theorem nr_val : nr 3 = 4 := rfl\n",
    )
    .expect("where helper without return annotation should infer and elaborate");
    assert_empty_closure(&env, "nr");
    assert_empty_closure(&env, "nr_val");
}

/// SELF-recursive helper with genuine structural descent lowers through the
/// existing `let rec` structural-recursion lift (`<Inductive>.rec`) — no
/// axiom, no sorry, and it computes.
#[test]
fn test_where_self_recursive_structural_helper() {
    let env = elaborate_module(
        "def dbl (n : Nat) : Nat := go n where go (m : Nat) : Nat := \
         match m with | 0 => 0 | Nat.succ k => go k + 2\n\
         theorem dbl_val : dbl 3 = 6 := rfl\n",
    )
    .expect("structurally recursive where helper should lift and elaborate");
    assert_empty_closure(&env, "dbl");
    assert_empty_closure(&env, "dbl_val");
}

/// `theorem … where`: helper provides the proof term; its TYPE mentions the
/// parent's binder.
#[test]
fn test_theorem_where_proof_helper() {
    let env =
        elaborate_module("theorem tw (n : Nat) : n + 0 = n := pf where pf : n + 0 = n := rfl\n")
            .expect("theorem with where proof helper should elaborate");
    assert_empty_closure(&env, "tw");
}

// =========================================================================
// 2. LOUD NEGATIVES — unsupported shapes are typed hard failures, never
//    sorry-tainted registrations
// =========================================================================

/// Mutual recursion BETWEEN where decls is descoped: nesting cannot express
/// the cycle (Lean elaborates the group mutually), so it must fail loud.
#[test]
fn test_where_mutual_cycle_fails_loud() {
    expect_rejected(
        "def mu (n : Nat) : Nat := p n where p (k : Nat) : Nat := q k\n  \
         q (k : Nat) : Nat := p k\n",
        "mutually recursive where decls",
        &["where", "cyclic", "p", "q"],
    );
}

/// Self-recursion with no structurally decreasing parameter (would need
/// well-founded recursion) fails loud with the typed error.
#[test]
fn test_where_nonstructural_recursion_fails_loud() {
    expect_rejected(
        "def bad (n : Nat) : Nat := g n where g (m : Nat) : Nat := g m\n",
        "non-structural recursive where helper",
        &["unsupported `where`/`let rec`", "`g`", "decreasing"],
    );
}

/// Recursion through a non-variable argument (`g (m - 1)`) is not detected
/// structural descent — Lean needs well-founded recursion here. Descoped:
/// must fail loud, never register.
#[test]
fn test_where_subtraction_recursion_fails_loud() {
    expect_rejected(
        "def wf (n : Nat) : Nat := g n where g (m : Nat) : Nat := \
         if m = 0 then 0 else g (m - 1)\n",
        "well-founded-style where helper",
        &["unsupported `where`/`let rec`", "`g`"],
    );
}

/// A zero-parameter helper referencing itself is a value-level fixpoint —
/// no terminating interpretation. Pre-fix this SILENTLY registered `z` with
/// the mangled signature `{c : Nat} → Nat` (the unresolved self-reference was
/// auto-implicit-captured). Now it fails loud.
#[test]
fn test_where_zero_param_self_reference_fails_loud() {
    let err = expect_rejected(
        "def z : Nat := c where c : Nat := c\n",
        "zero-param self-referencing where helper",
        &["unsupported `where`/`let rec`", "`c`", "no parameters"],
    );
    assert!(
        err.contains("self-recursive"),
        "should name the self-recursive shape, got: {err}"
    );
}

/// Duplicate helper names in one where block fail loud.
#[test]
fn test_where_duplicate_names_fail_loud() {
    expect_rejected(
        "def du (n : Nat) : Nat := g n where g (m : Nat) : Nat := m\n  \
         g (m : Nat) : Nat := m + 1\n",
        "duplicate where decl names",
        &["where", "duplicate", "`g`"],
    );
}

// =========================================================================
// 3. REGRESSION — NO `where` decl can register with a sorry axiom
// =========================================================================

/// Every `where`-shaped source either fails LOUD or registers with a
/// sorry-free transitive axiom closure for every declaration in the module.
/// This is the d04 ratchet: the synthetic-`sorry` fallback must never come
/// back in any disguise.
#[test]
fn test_no_where_decl_ever_registers_with_sorry_axiom() {
    let sources: &[&str] = &[
        // positives (must register sorry-free)
        "def f (n : Nat) : Nat := g n where g (m : Nat) : Nat := m + 1\n",
        "def pc (n : Nat) : Nat := h 1 where h (m : Nat) : Nat := m + n\n",
        "def f3 (n : Nat) : Nat := a n + b n where a (m : Nat) : Nat := m + 1\n  b (m : Nat) : Nat := a m + 1\n",
        "def fw (n : Nat) : Nat := a n where a (m : Nat) : Nat := b m\n  b (m : Nat) : Nat := m + 1\n",
        "def z2 : Nat := c + 1 where c : Nat := 41\n",
        "def nr (n : Nat) : Nat := g n where g (m : Nat) := m + 1\n",
        "def dbl (n : Nat) : Nat := go n where go (m : Nat) : Nat := match m with | 0 => 0 | Nat.succ k => go k + 2\n",
        "theorem tw (n : Nat) : n + 0 = n := pf where pf : n + 0 = n := rfl\n",
        // negatives (must fail loud — checked implicitly: Err is acceptable,
        // a sorry-tainted Ok is not)
        "def z : Nat := c where c : Nat := c\n",
        "def bad (n : Nat) : Nat := g n where g (m : Nat) : Nat := g m\n",
        "def mu (n : Nat) : Nat := p n where p (k : Nat) : Nat := q k\n  q (k : Nat) : Nat := p k\n",
        "def wf (n : Nat) : Nat := g n where g (m : Nat) : Nat := if m = 0 then 0 else g (m - 1)\n",
        "def du (n : Nat) : Nat := g n where g (m : Nat) : Nat := m\n  g (m : Nat) : Nat := m + 1\n",
    ];

    for source in sources {
        // Independently collect the declared top-level names so we can audit
        // whatever actually registered.
        let decl_names: Vec<String> = parse_file(source)
            .map(|decls| {
                decls
                    .iter()
                    .filter_map(|d| match d {
                        SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => {
                            Some(name.clone())
                        }
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();

        match elaborate_module(source) {
            Err(_) => {} // loud failure is always acceptable
            Ok(env) => {
                for name in &decl_names {
                    let Some(deps) = env.axiom_deps(&Name::from_string(name)) else {
                        continue; // not registered — nothing to taint
                    };
                    let tainted: Vec<String> = deps
                        .iter()
                        .map(ToString::to_string)
                        .filter(|d| d.to_lowercase().contains("sorry"))
                        .collect();
                    assert!(
                        tainted.is_empty(),
                        "REGRESSION (audit d04): `{name}` registered with sorry axiom(s) \
                         {tainted:?} from a `where` declaration.\nsource: {source}"
                    );
                }
            }
        }
    }
}
