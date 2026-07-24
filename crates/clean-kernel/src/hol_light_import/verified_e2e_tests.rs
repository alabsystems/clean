// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end verification that the HOL proof-object bridge produces a
//! *genuinely kernel-verified* theorem: a translated HOL proof is added to a
//! real [`Environment`] via the checking `add_decl` path, and its transitive
//! axiom closure is `⊆ FOUNDATIONAL_AXIOMS` (clean's 3 axioms).
//!
//! This is the *endpoint* the Isabelle/HOL native-import bridge feeds into:
//! HOL primitive proof terms (`refl`/`trans`/`mk_comb`/`abs`/`beta`/`assume`/
//! `eq_mp`/`deduct_antisym`/`inst`/`inst_type`) — the same primitives Isabelle's
//! Pure proof terms expand to — translate to CIC proof terms whose only axiom
//! leaves are clean's foundational set. Confirming this closes the soundness
//! question for the bridge: what it emits is `KernelVerified`, not merely
//! `SourceVerified`.

use crate::env::is_foundational_axiom;
use crate::hol_light_import::import_proof_object_json;
use crate::Environment;

/// A `refl` proof object for `x = x` at a type-variable-typed term.
const REFL_X_JSON: &str = r#"{
  "name": "hol.refl_x",
  "proof": { "rule": "refl", "term": { "kind": "var", "name": "x", "ty": { "kind": "var", "name": "a" } } }
}"#;

/// A `trans` proof object composing two `refl`s: `x = x` and `x = x`, yielding
/// `x = x`. Exercises a non-leaf rule that introduces `Eq.trans`.
const TRANS_JSON: &str = r#"{
  "name": "hol.trans_xx",
  "proof": {
    "rule": "trans",
    "left":  { "rule": "refl", "term": { "kind": "var", "name": "x", "ty": { "kind": "var", "name": "a" } } },
    "right": { "rule": "refl", "term": { "kind": "var", "name": "x", "ty": { "kind": "var", "name": "a" } } }
  }
}"#;

/// Translate a HOL proof object, register its support declarations + the
/// theorem into a prelude environment via the *checking* `add_decl`, and return
/// the theorem name on success. Panics with a descriptive message on any
/// kernel rejection — i.e. this only returns if the kernel genuinely accepted
/// the proof.
fn verify_into_prelude(json: &str) -> crate::Name {
    let translated = import_proof_object_json(json).expect("HOL proof object should translate");
    let mut env = Environment::with_prelude();

    for decl in &translated.support_declarations {
        // Support decls may already exist in the prelude (e.g. `Eq`); ignore
        // duplicate-name errors, surface anything else.
        if let Err(e) = env.add_decl(decl.clone()) {
            let msg = format!("{e:?}");
            assert!(
                msg.contains("Duplicate") || msg.contains("already"),
                "support declaration rejected by kernel: {e:?}"
            );
        }
    }

    let thm = translated.theorem_declaration();
    env.add_decl(thm)
        .expect("kernel add_decl must accept the translated HOL proof (KernelVerified)");
    translated.theorem_name
}

#[test]
fn hol_refl_proof_is_kernel_verified_to_three_axioms() {
    let name = verify_into_prelude(REFL_X_JSON);

    // Rebuild the environment to inspect the axiom closure of the accepted thm.
    let translated = import_proof_object_json(REFL_X_JSON).unwrap();
    let mut env = Environment::with_prelude();
    for decl in &translated.support_declarations {
        let _ = env.add_decl(decl.clone());
    }
    env.add_decl(translated.theorem_declaration()).unwrap();

    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should be computable for an added theorem");
    // Every axiom in the transitive closure must be foundational (⊆ the 3 + prims).
    for ax in &deps {
        assert!(
            is_foundational_axiom(ax),
            "refl proof reached a NON-foundational axiom {ax:?} — not reducible to clean's 3 axioms"
        );
    }
}

#[test]
fn hol_trans_proof_is_kernel_verified_to_three_axioms() {
    let name = verify_into_prelude(TRANS_JSON);

    let translated = import_proof_object_json(TRANS_JSON).unwrap();
    let mut env = Environment::with_prelude();
    for decl in &translated.support_declarations {
        let _ = env.add_decl(decl.clone());
    }
    env.add_decl(translated.theorem_declaration()).unwrap();

    let deps = env.axiom_deps(&name).expect("axiom_deps computable");
    for ax in &deps {
        assert!(
            is_foundational_axiom(ax),
            "trans proof reached non-foundational axiom {ax:?}"
        );
    }
}

// ── Remaining primitive inference rules of HOL/Isabelle's kernel ──
//
// Together with refl/trans above, these are the full primitive basis every
// Isabelle/HOL proof bottoms out in. Each is checked to (a) translate, (b) be
// accepted by the kernel's `add_decl`, and (c) have axiom closure ⊆ the 3.

const BETA_JSON: &str = r#"{
  "name": "hol.beta_id",
  "proof": {
    "rule": "beta",
    "binder": { "name": "x", "ty": { "kind": "var", "name": "a" } },
    "body": { "kind": "var", "name": "x", "ty": { "kind": "var", "name": "a" } },
    "argument": { "kind": "var", "name": "y", "ty": { "kind": "var", "name": "a" } }
  }
}"#;

const ABS_JSON: &str = r#"{
  "name": "hol.abs_id",
  "proof": {
    "rule": "abs",
    "binder": { "name": "x", "ty": { "kind": "var", "name": "a" } },
    "proof": { "rule": "refl", "term": { "kind": "var", "name": "x", "ty": { "kind": "var", "name": "a" } } }
  }
}"#;

const MKCOMB_JSON: &str = r#"{
  "name": "hol.mk_comb_ff",
  "proof": {
    "rule": "mk_comb",
    "function": { "rule": "refl", "term": { "kind": "var", "name": "f",
      "ty": { "kind": "fun", "domain": { "kind": "var", "name": "a" }, "codomain": { "kind": "var", "name": "b" } } } },
    "argument": { "rule": "refl", "term": { "kind": "var", "name": "x", "ty": { "kind": "var", "name": "a" } } }
  }
}"#;

const ASSUME_JSON: &str = r#"{
  "name": "hol.assume_p",
  "proof": { "rule": "assume", "proposition": { "kind": "var", "name": "p", "ty": { "kind": "bool" } } }
}"#;

fn assert_kernel_verified_to_three_axioms(json: &str) {
    let name = verify_into_prelude(json);
    let translated = import_proof_object_json(json).unwrap();
    let mut env = Environment::with_prelude();
    for decl in &translated.support_declarations {
        let _ = env.add_decl(decl.clone());
    }
    env.add_decl(translated.theorem_declaration()).unwrap();
    let deps = env.axiom_deps(&name).expect("axiom_deps computable");
    for ax in &deps {
        assert!(
            is_foundational_axiom(ax),
            "proof reached non-foundational axiom {ax:?}"
        );
    }
}

#[test]
fn hol_beta_proof_is_kernel_verified() {
    assert_kernel_verified_to_three_axioms(BETA_JSON);
}

#[test]
fn hol_abs_proof_is_kernel_verified() {
    assert_kernel_verified_to_three_axioms(ABS_JSON);
}

#[test]
fn hol_mk_comb_proof_is_kernel_verified() {
    assert_kernel_verified_to_three_axioms(MKCOMB_JSON);
}

#[test]
fn hol_assume_proof_is_kernel_verified() {
    assert_kernel_verified_to_three_axioms(ASSUME_JSON);
}

/// The **complete** primitive inference basis of HOL/Isabelle — every rule a
/// Pure/HOL proof bottoms out in — translates to a kernel-accepted proof term
/// reducible to clean's 3 axioms. This is the soundness foundation of native
/// Isabelle verification: anything built from these primitives is `KernelVerified`.
///
/// Covers **all 10** HolProof rules: the term-level six plus `eq_mp`
/// (modus-ponens transport), `deduct_antisym` (propositional-extensionality
/// deduction), `inst` (term instantiation), and `inst_type` (type
/// instantiation, handled by pushing the substitution into the proof leaves).
#[test]
fn full_primitive_basis_is_kernel_verified() {
    for json in [
        REFL_X_JSON,
        TRANS_JSON,
        BETA_JSON,
        MKCOMB_JSON,
        ABS_JSON,
        ASSUME_JSON,
        EQMP_JSON,
        DEDUCT_JSON,
        INST_JSON,
        INSTTYPE_JSON,
    ] {
        // Panics unless the kernel accepts the proof AND its axiom closure ⊆ 3.
        assert_kernel_verified_to_three_axioms(json);
    }
}

#[test]
fn hol_inst_type_proof_is_kernel_verified() {
    assert_kernel_verified_to_three_axioms(INSTTYPE_JSON);
}

const EQMP_JSON: &str = r#"{"name":"hol.eq_mp","proof":{"rule":"eq_mp",
  "equality":{"rule":"refl","term":{"kind":"var","name":"p","ty":{"kind":"bool"}}},
  "proof":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}}}}"#;
const DEDUCT_JSON: &str = r#"{"name":"hol.deduct","proof":{"rule":"deduct_antisym",
  "left":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}},
  "right":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}}}}"#;
const INST_JSON: &str = r#"{"name":"hol.inst","proof":{"rule":"inst",
  "proof":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}},
  "substitutions":[{"variable":{"name":"x","ty":{"kind":"var","name":"a"}},"replacement":{"kind":"var","name":"y","ty":{"kind":"var","name":"a"}}}]}}"#;
/// INST_TYPE: instantiate `'a := bool` in `x = x`, yielding `p = p` at `bool`.
const INSTTYPE_JSON: &str = r#"{"name":"hol.inst_type","proof":{"rule":"inst_type",
  "proof":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}},
  "substitutions":[{"variable":"a","replacement":{"kind":"bool"}}]}}"#;
