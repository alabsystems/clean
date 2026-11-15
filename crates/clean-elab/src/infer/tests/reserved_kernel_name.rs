// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A source declaration may not take a name reserved for a kernel-owned
//! axiom — a foundational axiom (`propext`, `Quot.sound`, `Classical.choice`,
//! the `Quot` primitives) or a trust marker (`sorry`, `sorryAx`,
//! `trustedArith`, `trustedAy`) — structurally OR by printed form
//! (`ElabCtx::check_not_reserved_kernel_name`, with the registration backstop
//! in `register::register_elab_result`).
//!
//! # The failure, measured before the fix (origin/main 4bacc8770)
//!
//! ```text
//! axiom «Quot.sound» : False           clean check: exit 0, status pass,
//! theorem bad : False := «Quot.sound»  sorry_axioms 0, assumptions []
//! ```
//!
//! `«Quot.sound»` is ONE component that prints `Quot.sound`; the axiom
//! classifier compared printed names, so the proof of `False` was credited as
//! resting on the foundation. The same held for `«Classical.choice»`,
//! `«Eq.refl»`, `«WellFounded.fix»`, `«Quot.lift»` and `«String.decEq»`.
//! The classifier is structural and statement-exact now (clean-kernel
//! `tests_axiom_audit.rs`); these tests pin that the NAMES are refused at the
//! declaration too, with a clear error, in every declaration position, while
//! ordinary names that merely contain a reserved spelling stay declarable.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Elaborate `src` declaration by declaration as `clean check` does, over the
/// builtin prelude. Returns `(env, per-declaration error text)`; `None` for a
/// declaration that elaborated (every leaf registered).
fn elab(src: &str) -> (Environment, Vec<Option<String>>) {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("must parse: {e}\n{src}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                let failure = leaves.iter().find_map(|leaf| match leaf {
                    ElabResult::Failed { error, .. } => Some(error.to_string()),
                    _ => None,
                });
                verdicts.push(failure);
            }
            Err(error) => verdicts.push(Some(error.to_string())),
        }
    }
    (env, verdicts)
}

fn assert_reserved(src: &str, rendered: &str) {
    let (env, verdicts) = elab(src);
    let first = verdicts
        .first()
        .cloned()
        .flatten()
        .unwrap_or_else(|| panic!("the reserved declaration must be refused:\n{src}"));
    assert!(
        first.contains("is reserved") && first.contains(rendered),
        "wrong refusal for\n{src}\n  got: {first}"
    );
    // The kernel's own foundations are untouched.
    for foundation in ["propext", "Quot.sound", "Classical.choice"] {
        assert!(
            env.is_canonical_foundational_axiom(&Name::from_string(foundation)),
            "{foundation} stays the kernel's canonical declaration"
        );
    }
}

#[test]
fn printed_form_foundation_spoofs_are_refused() {
    for (printed, statement) in [
        ("Quot.sound", "False"),
        ("Classical.choice", "False"),
        ("Quot.lift", "(0 : Nat) = 1"),
        ("Quot.mk", "False"),
        ("Quot.ind", "False"),
        ("propext", "False"),
        ("sorryAx", "False"),
        ("trustedAy", "False"),
    ] {
        let src = format!("axiom «{printed}» : {statement}\n");
        assert_reserved(&src, printed);
    }
    // Nothing downstream is credited through the refused name: the citation
    // resolves to the kernel's own declaration, whose statement is not `False`.
    for printed in ["Quot.sound", "Classical.choice", "propext"] {
        let src = format!("axiom «{printed}» : False\ntheorem bad : False := «{printed}»\n");
        let (_, verdicts) = elab(&src);
        assert!(
            verdicts.iter().all(Option::is_some),
            "no declaration of\n{src}\nmay elaborate: {verdicts:?}"
        );
    }
}

#[test]
fn reserved_names_are_refused_in_every_declaration_position() {
    let cases = [
        // theorem / def / opaque / instance names, printed-form spoofs
        (
            "theorem «Quot.sound» : True := True.intro\ntheorem ok : True := «Quot.sound»\n",
            "«Quot.sound»",
        ),
        ("def «Classical.choice» : Nat := 1\ntheorem ok : True := True.intro\n", "«Classical.choice»"),
        ("opaque «Classical.choice» : Nat\ntheorem ok : True := True.intro\n", "«Classical.choice»"),
        // private and protected change nothing
        ("private axiom «Quot.sound» : False\ntheorem bad : False := «Quot.sound»\n", "«Quot.sound»"),
        // `_root_` from inside a namespace
        (
            "namespace Foo\naxiom _root_.sorryAx : False\nend Foo\ntheorem bad : False := sorryAx\n",
            "sorryAx",
        ),
        (
            "namespace Foo\naxiom _root_.trustedAy : False\nend Foo\ntheorem bad : False := trustedAy\n",
            "trustedAy",
        ),
        // structural: a namespace that assembles the kernel's name
        ("namespace Quot\naxiom sound : False\nend Quot\ntheorem bad : False := Quot.sound\n", "Quot.sound"),
        // mutual members
        (
            "mutual\ndef «Quot.mk» : Nat → Nat\n  | n => n\nend\ntheorem ok : True := True.intro\n",
            "«Quot.mk»",
        ),
    ];
    for (src, rendered) in cases {
        let (_, verdicts) = elab(src);
        let first = verdicts
            .iter()
            .flatten()
            .next()
            .unwrap_or_else(|| panic!("a reserved name must be refused:\n{src}"));
        assert!(
            first.contains("is reserved") && first.contains(rendered),
            "wrong refusal for\n{src}\n  got: {first}"
        );
    }
}

/// The boundary, in equal weight: names that only CONTAIN a reserved spelling,
/// and the legacy whitelist names that are not kernel axioms at all, stay
/// declarable (Lean accepts all of them). A user `axiom proofIrrel` is an
/// ordinary domain axiom — disclosed by every closure report, never refused.
#[test]
fn names_that_only_resemble_reserved_ones_stay_declarable() {
    for src in [
        "def «propext.x» : Nat := 1\ntheorem ok : «propext.x» = 1 := rfl\n",
        "axiom «sorryAx.» : False\n",
        "axiom proofIrrel : False\ntheorem bad : False := proofIrrel\n",
        "axiom «Eq.refl» : False\n",
        "axiom «WellFounded.fix» : False\n",
        "axiom «String.decEq» : (1 : Nat) = 2\n",
        "namespace Foo\naxiom propext : False\nend Foo\n",
        "def trustedAyCount : Nat := 0\n",
    ] {
        let (env, verdicts) = elab(src);
        assert!(
            verdicts.iter().all(Option::is_none),
            "must stay declarable:\n{src}\n{verdicts:?}"
        );
        // Whatever was declared, the foundations are still the kernel's.
        assert!(env.is_canonical_foundational_axiom(&Name::from_string("propext")));
    }
    // And the legacy names are DISCLOSED, never classified foundational.
    let (env, _) = elab("axiom proofIrrel : False\ntheorem bad : False := proofIrrel\n");
    let deps = env
        .axiom_deps(&Name::from_string("bad"))
        .expect("bad is registered");
    assert!(deps.contains(&Name::from_string("proofIrrel")), "{deps:?}");
}

#[test]
fn the_refusal_names_the_spoof_unambiguously() {
    let error = ElabError::ReservedKernelName {
        name: Name::anon().str("Quot.sound").to_unambiguous_string(),
        printed: Name::anon().str("Quot.sound").to_string(),
    };
    let text = error.to_string();
    assert!(text.contains("`«Quot.sound»` is reserved"), "{text}");
    assert!(text.contains("prints as `Quot.sound`"), "{text}");
}
