// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! I1 — HEADER AGREEMENT: the declaration the kernel holds must be the one
//! everything else was elaborated against.
//!
//! Ruling of record: `docs/design/2026-08-05-i1-ruling-header-elaboration.md`
//! (Trust superproject). Staging a signature buys source-order independence
//! only if the signature is the one that finally gets registered. If it is not,
//! some other declaration in the batch resolved a name against a type the
//! kernel does not hold — the same source-to-kernel fidelity failure the ruling
//! is about, arriving one step later.
//!
//! This is not hypothetical. `elab_def_body.rs` unifies the body's inferred type
//! against the DECLARED type specifically to solve level constraints (its own
//! comment names `def foo : Type → Prop := Nonempty`, which needs `u_0 = 1`),
//! and `elab_decl_value.rs` computes a definition's surviving universe
//! parameters from `collect_def_level_params(ty) ∪ collect_def_level_params
//! (val)`. A header-only pass sees only the type. So a header and its
//! registered declaration CAN legitimately differ, silently, in exactly the
//! signature the kernel gets.
//!
//! Two tests, and the pair is the point:
//!
//!   1. `test_a_registered_signature_that_differs_from_its_header_is_refused` —
//!      the MUST-FAIL control. When the two disagree, the batch is REFUSED and
//!      nothing is registered. Accepting would mean publishing a declaration
//!      under a signature its users never saw.
//!   2. `test_the_same_program_with_explicit_levels_is_accepted` — the control
//!      that "refuse everything" cannot pass. Write the universes explicitly
//!      and the header is exact, so the batch must go through.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

struct Checked {
    env: Environment,
    committed: bool,
    rejections: String,
}

fn check(source: &str) -> Checked {
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    Checked {
        committed: outcome.committed,
        rejections: outcome.render_rejections(),
        env,
    }
}

/// A declaration whose staged signature and registered signature agree is
/// published; one whose signatures disagree refuses the batch.
///
/// The assertion is deliberately written as an INVARIANT rather than as a
/// prediction about one fixture: whatever the batch commits, every staged
/// header must match the constant registered under its name. A checker that
/// stops enforcing this passes only by also failing the control below.
#[test]
fn test_a_registered_signature_that_differs_from_its_header_is_refused() {
    // `Nonempty : Sort u -> Prop`, so `bare`'s declared `Type -> Prop` forces
    // `u = 1` — and that solution comes from unifying against the BODY. An
    // earlier declaration names `bare`, so `bare` is genuinely staged first.
    let checked = check(
        "\
set_option autoImplicit false
def early (a : Type) : Prop := bare a
def bare : Type → Prop := Nonempty
",
    );
    if checked.committed {
        // Accepted — then the published signature must be exactly the staged
        // one. Header agreement is checked inside the batch; this re-checks the
        // consequence from outside, so a bug in the check itself is still
        // caught.
        let bare = checked
            .env
            .get_const(&Name::from_string("bare"))
            .expect("`bare` must be registered when the batch commits");
        let early = checked
            .env
            .get_const(&Name::from_string("early"))
            .expect("`early` must be registered when the batch commits");
        let mut referenced = std::collections::HashSet::new();
        early
            .value
            .as_ref()
            .expect("`early` must have a value")
            .collect_constants_into(&mut referenced);
        assert!(
            referenced.contains(&Name::from_string("bare")),
            "`early` no longer mentions `bare`, so this fixture stopped testing \
             the forward reference it was written for"
        );
        assert!(
            bare.level_params.is_empty(),
            "`bare` published with level parameters {:?}, but `early` was \
             elaborated against a header. If those differ, `early` resolved \
             `bare` at a signature the kernel does not hold — that is a \
             source-to-kernel fidelity failure, and the batch must be REFUSED \
             with HeaderTypeDivergence rather than published.",
            bare.level_params
        );
    } else {
        // Refused — then it must be refused CLEANLY: nothing registered.
        assert!(
            checked.rejections.contains("error:"),
            "refused with no diagnostic at all; a refusal must say what to do"
        );
        for name in ["early", "bare"] {
            assert!(
                checked.env.get_const(&Name::from_string(name)).is_none(),
                "`{name}` reached the environment from a REFUSED batch"
            );
        }
    }
}

/// CONTROL — "refuse everything" cannot pass this. With the universe written
/// explicitly there is nothing for the body to solve, the header is exact, and
/// the forward reference must go through.
#[test]
fn test_the_same_program_with_explicit_levels_is_accepted() {
    let checked = check(
        "\
set_option autoImplicit false
def early (a : Type) : Prop := bare a
def bare (a : Type) : Prop := Nonempty a
",
    );
    assert!(
        checked.committed,
        "REJECTED a program whose header is exact — the declared type mentions \
         no universe the body has to solve, so the staged and registered \
         signatures cannot differ. Header agreement must refuse DIVERGENCE, not \
         forward references: {}",
        checked.rejections
    );
    let bare = checked
        .env
        .get_const(&Name::from_string("bare"))
        .expect("`bare` must be registered");
    assert!(
        bare.value.is_some(),
        "`bare` was published without a value — that is a staged header, not a \
         definition"
    );
}
