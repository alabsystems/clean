// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `deriving DecidableEq` over an APPLIED type-constructor field (`xs : List T`).
//!
//! Before the parametric `instDecidableEqList` landed in the prelude and
//! `resolve_field_instance` learned the applied shape, `resolve_field_instance`
//! opened with `bare_const_name(field_ty)?` — so `List Nat` was refused before
//! any instance was consulted and the whole derive fail-closed with
//! `Unsupported: … has no closed proof-producing construction for this
//! parameter/field shape`. Nested STRUCT fields already worked; only the applied
//! constructor had no path.
//!
//! What is pinned here:
//!   - a struct with a `List Nat` field derives, kernel-checks, and has an EMPTY
//!     axiom closure (no `sorry`, no `sorryAx`);
//!   - the same for a `List OtherStruct` field, whose element instance is itself
//!     a derived one — so the resolver composes derived with prelude instances;
//!   - the instance COMPUTES: `if a = b then 1 else 0` reduces to the right
//!     `Nat` on equal, element-differing, and length-differing lists. A term
//!     that merely type-checks is not a decision procedure;
//!   - `List (List Nat)` nests;
//!   - the refusal is NOT weakened: a field whose element type carries no
//!     `DecidableEq` still fails closed.

use crate::elaborate_decl_and_register;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, TypeChecker};
use clean_parser::parse_decl;

/// Whether `e` references a `sorry`/`sorryAx` constant anywhere.
fn mentions_sorry(e: &Expr) -> bool {
    fn name_is_sorry(n: &Name) -> bool {
        let s = n.to_string();
        s == "sorry" || s == "sorryAx" || s.ends_with(".sorry") || s.ends_with(".sorryAx")
    }
    match e.kind() {
        ExprKind::Const(n, _) => name_is_sorry(n),
        ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => mentions_sorry(t) || mentions_sorry(b),
        _ => false,
    }
}

/// Elaborate and register each declaration source in order, failing loudly.
fn env_with(decls: &[&str]) -> Environment {
    let mut env = Environment::with_prelude();
    for src in decls {
        let decl = parse_decl(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|e| panic!("register `{src}`: {e:?}"));
    }
    env
}

/// The derived instance is present, sorry-free, axiom-free, and infer-types
/// against its own declared type.
fn assert_sound_instance(env: &Environment, inst_name: &str) {
    let inst = Name::from_string(inst_name);
    let info = env
        .get_const(&inst)
        .unwrap_or_else(|| panic!("{inst_name} must be registered"));
    let value = info.value.as_ref().expect("instance has a value");

    assert!(
        !mentions_sorry(value),
        "{inst_name} must NOT emit sorry/sorryAx"
    );
    let deps = env
        .axiom_deps(&inst)
        .unwrap_or_else(|| panic!("{inst_name} present for axiom_deps"));
    assert!(
        deps.is_empty(),
        "{inst_name} must have EMPTY axiom_deps, got {deps:?}"
    );

    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("{inst_name} value must infer-type: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{inst_name}: inferred type must match the declared DecidableEq type"
    );
}

/// Evaluate `if a = b then (1:Nat) else 0` through the derived instance and
/// WHNF the result to a `Nat` literal's debug form.
fn pick_reduces(env: &Environment, a_src: &str, b_src: &str) -> String {
    let mut env = env.clone();
    let d = parse_decl(&format!(
        "def __pick : Nat := if ({a_src} = {b_src}) then 1 else 0"
    ))
    .expect("parse pick");
    elaborate_decl_and_register(&mut env, &d).expect("register pick");
    let pick = Expr::const_(Name::from_string("__pick"), vec![]);
    let tc = TypeChecker::new(&env);
    format!("{:?}", tc.whnf(&pick).kind())
}

const PB_TERM: &str = r"structure PbTerm where
  coeff : Nat
  lit : Nat
deriving DecidableEq";

const PB_CONSTRAINT: &str = r"structure PbConstraint where
  terms : List PbTerm
  bound : Nat
deriving DecidableEq";

// ---------------------------------------------------------------------------
// 1. A `List Nat` field
// ---------------------------------------------------------------------------

#[test]
fn list_nat_field_derives_sound_decidable_eq() {
    let env = env_with(&[r"structure SNat where
  xs : List Nat
deriving DecidableEq"]);
    assert_sound_instance(&env, "instSNatDecidableEq");
}

// ---------------------------------------------------------------------------
// 2. A `List OtherStruct` field — the z4 `PbConstraint` shape
// ---------------------------------------------------------------------------

#[test]
fn list_of_struct_field_derives_sound_decidable_eq() {
    let env = env_with(&[PB_TERM, PB_CONSTRAINT]);
    assert_sound_instance(&env, "instPbTermDecidableEq");
    assert_sound_instance(&env, "instPbConstraintDecidableEq");
}

// ---------------------------------------------------------------------------
// 3. It COMPUTES
// ---------------------------------------------------------------------------

#[test]
fn list_nat_field_instance_decides_correctly() {
    let env = env_with(&[r"structure SNat where
  xs : List Nat
deriving DecidableEq"]);

    // Equal lists ⇒ true branch ⇒ 1.
    assert!(
        pick_reduces(&env, "SNat.mk [1, 2]", "SNat.mk [1, 2]").contains("Small(1)"),
        "equal `List Nat` fields must take the true branch (1)"
    );
    // Same length, different element ⇒ 0.
    assert!(
        pick_reduces(&env, "SNat.mk [1, 2]", "SNat.mk [1, 3]").contains("Small(0)"),
        "a differing element must take the false branch (0)"
    );
    // Different length ⇒ 0 (the nil/cons noConfusion arms).
    assert!(
        pick_reduces(&env, "SNat.mk [1]", "SNat.mk [1, 2]").contains("Small(0)"),
        "a differing length must take the false branch (0)"
    );
    // Both empty ⇒ 1 (the nil/nil arm).
    assert!(
        pick_reduces(&env, "SNat.mk []", "SNat.mk []").contains("Small(1)"),
        "two empty lists must take the true branch (1)"
    );
}

#[test]
fn list_of_struct_field_instance_decides_correctly() {
    let env = env_with(&[PB_TERM, PB_CONSTRAINT]);

    assert!(
        pick_reduces(
            &env,
            "PbConstraint.mk [PbTerm.mk 1 2] 3",
            "PbConstraint.mk [PbTerm.mk 1 2] 3"
        )
        .contains("Small(1)"),
        "equal `List PbTerm` fields must decide true"
    );
    assert!(
        pick_reduces(
            &env,
            "PbConstraint.mk [PbTerm.mk 1 2] 3",
            "PbConstraint.mk [PbTerm.mk 1 9] 3"
        )
        .contains("Small(0)"),
        "a differing element FIELD must decide false"
    );
}

// ---------------------------------------------------------------------------
// 4. Nesting
// ---------------------------------------------------------------------------

#[test]
fn nested_list_field_derives_sound_decidable_eq() {
    let env = env_with(&[r"structure Matrix where
  rows : List (List Nat)
deriving DecidableEq"]);
    assert_sound_instance(&env, "instMatrixDecidableEq");
    assert!(
        pick_reduces(&env, "Matrix.mk [[1], [2]]", "Matrix.mk [[1], [2]]").contains("Small(1)"),
        "equal nested lists must decide true"
    );
    assert!(
        pick_reduces(&env, "Matrix.mk [[1], [2]]", "Matrix.mk [[1], [3]]").contains("Small(0)"),
        "a differing nested element must decide false"
    );
}

// ---------------------------------------------------------------------------
// 5. The refusal is NOT weakened
// ---------------------------------------------------------------------------

/// A `List T` field whose ELEMENT type carries no `DecidableEq` must still fail
/// closed with `Unsupported` — the applied-shape resolver requires the
/// argument's own instance and never manufactures one.
#[test]
fn list_of_undecidable_element_still_fails_closed() {
    let mut env = Environment::with_prelude();
    for src in [
        // `NoDecEq` derives nothing, so there is no `DecidableEq NoDecEq`.
        r"structure NoDecEq where
  a : Nat",
        r"structure HasNoDecEqList where
  xs : List NoDecEq
deriving DecidableEq",
    ] {
        let decl = parse_decl(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        let result = elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|e| panic!("the structure itself registers: {e:?}"));
        if src.contains("deriving") {
            // Lean declares the structure before running the handler, so the
            // refusal is a failed leaf BESIDE the structure, not instead of it.
            let mut leaves = Vec::new();
            result.leaf_decls(&mut leaves);
            let msg = leaves
                .iter()
                .find_map(|leaf| match leaf {
                    crate::ElabResult::Failed { error, .. } => Some(format!("{error:?}")),
                    _ => None,
                })
                .expect(
                    "deriving DecidableEq over `List NoDecEq` must fail closed, not synthesize a sorry",
                );
            assert!(
                msg.contains("no closed proof-producing construction"),
                "expected the fail-closed Unsupported refusal, got {msg}"
            );
        }
    }
    assert!(env
        .get_const(&Name::from_string("HasNoDecEqList"))
        .is_some());
    assert!(
        env.get_const(&Name::from_string("instHasNoDecEqListDecidableEq"))
            .is_none(),
        "no instance may be registered for the refused shape"
    );
}

// ---------------------------------------------------------------------------
// 6. The prelude instance itself resolves through ordinary synthesis
// ---------------------------------------------------------------------------

/// `Decidable (xs = ys)` for `List Nat` now has a candidate: the `decEq` bridge
/// composed with the parametric `instDecidableEqList`. This is probe 2 of the
/// motivating measurement, as a unit test.
#[test]
fn decidable_eq_on_a_bare_list_literal_resolves_and_reduces() {
    let env = env_with(&[]);
    assert!(
        env.is_instance(&Name::from_string("instDecidableEqList")),
        "with_prelude must register the parametric List DecidableEq instance"
    );
    assert!(
        pick_reduces(&env, "([1, 2] : List Nat)", "([1, 2] : List Nat)").contains("Small(1)"),
        "`if ([1,2] = [1,2]) then 1 else 0` must reduce to 1"
    );
    assert!(
        pick_reduces(&env, "([1, 2] : List Nat)", "([1, 3] : List Nat)").contains("Small(0)"),
        "`if ([1,2] = [1,3]) then 1 else 0` must reduce to 0"
    );
}
