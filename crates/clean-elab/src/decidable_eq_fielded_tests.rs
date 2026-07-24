// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness + behavior tests for the sorry-free fielded `DecidableEq` derive
//! (Track L, part 2).
//!
//! These go through the FULL surface pipeline (`elaborate_decl_and_register`)
//! and assert:
//!   - the derived `instColorDecidableEq` registers and INFER-TYPES against the
//!     kernel-generated `Color.casesOn` / `Color.noConfusion`,
//!   - it contains NO `sorry` / `sorryAx` constant and its `axiom_deps` is
//!     EMPTY,
//!   - it actually DECIDES: `if a = b then 1 else 0` reduces to the right Nat.

use crate::elaborate_decl_and_register;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, TypeChecker};
use clean_parser::parse_decl;

fn color_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "inductive Color where \
         | rgb : Nat -> Color \
         | named : Nat -> Color \
         deriving DecidableEq",
    )
    .expect("parse Color");
    elaborate_decl_and_register(&mut env, &decl).expect("register Color + derive DecidableEq");
    env
}

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

#[test]
fn fielded_decidable_eq_registers_and_infers() {
    let env = color_env();
    let inst = Name::from_string("instColorDecidableEq");
    let info = env
        .get_const(&inst)
        .expect("instColorDecidableEq must be registered");
    let value = info.value.as_ref().expect("instance has a value");

    // No `sorry` anywhere in the derived term.
    assert!(
        !mentions_sorry(value),
        "fielded DecidableEq derive must NOT emit sorry/sorryAx"
    );

    // Infer-types against the kernel (drives Color.casesOn / noConfusion).
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("instColorDecidableEq value must infer-type");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared DecidableEq Color type"
    );
}

#[test]
fn fielded_decidable_eq_has_no_sorry_axioms() {
    let env = color_env();
    let inst = Name::from_string("instColorDecidableEq");
    let deps = env
        .axiom_deps(&inst)
        .expect("instColorDecidableEq present for axiom_deps");
    assert!(
        deps.is_empty(),
        "fielded DecidableEq must have EMPTY axiom_deps (no sorry/trust markers), got {deps:?}"
    );
}

/// Evaluate `if a = b then (1:Nat) else 0` through the derived DecidableEq and
/// WHNF the result to a Nat literal.
fn pick_reduces(env: &Environment, a_src: &str, b_src: &str) -> String {
    let mut env = env.clone();
    let d = parse_decl(&format!(
        "def __pick : Nat := if ({a_src} = {b_src}) then 1 else 0"
    ))
    .expect("parse pick");
    elaborate_decl_and_register(&mut env, &d).expect("register pick");
    let pick = Expr::const_(Name::from_string("__pick"), vec![]);
    let tc = TypeChecker::new(&env);
    let whnf = tc.whnf(&pick);
    format!("{:?}", whnf.kind())
}

#[test]
fn fielded_decidable_eq_decides_correctly() {
    let env = color_env();
    // same ctor + same field ⇒ true branch ⇒ 1
    assert!(
        pick_reduces(&env, "Color.rgb 5", "Color.rgb 5").contains("Small(1)"),
        "equal values must take the true branch (1)"
    );
    // same ctor, different field ⇒ 0
    assert!(
        pick_reduces(&env, "Color.rgb 1", "Color.rgb 2").contains("Small(0)"),
        "distinct fields must take the false branch (0)"
    );
    // different ctor ⇒ 0
    assert!(
        pick_reduces(&env, "Color.rgb 1", "Color.named 1").contains("Small(0)"),
        "distinct constructors must take the false branch (0)"
    );
    // other ctor, same field ⇒ 1
    assert!(
        pick_reduces(&env, "Color.named 9", "Color.named 9").contains("Small(1)"),
        "equal named values must take the true branch (1)"
    );
}

/// Build `namespace TrustIr inductive Permission ... deriving DecidableEq end`,
/// mirroring the real `TrustIr/State/Permission.lean` enum: a NAMESPACED
/// inductive with one fielded ctor (`sharedBorrow : Nat -> Permission`). The
/// fielded derive used to name ctors from the SHORT inductive segment
/// (`Permission.owned`) instead of the registered fully-qualified name
/// (`TrustIr.Permission.owned`), so the instance failed the kernel check with
/// `Unknown constant: Permission.owned`. This env construction must succeed.
fn permission_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "namespace TrustIr \
         inductive Permission where \
         | owned : Permission \
         | uniqueBorrow : Permission \
         | sharedBorrow : Nat -> Permission \
         | rawPtr : Permission \
         | arcRef : Permission \
         deriving DecidableEq \
         end TrustIr",
    )
    .expect("parse namespaced Permission");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("register TrustIr.Permission + derive DecidableEq (fully-qualified ctor names)");
    env
}

#[test]
fn namespaced_fielded_decidable_eq_uses_qualified_ctor_names() {
    let env = permission_env();
    let inst = Name::from_string("instTrustIr.PermissionDecidableEq");
    let info = env
        .get_const(&inst)
        .expect("instTrustIr.PermissionDecidableEq must be registered");
    let value = info.value.as_ref().expect("instance has a value");

    // No `sorry` — the fielded path builds a real casesOn/congrArg/noConfusion term.
    assert!(
        !mentions_sorry(value),
        "namespaced fielded DecidableEq must NOT emit sorry/sorryAx"
    );

    // Empty axiom_deps — fully kernel-checked, no trust markers.
    let deps = env
        .axiom_deps(&inst)
        .expect("instTrustIr.PermissionDecidableEq present for axiom_deps");
    assert!(
        deps.is_empty(),
        "namespaced fielded DecidableEq must have EMPTY axiom_deps, got {deps:?}"
    );

    // Infer-types against the kernel: this is what previously failed with
    // `Unknown constant: Permission.owned` when the ctor name dropped the
    // `TrustIr.` namespace prefix.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("instTrustIr.PermissionDecidableEq value must infer-type");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared DecidableEq TrustIr.Permission type"
    );
}

#[test]
fn namespaced_fielded_decidable_eq_decides_correctly() {
    let env = permission_env();
    // nullary ctor reflexivity
    assert!(
        pick_reduces(&env, "TrustIr.Permission.owned", "TrustIr.Permission.owned")
            .contains("Small(1)"),
        "equal nullary ctors must take the true branch (1)"
    );
    // distinct nullary ctors
    assert!(
        pick_reduces(
            &env,
            "TrustIr.Permission.owned",
            "TrustIr.Permission.rawPtr"
        )
        .contains("Small(0)"),
        "distinct nullary ctors must take the false branch (0)"
    );
    // fielded ctor, equal field
    assert!(
        pick_reduces(
            &env,
            "TrustIr.Permission.sharedBorrow 3",
            "TrustIr.Permission.sharedBorrow 3"
        )
        .contains("Small(1)"),
        "equal sharedBorrow counts must take the true branch (1)"
    );
    // fielded ctor, distinct field
    assert!(
        pick_reduces(
            &env,
            "TrustIr.Permission.sharedBorrow 3",
            "TrustIr.Permission.sharedBorrow 4"
        )
        .contains("Small(0)"),
        "distinct sharedBorrow counts must take the false branch (0)"
    );
}

/// Build `namespace TrustIr structure ValueId where index : Nat deriving
/// DecidableEq end`, mirroring the real `TrustIr/Basic.lean` `ValueId` wrapper
/// struct. The single-field STRUCTURE `DecidableEq` derive used to emit a
/// `sorry`-based instance value (`derive_decidable_eq` in `infer/derive/
/// structure.rs`), so `decide (a = b)` / `a == b` on `ValueId` fell back to
/// `sorry`. Track TT routes the monomorphic struct case through the sound
/// `decidable_eq_struct_value` builder. This env construction must succeed.
fn value_id_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "namespace TrustIr \
         structure ValueId where \
         index : Nat \
         deriving DecidableEq \
         end TrustIr",
    )
    .expect("parse namespaced ValueId struct");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("register TrustIr.ValueId + derive DecidableEq (sound, sorry-free)");
    env
}

#[test]
fn single_field_struct_decidable_eq_is_sound_and_sorry_free() {
    let env = value_id_env();
    let inst = Name::from_string("instTrustIr.ValueIdDecidableEq");
    let info = env
        .get_const(&inst)
        .expect("instTrustIr.ValueIdDecidableEq must be registered");
    let value = info.value.as_ref().expect("instance has a value");

    // The single-field struct derive must build a REAL term — no sorry/sorryAx.
    assert!(
        !mentions_sorry(value),
        "single-field struct DecidableEq derive must NOT emit sorry/sorryAx"
    );

    // Empty axiom_deps — fully kernel-checked, no trust markers.
    let deps = env
        .axiom_deps(&inst)
        .expect("instTrustIr.ValueIdDecidableEq present for axiom_deps");
    assert!(
        deps.is_empty(),
        "single-field struct DecidableEq must have EMPTY axiom_deps, got {deps:?}"
    );

    // Infer-types against the kernel (drives the struct projections + congrArg).
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("instTrustIr.ValueIdDecidableEq value must infer-type");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared DecidableEq TrustIr.ValueId type"
    );
}

#[test]
fn single_field_struct_decidable_eq_decides_correctly() {
    let env = value_id_env();
    // equal index ⇒ true branch ⇒ 1
    assert!(
        pick_reduces(&env, "TrustIr.ValueId.mk 7", "TrustIr.ValueId.mk 7").contains("Small(1)"),
        "equal ValueId indices must take the true branch (1)"
    );
    // distinct index ⇒ false branch ⇒ 0
    assert!(
        pick_reduces(&env, "TrustIr.ValueId.mk 7", "TrustIr.ValueId.mk 8").contains("Small(0)"),
        "distinct ValueId indices must take the false branch (0)"
    );
}

/// End-to-end Track TT gate: `a == b` on a `deriving DecidableEq` (NOT
/// `deriving BEq`) struct resolves via the `instBEqOfDecidableEq` bridge and the
/// sound struct `DecidableEq` instance, and EVALUATES correctly. Mirrors
/// `ValueMap.set`/`PermissionMap.set`'s `id' == id`.
#[test]
fn beq_eq_eq_on_decidable_eq_struct_resolves_and_evaluates() {
    let env = value_id_env();

    // `(ValueId.mk 1 == ValueId.mk 2)` must elaborate (no free var, no sorry)
    // and reduce to `false`; `(== same)` to `true`.
    let mut env_t = env.clone();
    let d_t = parse_decl("def __beq_t : Bool := (TrustIr.ValueId.mk 4 == TrustIr.ValueId.mk 4)")
        .expect("parse __beq_t");
    elaborate_decl_and_register(&mut env_t, &d_t)
        .expect("`a == b` on DecidableEq struct must elaborate via instBEqOfDecidableEq");
    let tc_t = TypeChecker::new(&env_t);
    let whnf_t = format!(
        "{:?}",
        tc_t.whnf(&Expr::const_(Name::from_string("__beq_t"), vec![]))
            .kind()
    );
    assert!(
        whnf_t.contains("true") || whnf_t.contains("Bool.true"),
        "equal `==` must reduce to true, got {whnf_t}"
    );

    let mut env_f = env;
    let d_f = parse_decl("def __beq_f : Bool := (TrustIr.ValueId.mk 1 == TrustIr.ValueId.mk 2)")
        .expect("parse __beq_f");
    elaborate_decl_and_register(&mut env_f, &d_f)
        .expect("`a == b` on DecidableEq struct must elaborate via instBEqOfDecidableEq");
    let tc_f = TypeChecker::new(&env_f);
    let whnf_f = format!(
        "{:?}",
        tc_f.whnf(&Expr::const_(Name::from_string("__beq_f"), vec![]))
            .kind()
    );
    assert!(
        whnf_f.contains("false") || whnf_f.contains("Bool.false"),
        "distinct `==` must reduce to false, got {whnf_f}"
    );
}
