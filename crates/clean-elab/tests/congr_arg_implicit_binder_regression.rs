// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression test: `congrArg` applied to a BARE polymorphic constant whose
//! own type leads with implicit `Sort`/`Type`-valued binders (e.g.
//! `Except.ok : {ε α : Type u} → α → Except ε α`) must have those leading
//! implicits properly instantiated with fresh metavariables before the
//! result is matched against `congrArg`'s `f : α → β` slot — NOT have `f`'s
//! slot unified directly against `Except.ok`'s own polymorphic Pi telescope.
//!
//! Regressed by Brick P1 (`unify/unifier/unify_expr.rs` / `unify_ext.rs`'s
//! Pi/Lam `BinderInfo`-blind unification — a deliberate, correct Lean/kernel
//! parity change needed elsewhere for higher-kinded prelude heads):
//! `apply_implicit_to_expected_type`'s "is this already a direct match"
//! probes (`elab_app_support.rs`) started accepting
//! `unify(Pi(Implicit,...), Pi(Default,...))` as a match, so they stopped
//! inserting `Except.ok`'s own `ε`/`α` implicits and instead pinned
//! `congrArg`'s `α`/`β` to `Except.ok`'s *implicit parameter types*
//! (`Type u`) — producing a bogus TYPE-valued `Eq` and a kernel-rejected
//! "level mismatch" TypeMismatch.
//!
//! Root-caused and fixed via `direct_type_match` (`elab_app_support.rs`),
//! which restores a binder-info-sensitive gate for every "is this already a
//! match" decision in `apply_implicit_to_expected_type`, without
//! reintroducing binder-info comparison into the general Pi/Lam unifier
//! (which must stay Lean/kernel-parity for Brick P1's own motivating case).
//!
//! Found via the trust-ir bridge PRELUDE_SRC regression (`congrArg
//! Except.ok (wrap_eq_self …)`; trust `crates/trust-clean/src/
//! trustir_bridge.rs:643`, `TRUST_BRIDGE_GATE=spot cargo test -p trust-clean
//! --test lean_clean_bridge`). FAILS before the fix (TypeMismatch: "level
//! mismatch: Zero vs Succ(u)"), PASSES after.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on
/// top of the default prelude (with `Except` explicitly initialized, since
/// it is otherwise lazily gated behind `Environment::init_except_t`).
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    env.init_except_t().map_err(|e| format!("{e:?}"))?;
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| format!("{e:?}"))?;
    }
    Ok(env)
}

#[test]
fn congr_arg_bare_polymorphic_constant_with_leading_implicit_sort_binders() {
    // `Except.ok : {ε α : Type u} → α → Except ε α` — TWO leading implicit
    // Type-valued binders before the explicit value argument, structurally
    // identical to the trust-ir bridge's real `Except.ok : {ε:Type u1}
    // {α:Type u2} → α → Except ε α`. Passing it BARE (not eta-expanded) as
    // `congrArg`'s `f` argument is exactly the shape that regressed: the
    // stated goal (`Except.ok a = Except.ok b`, an ordinary VALUE-level
    // equality) forces `congrArg`'s `f : α → β` expected type down onto the
    // bare `Except.ok` reference before its own implicits are resolved.
    let source = r#"
theorem congr_arg_except_ok_bare (a b : Nat) (h : a = b) :
    (Except.ok a : Except Nat Nat) = Except.ok b :=
  congrArg Except.ok h
"#;
    let env =
        elaborate_module(source).expect("congrArg Except.ok h must elaborate and kernel-check");
    assert!(
        env.get_const(&Name::from_string("congr_arg_except_ok_bare"))
            .is_some(),
        "theorem must be registered in the environment"
    );
}
