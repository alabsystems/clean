// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dot-notation on a receiver whose type is a `Pi` (`elab_dot_notation`).
//!
//! Two shapes previously failed with `NotImplemented("cannot extract type name
//! from Pi(...)")` because `get_type_name` cannot name a Pi head:
//!
//! * **Fix A** — method dot-notation on a receiver whose type is a Pi of
//!   LEADING IMPLICIT/INSTANCE binders, e.g. an *unapplied* lemma
//!   `lemma : {a : Prop} → Iff a a` used as `lemma.mpr` / `lemma.symm`. The
//!   leading implicit binders are peeled (fresh metavars) until the concrete
//!   head `Iff` is exposed, then `Iff.mpr` / `Iff.symm` resolves with the
//!   peeled application as the receiver.
//! * **Fix B** — dot-notation on a genuinely function-typed (explicit-arrow
//!   `Pi`) receiver `g : β → α` used as `g.Injective`, which resolves in the
//!   `Function` namespace as `Function.Injective g`.
//!
//! Both fixes change only *which constant* the dot head resolves to (plus the
//! inserted implicit/instance args); the resulting application is fully
//! elaborated and kernel-re-checked, so the soundness assertions below demand
//! an EMPTY axiom closure.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

/// Elaborate every decl in `code` into a fresh prelude environment, asserting
/// each one elaborates and registers without error.
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!("decl {i} fell through to RawDecl (parser error recovery): content={content:?}, span={span:?}");
        }
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

/// Assert a constant is registered, its value infers a type def-eq to its
/// declared type (well-typed), and its axiom closure is empty.
fn assert_sound_const(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let info = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should be a definition with a value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("infer_type({name}.value) failed: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred value type not def-eq to declared type"
    );
    let deps = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should return Some"));
    let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "{name} must have an EMPTY axiom closure, got {dep_names:?}"
    );
}

/// Fix A: `lemma.mpr` / `lemma.symm` where `lemma`'s type is a leading-implicit
/// Pi (`{a : Prop} → Iff a a`). The receiver type WHNFs to an implicit-led Pi;
/// peeling the implicits exposes the `Iff` head so `Iff.mpr` / `Iff.symm`
/// resolve. Both dependents must elaborate, be well-typed, and be axiom-free.
#[test]
fn test_dot_notation_implicit_led_pi_receiver_resolves_iff_methods() {
    let code = r#"
theorem iff_self_lemma {a : Prop} : Iff a a := Iff.intro (fun x => x) (fun x => x)
theorem use_mpr (p : Prop) : p → p := iff_self_lemma.mpr
theorem use_symm (q : Prop) : Iff q q := iff_self_lemma.symm
"#;
    let env = elab_all(code);
    assert_sound_const(&env, "use_mpr");
    assert_sound_const(&env, "use_symm");
}

/// Numeric `.1`/`.2` projection through a LEADING-IMPLICIT Pi receiver:
/// `iff_self_lemma.1` where `iff_self_lemma : {a : Prop} → Iff a a`. The receiver
/// type WHNFs to an implicit-led Pi that `resolve_projection_target` cannot name;
/// peeling the leading implicit exposes the single-constructor `Iff` structure so
/// the numeric field projects. Mirrors `Ne.ne_or_ne`'s `not_and_or.1` in
/// Mathlib/Logic/Basic. The `.field`-named counterpart already resolved via Fix A;
/// this closes the Index path. Both dependents must be well-typed and axiom-free.
#[test]
fn test_index_projection_through_implicit_led_pi_receiver_resolves_iff_fields() {
    let code = r#"
theorem iff_self_lemma {a : Prop} : Iff a a := Iff.intro (fun x => x) (fun x => x)
theorem use_fst (p : Prop) : p → p := iff_self_lemma.1
theorem use_snd (p : Prop) : p → p := iff_self_lemma.2
"#;
    let env = elab_all(code);
    assert_sound_const(&env, "use_fst");
    assert_sound_const(&env, "use_snd");
}

/// Prelude AXIOM-stub discharge on a source `class` redeclaration:
/// `Mathlib/Logic/Basic` re-declares the genuine `class Fact (p : Prop) : Prop
/// where out : p`, whose name collides with the prelude's hand-rolled `Fact`
/// carrier stub (`Fact : Prop → Prop`, `Fact.mk`, `Fact.out` — all opaque
/// axioms). Before the fix, `add_inductive` errored "Duplicate declaration:
/// Fact" and the stub (an axiom, not a projectable inductive) stayed in place, so
/// `Fact.elim`'s `h.1` and `fact_iff` failed with "index projection on
/// non-structure type". After discharging the value-less stubs, the real
/// structure registers and its field projections resolve. The prelude env
/// (`with_prelude`) carries the stub, so this test genuinely exercises the
/// discharge. Each dependent must be well-typed and axiom-free.
#[test]
fn test_source_class_redeclaration_discharges_prelude_axiom_stub_fact() {
    let code = r#"
class Fact (p : Prop) : Prop where
  out : p
theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩
theorem fact_iff_symm {p : Prop} : p ↔ Fact p := fact_iff.symm
theorem fact_of {p : Prop} (hp : p) : Fact p := ⟨hp⟩
"#;
    let env = elab_all(code);
    // The stub must be gone: `Fact` is now a genuine single-constructor inductive.
    assert!(
        env.get_inductive(&Name::from_string("Fact")).is_some(),
        "Fact should register as a real inductive (stub discharged)"
    );
    assert_sound_const(&env, "Fact.elim");
    assert_sound_const(&env, "fact_iff");
    assert_sound_const(&env, "fact_iff_symm");
    assert_sound_const(&env, "fact_of");
}

/// Fix B: `g.Injective` where `g : Nat → Nat` (an explicit-arrow Pi) resolves as
/// `Function.Injective g`. The receiver lands in the (first explicit) function
/// argument slot — if it were mis-placed the def-eq check in
/// `assert_sound_const` (declared `(Nat → Nat) → Prop`) would fail.
#[test]
fn test_dot_notation_function_typed_receiver_resolves_function_namespace() {
    let code = r#"
namespace Function
def Injective {α : Sort u} {β : Sort v} (f : α → β) : Prop := ∀ a b, f a = f b → a = b
end Function
def inj (g : Nat → Nat) : Prop := g.Injective
"#;
    let env = elab_all(code);
    assert_sound_const(&env, "inj");
}
