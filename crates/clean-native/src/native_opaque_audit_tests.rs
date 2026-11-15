// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The native opaque audit: the table matches the prelude, and the refusal
//! fires through the production `clean compile` / `clean run` path.

use std::collections::{BTreeSet, HashSet};
use std::path::PathBuf;

use clean_kernel::{ConstantInfo, ConstantKind, Environment, Expr, Name};

use super::*;
use crate::native_build::emit_entry_c_with_type;

/// The environment every native build elaborates against, before the source
/// file's own declarations (`compile::elaborate_file_to_env`).
fn native_base_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_io_ops().expect("init_io_ops on the prelude");
    env
}

fn write_temp_lean(source: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("opaque_fixture.lean");
    std::fs::write(&file, source).expect("write fixture");
    (dir, file)
}

/// THE AUDIT. Every value-bearing `Opaque` the native path can reach is
/// classified, and no entry is stale: a table entry must name a value-bearing
/// prelude opaque that is NOT shimmed (a shimmed one never reaches the check,
/// so its entry would be dead weight that could hide a lost shim).
#[test]
fn test_native_opaque_audit_classifies_every_prelude_opaque() {
    let env = native_base_env();
    let prelude_opaques: BTreeSet<String> = env
        .constants()
        .filter(|info| info.kind == ConstantKind::Opaque && info.value.is_some())
        .map(|info| info.name.to_string())
        .collect();
    assert!(
        !prelude_opaques.is_empty(),
        "the enumeration must see the prelude's opaques, or this audit audits nothing"
    );

    let unclassified: Vec<&String> = prelude_opaques
        .iter()
        .filter(|name| audit_entry(name).is_none())
        .filter(|name| !is_primitive_denylisted(&mangle_name(&Name::from_string(name))))
        .collect();
    assert!(
        unclassified.is_empty(),
        "value-bearing prelude opaques missing from PRELUDE_OPAQUE_AUDIT (classify each as \
         Genuine or Placeholder): {unclassified:?}"
    );

    let stale: Vec<&str> = PRELUDE_OPAQUE_AUDIT
        .iter()
        .map(|entry| entry.name)
        .filter(|name| {
            !prelude_opaques.contains(*name)
                || is_primitive_denylisted(&mangle_name(&Name::from_string(name)))
        })
        .collect();
    assert!(
        stale.is_empty(),
        "PRELUDE_OPAQUE_AUDIT names constants that are no longer unshimmed value-bearing \
         prelude opaques: {stale:?}"
    );
}

/// Does `value` hide a stand-in: a `fun`, at the top of the value or as an
/// argument of the application the value is (a class instance
/// `C.mk (fun _ _ => "")`), that takes at least one argument and ignores all of
/// them to return a literal?
fn ignores_args_returns_literal(value: &Expr) -> bool {
    let literal_lambda = |e: &Expr| {
        let mut body = e.strip_mdata();
        let mut binders = 0;
        while let clean_kernel::ExprKind::Lam(_, _, inner) = body.kind() {
            body = inner.as_ref().strip_mdata();
            binders += 1;
        }
        binders > 0 && matches!(body.kind(), clean_kernel::ExprKind::Lit(_))
    };
    let mut cur = value.strip_mdata();
    while let clean_kernel::ExprKind::Lam(_, _, inner) = cur.kind() {
        cur = inner.as_ref().strip_mdata();
    }
    let mut args = Vec::new();
    while let clean_kernel::ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref().strip_mdata();
    }
    literal_lambda(value) || args.into_iter().any(literal_lambda)
}

/// Every unshimmed prelude definition of `env` whose value ignores its
/// arguments to return a literal.
fn literal_stubs(env: &Environment) -> BTreeSet<String> {
    env.constants()
        .filter(|info| info.kind == ConstantKind::Definition)
        .filter(|info| {
            info.value
                .as_ref()
                .is_some_and(ignores_args_returns_literal)
        })
        .filter(|info| !is_primitive_denylisted(&mangle_name(&info.name)))
        .map(|info| info.name.to_string())
        .collect()
}

/// THE DEFINITION AUDIT. Every prelude definition in the native base
/// environment whose value ignores its arguments to return a literal is
/// classified in PRELUDE_DEFINITION_AUDIT, and no entry is stale. The shape is
/// the one the measured stand-ins took (`Repr.mk (fun _ _ => "")`); a genuine
/// constant function is classified `Genuine` by name.
#[test]
fn test_native_definition_audit_classifies_every_literal_stub() {
    let env = native_base_env();
    let stubs = literal_stubs(&env);
    // The scan must still SEE a stand-in, or it scans nothing. The measured
    // `Repr` stand-ins are gone (they route through the audited opaque
    // `Clean.Repr.render` now), so register the exact shape they had and
    // require the scan to report it unclassified — the branch that fails
    // this test the day a new literal stub lands in the prelude.
    let mut canary_env = env.clone();
    canary_env
        .add_decl(clean_kernel::Declaration::Definition {
            name: Name::from_string("nativeAuditCanaryStub"),
            level_params: vec![],
            type_: Expr::app(
                Expr::const_(Name::from_string("Repr"), vec![clean_kernel::Level::zero()]),
                Expr::const_str("Nat"),
            ),
            value: Expr::apps(
                Expr::const_(
                    Name::from_string("Repr.mk"),
                    vec![clean_kernel::Level::zero()],
                ),
                [
                    Expr::const_str("Nat"),
                    Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        Expr::const_str("Nat"),
                        Expr::lam(
                            clean_kernel::BinderInfo::Default,
                            Expr::const_str("Nat"),
                            Expr::str_lit(""),
                        ),
                    ),
                ],
            ),
            is_reducible: true,
        })
        .expect("the canary stub is a well-typed Repr Nat");
    let canary_stubs = literal_stubs(&canary_env);
    assert!(
        canary_stubs.contains("nativeAuditCanaryStub")
            && definition_audit_entry("nativeAuditCanaryStub").is_none(),
        "the scan must report an unclassified `Repr.mk (fun _ _ => \"\")`: {canary_stubs:?}"
    );
    let unclassified: Vec<&String> = stubs
        .iter()
        .filter(|name| definition_audit_entry(name).is_none())
        .collect();
    assert!(
        unclassified.is_empty(),
        "prelude definitions returning a literal regardless of their arguments, missing from \
         PRELUDE_DEFINITION_AUDIT (classify each as Genuine or Placeholder): {unclassified:?}"
    );
    let stale: Vec<&str> = PRELUDE_DEFINITION_AUDIT
        .iter()
        .map(|entry| entry.name)
        .filter(|name| !stubs.contains(*name))
        .collect();
    // The silently-panicking table is audited by name rather than by shape:
    // each entry must be a definition the native base environment has.
    let missing: Vec<&str> = PRELUDE_SILENT_PANIC_AUDIT
        .iter()
        .map(|entry| entry.name)
        .filter(|name| {
            env.get_const(&Name::from_string(name))
                .is_none_or(|info| info.kind != ConstantKind::Definition || info.value.is_none())
        })
        .collect();
    assert!(
        missing.is_empty(),
        "PRELUDE_SILENT_PANIC_AUDIT names constants that are not value-bearing prelude \
         definitions: {missing:?}"
    );
    assert!(
        stale.is_empty(),
        "PRELUDE_DEFINITION_AUDIT names constants that no longer have a stub-shaped value: \
         {stale:?}"
    );
}

/// The two measured wrong answers stay refused by name, so a reclassification
/// is a visible edit to this file, not a table drift: the `Float` family as
/// opaque placeholders, `Int.div`/`Int.mod` (definitions since they compute
/// in the kernel) as Lean-divergent.
#[test]
fn test_native_opaque_audit_int_divmod_are_lean_divergent_and_float_ops_are_placeholders() {
    for name in ["Int.div", "Int.mod"] {
        assert!(audit_entry(name).is_none(), "{name} is no longer an opaque");
        let entry =
            definition_audit_entry(name).unwrap_or_else(|| panic!("{name} must be audited"));
        assert_eq!(
            entry.runtime,
            OpaqueRuntime::LeanDivergent,
            "{name} must be refused"
        );
    }
    for name in [
        "Float.add",
        "Float.mul",
        "Float.ofNat",
        "Float.ofScientific",
        "Float.toUInt64",
    ] {
        let entry = audit_entry(name).unwrap_or_else(|| panic!("{name} must be audited"));
        assert_eq!(
            entry.runtime,
            OpaqueRuntime::Placeholder,
            "{name} must be refused"
        );
    }
}

fn opaque_info(name: &str) -> ConstantInfo {
    let mut info = ConstantInfo::new(
        Name::from_string(name),
        vec![],
        Expr::const_str("Nat"),
        Some(Expr::nat_lit(0)),
        false,
    );
    info.kind = ConstantKind::Opaque;
    info
}

#[test]
fn test_refuse_unfaithful_body_placeholder_is_refused_by_name() {
    let err = refuse_unfaithful_body(
        &opaque_info("Float.add"),
        &Name::from_string("main"),
        &HashSet::new(),
    )
    .expect_err("Float.add must be refused");
    let msg = err.to_string();
    assert!(msg.contains("native-opaque-placeholder"), "{msg}");
    assert!(
        msg.contains("`Float.add`") && msg.contains("`main`"),
        "{msg}"
    );
}

/// THE LEAN-DIVERGENT AUDIT. Every entry names a value-bearing DEFINITION of
/// the native base environment (so the refusal is not keyed on a name that
/// changed kind or vanished), and the refusal fires on that very constant.
/// `Int.div`/`Int.mod` must be here: they are real definitions now, and
/// Clean's `/`/`%` on `Int` reach them where Lean's reach `Int.ediv`/`Int.emod`.
#[test]
fn test_native_lean_divergent_audit_names_prelude_definitions() {
    let env = native_base_env();
    let root = Name::from_string("main");
    let names: Vec<&str> = PRELUDE_LEAN_DIVERGENT_AUDIT
        .iter()
        .map(|e| e.name)
        .collect();
    assert_eq!(names, ["Int.div", "Int.mod"]);
    for name in names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} is in the native base environment"));
        assert_eq!(info.kind, ConstantKind::Definition, "{name}");
        assert!(info.value.is_some(), "{name} carries its value");
        assert!(
            !is_primitive_denylisted(&mangle_name(&info.name)),
            "{name} is not shimmed, so its value would be compiled"
        );
        let err = refuse_unfaithful_body(info, &root, &HashSet::new())
            .expect_err("a Lean-divergent definition must be refused");
        let msg = err.to_string();
        assert!(msg.contains("native-lean-divergent"), "{msg}");
        assert!(msg.contains(&format!("`{name}`")), "{msg}");
    }
}

#[test]
fn test_refuse_unfaithful_body_unaudited_opaque_is_refused() {
    let err = refuse_unfaithful_body(
        &opaque_info("Some.Imported.opaqueThing"),
        &Name::from_string("main"),
        &HashSet::new(),
    )
    .expect_err("an opaque nobody vouches for must be refused");
    assert!(err.to_string().contains("native-opaque-unaudited"), "{err}");
}

#[test]
fn test_refuse_unfaithful_body_source_declared_and_genuine_are_compiled() {
    let root = Name::from_string("main");
    let mut sources = HashSet::new();
    sources.insert(Name::from_string("mySecret"));
    refuse_unfaithful_body(&opaque_info("mySecret"), &root, &sources)
        .expect("a source file's own opaque compiles from its value, as in Lean");
    refuse_unfaithful_body(
        &opaque_info("System.Platform.getNumBits"),
        &root,
        &HashSet::new(),
    )
    .expect("a Genuine prelude opaque compiles");
    // A definition the definition audit does not name compiles.
    let mut def = opaque_info("Int.add");
    def.kind = ConstantKind::Definition;
    refuse_unfaithful_body(&def, &root, &HashSet::new()).expect("unaudited definitions pass");
    // ...and a placeholder definition is refused by name.
    let mut stub = opaque_info("List.head!");
    stub.kind = ConstantKind::Definition;
    let err = refuse_unfaithful_body(&stub, &root, &HashSet::new())
        .expect_err("a silently-panicking stand-in must be refused");
    assert!(
        err.to_string().contains("native-opaque-placeholder"),
        "{err}"
    );
}

/// END TO END: `repr 5` reached the `Repr.mk (fun _ _ => "")` stand-in and
/// printed an empty line at exit 0 (measured 2026-09-25; pinned Lean v4.30.0-rc2
/// prints `5`). The instance now renders through `Clean.Repr.render`, which
/// is what the refusal names.
#[test]
fn test_native_emit_repr_program_is_refused_not_miscompiled() {
    let (_dir, file) = write_temp_lean("def main : IO Unit := IO.println (toString (repr 5))\n");
    let err = emit_entry_c_with_type(&file, "main", 0)
        .expect_err("the Repr stand-in must be refused, not compiled to an empty string");
    let msg = format!("{err:#}");
    assert!(msg.contains("native-opaque-placeholder"), "{msg}");
    assert!(msg.contains("`Clean.Repr.render`"), "{msg}");
}

/// END TO END: a DERIVED `Repr` used to render a structure as its bare name —
/// `clean run` printed `P` at exit 0 where pinned Lean v4.30.0-rc2 prints
/// `{ x := 1 }` (measured 2026-09-30) — and an inductive constructor with
/// fields as its bare name (`T.mk` where Lean prints `T.mk 1`). Both bodies
/// route through the audited opaque now, so both programs are refused.
#[test]
fn test_native_emit_derived_repr_programs_are_refused_not_miscompiled() {
    for source in [
        "structure P where\n  x : Nat\n  deriving Repr\n\
         def main : IO Unit := IO.println (repr (P.mk 1))\n",
        "inductive T where\n  | mk (n : Nat)\n  | z\n  deriving Repr\n\
         def main : IO Unit := IO.println (repr (T.mk 1))\n",
    ] {
        let (_dir, file) = write_temp_lean(source);
        let err = emit_entry_c_with_type(&file, "main", 0)
            .expect_err("a derived stub rendering must be refused, not printed");
        let msg = format!("{err:#}");
        assert!(msg.contains("native-opaque-placeholder"), "{msg}");
        assert!(msg.contains("`Clean.Repr.render`"), "{msg}");
    }
}

/// Every default-prelude `Repr` instance renders through the one audited
/// opaque, and that opaque is classified a placeholder — the single entry the
/// refusals above rest on.
#[test]
fn test_native_repr_instances_route_through_the_audited_render_opaque() {
    let env = native_base_env();
    let render = Name::from_string("Clean.Repr.render");
    let entry = audit_entry("Clean.Repr.render").expect("the renderer is audited");
    assert_eq!(entry.runtime, OpaqueRuntime::Placeholder);
    for name in [
        "instReprNat",
        "instReprString",
        "instReprBool",
        "instReprInt",
        "instReprList",
        "instReprOption",
        "Clean.instReprProdOfRepr",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} is in the native base environment"));
        let mut constants = HashSet::new();
        info.value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} carries its value"))
            .collect_constants_into(&mut constants);
        assert!(
            constants.contains(&render),
            "{name} must render through {render}"
        );
    }
}

/// The explicit legacy T-rounding heads retain their native audit refusal.
/// Int notation now uses checked E-rounding definitions, whose actual output
/// is checked by clean's tostring_instances_cli integration suite. That repair
/// must not silently admit these separately unqualified native operations.
#[test]
fn test_native_emit_int_div_program_is_refused_not_miscompiled() {
    for head in ["Int.div", "Int.mod"] {
        let source = format!(
            "@[noinline] def truncating (a b : Int) : Int := {head} a b\n\
             def main : IO Unit := IO.println (toString (truncating (-7) 2))\n"
        );
        let (_dir, file) = write_temp_lean(&source);
        let err = emit_entry_c_with_type(&file, "main", 0)
            .expect_err("the explicit T-rounding native audit must remain closed");
        let msg = format!("{err:#}");
        assert!(msg.contains("native-lean-divergent"), "{head}: {msg}");
        assert!(msg.contains(&format!("`{head}`")), "{head}: {msg}");
    }
}

/// Measured before the refusal: `(2.5 * 4.0).toUInt64` printed `0` at exit 0
/// (Lean: `10`).
#[test]
fn test_native_emit_float_program_is_refused_not_miscompiled() {
    let (_dir, file) = write_temp_lean(
        "def main : IO Unit := do\n  \
         let x : Float := 2.5\n  \
         let y : Float := 4.0\n  \
         IO.println (toString (x * y).toUInt64)\n",
    );
    let err = emit_entry_c_with_type(&file, "main", 0)
        .expect_err("Float arithmetic must be refused, not compiled to constants");
    let msg = format!("{err:#}");
    assert!(msg.contains("native-opaque-placeholder"), "{msg}");
    assert!(msg.contains("`Float."), "{msg}");
}

/// The control: a USER `opaque` keeps compiling from its value. Pinned Lean
/// v4.30.0-rc2 on this program prints `7`.
#[test]
fn test_native_emit_user_opaque_still_compiles() {
    let (_dir, file) = write_temp_lean(
        "opaque mySecret : Nat := 7\n\
         def main : IO Unit := IO.println (toString mySecret)\n",
    );
    let (emitted, _) =
        emit_entry_c_with_type(&file, "main", 0).expect("a user opaque must still compile");
    assert!(
        emitted.contains("l_mySecret("),
        "the user opaque's body is compiled: {emitted}"
    );
}

/// END TO END: `#[1, 2][5]!` returned `default` with an empty stderr, where
/// pinned Lean v4.30.0-rc2 prints `Error: index out of bounds` on stderr.
#[test]
fn test_native_emit_bang_index_is_refused_not_silenced() {
    let (_dir, file) = write_temp_lean(
        "def main : IO Unit := do\n  \
         let a := #[1, 2]\n  \
         IO.println (toString (a[5]!))\n",
    );
    let err = emit_entry_c_with_type(&file, "main", 0)
        .expect_err("a silently-panicking accessor must be refused");
    let msg = format!("{err:#}");
    assert!(msg.contains("native-opaque-placeholder"), "{msg}");
    assert!(msg.contains("`GetElem?.getElem!`"), "{msg}");
}
