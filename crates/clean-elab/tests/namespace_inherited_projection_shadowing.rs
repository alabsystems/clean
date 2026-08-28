// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SRCELAB cluster **C6 — rigid head clash**, the dominant Pi-vs-FVar cause.
//!
//! For `structure C extends P`, Clean materializes a DERIVED projection
//! `C.f := fun {params} (self : C params) => P.f … (C.toP … self)` for every
//! field `f` projectable on `P`. Lean 4 declares no such constant — it builds
//! that composition on the fly at each use site (`mkBaseProjections`,
//! `src/Lean/Elab/App.lean`). Measured against the real Lean 4 `Init` oleans
//! (93,172 constants loaded through `clean check --imports-prefer-olean`),
//! `Monad.toApplicative` EXISTS while `Monad.pure` and `Applicative.pure` do
//! NOT.
//!
//! Because Clean's constant does exist it joined the current-namespace-outward
//! candidate set in `elab_ident`, so inside `namespace C` a bare `f` resolved
//! to `C.f` and shadowed the root/exported `f` the author wrote. `C.f` takes an
//! EXPLICIT `self` nobody supplied, so the term stayed under-applied with a
//! `Pi` type where the field type belonged.
//!
//! That is exactly what killed four declarations of `Mathlib/Logic/Unique.lean`
//! (`Unique extends Inhabited α` ⇒ `Unique.default`) under
//! `scripts/source_elab_gate.sh`:
//!
//! ```text
//! Unique.eq_default: Type mismatch: expected FVar(FVarId(0)), got cannot
//!   unify expressions of different shape: Discriminant(6) vs Discriminant(1)
//! Unique.default_eq: Type mismatch: expected Pi(BinderData { info: Default,
//!   mult: Many }, App(Const(Unique, [Param(u_3)]),
//!   FVar(FVarId(9223372036854775809))), FVar(FVarId(9223372036854775809))),
//!   got cannot unify expressions of different shape: Discriminant(1) vs
//!   Discriminant(6)
//! Unique.forall_iff: … Discriminant(6) vs Discriminant(1)
//! Unique.exists_iff: … Discriminant(6) vs Discriminant(1)
//! ```
//!
//! `Discriminant(6)` is `ExprKind::Pi`, `Discriminant(1)` is `ExprKind::FVar`
//! (`crates/clean-kernel/src/expr/kind.rs`), and `Unique.default_eq`'s printed
//! *expected* type is literally `Unique ?m → ?m`: the under-applied projection.
//!
//! These tests drive the same pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a verdict here matches the observable `clean check` verdict. Every accept
//! is kernel-checked by `elaborate_decl_and_register`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

fn fixture(name: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/namespace_shadowing")
        .join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("C6 fixture must exist at {}: {e}", path.display()))
}

/// Elaborate every declaration of `source`, returning the environment. Any
/// failure is reported with the declaration that produced it, because the
/// point of these fixtures is WHICH declaration breaks.
fn elaborate_all(source: &str) -> (Environment, Vec<ElabResult>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    let mut results = Vec::new();
    for (idx, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register(&mut env, &processed) {
            Ok(result) => results.push(result),
            Err(e) => panic!(
                "declaration #{idx} (bytes {}..{}) must elaborate, got: {e}",
                processed.span().start,
                processed.span().end
            ),
        }
    }
    (env, results)
}

/// The repro: the same theorem text must check inside and outside the
/// structure's namespace.
#[test]
fn bare_name_inside_structure_namespace_is_not_shadowed_by_inherited_projection() {
    let (env, _) = elaborate_all(&fixture("inherited_projection_shadows_root.lean"));

    for thm in ["outside", "appliedRoot", "MyU.inside", "MyU.applied"] {
        assert!(
            env.get_const(&Name::from_string(thm)).is_some(),
            "`{thm}` must be registered"
        );
    }
}

/// The fix is a RESOLUTION fix, not a deletion: the derived projection is
/// still materialized and still reachable by its qualified name. If this ever
/// starts failing while the test above passes, the defect was "fixed" by
/// dropping inherited projections, which would break dot notation and
/// structure-literal parent assembly instead.
///
/// WHAT THIS PIN MEANS AFTER 2026-08-24. The divergence it guards has since
/// been measured and DECIDED: Lean 4 declares no such constant (1,235
/// inherited (structure, field) pairs in `import Lean`, 0 declared; 9,185 over
/// the whole of Mathlib, 0 declared, 0 name collisions), Clean's own
/// `.olean` import path declares none either, and the decision is to compose
/// on the fly instead — `designs/2026-08-24-inherited-projection-parity.md`.
/// So this test does NOT say the constants are correct. It says: while they
/// exist, they must keep existing, because dot notation and the
/// structure-literal update rewrite still find them by name. The lane that
/// finally drops them must re-point those consumers at
/// `name_resolution::compose_subobject_projection` (whose output is proved
/// definitionally equal to these constants by
/// `composed_inherited_projection_is_def_eq_to_generated_constant` below),
/// flip `CLEAN_LEAN4_STRUCT_PARITY` to on-by-default, and REWRITE this test to
/// assert the constants are ABSENT — never delete it, since the absence is
/// then the property worth pinning.
#[test]
fn derived_inherited_projection_is_still_registered() {
    let (env, _) = elaborate_all(&fixture("inherited_projection_shadows_root.lean"));
    assert!(
        env.get_const(&Name::from_string("MyU.default")).is_some(),
        "the derived inherited projection `MyU.default` must still exist — \
         the C6 fix hides it from BARE-name resolution, it does not delete it"
    );
    assert!(
        env.get_const(&Name::from_string("MyU.toInhabited"))
            .is_some(),
        "the parent subobject projection must still exist"
    );
}

/// Negative control: a bare inherited-field name with NO other binding must
/// still resolve to the derived projection. Lean would say `unknown
/// identifier` here; accepting more is safe (the kernel re-checks), and the
/// point is that the fix cannot un-resolve a name that resolved before it.
#[test]
fn bare_inherited_field_still_resolves_when_nothing_shadows_it() {
    let (env, _) = elaborate_all(&fixture("inherited_projection_bare_fallback.lean"));
    for d in ["MyDer.viaBare", "MyDer.viaQualified"] {
        assert!(
            env.get_const(&Name::from_string(d)).is_some(),
            "`{d}` must be registered"
        );
    }
}

/// Does `e`'s body mention the constant `name` anywhere?
fn mentions_const(e: &clean_kernel::Expr, name: &str) -> bool {
    use clean_kernel::ExprKind;
    match e.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => mentions_const(f, name) || mentions_const(a, name),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            mentions_const(t, name) || mentions_const(b, name)
        }
        ExprKind::Let(_, t, v, b, _) => {
            mentions_const(t, name) || mentions_const(v, name) || mentions_const(b, name)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => mentions_const(inner, name),
        _ => false,
    }
}

/// Depth of the outermost `Proj` spine of `e`, after stripping binders.
fn proj_spine_depth(e: &clean_kernel::Expr) -> usize {
    use clean_kernel::ExprKind;
    let mut cur = e;
    while let ExprKind::Lam(_, _, b) | ExprKind::MData(_, b) = cur.kind() {
        cur = b;
    }
    let mut n = 0;
    while let ExprKind::Proj(_, _, inner) = cur.kind() {
        n += 1;
        cur = inner;
    }
    n
}

/// The COST OF CLOSING the divergence, discharged by the kernel rather than
/// asserted here.
///
/// Clean materializes `C.f` for every inherited field; Lean 4 declares none and
/// composes `P.f (C.toP c)` at each use site. Removing Clean's constants is only
/// safe if the composition MEANS the same thing — and the fixture's `rfl` is
/// exactly that claim, checked by the kernel:
///
/// ```text
/// def viaDot   (x : MyDer Nat) : Nat := x.widget            -- the CONSTANT
/// def viaChain (x : MyDer Nat) : Nat := x.toMyBase.widget   -- the composed spine
/// theorem composedEqGenerated (x : MyDer Nat) : viaDot x = viaChain x := rfl
/// ```
///
/// plus the two-level (grandparent) case, plus two value-distinguishing rows so
/// neither side can be vacuously equal by both being stuck.
///
/// This test's job is to prove the two sides are NOT the same term: `viaDot`'s
/// body must mention the generated constant and `viaChain`'s must be a bare
/// `Proj` spine of the expected depth. Without that, `rfl` would be comparing a
/// term with itself and would prove nothing.
///
/// If this ever fails, the composer and the generated constant have drifted
/// apart, and NEITHER removing the constants nor keeping them is safe until
/// they agree again.
#[test]
fn composed_inherited_projection_is_def_eq_to_generated_constant() {
    let (env, _) = elaborate_all(&fixture("inherited_projection_composed.lean"));

    for thm in [
        "composedEqGenerated",
        "composedEqGeneratedDeep",
        "sampleDot",
        "sampleChain",
    ] {
        assert!(
            env.get_const(&Name::from_string(thm)).is_some(),
            "`{thm}` must be registered — its `rfl` is the kernel-checked \
             composed-vs-generated definitional equality"
        );
    }

    // The generated constants must exist, or the `viaDot` side is not the
    // constant side and the fixture proves nothing.
    for generated in ["MyDer.widget", "MyTop.widget"] {
        assert!(
            env.get_const(&Name::from_string(generated)).is_some(),
            "`{generated}` is a DERIVED inherited projection and must still be \
             registered while CLEAN_LEAN4_STRUCT_PARITY is off"
        );
    }

    // THE TWO SIDES ARE GENUINELY DIFFERENT TERMS.
    for (dot, chain, depth) in [
        ("viaDot", "viaChain", 2usize),
        ("viaDotDeep", "viaChainDeep", 3usize),
    ] {
        let dot_body = env
            .get_const(&Name::from_string(dot))
            .and_then(|c| c.value.clone())
            .unwrap_or_else(|| panic!("`{dot}` must have a body"));
        let chain_body = env
            .get_const(&Name::from_string(chain))
            .and_then(|c| c.value.clone())
            .unwrap_or_else(|| panic!("`{chain}` must have a body"));
        let generated = format!("{}.widget", if depth == 2 { "MyDer" } else { "MyTop" });
        assert!(
            mentions_const(&dot_body, &generated),
            "`{dot}` must go through the generated constant `{generated}` \
             (else the fixture's `rfl` compares a term with itself): {dot_body:?}"
        );
        assert!(
            !mentions_const(&chain_body, &generated),
            "`{chain}` must NOT go through `{generated}` — it is the composed \
             spine: {chain_body:?}"
        );
        assert_eq!(
            proj_spine_depth(&chain_body),
            depth,
            "`{chain}` must be a {depth}-deep kernel `Proj` spine — the exact \
             shape `compose_subobject_projection` builds: {chain_body:?}"
        );
    }
}
