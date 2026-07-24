// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{ConstantOrigin, Declaration, Environment, OriginTrust};
use crate::expr::Expr;
use crate::name::Name;

#[test]
fn test_constant_origin_can_be_recorded_and_read() {
    let mut env = Environment::new();
    let name = Name::from_string("OriginAudit.sample");
    let origin = ConstantOrigin::olean_import(Some("OriginAudit.Module".to_string()));

    assert!(
        !env.set_constant_origin(name.clone(), origin.clone()),
        "origin metadata should not be recorded for missing constants"
    );
    assert!(env.get_constant_origin(&name).is_none());

    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("sample axiom should register");

    assert!(env.set_constant_origin(name.clone(), origin.clone()));
    assert_eq!(env.get_constant_origin(&name), Some(&origin));
    assert_eq!(
        env.constant_origin_trust(&name),
        Some(OriginTrust::OleanUnpinned)
    );
    assert!(env.is_unpinned_olean_import(&name));
    assert_eq!(origin.module_name(), Some("OriginAudit.Module"));
}

#[test]
fn test_batch_origin_setter_skips_missing_constants() {
    let mut env = Environment::new();
    let present = Name::from_string("OriginAudit.present");
    let missing = Name::from_string("OriginAudit.missing");

    env.add_decl(Declaration::Axiom {
        name: present.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("present axiom should register");

    let changed = env.set_constant_origins(
        [present.clone(), missing.clone()],
        ConstantOrigin::kernel_checked(),
    );

    assert_eq!(changed, 1);
    assert_eq!(
        env.constant_origin_trust(&present),
        Some(OriginTrust::KernelChecked)
    );
    assert!(env.get_constant_origin(&missing).is_none());
}

// -- G5: fail-closed needs_recheck → KernelChecked promotion gate --------------

/// Register a structurally-imported constant carrying an unpinned `.olean`
/// origin — the exact shape the STRUCTURAL import lane produces.
fn add_structural_import(env: &mut Environment, name: &Name) {
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("import axiom should register");
    // The structural lane tags every inserted constant with an unpinned import
    // origin (needs_recheck == true).
    assert!(env.set_constant_origin(
        name.clone(),
        ConstantOrigin::olean_import(Some("G5.Module".to_string())),
    ));
    assert!(
        env.constant_needs_recheck(name),
        "a fresh structural import must report needs_recheck"
    );
    assert!(!env.constant_is_kernel_checked(name));
}

/// G5 CORE: the general origin setter MUST NOT silently promote a still
/// `needs_recheck` (structurally-imported) constant to a `KernelChecked` origin.
/// Attempting it is fail-closed — the constant stays at its unpinned import
/// origin, unchanged.
#[test]
#[cfg(not(debug_assertions))] // debug builds intentionally debug_assert! on the misuse
fn test_g5_set_origins_refuses_unearned_kernel_checked_promotion() {
    let mut env = Environment::new();
    let name = Name::from_string("G5.import");
    add_structural_import(&mut env, &name);

    // Attempt the illegitimate raise through the general path.
    let changed = env.set_constant_origins([name.clone()], ConstantOrigin::kernel_checked());
    assert_eq!(changed, 0, "unearned KernelChecked raise must be dropped");
    // Fail-closed: still an unpinned import that needs a recheck.
    assert!(
        env.constant_needs_recheck(&name),
        "constant must remain needs_recheck after a refused promotion"
    );
    assert_eq!(
        env.constant_origin_trust(&name),
        Some(OriginTrust::OleanUnpinned)
    );
}

/// G5 CORE: the ONLY sanctioned promotion path
/// (`promote_origin_kernel_checked`, called after a passing kernel re-check)
/// DOES raise a `needs_recheck` import to `KernelChecked`, preserving module
/// provenance, and is idempotent.
#[test]
fn test_g5_gated_promotion_raises_trust_after_recheck() {
    let mut env = Environment::new();
    let name = Name::from_string("G5.rechecked");
    add_structural_import(&mut env, &name);

    // (In production this is only reached after typecheck_constants_full passed.)
    assert!(
        env.promote_origin_kernel_checked(&name),
        "gated promotion must succeed for a needs_recheck constant"
    );
    assert!(
        env.constant_is_kernel_checked(&name),
        "constant must now be KernelChecked"
    );
    assert!(
        !env.constant_needs_recheck(&name),
        "a promoted constant no longer needs a recheck"
    );
    // Module provenance is preserved (only the trust byte changed).
    assert_eq!(
        env.get_constant_origin(&name)
            .and_then(ConstantOrigin::module_name),
        Some("G5.Module")
    );
    // Idempotent: a second promotion is a no-op (already KernelChecked).
    assert!(!env.promote_origin_kernel_checked(&name));
}

/// G5: the gated promoter is a no-op for constants that are NOT structural
/// imports (no recorded origin, or already kernel-checked) — it can only ever
/// promote a genuine `needs_recheck` import, never fabricate trust elsewhere.
#[test]
fn test_g5_gated_promotion_noop_for_non_needs_recheck() {
    let mut env = Environment::new();
    let local = Name::from_string("G5.local");
    env.add_decl(Declaration::Axiom {
        name: local.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("local axiom should register");
    // A kernel-added local has no recorded origin ⇒ not a needs_recheck import.
    assert!(!env.constant_needs_recheck(&local));
    assert!(
        !env.promote_origin_kernel_checked(&local),
        "promotion must be a no-op for a constant with no structural-import origin"
    );

    // Also a no-op for a name that is not a registered constant.
    assert!(!env.promote_origin_kernel_checked(&Name::from_string("G5.absent")));
}
