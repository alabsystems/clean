// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the 10 C009 sorry-inhabited Opaque carrier sites.
//!
//! See `reports/audit/2026-04-20-3570-c009-sorry-pi-carrier-classification.md`
//! for the full classification. All 10 sites share the same registration
//! shape today (see `crates/clean-kernel/src/env/nn_verification_c009.rs`
//! `register_c009_opaque_group`):
//!
//! ```text
//! Declaration::Opaque {
//!     level_params: [u],               // universe-polymorphic
//!     type_: Sort(succ(u)),            // Type universe (not a proposition)
//!     value: @sorryAx.{succ(succ(u))} Sort(succ(u)) true,
//!     // or legacy @sorry.{succ(succ(u))} Sort(succ(u))
//! }
//! ```
//!
//! The issue #3570 scope is the 6 "tractable" sites (3 CROWN correlation +
//! 2 depth scaling + 1 summary conjecture). This audit concluded that ALL
//! 6 are MASQUERADE-prone under Rule M3 (statement-rewriting) of
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`: reducing any of them
//! via the #3462-style `True:Prop` + `True.intro` recipe would restage
//! precisely the masquerade that #3580 demoted on the 3 IBP-wrapping
//! sibling sites.
//!
//! The 4 remaining sites are the exponential-gap family, explicitly
//! deferred by the issue body pending `Rat.exp` / `rat_pow` / Mathlib
//! `Real.exp_monotone` infrastructure.
//!
//! **Action:** ALL 10 sites remain `ConstantKind::Opaque` with:
//!
//! 1. A stored `value` (the direct `@sorryAx`/`@sorry` application — the body
//!    is not None, distinguishing Opaque from Axiom).
//! 2. `type_` of shape `ExprKind::Sort(_)` (universe-polymorphic Pi). NOT
//!    `ExprKind::Const("True", _)` — that would be the #3462 masquerade.
//! 3. The stored `value` is a direct canonical synthetic `sorryAx` spine
//!    (`sorryAx α true`) when the prelude has registered `sorryAx`, or the
//!    legacy `sorry α` fallback in bootstrap environments. This pins the
//!    direct type-level sorry shape and distinguishes it from any
//!    `sorry_inhabit_pi` lambda spine or a fresh constructive lambda.
//!
//! Any future reduction of any of these 10 sites MUST commit a commensurate
//! update to this guard test AND to
//! `reports/audit/2026-04-20-3570-c009-sorry-pi-carrier-classification.md`
//! demonstrating that the reduction does not satisfy Rule M3.
//!
//! Part of #3570. See also: #3580 (sibling #3462 demotion), #3569 (C003
//! classification precedent), #3566/#3567/#3568/#3578/#3579 (wave-3
//! demasquerade sweep).

use super::*;
use crate::env::ConstantKind;
use crate::expr::ExprKind;
use crate::name::Name;

/// Bucket Z (in-scope per #3570): 6 sites that MUST NOT be reduced via
/// the #3462 `True:Prop` + `True.intro` recipe. Each would produce a
/// Rule M3 masquerade.
const C009_BUCKET_Z_TRACTABLE_SITES: &[(&str, &str)] = &[
    // CROWN correlation (3)
    (
        "NNVerification.crown_backsubstitution",
        "crown_correlation (1/3): CROWN backward linearization composes affine layers",
    ),
    (
        "NNVerification.crown_combined_matrix",
        "crown_correlation (2/3): combined CROWN matrix = product W_N * diag(α) * ... * W_1",
    ),
    (
        "NNVerification.crown_correlation_retained",
        "crown_correlation (3/3): CROWN width uses combined matrix norm",
    ),
    // Depth scaling (2)
    (
        "NNVerification.ratio_monotone_depth",
        "depth_scaling (1/2): ratio(N+1) ≤ ratio(N) · r",
    ),
    (
        "NNVerification.ratio_limit_zero",
        "depth_scaling (2/2): lim_{N→∞} ratio(N) = 0",
    ),
    // Summary conjecture (1)
    (
        "NNVerification.c009_exponentially_tighter_than_ibp",
        "summary_conjecture: ∃ C > 0, r ∈ (0,1), ∀ N, crown/ibp ≤ C · r^N",
    ),
];

/// Bucket Z-exp (deferred per #3570 issue body): 4 exponential-gap sites
/// deferred pending `Rat.exp` / `rat_pow` / Mathlib `Real.exp_monotone`.
/// Pinned here as a regression fence so a broader sorry-pi reduction sweep
/// cannot accidentally include these without also lifting the documented
/// deferral.
const C009_BUCKET_Z_EXP_DEFERRED_SITES: &[(&str, &str)] = &[
    (
        "NNVerification.norm_product_vs_product_norm",
        "exp_gap (1/4): ||∏ A_i||_∞ ≤ ∏ ||A_i||_∞ — needs Matrix.norm_mul_le",
    ),
    (
        "NNVerification.crown_uses_product",
        "exp_gap (2/4): CROWN width bounded by norm of product",
    ),
    (
        "NNVerification.ibp_uses_product_of_norms",
        "exp_gap (3/4): IBP width equals product of norms",
    ),
    (
        "NNVerification.crown_ibp_ratio_exponential",
        "exp_gap (4/4): ratio ≤ C · r^N — needs Rat.exp / rat_pow",
    ),
];

/// Helper: build the C009-initialized environment.
fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verification_c009()
        .expect("init_nn_verification_c009 should succeed");
    env
}

/// Per-site invariants. Top-level dispatcher — each invariant is a small
/// helper below. See the module-level doc for the four properties we pin.
fn check_site_is_honest_sorry_opaque(env: &Environment, name: &str, rationale: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{}: missing declaration ({})", name, rationale));

    check_kind_is_opaque(info, name, rationale);
    check_value_present(info, name, rationale);
    check_type_is_sort_not_true(info, name, rationale);
    check_value_is_sorry_app(env, info, name, rationale);
}

/// (1) ConstantKind::Opaque — not Theorem (would be #3462 masquerade),
///     not Axiom (would be the honest #3580 Branch-A demotion applied to
///     this site, which is a valid follow-up but requires audit update),
///     not Definition (would be a carrier promotion that must come with
///     its own Branch B content plus audit update).
fn check_kind_is_opaque(info: &ConstantInfo, name: &str, rationale: &str) {
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "{name} ({rationale}): expected ConstantKind::Opaque (honest sorry \
         inhabitation); got {:?}. If this is a deliberate Branch A/B \
         change, update the C009 sorry-pi carrier classification audit \
         (reports/audit/2026-04-20-3570-c009-sorry-pi-carrier-classification.md) \
         and this guard test in the same commit, and explicitly address \
         whether the change satisfies Rule M3 of \
         designs/2026-04-19-demasquerade-cxxx-pattern.md.",
        info.kind,
    );
}

/// (2) Opaque carries a stored value (a non-None body).
fn check_value_present(info: &ConstantInfo, name: &str, rationale: &str) {
    assert!(
        info.value.is_some(),
        "{name} ({rationale}): Opaque must carry a value (the direct \
         `@sorry` term); got None. A None value would suggest the \
         Opaque was silently flipped to an Axiom shape.",
    );
}

/// (3) Type must be ExprKind::Sort(_) — universe-polymorphic Pi shape.
///     A regression to ExprKind::Const("True", _) would be the #3462
///     `True:Prop` masquerade — the exact shape demoted by #3580 on
///     the sibling IBP-wrapping triple. Debug-repr scan is a defensive
///     second gate.
fn check_type_is_sort_not_true(info: &ConstantInfo, name: &str, rationale: &str) {
    match info.type_.kind() {
        ExprKind::Sort(_) => {
            // Good: Sort(succ(u)) carrier preserved.
        }
        ExprKind::Const(n, _) => panic!(
            "{name} ({rationale}): type must be Sort(succ(u)); got \
             Const({n}). If this is Const(\"True\", _), the declaration \
             has been retyped to `True:Prop` — the #3462 Rule M3 \
             masquerade demoted by #3580. Revert or update the \
             classification audit.",
        ),
        other => panic!(
            "{name} ({rationale}): type must be Sort(succ(u)); got {other:?}. \
             A non-Sort, non-Const type means the carrier has been \
             restructured; update the classification audit.",
        ),
    }

    let type_dbg = format!("{:?}", info.type_);
    assert!(
        !type_dbg.contains("True"),
        "{name} ({rationale}): type debug form must not reference `True` \
         after the honest sorry-inhabited state; got: {type_dbg}. A `True` \
         reference suggests the #3462 `True:Prop` masquerade was \
         re-introduced.",
    );
}

/// (4) Value shape: must be a direct canonical synthetic `sorryAx` spine
///     when `sorryAx` is registered, or an App of Const("sorry", _) to the
///     type in legacy bootstrap environments.
///     A regression to `Const("True.intro", _)` would signal the #3462
///     recipe; a regression to a `Lam` without sorry inside would signal
///     some other (possibly masquerade) reduction.
fn check_value_is_sorry_app(env: &Environment, info: &ConstantInfo, name: &str, rationale: &str) {
    let value = info
        .value
        .as_ref()
        .expect("value presence already checked by check_value_present");
    let value_dbg = format!("{:?}", value);
    match value.kind() {
        ExprKind::App(_, _) => match value.get_app_fn().kind() {
            ExprKind::Const(const_name, _) => {
                let cs = const_name.to_string();
                assert!(
                    is_direct_sorry_placeholder(env, value),
                    "{name} ({rationale}): value head must be \
                     canonical synthetic Const(\"sorryAx\", _) or legacy \
                     Const(\"sorry\", _); got Const({cs}). A \
                     `True.intro` / `Exists.intro` / `Eq.refl` head would \
                     signal a sorry-pi reduction that must be classified \
                     against Rule M3. Full value: {value_dbg}",
                );
            }
            other => panic!(
                "{name} ({rationale}): value is an App, but its head is \
                 not Const(\"sorryAx\", _) or Const(\"sorry\", _); got \
                 App-head {other:?}. Full value: {value_dbg}",
            ),
        },
        other => panic!(
            "{name} ({rationale}): value must be a direct canonical \
             sorryAx/sorry application per register_c009_opaque_group; got \
             {other:?}. Full value: {value_dbg}",
        ),
    }

    assert!(
        !value_dbg.contains("True.intro"),
        "{name} ({rationale}): value debug form must not reference \
         `True.intro` — that would signal the #3462 Rule M3 masquerade \
         was re-introduced. Full value: {value_dbg}",
    );
}

fn is_direct_sorry_placeholder(env: &Environment, value: &Expr) -> bool {
    let ExprKind::Const(const_name, _) = value.get_app_fn().kind() else {
        return false;
    };
    let cs = const_name.to_string();
    if cs == "sorry" || cs.ends_with(".sorry") {
        return value.get_app_num_args() == 1;
    }
    if cs != "sorryAx" && !cs.ends_with(".sorryAx") {
        return false;
    }
    env.get_const(&Name::from_string("sorryAx")).is_some()
        && value.get_app_num_args() == 2
        && value.is_synthetic_sorry()
}

// ---------------------------------------------------------------------
// Bucket Z (in-scope for #3570): 6 sites, all MASQUERADE-prone.
// ---------------------------------------------------------------------

#[test]
fn guard_c009_bucket_z1_crown_backsubstitution_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_TRACTABLE_SITES[0];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z2_crown_combined_matrix_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_TRACTABLE_SITES[1];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z3_crown_correlation_retained_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_TRACTABLE_SITES[2];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_ay_ratio_monotone_depth_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_TRACTABLE_SITES[3];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z5_ratio_limit_zero_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_TRACTABLE_SITES[4];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z6_summary_conjecture_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_TRACTABLE_SITES[5];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

// ---------------------------------------------------------------------
// Bucket Z-exp (deferred per #3570 issue body): 4 exponential-gap sites.
// ---------------------------------------------------------------------

#[test]
fn guard_c009_bucket_z_exp1_norm_product_vs_product_norm_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_EXP_DEFERRED_SITES[0];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z_exp2_crown_uses_product_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_EXP_DEFERRED_SITES[1];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z_exp3_ibp_uses_product_of_norms_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_EXP_DEFERRED_SITES[2];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

#[test]
fn guard_c009_bucket_z_exp4_crown_ibp_ratio_exponential_is_honest_sorry() {
    let env = make_env();
    let (name, rationale) = C009_BUCKET_Z_EXP_DEFERRED_SITES[3];
    check_site_is_honest_sorry_opaque(&env, name, rationale);
}

// ---------------------------------------------------------------------
// Inventory invariant: the two buckets together cover EXACTLY the 10
// sorry-inhabited Opaques in C009. Catches drift if a new site is added
// without updating the classification.
// ---------------------------------------------------------------------

/// The union of C009_BUCKET_Z_TRACTABLE_SITES and
/// C009_BUCKET_Z_EXP_DEFERRED_SITES must exactly match the set of
/// `NNVerification.*` constants that are `ConstantKind::Opaque` and whose
/// stored value is a direct canonical `sorryAx` or legacy `sorry` placeholder
/// produced by `register_c009_opaque_group`. A new site in one bucket without
/// an entry in `C009_BUCKET_Z_*_SITES` fails this test and forces the
/// classification audit to be updated.
///
/// Note: this test intentionally EXCLUDES the 7 data Opaques (c009_ibp_width,
/// c009_crown_width, etc.) registered by `register_c009_opaques` — those
/// have bodies built via `nn_verification_c009_defs::build_*_value` (a
/// function, literal, or structure reference), not `@sorry`.
#[test]
fn guard_c009_sorry_opaque_inventory_matches_classification() {
    let env = make_env();

    let mut classified: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (name, _) in C009_BUCKET_Z_TRACTABLE_SITES
        .iter()
        .chain(C009_BUCKET_Z_EXP_DEFERRED_SITES.iter())
    {
        classified.insert((*name).to_string());
    }
    assert_eq!(
        classified.len(),
        10,
        "C009 classification buckets must cover exactly 10 sites \
         (6 tractable + 4 deferred); found {}. Update the per-bucket \
         const arrays if the inventory changes.",
        classified.len(),
    );

    // Walk all NNVerification. Opaques whose value is a direct sorry
    // placeholder and confirm every one is classified.
    let mut discovered: std::collections::HashSet<String> = std::collections::HashSet::new();
    for info in env.constants() {
        let s = info.name.to_string();
        if !s.starts_with("NNVerification.") {
            continue;
        }
        if info.kind != ConstantKind::Opaque {
            continue;
        }
        let Some(value) = info.value.as_ref() else {
            continue;
        };
        if is_direct_sorry_placeholder(&env, value) {
            discovered.insert(s);
        }
    }

    assert_eq!(
        discovered, classified,
        "C009 sorry-opaque inventory drift.\n\
         Classified (from C009_BUCKET_Z_*_SITES): {:?}\n\
         Discovered (from env scan): {:?}\n\
         Any site in `discovered` not in `classified` must be added to \
         one of the two bucket const arrays and to the audit report \
         reports/audit/2026-04-20-3570-c009-sorry-pi-carrier-classification.md. \
         Any site in `classified` not in `discovered` indicates a \
         silent reduction / demotion — update both.",
        classified, discovered,
    );
}
