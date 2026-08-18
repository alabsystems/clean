// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for Packets 1+2 of #2859 (par_reduces + the par_strips_witness
//! diamond vocabulary; the false single-step leaves par_subsumes_beta /
//! par_subst / par_strips were deleted 2026-07-01).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// Build the substitution subset of the spec. This bypasses the known
/// pre-existing `beta_subst_commutes` elaboration failure that blocks
/// `Specification::new()` (see design doc memory). `par_reduces` is in the
/// substitution bundle (`in_substitution: true` in `bundles.rs`).
fn build_par_test_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// `par_reduces` inductive is registered with its recursor.
#[test]
fn test_par_reduces_inductive_registered() {
    let spec = build_par_test_spec();
    assert!(
        spec.definitions().contains_key("par_reduces"),
        "par_reduces inductive should be registered"
    );
    assert!(
        spec.definitions().contains_key("par_reduces.rec"),
        "par_reduces recursor should be registered"
    );
}

/// All 9 `par_reduces` constructors are present: refl, beta, app, lam, pi,
/// forall_, let_ (the parallel zeta on the genuine KExpr.let_ constructor),
/// iota, let_cong (the trailing positional let congruence — let-promotion).
#[test]
fn test_par_reduces_has_nine_constructors() {
    let spec = build_par_test_spec();
    for ctor in [
        "par_reduces.refl",
        "par_reduces.beta",
        "par_reduces.app",
        "par_reduces.lam",
        "par_reduces.pi",
        "par_reduces.forall_",
        "par_reduces.let_",
        "par_reduces.iota",
        "par_reduces.let_cong",
    ] {
        assert!(
            spec.definitions().contains_key(ctor),
            "par_reduces constructor {ctor} should be registered"
        );
    }
}

/// `par_refl` is a DerivedProved lemma with zero axiom dependencies.
#[test]
fn test_par_refl_is_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_refl")
        .expect("par_refl should be registered");
    assert!(!def.is_axiom, "par_refl should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_refl should be tracked as a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_refl should be DerivedProved (direct constructor application)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_refl should carry no axiom dependencies: {:?}",
        def.axiom_deps
    );
    assert!(
        def.value_src.is_some(),
        "par_refl should have a constructive proof term"
    );
}

/// Wave 124 (Route B): the iota-free `par_reduces_bd` inductive is
/// registered with its recursor and exactly 8 constructors (no iota;
/// let_ = parallel zeta on the genuine KExpr.let_ constructor, let_cong =
/// its trailing positional congruence — let-promotion).
#[test]
fn test_par_reduces_bd_inductive_registered() {
    let spec = build_par_test_spec();
    assert!(
        spec.definitions().contains_key("par_reduces_bd"),
        "par_reduces_bd inductive should be registered"
    );
    assert!(
        spec.definitions().contains_key("par_reduces_bd.rec"),
        "par_reduces_bd recursor should be registered"
    );
    for ctor in [
        "par_reduces_bd.refl",
        "par_reduces_bd.beta",
        "par_reduces_bd.app",
        "par_reduces_bd.lam",
        "par_reduces_bd.pi",
        "par_reduces_bd.forall_",
        "par_reduces_bd.let_",
        "par_reduces_bd.let_cong",
    ] {
        assert!(
            spec.definitions().contains_key(ctor),
            "par_reduces_bd constructor {ctor} should be registered"
        );
    }
    // The iota constructor must NOT exist on the iota-free relation.
    assert!(
        !spec.definitions().contains_key("par_reduces_bd.iota"),
        "par_reduces_bd must have no iota constructor (it is iota-free)"
    );
}

/// Wave 124 (Route B): `par_reduces_bd_subsumes_par` is a DerivedProved
/// lemma (kernel-checked closed term) with zero axiom dependencies.
#[test]
fn test_par_reduces_bd_subsumes_par_is_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_bd_subsumes_par")
        .expect("par_reduces_bd_subsumes_par should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_bd_subsumes_par should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_bd_subsumes_par should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_bd_subsumes_par should be DerivedProved (Wave 124)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_bd_subsumes_par should carry no axiom dependencies: {:?}",
        def.axiom_deps
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_bd_subsumes_par should have a constructive proof term"
    );
}

/// Wave 125 (Route B): `par_subst_bd` is registered over the iota-free
/// relation with no axiom dependencies. It carries no iota dependency,
/// which is the whole point — the iota wall does not arise here.
#[test]
fn test_par_subst_bd_is_iota_free_derived_lemma() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_subst_bd")
        .expect("par_subst_bd should be registered");
    assert!(!def.is_axiom, "par_subst_bd should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_subst_bd should be a DerivedLemma"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_subst_bd should carry no axiom dependencies: {:?}",
        def.axiom_deps
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_subst_bd should record dependencies");
    assert!(
        deps.contains("par_reduces_bd.rec"),
        "par_subst_bd should depend on par_reduces_bd.rec"
    );
    // The defining property of Route B: par_subst_bd does NOT touch iota.
    assert!(
        !deps.contains("par_reduces.iota") && !deps.contains("iota_reduces"),
        "par_subst_bd must be iota-free (no iota dependency): {deps:?}"
    );
}

/// Wave 126 (Route B): the prerequisite chain for `par_subst_bd` is
/// registered in dependency order. Each lemma is a DerivedLemma carrying no
/// axiom dependencies and no iota dependency (Route B keeps the whole chain
/// iota-free). The proof terms land in subsequent waves bottom-up:
/// lift_instantiate_swap -> par_lift_bd -> par_subst_refl_bd -> par_subst_bd.
#[test]
fn test_par_subst_bd_prereq_chain_is_iota_free() {
    let spec = build_par_test_spec();
    for name in ["lift_instantiate_swap", "par_lift_bd", "par_subst_refl_bd"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
        if let Some(deps) = def.dependencies.as_ref() {
            assert!(
                !deps.contains("par_reduces.iota") && !deps.contains("iota_reduces"),
                "{name} must be iota-free (Route B): {deps:?}"
            );
        }
    }
    // The chain is ordered: par_lift_bd depends on lift_instantiate_swap, and
    // par_subst_refl_bd depends on par_lift_bd.
    let par_lift_bd_deps = spec
        .definitions()
        .get("par_lift_bd")
        .and_then(|d| d.dependencies.as_ref())
        .expect("par_lift_bd should record dependencies");
    assert!(
        par_lift_bd_deps.contains("lift_instantiate_swap"),
        "par_lift_bd should depend on lift_instantiate_swap"
    );
    let refl_deps = spec
        .definitions()
        .get("par_subst_refl_bd")
        .and_then(|d| d.dependencies.as_ref())
        .expect("par_subst_refl_bd should record dependencies");
    assert!(
        refl_deps.contains("par_lift_bd"),
        "par_subst_refl_bd should depend on par_lift_bd"
    );
}

/// The three false/unprovable single-step leaves over the iota-ful
/// `par_reduces` are DELETED (owner-approved 2026-07-01), not "drained":
/// `par_subsumes_beta` bundled two reductions through the widened `let_body`
/// arm; `par_subst`/`par_strips` were false at the ATOMIC `par_reduces.iota`
/// arm. This test fails closed against their silent reintroduction AND pins
/// the honest counterparts that carry the actual confluence content.
#[test]
fn test_false_single_step_leaves_are_deleted() {
    let spec = build_par_test_spec();
    for deleted in ["par_subsumes_beta", "par_subst", "par_strips"] {
        assert!(
            !spec.definitions().contains_key(deleted),
            "{deleted} was deleted as false/unprovable-as-stated \
             (owner-approved 2026-07-01); it must not be re-registered"
        );
    }
    // Honest counterparts: the star embedding and the iota-free single-step
    // substitution/diamond fragment must exist with real proof values.
    for (honest, needs_value) in [
        ("beta_subsumes_par_star", true),
        ("par_subst_bd", true),
        ("par_strips_bd", true),
    ] {
        let def = spec
            .definitions()
            .get(honest)
            .unwrap_or_else(|| panic!("honest counterpart {honest} should be registered"));
        if needs_value {
            assert!(
                def.value_src.is_some(),
                "{honest} should carry a real proof value"
            );
        }
    }
}

/// `beta_reduces_star` (reflexive-transitive closure) is registered with both
/// constructors (refl, step) and its recursor.
#[test]
fn test_beta_reduces_star_registered() {
    let spec = build_par_test_spec();
    assert!(
        spec.definitions().contains_key("beta_reduces_star"),
        "beta_reduces_star inductive should be registered"
    );
    assert!(
        spec.definitions().contains_key("beta_reduces_star.rec"),
        "beta_reduces_star recursor should be registered"
    );
    for ctor in ["beta_reduces_star.refl", "beta_reduces_star.step"] {
        assert!(
            spec.definitions().contains_key(ctor),
            "beta_reduces_star constructor {ctor} should be registered"
        );
    }
}

/// `beta_subsumes_par_star` is a DerivedLemma with zero axiom deps,
/// structurally dependent on the par_reduces recursor and beta_reduces_star
/// constructors.
#[test]
fn test_beta_subsumes_par_star_is_derived_lemma() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("beta_subsumes_par_star")
        .expect("beta_subsumes_par_star should be registered");
    assert!(
        !def.is_axiom,
        "beta_subsumes_par_star should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "beta_subsumes_par_star should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_subsumes_par_star should be DerivedProved (Wave 119)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "beta_subsumes_par_star should not carry axiom dependencies: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("beta_subsumes_par_star should record dependencies");
    for expected in [
        "par_reduces.rec",
        "beta_reduces_star.refl",
        "beta_reduces_star.step",
        "beta_reduces_star_trans",
        "beta_reduces_star_app_left",
        "beta_reduces_star_pi_dom",
        "beta_reduces_subsumes_star",
    ] {
        assert!(
            deps.contains(expected),
            "beta_subsumes_par_star should depend on {expected}: {deps:?}"
        );
    }
    // Proof term must induct via par_reduces.rec and compose through
    // beta_reduces_star_trans — lock the shape.
    let value = def
        .value_src
        .as_ref()
        .expect("beta_subsumes_par_star should have a constructive proof term");
    assert!(
        value.contains("par_reduces.rec") && value.contains("beta_reduces_star_trans"),
        "beta_subsumes_par_star proof term should induct via par_reduces.rec \
         and compose via beta_reduces_star_trans: {value}"
    );
}

/// `par_reduces` constructor coverage across refl/beta/app/lam/pi/iota cases
/// — one sentinel per canonical shape to lock the surface contract.
#[test]
fn test_par_reduces_constructor_coverage_by_shape() {
    let spec = build_par_test_spec();

    // refl — unary reflexivity constructor.
    assert!(spec.definitions().contains_key("par_reduces.refl"));
    // beta — parallel beta with three sub-reductions (ty, body, arg).
    assert!(spec.definitions().contains_key("par_reduces.beta"));
    // app — congruence on head and argument (two sub-reductions).
    assert!(spec.definitions().contains_key("par_reduces.app"));
    // lam — binder congruence (ty + body) for lambda.
    assert!(spec.definitions().contains_key("par_reduces.lam"));
    // pi — binder congruence (dom + body) for Pi.
    assert!(spec.definitions().contains_key("par_reduces.pi"));
    // iota — lifts iota_reduces witnesses into parallel reduction.
    assert!(spec.definitions().contains_key("par_reduces.iota"));
}

// =============================================================
// Packet 2 (#2859) — par_strips_witness (single-step diamond vocabulary)
// =============================================================
// The Packet-2 single-step leaves par_subst/par_strips (and Packet-1's
// par_subsumes_beta) were DELETED as false/unprovable-as-stated
// (owner-approved 2026-07-01); see test_false_single_step_leaves_are_deleted
// and the tombstones in par_reduction.rs.

/// `par_strips_witness` packages the diamond existential (no Sigma/Exists
/// in-tree). The witness vocabulary STAYS after the `par_strips` deletion —
/// it is consumed by the star-level diamond machinery.
#[test]
fn test_par_strips_witness_surface() {
    let spec = build_par_test_spec();
    for key in [
        "par_strips_witness",
        "par_strips_witness.intro",
        "par_strips_witness.rec",
    ] {
        assert!(
            spec.definitions().contains_key(key),
            "{key} should be registered"
        );
    }
}

/// Wave 138 (Route B): `par_strips_witness_bd` packages the iota-free
/// diamond existential, and `par_strips_bd` (the iota-free single-step
/// diamond) is now a DerivedProved lemma — a full closed proof term checked
/// by the kernel/spec when `build_par_test_spec()` constructed the spec. It
/// has zero axiom deps and a signature returning `par_strips_witness_bd e1 e2`
/// over `par_reduces_bd`, and depends on the Wave 134/135 diagonal/refl/symm
/// combinators plus the Wave 136/137 inversions and cross helpers — but never
/// on the iota constructor.
#[test]
fn test_par_strips_bd_packet_surface() {
    let spec = build_par_test_spec();
    for key in [
        "par_strips_witness_bd",
        "par_strips_witness_bd.intro",
        "par_strips_witness_bd.rec",
    ] {
        assert!(
            spec.definitions().contains_key(key),
            "{key} should be registered"
        );
    }
    let def = spec
        .definitions()
        .get("par_strips_bd")
        .expect("par_strips_bd should be registered");
    assert!(!def.is_axiom, "par_strips_bd should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_strips_bd should be a DerivedLemma"
    );
    // The keystone claim: par_strips_bd is now constructively proved. Reaching
    // this assertion is the kernel-check witness — the closed proof term was
    // type-checked by add_decl during spec construction, so a faked or
    // ill-typed term would have failed the build before any assertion ran.
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_strips_bd should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_strips_bd should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_strips_bd should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains("par_reduces_bd e e1")
            && def.type_src.contains("par_reduces_bd e e2")
            && def.type_src.contains("par_strips_witness_bd e1 e2"),
        "par_strips_bd signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_strips_bd should record dependencies");
    // The iota-free diamond must NOT mention the iota constructor anywhere
    // in its dependency surface — that is the entire point of Route B.
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "par_strips_bd must be iota-free: {deps:?}"
    );
    // The assembled term consumes the diagonal/refl/symm combinators, the
    // cross helper, the substitution lemma, and the inversions — including
    // the let-promotion let_-headed inversion and let diagonal combinator.
    for expected in [
        "par_subst_bd",
        "par_strips_bd_app",
        "par_strips_bd_app_beta",
        "par_strips_witness_bd_symm",
        "par_reduces_bd_app_inv",
        "par_reduces_bd_lam_inv_eq",
        "par_reduces_bd_let_inv",
        "par_strips_bd_let",
        "par_reduces_bd.let_cong",
    ] {
        assert!(
            deps.contains(expected),
            "par_strips_bd should depend on {expected}: {deps:?}"
        );
    }
}

/// Wave 139 (Route B iota seam): a small DerivedProved checker that does NOT
/// forbid recursors in the proof term (unlike `assert_proved_wrapper`), since
/// the embedding lemma legitimately runs `par_strips_witness_bd.rec`. Reaching
/// the assertions is the kernel-check witness — the proof term was type-checked
/// by add_decl when `build_par_test_spec()` constructed the spec, so a faked or
/// ill-typed term would have failed the build before any assertion ran.
fn assert_seam_proved(spec: &Specification, name: &str, deps_expected: &[&str]) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered (Wave 139)"));
    assert!(!def.is_axiom, "{name} should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "{name} should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should carry zero axiom dependencies: {:?}",
        def.axiom_deps
    );
    assert!(
        def.value_src.is_some(),
        "{name} should carry a closed proof term"
    );
    let deps = def
        .dependencies
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should record dependencies"));
    for expected in deps_expected {
        assert!(
            deps.contains(*expected),
            "{name} should depend on {expected}: {deps:?}"
        );
    }
}

/// Wave 139 (Route B iota seam): `par_strips_witness_bd_subsumes_par` embeds
/// the iota-free diamond witness into the full `par_strips_witness` by lifting
/// both legs through `par_reduces_bd_subsumes_par`. DerivedProved, zero
/// axiom_deps, no iota dependency.
#[test]
fn test_par_strips_witness_bd_subsumes_par_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_strips_witness_bd_subsumes_par",
        &[
            "par_reduces_bd_subsumes_par",
            "par_strips_witness",
            "par_strips_witness.intro",
            "par_strips_witness_bd",
            "par_strips_witness_bd.rec",
        ],
    );
    let def = spec
        .definitions()
        .get("par_strips_witness_bd_subsumes_par")
        .expect("par_strips_witness_bd_subsumes_par should be registered");
    assert!(
        def.type_src.contains("par_strips_witness_bd e1 e2")
            && def.type_src.contains("par_strips_witness e1 e2"),
        "embedding signature surface drift: {}",
        def.type_src
    );
    let deps = def.dependencies.as_ref().expect("deps");
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "the iota-free embedding must not mention iota: {deps:?}"
    );
}

/// Wave 139 (Route B iota seam): `par_strips_bd_to_par` delivers the iota-free
/// single-step diamond at the full `par_reduces` witness level — when both
/// input derivations are iota-free (`par_reduces_bd`), the full diamond reduces
/// to `par_strips_bd`. This is the iota-free arm the eventual `par_strips`
/// recursor term consumes. DerivedProved, zero axiom_deps, no iota dependency.
#[test]
fn test_par_strips_bd_to_par_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_strips_bd_to_par",
        &[
            "par_strips_bd",
            "par_strips_witness",
            "par_strips_witness_bd_subsumes_par",
        ],
    );
    let def = spec
        .definitions()
        .get("par_strips_bd_to_par")
        .expect("par_strips_bd_to_par should be registered");
    assert!(
        def.type_src.contains("par_reduces_bd e e1")
            && def.type_src.contains("par_reduces_bd e e2")
            && def.type_src.contains("par_strips_witness e1 e2"),
        "iota-free-to-full diamond signature surface drift: {}",
        def.type_src
    );
    let deps = def.dependencies.as_ref().expect("deps");
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "the iota-free arm must not mention iota: {deps:?}"
    );
}

/// Wave 139 (Route B iota seam): the two closable iota-headed join handlers,
/// `par_strips_iota_left_refl` (iota, refl) and `par_strips_iota_right_refl`
/// (refl, iota), join an iota reduct against the identity at the reduct itself
/// by forwarding the iota witness. DerivedProved, zero axiom_deps, with the
/// signature meeting an `iota_reduces` hypothesis and returning the packaged
/// witness. These are the only iota-headed cross cases dischargeable from the
/// abstract iota witness alone.
#[test]
fn test_par_strips_iota_refl_seams_are_derived_proved() {
    let spec = build_par_test_spec();
    for (name, ty_target) in [
        ("par_strips_iota_left_refl", "par_strips_witness e' e"),
        ("par_strips_iota_right_refl", "par_strips_witness e e'"),
    ] {
        assert_seam_proved(
            &spec,
            name,
            &[
                "iota_reduces",
                "par_reduces.refl",
                "par_reduces.iota",
                "par_strips_witness",
                "par_strips_witness.intro",
            ],
        );
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            def.type_src.contains("iota_reduces e e'") && def.type_src.contains(ty_target),
            "{name} signature surface drift: {}",
            def.type_src
        );
    }
}

/// Wave 134 (Route B): the two refl meeting-point helpers for the
/// iota-free diamond are DerivedProved closed terms (no recursion),
/// kernel-checked with zero axiom_deps.
#[test]
fn test_par_strips_bd_refl_helpers_are_derived_proved() {
    let spec = build_par_test_spec();
    for name in ["par_strips_bd_refl_left", "par_strips_bd_refl_right"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have zero axiom_deps: {:?}",
            def.axiom_deps
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
    }
}

/// Wave 135 (Route B): the four binary congruence combinators
/// (app/lam/pi/forall_) and the symmetry combinator for the iota-free
/// single-step diamond are DerivedProved closed terms (recursion only on
/// par_strips_witness_bd, never on par_reduces_bd), kernel-checked with
/// zero axiom_deps and iota-free dependency surfaces. These discharge the
/// congruence-diagonal arms of par_strips_bd. Reaching this assertion is
/// itself the kernel-check witness: the proof terms were checked by add_decl
/// when build_par_test_spec() constructed the spec, so a faked or ill-typed
/// term would have failed the build before any assertion ran.
#[test]
fn test_par_strips_bd_congruence_combinators_are_derived_proved() {
    let spec = build_par_test_spec();
    for (name, ctor_dep) in [
        ("par_strips_bd_app", "par_reduces_bd.app"),
        ("par_strips_bd_lam", "par_reduces_bd.lam"),
        ("par_strips_bd_pi", "par_reduces_bd.pi"),
        ("par_strips_bd_forall", "par_reduces_bd.forall_"),
        ("par_strips_witness_bd_symm", "par_reduces_bd"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered (Wave 135 of #2859)"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (kernel-checked closed term)"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry zero axiom_deps: {:?}",
            def.axiom_deps
        );
        let value = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should carry a closed proof term"));
        // The diamond witness recursor is the only eliminator used: the
        // combinators destructure the input witnesses, never recursing on
        // the par_reduces_bd derivations themselves.
        assert!(
            value.contains("par_strips_witness_bd.rec"),
            "{name} should use par_strips_witness_bd.rec to project the witnesses"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record dependencies"));
        assert!(
            deps.contains(ctor_dep),
            "{name} should depend on {ctor_dep}: {deps:?}"
        );
        // Route B invariant: the iota-free diamond fragment never threads
        // the iota constructor through any of its combinators.
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// Wave 135 (Route B): the congruence combinators expose exactly the
/// compound diamond shapes the diagonal arms of par_strips_bd need — the
/// app combinator on `KExpr.app`, the binder combinators on their matching
/// `KExpr.lam`/`KExpr.pi`/`KExpr.forall_` heads — and the symmetry
/// combinator swaps the two diamond sources.
#[test]
fn test_par_strips_bd_combinator_signatures_match_diagonal_arms() {
    let spec = build_par_test_spec();
    for (name, head) in [
        ("par_strips_bd_app", "KExpr.app"),
        ("par_strips_bd_lam", "KExpr.lam"),
        ("par_strips_bd_pi", "KExpr.pi"),
        ("par_strips_bd_forall", "KExpr.forall_"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            def.type_src
                .contains(&format!("par_strips_witness_bd ({head}")),
            "{name} conclusion should produce a {head} diamond witness: {}",
            def.type_src
        );
    }
    let symm = spec
        .definitions()
        .get("par_strips_witness_bd_symm")
        .expect("par_strips_witness_bd_symm should be registered");
    assert!(
        symm.type_src.contains("par_strips_witness_bd e1 e2")
            && symm.type_src.contains("par_strips_witness_bd e2 e1"),
        "symmetry combinator should swap the two sources: {}",
        symm.type_src
    );
}

/// Wave 137 (Route B): the three cross-arm support lemmas the full
/// `par_strips_bd` assembly consumes are DerivedProved closed terms with
/// zero axiom_deps and iota-free dependency surfaces.
///
/// `par_reduces_bd_lam_inv_eq` is the Eq-data lam inversion (hands the reduct
/// equality to the continuation so two derivations can be joined on the same
/// reduct); `par_strips_witness_bd_lam_meet` is body sub-meet recovery from a
/// lam-lam diamond witness; `par_strips_bd_app_beta` is the (app, beta) cross
/// core (first side a syntactic redex contracted via par_reduces_bd.beta,
/// second via par_subst_bd).
///
/// Reaching this assertion is itself the kernel-check witness: the proof
/// terms were checked by add_decl when build_par_test_spec() constructed the
/// spec, so a faked or ill-typed term would have failed the build first.
#[test]
fn test_par_strips_bd_cross_support_lemmas_are_derived_proved() {
    let spec = build_par_test_spec();
    for (name, expected_dep) in [
        ("par_reduces_bd_lam_inv_eq", "par_reduces_bd.rec"),
        (
            "par_strips_witness_bd_lam_meet",
            "par_reduces_bd_lam_inv_eq",
        ),
        ("par_strips_bd_app_beta", "par_subst_bd"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered (Wave 137 of #2859)"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (kernel-checked closed term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry zero axiom_deps: {:?}",
            def.axiom_deps
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record dependencies"));
        assert!(
            deps.contains(expected_dep),
            "{name} should depend on {expected_dep}: {deps:?}"
        );
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// `beta_reduces_subsumes_star` (Wave 115): single-step beta_reduces
/// embeds into beta_reduces_star. DerivedProved with a closed term
/// built directly from beta_reduces_star.step + beta_reduces_star.refl
/// — no recursion on the input, zero axiom_deps.
#[test]
fn test_beta_reduces_subsumes_star_is_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("beta_reduces_subsumes_star")
        .expect("beta_reduces_subsumes_star should be registered");
    assert!(
        !def.is_axiom,
        "beta_reduces_subsumes_star should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "beta_reduces_subsumes_star should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_subsumes_star should be DerivedProved (closed \
         constructor application)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "beta_reduces_subsumes_star should carry no axiom dependencies: \
         {:?}",
        def.axiom_deps
    );
    assert!(
        def.value_src.is_some(),
        "beta_reduces_subsumes_star should have a constructive proof term"
    );
    let value = def.value_src.as_ref().expect("checked Some above");
    // Lock the proof-term shape: it must use both beta_reduces_star
    // constructors (step + refl) and route through the input h directly,
    // with no recursor invocation.
    assert!(
        value.contains("beta_reduces_star.step") && value.contains("beta_reduces_star.refl"),
        "beta_reduces_subsumes_star proof term should use step + refl \
         constructors directly: {value}"
    );
    assert!(
        !value.contains(".rec"),
        "beta_reduces_subsumes_star proof term should not use any \
         recursor (single-step embedding, no induction): {value}"
    );
}

/// `beta_reduces_star_trans` (Wave 117): transitivity of the reflexive-
/// transitive closure of beta_reduces. DerivedProved with zero axiom
/// dependencies — the closed term is a single `beta_reduces_star.rec`
/// induction on the first argument that prefixes each step onto the
/// recursively-extended tail. The explicit helper cited by
/// `beta_subsumes_par_star` for congruence composition.
#[test]
fn test_beta_reduces_star_trans_packet_surface() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("beta_reduces_star_trans")
        .expect("beta_reduces_star_trans should be registered");
    assert!(
        !def.is_axiom,
        "beta_reduces_star_trans should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "beta_reduces_star_trans should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_star_trans should be DerivedProved (Wave 117)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "beta_reduces_star_trans should have zero HelperAxiom deps: {:?}",
        def.axiom_deps
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("beta_reduces_star_trans should record dependencies");
    for expected in [
        "beta_reduces_star",
        "beta_reduces_star.rec",
        "beta_reduces_star.refl",
        "beta_reduces_star.step",
    ] {
        assert!(
            deps.contains(expected),
            "beta_reduces_star_trans should depend on {expected}: {deps:?}"
        );
    }
    // Proof term must induct via the recursor and rebuild with the step
    // constructor — lock the shape against drift.
    let value = def
        .value_src
        .as_ref()
        .expect("beta_reduces_star_trans should have a constructive proof term");
    assert!(
        value.contains("beta_reduces_star.rec") && value.contains("beta_reduces_star.step"),
        "beta_reduces_star_trans proof term should induct via .rec and rebuild via .step: {value}"
    );
    // Signature sanity: three-argument transitivity surface. Locks the
    // contract against accidental shape drift in future packets.
    assert!(
        def.type_src.contains("beta_reduces_star e1 e2")
            && def.type_src.contains("beta_reduces_star e2 e3")
            && def.type_src.contains("beta_reduces_star e1 e3"),
        "beta_reduces_star_trans signature surface drift: {}",
        def.type_src
    );
}

/// Shared DerivedProved-wrapper assertion for the Wave 116 par_reduces
/// single-side congruence helpers. Each is a closed constructor term with
/// no recursor invocation and zero axiom dependencies.
fn assert_proved_wrapper(
    spec: &Specification,
    name: &str,
    deps_expected: &[&str],
    value_must_contain: &[&str],
) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered (Wave 116)"));
    assert!(!def.is_axiom, "{name} should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "{name} should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved (closed constructor application)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should carry no axiom dependencies: {:?}",
        def.axiom_deps
    );
    let value = def
        .value_src
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should have a constructive proof term"));
    assert!(
        !value.contains(".rec"),
        "{name} proof term should not invoke any recursor (direct \
         constructor wrapper): {value}"
    );
    for fragment in value_must_contain {
        assert!(
            value.contains(*fragment),
            "{name} proof term should contain {fragment}: {value}"
        );
    }
    let deps = def
        .dependencies
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should record dependencies"));
    for expected in deps_expected {
        assert!(
            deps.contains(*expected),
            "{name} should depend on {expected}: {deps:?}"
        );
    }
}

/// `par_reduces_star` (Wave 120): reflexive-transitive closure of
/// par_reduces, registered with both constructors and its recursor.
#[test]
fn test_par_reduces_star_registered() {
    let spec = build_par_test_spec();
    assert!(
        spec.definitions().contains_key("par_reduces_star"),
        "par_reduces_star inductive should be registered"
    );
    assert!(
        spec.definitions().contains_key("par_reduces_star.rec"),
        "par_reduces_star recursor should be registered"
    );
    for ctor in ["par_reduces_star.refl", "par_reduces_star.step"] {
        assert!(
            spec.definitions().contains_key(ctor),
            "par_reduces_star constructor {ctor} should be registered"
        );
    }
}

/// `par_subsumes_par_star` and `par_reduces_star_trans` (Wave 120) are
/// DerivedProved with zero axiom deps: the single-step embedding (direct
/// constructor, no recursion) and the transitivity (par_reduces_star.rec
/// induction on the first argument).
#[test]
fn test_par_reduces_star_lemmas_are_derived_proved() {
    let spec = build_par_test_spec();

    let embed = spec
        .definitions()
        .get("par_subsumes_par_star")
        .expect("par_subsumes_par_star should be registered");
    assert!(
        !embed.is_axiom,
        "par_subsumes_par_star should not be an axiom"
    );
    assert_eq!(embed.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        embed.proof_status,
        ProofStatus::DerivedProved,
        "par_subsumes_par_star should be DerivedProved (Wave 120)"
    );
    assert!(
        embed.axiom_deps.is_empty(),
        "par_subsumes_par_star zero axiom_deps: {:?}",
        embed.axiom_deps
    );
    let embed_value = embed
        .value_src
        .as_ref()
        .expect("par_subsumes_par_star should have a proof term");
    assert!(
        embed_value.contains("par_reduces_star.step")
            && embed_value.contains("par_reduces_star.refl")
            && !embed_value.contains(".rec"),
        "par_subsumes_par_star should be a direct constructor term (no .rec): {embed_value}"
    );

    let trans = spec
        .definitions()
        .get("par_reduces_star_trans")
        .expect("par_reduces_star_trans should be registered");
    assert!(
        !trans.is_axiom,
        "par_reduces_star_trans should not be an axiom"
    );
    assert_eq!(trans.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        trans.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_star_trans should be DerivedProved (Wave 120)"
    );
    assert!(
        trans.axiom_deps.is_empty(),
        "par_reduces_star_trans zero axiom_deps: {:?}",
        trans.axiom_deps
    );
    let trans_value = trans
        .value_src
        .as_ref()
        .expect("par_reduces_star_trans should have a proof term");
    assert!(
        trans_value.contains("par_reduces_star.rec")
            && trans_value.contains("par_reduces_star.step"),
        "par_reduces_star_trans should induct via .rec and rebuild via .step: {trans_value}"
    );
    assert!(
        trans.type_src.contains("par_reduces_star e1 e2")
            && trans.type_src.contains("par_reduces_star e2 e3")
            && trans.type_src.contains("par_reduces_star e1 e3"),
        "par_reduces_star_trans signature surface drift: {}",
        trans.type_src
    );
}

/// Wave 121 par-level star congruence helpers + the corrected
/// `par_subsumes_beta_star` (beta ⊆ par*). The nine helpers each induct via
/// par_reduces_star.rec and prefix the matching par_reduces congruence
/// constructor (the three let positions via par_reduces.let_cong on the
/// genuine KExpr.let_ constructor — let-promotion); par_subsumes_beta_star
/// inducts via beta_reduces.rec and composes them (the zeta arm is a single
/// par step — the pre-promotion bundled let_body arm and its two-step
/// par_reduces_star_trans composition are gone). All DerivedProved, zero
/// axiom deps.
#[test]
fn test_par_reduces_star_congruence_helpers_are_derived_proved() {
    let spec = build_par_test_spec();
    for (name, par_ctor) in [
        ("par_reduces_star_app_left", "par_reduces.app"),
        ("par_reduces_star_app_right", "par_reduces.app"),
        ("par_reduces_star_lam_ty", "par_reduces.lam"),
        ("par_reduces_star_lam_body", "par_reduces.lam"),
        ("par_reduces_star_pi_dom", "par_reduces.pi"),
        ("par_reduces_star_pi_cod", "par_reduces.pi"),
        ("par_reduces_star_let_ty", "par_reduces.let_cong"),
        ("par_reduces_star_let_val", "par_reduces.let_cong"),
        ("par_reduces_star_let_body", "par_reduces.let_cong"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered (Wave 121)"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(def.category, AxiomCategory::DerivedLemma);
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (Wave 121)"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have zero HelperAxiom deps: {:?}",
            def.axiom_deps
        );
        let value = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a constructive proof term"));
        assert!(
            value.contains("par_reduces_star.rec")
                && value.contains("par_reduces_star.step")
                && value.contains(par_ctor),
            "{name} proof term should induct via .rec and prefix {par_ctor}: {value}"
        );
    }
}

/// `par_subsumes_beta_star` (Wave 121): the corrected beta ⊆ par* embedding
/// (replacing the unprovable single→single par_subsumes_beta). DerivedProved,
/// zero axiom deps, inducts via beta_reduces.rec. Post let-promotion its zeta
/// arm embeds ONE par step (par_reduces.let_, the parallel zeta) and the
/// let_ty/let_val/let_body arms lift through the genuine-let_ positional star
/// congruence helpers (the old bundled let_body arm and its two-step
/// par_reduces_star_trans composition are gone).
#[test]
fn test_par_subsumes_beta_star_is_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_subsumes_beta_star")
        .expect("par_subsumes_beta_star should be registered (Wave 121)");
    assert!(
        !def.is_axiom,
        "par_subsumes_beta_star should not be an axiom"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_subsumes_beta_star should be DerivedProved (Wave 121)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_subsumes_beta_star should have zero HelperAxiom deps: {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains("beta_reduces e e'")
            && def.type_src.contains("par_reduces_star e e'"),
        "par_subsumes_beta_star signature surface drift: {}",
        def.type_src
    );
    let value = def
        .value_src
        .as_ref()
        .expect("par_subsumes_beta_star should have a constructive proof term");
    assert!(
        value.contains("beta_reduces.rec")
            && value.contains("par_subsumes_par_star")
            && value.contains("par_reduces_star_let_body"),
        "par_subsumes_beta_star proof term should induct via beta_reduces.rec, \
         embed single steps via par_subsumes_par_star, and lift the let \
         congruences through the genuine-let_ star helpers: {value}"
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_subsumes_beta_star should record dependencies");
    for expected in [
        "beta_reduces.rec",
        "par_reduces_star",
        "par_subsumes_par_star",
        "par_reduces_star_app_left",
        "par_reduces.let_",
        "par_reduces_star_let_ty",
        "par_reduces_star_let_val",
        "par_reduces_star_let_body",
    ] {
        assert!(
            deps.contains(expected),
            "par_subsumes_beta_star should depend on {expected}: {deps:?}"
        );
    }
}

/// Wave 118 star-level congruence helpers: each lifts a multi-step
/// reduction in one position into the surrounding constructor via
/// `beta_reduces_star.rec`. DerivedProved, zero axiom deps, and the proof
/// term must induct (uses `.rec`) and prefix the matching single-step
/// `beta_reduces` congruence constructor.
#[test]
fn test_beta_reduces_star_congruence_helpers_are_derived_proved() {
    let spec = build_par_test_spec();
    for (name, beta_ctor) in [
        ("beta_reduces_star_app_left", "beta_reduces.app_left"),
        ("beta_reduces_star_app_right", "beta_reduces.app_right"),
        ("beta_reduces_star_lam_ty", "beta_reduces.lam_ty"),
        ("beta_reduces_star_lam_body", "beta_reduces.lam_body"),
        ("beta_reduces_star_pi_dom", "beta_reduces.pi_dom"),
        ("beta_reduces_star_pi_cod", "beta_reduces.pi_cod"),
        ("beta_reduces_star_let_ty", "beta_reduces.let_ty"),
        ("beta_reduces_star_let_val", "beta_reduces.let_val"),
        ("beta_reduces_star_let_body", "beta_reduces.let_body"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered (Wave 118)"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (Wave 118)"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have zero HelperAxiom deps: {:?}",
            def.axiom_deps
        );
        let value = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a constructive proof term"));
        assert!(
            value.contains("beta_reduces_star.rec")
                && value.contains("beta_reduces_star.step")
                && value.contains(beta_ctor),
            "{name} proof term should induct via .rec and prefix {beta_ctor}: {value}"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record dependencies"));
        assert!(
            deps.contains("beta_reduces_star.rec") && deps.contains(beta_ctor),
            "{name} should depend on beta_reduces_star.rec and {beta_ctor}: {deps:?}"
        );
    }
}

/// `par_reduces_app_left` (Wave 116): left congruence of par_reduces over
/// application, holding the argument fixed via par_reduces.refl.
#[test]
fn test_par_reduces_app_left_is_proved_wrapper() {
    let spec = build_par_test_spec();
    assert_proved_wrapper(
        &spec,
        "par_reduces_app_left",
        &["par_reduces", "par_reduces.app", "par_reduces.refl"],
        &["par_reduces.app", "par_reduces.refl"],
    );
    let def = spec
        .definitions()
        .get("par_reduces_app_left")
        .expect("registered");
    assert!(
        def.type_src
            .contains("par_reduces (KExpr.app f a) (KExpr.app f' a)"),
        "par_reduces_app_left signature surface drift: {}",
        def.type_src
    );
}

/// `par_reduces_app_right` (Wave 116): right congruence of par_reduces
/// over application, holding the head fixed via par_reduces.refl.
#[test]
fn test_par_reduces_app_right_is_proved_wrapper() {
    let spec = build_par_test_spec();
    assert_proved_wrapper(
        &spec,
        "par_reduces_app_right",
        &["par_reduces", "par_reduces.app", "par_reduces.refl"],
        &["par_reduces.app", "par_reduces.refl"],
    );
    let def = spec
        .definitions()
        .get("par_reduces_app_right")
        .expect("registered");
    assert!(
        def.type_src
            .contains("par_reduces (KExpr.app f a) (KExpr.app f a')"),
        "par_reduces_app_right signature surface drift: {}",
        def.type_src
    );
}

/// `par_reduces_iota_lift` (Wave 116): lift an iota_reduces witness into
/// par_reduces via the par_reduces.iota constructor.
#[test]
fn test_par_reduces_iota_lift_is_proved_wrapper() {
    let spec = build_par_test_spec();
    assert_proved_wrapper(
        &spec,
        "par_reduces_iota_lift",
        &["par_reduces", "par_reduces.iota", "iota_reduces"],
        &["par_reduces.iota"],
    );
    let def = spec
        .definitions()
        .get("par_reduces_iota_lift")
        .expect("registered");
    assert!(
        def.type_src
            .contains("iota_reduces e e' -> par_reduces e e'"),
        "par_reduces_iota_lift signature surface drift: {}",
        def.type_src
    );
}

/// Wave 136 (Route B): shared assertions for the four par_reduces_bd
/// shape-recovery (inversion) lemmas. Each is a DerivedProved closed term
/// (kernel-checked by add_decl when build_par_test_spec() built the spec —
/// reaching the assertion is itself the kernel-check witness) carrying a
/// proof term, zero axiom_deps, and an iota-free dependency surface (Route B).
fn assert_inversion_lemma(spec: &Specification, name: &str, deps_expected: &[&str]) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered (Wave 136 of #2859)"));
    assert!(!def.is_axiom, "{name} should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "{name} should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved (kernel-checked closed term)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should carry zero axiom_deps (FOUNDATIONAL closure only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.value_src.is_some(),
        "{name} should carry a closed constructive proof term"
    );
    let deps = def
        .dependencies
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should record dependencies"));
    for expected in deps_expected {
        assert!(
            deps.contains(*expected),
            "{name} should depend on {expected}: {deps:?}"
        );
    }
    // Route B keeps the inversion convoy iota-free: the iota-free relation
    // par_reduces_bd has no iota constructor, so no inversion arm can mention
    // it. The dependency surface must reflect that.
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "{name} must be iota-free (Route B): {deps:?}"
    );
}

/// Wave 136 (Route B): `par_reduces_bd_app_inv` recovers the constructor
/// shape of an app-headed iota-free parallel reduction. The refl/app
/// constructors fold into the congruence continuation; beta folds into the
/// contraction continuation; lam/pi/forall_ are discharged by no-confusion
/// (lam_ne_app/pi_ne_app), and — post let-promotion — so are the let_-headed
/// let_/let_cong sources (let_ne_app). This is the
/// keystone convoy lemma that was the documented blocker for par_strips_bd.
#[test]
fn test_par_reduces_bd_app_inv_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_inversion_lemma(
        &spec,
        "par_reduces_bd_app_inv",
        &[
            "par_reduces_bd.rec",
            "par_reduces_bd.refl",
            "app_inj_fst",
            "app_inj_snd",
            "lam_ne_app",
            "pi_ne_app",
            "let_ne_app",
            "Eq.substType",
        ],
    );
    let def = spec
        .definitions()
        .get("par_reduces_bd_app_inv")
        .expect("registered");
    assert!(
        def.type_src.contains("par_reduces_bd (KExpr.app f a) t")
            && def.type_src.contains("C (KExpr.app f' a')")
            && def.type_src.contains("C (instantiate body' arg')"),
        "par_reduces_bd_app_inv signature surface drift: {}",
        def.type_src
    );
}

/// Wave 136 (Route B): `par_reduces_bd_lam_inv` recovers t = lam ty' body'
/// from a lam-headed iota-free parallel reduction. Every non-lam constructor
/// is impossible (app_ne_lam for the app-headed beta/app sources,
/// pi_ne_lam for the pi-headed pi/forall_ sources, let_ne_lam for the
/// let_-headed let_/let_cong sources — let-promotion).
#[test]
fn test_par_reduces_bd_lam_inv_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_inversion_lemma(
        &spec,
        "par_reduces_bd_lam_inv",
        &[
            "par_reduces_bd.rec",
            "par_reduces_bd.refl",
            "lam_inj_fst",
            "lam_inj_snd",
            "app_ne_lam",
            "pi_ne_lam",
            "let_ne_lam",
            "Eq.substType",
        ],
    );
    let def = spec
        .definitions()
        .get("par_reduces_bd_lam_inv")
        .expect("registered");
    assert!(
        def.type_src
            .contains("par_reduces_bd (KExpr.lam ty body) t")
            && def.type_src.contains("C (KExpr.lam ty' body')"),
        "par_reduces_bd_lam_inv signature surface drift: {}",
        def.type_src
    );
}

/// Wave 136 (Route B): the two pi-headed inversions
/// (`par_reduces_bd_pi_inv`, `par_reduces_bd_forall_inv`). Because
/// KExpr.forall_ is the reducible alias of KExpr.pi, BOTH the pi and forall_
/// constructor arms are genuine matching cases (recovered via pi_inj_fst/snd),
/// while the app-headed and lam arms discharge by app_ne_pi / lam_ne_pi and
/// the let_-headed let_/let_cong arms by let_ne_pi (let-promotion).
#[test]
fn test_par_reduces_bd_pi_like_inv_are_derived_proved() {
    let spec = build_par_test_spec();
    for (name, head, red_head) in [
        ("par_reduces_bd_pi_inv", "KExpr.pi", "KExpr.pi"),
        (
            "par_reduces_bd_forall_inv",
            "KExpr.forall_",
            "KExpr.forall_",
        ),
    ] {
        assert_inversion_lemma(
            &spec,
            name,
            &[
                "par_reduces_bd.rec",
                "par_reduces_bd.refl",
                "pi_inj_fst",
                "pi_inj_snd",
                "app_ne_pi",
                "lam_ne_pi",
                "let_ne_pi",
                "Eq.substType",
            ],
        );
        let def = spec.definitions().get(name).expect("registered");
        assert!(
            def.type_src
                .contains(&format!("par_reduces_bd ({head} dom body) t"))
                && def.type_src.contains(&format!("C ({red_head} dom' body')")),
            "{name} signature surface drift: {}",
            def.type_src
        );
    }
}

/// Let-promotion: `par_reduces_bd_let_inv` recovers the constructor shape of a
/// let_-HEADED iota-free parallel reduction (the genuine KExpr.let_
/// constructor gets its own inversion — before the promotion a let was
/// app-headed and the app inversion covered it). refl/let_cong fold into the
/// congruence continuation, let_ (zeta) into the zeta continuation; beta/app
/// discharge by app_ne_let, lam by lam_ne_let, pi/forall_ by pi_ne_let;
/// matching arms recover sub-terms via let_inj_fst/snd/thd.
#[test]
fn test_par_reduces_bd_let_inv_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_inversion_lemma(
        &spec,
        "par_reduces_bd_let_inv",
        &[
            "par_reduces_bd.rec",
            "par_reduces_bd.refl",
            "let_inj_fst",
            "let_inj_snd",
            "let_inj_thd",
            "app_ne_let",
            "lam_ne_let",
            "pi_ne_let",
            "Eq.substType",
        ],
    );
    let def = spec
        .definitions()
        .get("par_reduces_bd_let_inv")
        .expect("registered");
    assert!(
        def.type_src
            .contains("par_reduces_bd (KExpr.let_ ty val body) t")
            && def.type_src.contains("C (KExpr.let_ ty' val' body')")
            && def.type_src.contains("C (instantiate body' val')"),
        "par_reduces_bd_let_inv signature surface drift: {}",
        def.type_src
    );
}

/// Wave 140 (Route B): the iota-free multi-step closure `par_reduces_bd_star`
/// and the generalized join witness `par_strips_witness_bd_star` are both
/// registered as inductives (with recursor + constructors). These are the
/// carriers for the iota-free multi-step diamond — confluence of the
/// reflexive-transitive closure of `par_reduces_bd`.
#[test]
fn test_par_reduces_bd_star_inductives_registered() {
    let spec = build_par_test_spec();
    for key in [
        "par_reduces_bd_star",
        "par_reduces_bd_star.rec",
        "par_reduces_bd_star.refl",
        "par_reduces_bd_star.step",
        "par_strips_witness_bd_star",
        "par_strips_witness_bd_star.rec",
        "par_strips_witness_bd_star.intro",
    ] {
        assert!(
            spec.definitions().contains_key(key),
            "{key} should be registered (Wave 140)"
        );
    }
    // The closure must be iota-free: no iota constructor anywhere.
    assert!(
        !spec.definitions().contains_key("par_reduces_bd_star.iota"),
        "par_reduces_bd_star must have no iota constructor (it is iota-free)"
    );
}

/// Wave 140 (Route B): the closure-support lemmas `par_subsumes_bd_star`
/// (single-step embedding) and `par_reduces_bd_star_trans` (transitivity) are
/// DerivedProved with zero axiom_deps and no iota dependency. These are the
/// iota-free analogues of `par_subsumes_par_star` / `par_reduces_star_trans`.
#[test]
fn test_par_reduces_bd_star_support_lemmas_are_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_subsumes_bd_star",
        &[
            "par_reduces_bd",
            "par_reduces_bd_star",
            "par_reduces_bd_star.refl",
            "par_reduces_bd_star.step",
        ],
    );
    assert_seam_proved(
        &spec,
        "par_reduces_bd_star_trans",
        &[
            "par_reduces_bd_star",
            "par_reduces_bd_star.rec",
            "par_reduces_bd_star.refl",
            "par_reduces_bd_star.step",
        ],
    );
    for name in ["par_subsumes_bd_star", "par_reduces_bd_star_trans"] {
        let def = spec.definitions().get(name).expect("registered");
        let deps = def.dependencies.as_ref().expect("deps");
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// Wave 140 (Route B) — GOAL #2: the iota-free STRIP lemma
/// `par_strips_bd_star_strip` strips one multi-step leg against one single-step
/// leg into a multi-step join. It is DerivedProved — a full closed proof term
/// kernel-checked by `add_decl` when `build_par_test_spec()` constructed the
/// spec, so a faked or ill-typed term would have failed the build before any
/// assertion ran. Zero axiom_deps; consumes the single-step diamond
/// `par_strips_bd` (Wave 138); entirely iota-free.
#[test]
fn test_par_strips_bd_star_strip_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_strips_bd_star_strip",
        &[
            "par_strips_bd",
            "par_reduces_bd_star.rec",
            "par_strips_witness_bd.rec",
            "par_strips_witness_bd_star.intro",
            "par_subsumes_bd_star",
            "par_reduces_bd_star_trans",
        ],
    );
    let def = spec
        .definitions()
        .get("par_strips_bd_star_strip")
        .expect("par_strips_bd_star_strip should be registered");
    assert!(
        def.type_src.contains("par_reduces_bd_star e e1")
            && def.type_src.contains("par_reduces_bd e e2")
            && def.type_src.contains("par_strips_witness_bd_star e1 e2"),
        "strip lemma signature surface drift: {}",
        def.type_src
    );
    let deps = def.dependencies.as_ref().expect("deps");
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "the strip lemma must be iota-free: {deps:?}"
    );
}

/// Wave 140 (Route B) — GOAL #3: the iota-free MULTI-STEP DIAMOND
/// `par_reduces_bd_star_diamond` is the Tait-Martin-Löf confluence conclusion
/// for the iota-free closure: two multi-step reductions from a common source
/// join at a shared reduct. It is DerivedProved — the closed proof term was
/// kernel-checked by `add_decl` during spec construction; reaching this
/// assertion is the kernel-check witness. Zero axiom_deps; consumes the strip
/// lemma; entirely iota-free, so it sidesteps the untyped-model / delta / iota
/// church_rosser_whnf blockers by construction.
#[test]
fn test_par_reduces_bd_star_diamond_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_reduces_bd_star_diamond",
        &[
            "par_strips_bd_star_strip",
            "par_reduces_bd_star.rec",
            "par_strips_witness_bd_star.rec",
            "par_strips_witness_bd_star.intro",
            "par_reduces_bd_star_trans",
        ],
    );
    let def = spec
        .definitions()
        .get("par_reduces_bd_star_diamond")
        .expect("par_reduces_bd_star_diamond should be registered");
    assert!(
        def.type_src.contains("par_reduces_bd_star e e1")
            && def.type_src.contains("par_reduces_bd_star e e2")
            && def.type_src.contains("par_strips_witness_bd_star e1 e2"),
        "multi-step diamond signature surface drift: {}",
        def.type_src
    );
    let deps = def.dependencies.as_ref().expect("deps");
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "the iota-free multi-step diamond must be iota-free: {deps:?}"
    );
}

/// Wave 142 (Route B): the Eq-data pi inversion `par_reduces_bd_pi_inv_eq` (the
/// pi-headed dual of `par_reduces_bd_lam_inv_eq`) and the star-level pi inversion
/// `par_reduces_bd_star_pi_inv` are DerivedProved with zero axiom_deps and no
/// iota dependency. The Eq-data form hands back the reduct equality the star
/// induction's IH needs (the continuation-passing `par_reduces_bd_pi_inv` hides
/// it). `par_reduces_bd_star_pi_inv` is shape preservation for the iota-free
/// multi-step join: `pi dom body ⇒* w` forces `w = pi dom' body'` with the
/// components reducing componentwise — combined with the Wave-140 diamond this is
/// pi-injectivity for the iota-free join, the iota-free analogue of the
/// church_rosser_whnf content. Both terms were kernel-checked by `add_decl`
/// during spec construction; reaching this assertion is the kernel-check witness.
#[test]
fn test_par_reduces_bd_star_pi_inv_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_reduces_bd_pi_inv_eq",
        &[
            "par_reduces_bd",
            "par_reduces_bd.rec",
            "pi_inj_fst",
            "pi_inj_snd",
            "app_ne_pi",
            "lam_ne_pi",
            "Eq.substType",
        ],
    );
    assert_seam_proved(
        &spec,
        "par_reduces_bd_star_pi_inv",
        &[
            "par_reduces_bd_star.rec",
            "par_reduces_bd_star.refl",
            "par_reduces_bd_pi_inv_eq",
            "par_subsumes_bd_star",
            "par_reduces_bd_star_trans",
            "Eq.substType",
        ],
    );

    let eq_inv = spec
        .definitions()
        .get("par_reduces_bd_pi_inv_eq")
        .expect("par_reduces_bd_pi_inv_eq should be registered");
    assert!(
        eq_inv
            .type_src
            .contains("par_reduces_bd (KExpr.pi dom body) t")
            && eq_inv.type_src.contains("Eq KExpr t (KExpr.pi dom' body')"),
        "Eq-data pi inversion signature surface drift: {}",
        eq_inv.type_src
    );

    let star_inv = spec
        .definitions()
        .get("par_reduces_bd_star_pi_inv")
        .expect("par_reduces_bd_star_pi_inv should be registered");
    assert!(
        star_inv
            .type_src
            .contains("par_reduces_bd_star (KExpr.pi dom body) w")
            && star_inv.type_src.contains("par_reduces_bd_star dom dom'")
            && star_inv.type_src.contains("par_reduces_bd_star body body'")
            && star_inv.type_src.contains("C (KExpr.pi dom' body')"),
        "star pi inversion signature surface drift: {}",
        star_inv.type_src
    );

    for name in ["par_reduces_bd_pi_inv_eq", "par_reduces_bd_star_pi_inv"] {
        let def = spec.definitions().get(name).expect("registered");
        let deps = def.dependencies.as_ref().expect("deps");
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// Wave 143 (Route B): pi INJECTIVITY for the iota-free join. The Eq-data star
/// inversion `par_reduces_bd_star_pi_inv_eq` and the injectivity capstones
/// `par_bd_pi_injectivity_dom` / `par_bd_pi_injectivity_cod` are DerivedProved
/// with zero axiom_deps and no iota dependency. The injectivity lemmas state that
/// two pis with a shared iota-free reduct have join-able domains and codomains —
/// the iota-free analogue of pi-injectivity-for-DefEq (the church_rosser_whnf
/// payload). All three terms were kernel-checked by `add_decl` during spec
/// construction; reaching this assertion is the kernel-check witness.
#[test]
fn test_par_bd_pi_injectivity_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "par_reduces_bd_star_pi_inv_eq",
        &[
            "par_reduces_bd_star",
            "par_reduces_bd_star_pi_inv",
            "Eq.refl",
        ],
    );
    assert_seam_proved(
        &spec,
        "par_bd_pi_injectivity_dom",
        &[
            "par_strips_witness_bd_star.rec",
            "par_strips_witness_bd_star.intro",
            "par_reduces_bd_star_pi_inv_eq",
            "pi_inj_fst",
            "Eq.trans",
            "Eq.substType",
        ],
    );
    assert_seam_proved(
        &spec,
        "par_bd_pi_injectivity_cod",
        &[
            "par_strips_witness_bd_star.rec",
            "par_strips_witness_bd_star.intro",
            "par_reduces_bd_star_pi_inv_eq",
            "pi_inj_snd",
            "Eq.trans",
            "Eq.substType",
        ],
    );

    let dom = spec
        .definitions()
        .get("par_bd_pi_injectivity_dom")
        .expect("par_bd_pi_injectivity_dom should be registered");
    assert!(
        dom.type_src
            .contains("par_strips_witness_bd_star (KExpr.pi a1 b1) (KExpr.pi a2 b2)")
            && dom.type_src.contains("par_strips_witness_bd_star a1 a2"),
        "domain injectivity signature surface drift: {}",
        dom.type_src
    );
    let cod = spec
        .definitions()
        .get("par_bd_pi_injectivity_cod")
        .expect("par_bd_pi_injectivity_cod should be registered");
    assert!(
        cod.type_src.contains("par_strips_witness_bd_star b1 b2"),
        "codomain injectivity signature surface drift: {}",
        cod.type_src
    );

    for name in [
        "par_reduces_bd_star_pi_inv_eq",
        "par_bd_pi_injectivity_dom",
        "par_bd_pi_injectivity_cod",
    ] {
        let def = spec.definitions().get(name).expect("registered");
        let deps = def.dependencies.as_ref().expect("deps");
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// Wave 141 (Route B): the iota-free single-step beta relation
/// `beta_reduces_bd` and its closure `beta_reduces_bd_star` are registered as
/// inductives with recursors. `beta_reduces_bd` has exactly the 13 non-iota
/// constructors of `beta_reduces` (incl. the let-promotion zeta head
/// contraction on the genuine KExpr.let_ constructor and the
/// let_ty/let_val/let_body positional congruences — the pre-promotion bundled
/// let_body arm is GONE) and NO iota constructor (it is iota-free —
/// the whole point of the keystone). `beta_bd_join_witness` is the confluence
/// conclusion carrier.
#[test]
fn test_beta_reduces_bd_inductives_registered() {
    let spec = build_par_test_spec();
    for key in [
        "beta_reduces_bd",
        "beta_reduces_bd.rec",
        "beta_reduces_bd_star",
        "beta_reduces_bd_star.rec",
        "beta_reduces_bd_star.refl",
        "beta_reduces_bd_star.step",
        "beta_bd_join_witness",
        "beta_bd_join_witness.rec",
        "beta_bd_join_witness.intro",
    ] {
        assert!(
            spec.definitions().contains_key(key),
            "{key} should be registered (Wave 141)"
        );
    }
    for ctor in [
        "beta_reduces_bd.beta",
        "beta_reduces_bd.app_left",
        "beta_reduces_bd.app_right",
        "beta_reduces_bd.lam_ty",
        "beta_reduces_bd.lam_body",
        "beta_reduces_bd.pi_dom",
        "beta_reduces_bd.pi_cod",
        "beta_reduces_bd.forall_congr_dom",
        "beta_reduces_bd.forall_congr_cod",
        "beta_reduces_bd.zeta",
        "beta_reduces_bd.let_ty",
        "beta_reduces_bd.let_val",
        "beta_reduces_bd.let_body",
    ] {
        assert!(
            spec.definitions().contains_key(ctor),
            "beta_reduces_bd constructor {ctor} should be registered"
        );
    }
    // The iota-free relation must NOT carry an iota constructor anywhere.
    assert!(
        !spec.definitions().contains_key("beta_reduces_bd.iota"),
        "beta_reduces_bd must have no iota constructor (it is iota-free)"
    );
    assert!(
        !spec.definitions().contains_key("beta_reduces_bd_star.iota"),
        "beta_reduces_bd_star must have no iota constructor (it is iota-free)"
    );
}

/// Wave 141 (Route B): the iota-free beta-closure support lemmas
/// (`beta_subsumes_bd_star`, `beta_reduces_bd_star_trans`) and the six
/// single-position congruence helpers for BOTH the beta and parallel closures
/// are DerivedProved with zero axiom_deps and no iota dependency.
#[test]
fn test_beta_bd_star_support_and_congruence_lemmas_are_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "beta_subsumes_bd_star",
        &[
            "beta_reduces_bd",
            "beta_reduces_bd_star",
            "beta_reduces_bd_star.refl",
            "beta_reduces_bd_star.step",
        ],
    );
    assert_seam_proved(
        &spec,
        "beta_reduces_bd_star_trans",
        &[
            "beta_reduces_bd_star",
            "beta_reduces_bd_star.rec",
            "beta_reduces_bd_star.refl",
            "beta_reduces_bd_star.step",
        ],
    );
    // Both relations' nine single-position congruence helpers (the three let
    // positions are over the genuine KExpr.let_ constructor — let-promotion).
    for star in ["beta_reduces_bd_star", "par_reduces_bd_star"] {
        for suffix in [
            "app_left",
            "app_right",
            "lam_ty",
            "lam_body",
            "pi_dom",
            "pi_cod",
            "let_ty",
            "let_val",
            "let_body",
        ] {
            let name = format!("{star}_{suffix}");
            assert_seam_proved(&spec, &name, &[star, &format!("{star}.rec")]);
        }
    }
    // Route B invariant: none of the new closure machinery mentions iota.
    for star in ["beta_reduces_bd_star", "par_reduces_bd_star"] {
        for suffix in [
            "app_left",
            "app_right",
            "lam_ty",
            "lam_body",
            "pi_dom",
            "pi_cod",
        ] {
            let name = format!("{star}_{suffix}");
            let def = spec.definitions().get(&name).expect("registered");
            let deps = def.dependencies.as_ref().expect("deps");
            assert!(
                !deps.iter().any(|d| d.contains("iota")),
                "{name} must be iota-free: {deps:?}"
            );
        }
    }
}

/// Wave 141 (Route B) — GOAL #1: the two embeddings between the iota-free beta
/// and parallel fragments. `beta_subsumes_par_bd_star` (beta ⇒ par closure) and
/// `par_subsumes_beta_bd_star` (par ⇒ beta closure) are DerivedProved — full
/// closed proof terms kernel-checked by `add_decl` during spec construction, so
/// a faked or ill-typed term would have failed the build before any assertion
/// ran. Zero axiom_deps, no iota dependency.
#[test]
fn test_beta_bd_embeddings_are_derived_proved() {
    let spec = build_par_test_spec();
    // Post let-promotion every beta_subsumes_par_bd_star arm is a single par
    // step or congruence lift — no par_reduces_bd_star_trans composition (the
    // pre-promotion bundled let_body arm needed it); the zeta arm embeds via
    // par_reduces_bd.let_ and the let congruences lift through the
    // genuine-let_ star helpers.
    assert_seam_proved(
        &spec,
        "beta_subsumes_par_bd_star",
        &[
            "beta_reduces_bd.rec",
            "par_reduces_bd_star",
            "par_subsumes_bd_star",
            "par_reduces_bd.let_",
            "par_reduces_bd_star_let_ty",
            "par_reduces_bd_star_let_val",
            "par_reduces_bd_star_let_body",
        ],
    );
    assert_seam_proved(
        &spec,
        "par_subsumes_beta_bd_star",
        &[
            "par_reduces_bd.rec",
            "beta_reduces_bd_star",
            "beta_subsumes_bd_star",
            "beta_reduces_bd_star_trans",
        ],
    );
    for (name, src, tgt) in [
        (
            "beta_subsumes_par_bd_star",
            "beta_reduces_bd e e'",
            "par_reduces_bd_star e e'",
        ),
        (
            "par_subsumes_beta_bd_star",
            "par_reduces_bd e e'",
            "beta_reduces_bd_star e e'",
        ),
    ] {
        let def = spec.definitions().get(name).expect("registered");
        assert!(
            def.type_src.contains(src) && def.type_src.contains(tgt),
            "{name} signature surface drift: {}",
            def.type_src
        );
        let deps = def.dependencies.as_ref().expect("deps");
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// Wave 141 (Route B): the closure transports establishing that the iota-free
/// beta and parallel closures are interconvertible (GOAL #1's closure
/// equivalence). Both DerivedProved, zero axiom_deps, no iota dependency.
#[test]
fn test_beta_bd_closure_transports_are_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "beta_bd_star_subsumes_par_bd_star",
        &[
            "beta_reduces_bd_star.rec",
            "par_reduces_bd_star_trans",
            "beta_subsumes_par_bd_star",
        ],
    );
    assert_seam_proved(
        &spec,
        "par_bd_star_subsumes_beta_bd_star",
        &[
            "par_reduces_bd_star.rec",
            "beta_reduces_bd_star_trans",
            "par_subsumes_beta_bd_star",
        ],
    );
    for name in [
        "beta_bd_star_subsumes_par_bd_star",
        "par_bd_star_subsumes_beta_bd_star",
    ] {
        let def = spec.definitions().get(name).expect("registered");
        let deps = def.dependencies.as_ref().expect("deps");
        assert!(
            !deps.iter().any(|d| d.contains("iota")),
            "{name} must be iota-free: {deps:?}"
        );
    }
}

/// Wave 141 (Route B) — GOAL #2: `beta_bd_confluent` is the iota-free
/// Church-Rosser theorem for beta reduction. Two iota-free multi-step beta
/// reductions from a common source join at a shared reduct (packaged as
/// `beta_bd_join_witness`). It is DerivedProved — the closed proof term,
/// transporting through the parallel multi-step diamond, was kernel-checked by
/// `add_decl` during spec construction; reaching this assertion is the
/// kernel-check witness. Zero axiom_deps; entirely iota-free, so it sidesteps
/// the untyped-model / delta / iota-seam `church_rosser_whnf` blockers by
/// construction.
#[test]
fn test_beta_bd_confluent_is_derived_proved() {
    let spec = build_par_test_spec();
    assert_seam_proved(
        &spec,
        "beta_bd_confluent",
        &[
            "beta_reduces_bd_star",
            "beta_bd_join_witness.intro",
            "beta_bd_star_subsumes_par_bd_star",
            "par_bd_star_subsumes_beta_bd_star",
            "par_reduces_bd_star_diamond",
            "par_strips_witness_bd_star.rec",
        ],
    );
    let def = spec
        .definitions()
        .get("beta_bd_confluent")
        .expect("beta_bd_confluent should be registered");
    assert!(
        def.type_src.contains("beta_reduces_bd_star e e1")
            && def.type_src.contains("beta_reduces_bd_star e e2")
            && def.type_src.contains("beta_bd_join_witness e1 e2"),
        "beta_bd_confluent signature surface drift: {}",
        def.type_src
    );
    let deps = def.dependencies.as_ref().expect("deps");
    assert!(
        !deps.iter().any(|d| d.contains("iota")),
        "the iota-free beta Church-Rosser theorem must be iota-free: {deps:?}"
    );
}

/// L1a (#2859 Increment F+, confluence core): the lam-headed inversion lemmas for
/// `par_reduces_p` are DerivedProved closed terms with an empty axiom closure.
/// Reaching these assertions IS the kernel-check witness — the closed proof terms
/// were type-checked by `add_decl` during spec construction, so an ill-typed or
/// faked term would have failed `new_substitution_test_spec()` before any
/// assertion ran.
#[test]
fn test_par_reduces_p_lam_inv_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in [
        "par_reduces_p_lam_reduct_not_redex",
        "par_reduces_p_lam_inv",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
    }
    // par_reduces_p_lam_inv recovers t = lam ty' body' with the component reductions.
    let inv = spec
        .definitions()
        .get("par_reduces_p_lam_inv")
        .expect("par_reduces_p_lam_inv should be registered");
    assert!(
        inv.type_src
            .contains("par_reduces_p env (KExpr.lam ty body) t")
            && inv.type_src.contains("par_reduces_p env ty ty'")
            && inv.type_src.contains("par_reduces_p env body body'"),
        "par_reduces_p_lam_inv signature surface drift: {}",
        inv.type_src
    );
}

/// L1b (#2859 Increment F+, confluence core): `cd_refl` — every term
/// parallel-reduces to its complete development — is a DerivedProved closed term
/// with an empty axiom closure. The kernel-check witness for the L1b half of the
/// cd-triangle confluence core.
#[test]
fn test_cd_refl_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("cd_refl")
        .expect("cd_refl should be registered");
    assert!(!def.is_axiom, "cd_refl should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "cd_refl should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "cd_refl should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "cd_refl should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "cd_refl should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains("par_reduces_p env e (cd env e)"),
        "cd_refl signature surface drift: {}",
        def.type_src
    );
    // cd_refl is part of the confluence core, NOT the false church_rosser_whnf axiom.
    let deps = def
        .dependencies
        .as_ref()
        .expect("cd_refl should record deps");
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "cd_refl must not depend on church_rosser_whnf: {deps:?}"
    );
    assert!(
        deps.contains("par_reduces_p_lam_inv"),
        "cd_refl should consume the L1a inversion par_reduces_p_lam_inv: {deps:?}"
    );
}

/// L2 core (#2859 Increment F+, confluence core): `par_reduces_p_reduct_cong_spine`
/// — the structural-args iota reduct congruence — is a DerivedProved closed term
/// with an empty axiom closure. The kernel-check witness for the apply_spine
/// assembly half of `par_reduces_p_reduct_cong` (design §11): given the two spine
/// congruences, the two iota reducts par-reduce. Does NOT depend on the
/// non-porting guarded c-machinery (par_reduces_c_spine_cong) or
/// church_rosser_whnf.
#[test]
fn test_par_reduces_p_reduct_cong_spine_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_reduct_cong_spine")
        .expect("par_reduces_p_reduct_cong_spine should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_reduct_cong_spine should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_reduct_cong_spine should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_reduct_cong_spine should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_reduct_cong_spine should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_reduct_cong_spine should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // Consumes the par-reduction spine substrate, NOT the non-porting guarded
    // c-spine_cong machinery, and NOT church_rosser_whnf.
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_reduct_cong_spine should record deps");
    assert!(
        deps.contains("apply_spine_par_p")
            && deps.contains("list_drop_par_p")
            && deps.contains("list_take_par_p")
            && deps.contains("par_reduces_p_list_length_eq"),
        "par_reduces_p_reduct_cong_spine should consume the par-reduction spine bricks: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser"))
            && !deps.iter().any(|d| d.contains("par_reduces_c_spine_cong")),
        "par_reduces_p_reduct_cong_spine must not depend on church_rosser_whnf or the non-porting c-spine_cong: {deps:?}"
    );
}

/// #2859 Increment F++ keystone: `recenv_ctor_no_recmeta_cname` — the projector for
/// the SHARPENED constructor/recursor-disjointness interface `RecEnvCtorNoRecMeta` —
/// is a DerivedProved closed term with an empty axiom closure. Given the env is
/// ctor/no-recmeta and a term's head is a constructor `cname` of recursor `recname`,
/// the constructor `cname` carries no recursor metadata (`recmeta_for env cname =
/// none`). The faithful interface the (iota,app) both-fire join's major spine
/// congruence consumes; discharged at end-of-track with the real env witness.
#[test]
fn test_recenv_ctor_no_recmeta_cname_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("recenv_ctor_no_recmeta_cname")
        .expect("recenv_ctor_no_recmeta_cname should be registered");
    assert!(
        !def.is_axiom,
        "recenv_ctor_no_recmeta_cname should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "recenv_ctor_no_recmeta_cname should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "recenv_ctor_no_recmeta_cname should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "recenv_ctor_no_recmeta_cname should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "recenv_ctor_no_recmeta_cname should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // The conclusion is the sharpened recmeta_for(cname) = none form (NOT the weaker
    // iota_reduct major = none of RecEnvCtorRecDisjoint).
    assert!(
        def.type_src
            .contains("Eq (OptionType RecMeta) (recmeta_for env cname) (OptionType.none RecMeta)"),
        "recenv_ctor_no_recmeta_cname should conclude recmeta_for env cname = none: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("recenv_ctor_no_recmeta_cname should record deps");
    assert!(
        deps.contains("RecEnvCtorNoRecMeta")
            && deps.contains("RecEnvCtorNoRecMeta.rec")
            && deps.contains("recmeta_for")
            && deps.contains("recrule_for"),
        "recenv_ctor_no_recmeta_cname should project the RecEnvCtorNoRecMeta fact: {deps:?}"
    );
}

/// #2859 Increment F++ keystone: `par_reduces_p_reduct_cong` — the ASSEMBLED minimal
/// (LEFT-leg) reduct congruence — is a DerivedProved closed term with an empty axiom
/// closure. The p-side analogue of the c-side `par_reduces_c_reduct_cong` (D.3): given
/// the boundary-inverter witnesses + the sharpened disjointness interface
/// `RecEnvCtorNoRecMeta`, the (app f a)-side iota reduct par-reduces to the (app f' a')-
/// side reduct. The f-spine via the below-boundary congruence (recursor head, NO
/// interface) and the major-spine via the no-recmeta congruence (constructor head, via
/// the interface — needed because the p-side iota_p fires on the REDUCED premise).
#[test]
fn test_par_reduces_p_reduct_cong_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_reduct_cong")
        .expect("par_reduces_p_reduct_cong should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_reduct_cong should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_reduct_cong should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_reduct_cong should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_reduct_cong should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_reduct_cong should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // It threads the sharpened faithful interface RecEnvCtorNoRecMeta (NOT an axiom).
    assert!(
        def.type_src.contains("RecEnvCtorNoRecMeta env ->"),
        "par_reduces_p_reduct_cong should thread the RecEnvCtorNoRecMeta interface: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_reduct_cong should record deps");
    assert!(
        deps.contains("par_reduces_p_reduct_cong_spine")
            && deps.contains("par_reduces_p_spine_cong_below_boundary")
            && deps.contains("par_reduces_p_spine_cong_no_recmeta")
            && deps.contains("recenv_ctor_no_recmeta_cname")
            && deps.contains("kapp_args_par_p"),
        "par_reduces_p_reduct_cong should assemble the spine congruences + the interface projector: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_reduct_cong must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// #2859 Increment F++ keystone: `par_reduces_p_app_reduct_cong_minimal` — the
/// MINIMAL-case (f not a redex) symmetric app reduct congruence. Given the minimal guard
/// `iota_reduct env f = none`, the disjointness interface, the originals f ⇒_p f' /
/// a ⇒_p a', and BOTH endpoints as iota redexes, the two reducts join in
/// `par_reduces_p_star`. The LEFT leg via par_reduces_p_reduct_cong, the RIGHT leg pinned
/// by par_reduces_p_app_redex + iota_step_deterministic. The boundary-case half of the
/// keystone's app arm. A DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_app_reduct_cong_minimal_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_app_reduct_cong_minimal")
        .expect("par_reduces_p_app_reduct_cong_minimal should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_app_reduct_cong_minimal should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_app_reduct_cong_minimal should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_app_reduct_cong_minimal should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_app_reduct_cong_minimal should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_app_reduct_cong_minimal should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // Conclusion: the STAR-valued symmetric reduct congruence from two iota redex endpoints.
    assert!(
        def.type_src.contains(
            "iota_step env (KExpr.app f a) r0 -> iota_step env (KExpr.app f' a') rm0 -> \
             par_reduces_p_star env r0 rm0"
        ),
        "par_reduces_p_app_reduct_cong_minimal should conclude the minimal symmetric reduct congruence: {}",
        def.type_src
    );
    // It threads the sharpened faithful interface RecEnvCtorNoRecMeta (NOT an axiom).
    assert!(
        def.type_src.contains("RecEnvCtorNoRecMeta env ->"),
        "par_reduces_p_app_reduct_cong_minimal should thread the RecEnvCtorNoRecMeta interface: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_app_reduct_cong_minimal should record deps");
    assert!(
        deps.contains("par_reduces_p_reduct_cong")
            && deps.contains("par_reduces_p_app_redex")
            && deps.contains("iota_reduct_app_minimal_boundary_idx_type")
            && deps.contains("iota_step_deterministic"),
        "par_reduces_p_app_reduct_cong_minimal should assemble the LEFT/RIGHT legs + determinism: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_app_reduct_cong_minimal must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// #2859 Increment F++ keystone: `par_reduces_p_app_redex` — the p-side (iota,app)
/// minimal-join reduct RECONSTRUCTION. Given the boundary-inverter witnesses + the
/// sharpened disjointness interface + the originals f ⇒_p f' / a ⇒_p a', it delivers
/// `iota_reduct env (app f' a') = some reduct_m`. The RIGHT leg of the minimal join:
/// with par_reduces_p_reduct_cong's LEFT leg + iota_step_deterministic, this pins the
/// GIVEN opaque (app f' a')-reduct to reduct_m. Feeds iota_reduct_par_app_recon (reused
/// verbatim, par_reduces_c-free). A DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_app_redex_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_app_redex")
        .expect("par_reduces_p_app_redex should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_app_redex should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_app_redex should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_app_redex should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_app_redex should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_app_redex should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // It threads the sharpened faithful interface RecEnvCtorNoRecMeta (NOT an axiom).
    assert!(
        def.type_src.contains("RecEnvCtorNoRecMeta env ->"),
        "par_reduces_p_app_redex should thread the RecEnvCtorNoRecMeta interface: {}",
        def.type_src
    );
    // Conclusion: iota_reduct env (app f' a') = some reduct_m.
    assert!(
        def.type_src.contains(
            "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr"
        ),
        "par_reduces_p_app_redex should conclude the (app f' a') reduct reconstruction: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_app_redex should record deps");
    assert!(
        deps.contains("iota_reduct_par_app_recon")
            && deps.contains("par_reduces_p_preserves_head_const_below_boundary")
            && deps.contains("par_reduces_p_preserves_head_const_no_recmeta")
            && deps.contains("recenv_ctor_no_recmeta_cname")
            && deps.contains("list_head_drop_len_append"),
        "par_reduces_p_app_redex should reconstruct via the recon + the head-preservation bricks: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_app_redex must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// L2 over-application arm (#2859 Increment F+, design §15(ii)):
/// `par_reduces_p_reduct_cong_over` — the OVER-APPLICATION companion of the
/// boundary-case `par_reduces_p_reduct_cong_spine`. When (app f a) is an
/// over-applied iota redex (the major strictly inside f's spine, so f is itself a
/// redex), the over-application identity makes the outer reduct the inner reduct
/// re-applied; given the inner reduct congruence f1 ⇒_p f1' and a ⇒_p a' the two
/// actual outer reducts par-reduce by a single app congruence. Asserted to be a
/// DerivedProved closed term with an empty axiom closure (FOUNDATIONAL only). The
/// kernel-check witness for the over-application case of the full reduct
/// congruence (the kcong-sub over-app arm).
#[test]
fn test_par_reduces_p_reduct_cong_over_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_reduct_cong_over")
        .expect("par_reduces_p_reduct_cong_over should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_reduct_cong_over should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_reduct_cong_over should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_reduct_cong_over should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_reduct_cong_over should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_reduct_cong_over should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // Consumes the c-side over-application identity (iota_reduct_app_some) lifted
    // onto par_reduces_p, NOT church_rosser_whnf, NOT the non-porting c-spine_cong.
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_reduct_cong_over should record deps");
    assert!(
        deps.contains("iota_reduct_app_some")
            && deps.contains("par_reduces_p.app")
            && deps.contains("option_some_inj"),
        "par_reduces_p_reduct_cong_over should consume iota_reduct_app_some + par_reduces_p.app + option_some_inj: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser"))
            && !deps.iter().any(|d| d.contains("par_reduces_c_spine_cong")),
        "par_reduces_p_reduct_cong_over must not depend on church_rosser_whnf or the non-porting c-spine_cong: {deps:?}"
    );
}

/// L2 (#2859 Increment F+, confluence core): `par_reduces_p_iota_redex_to_reduct`
/// — an iota redex par-reduces to its reduct in one par_reduces_p step (the
/// refl-case content of design §11's redex_cong) — is a DerivedProved closed term
/// with an empty axiom closure.
#[test]
fn test_par_reduces_p_iota_redex_to_reduct_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_iota_redex_to_reduct")
        .expect("par_reduces_p_iota_redex_to_reduct should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_iota_redex_to_reduct should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_iota_redex_to_reduct should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_iota_redex_to_reduct should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_iota_redex_to_reduct should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src
            .contains("iota_step env e r -> par_reduces_p env e r"),
        "par_reduces_p_iota_redex_to_reduct signature surface drift: {}",
        def.type_src
    );
}

/// Target #1 (#2859 Increment F+, the enabling inversion): `par_reduces_p_app_inv`
/// — the CPS app shape-recovery (kcong / kbeta / kiota continuations, the kiota arm
/// carrying the PARALLEL-iota intermediate `e2` + premise) — is a DerivedProved
/// closed term with an empty axiom closure. The kernel-check witness for the app
/// inversion that enables the full reduct congruence and the cd_triangle iota_p arm.
#[test]
fn test_par_reduces_p_app_inv_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_app_inv")
        .expect("par_reduces_p_app_inv should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_app_inv should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_app_inv should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_app_inv should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_app_inv should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_app_inv should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // The kiota continuation carries the parallel-iota intermediate e2 and the
    // premise (app f a) ⇒_p e2 — the genuine-new content vs. the c-mirror.
    assert!(
        def.type_src
            .contains("par_reduces_p env (KExpr.app f a) e2 -> iota_step env e2 r -> C r"),
        "par_reduces_p_app_inv kiota continuation surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_app_inv should record deps");
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_app_inv must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// Target #1 (#2859 Increment F+, the cd app-arm resolution): `cd_iota_unfold` —
/// for `app f a` with original head not a lam and a developed-spine iota redex
/// (`iota_reduct env (app (cd f)(cd a)) = some r`), the complete development is that
/// reduct (`cd env (app f a) = r`) — is a DerivedProved closed term with an empty
/// axiom closure. The cd app-arm resolution the cd_triangle iota_p arm consumes.
#[test]
fn test_cd_iota_unfold_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("cd_iota_unfold")
        .expect("cd_iota_unfold should be registered");
    assert!(!def.is_axiom, "cd_iota_unfold should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "cd_iota_unfold should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "cd_iota_unfold should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "cd_iota_unfold should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "cd_iota_unfold should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains("Eq KExpr (cd env (KExpr.app f a)) r"),
        "cd_iota_unfold signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("cd_iota_unfold should record deps");
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "cd_iota_unfold must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// The cd_triangle app-congruence (kcong) arm (#2859 Increment F+):
/// `par_reduces_p_app_dev` — from f ⇒_p f', a ⇒_p a', and the post-IH developments
/// f' ⇒_p cd f, a' ⇒_p cd a, the reassembled app reaches the development target
/// (app f' a' ⇒_p cd (app f a)) — is a DerivedProved closed term with an empty axiom
/// closure. The non-circular kcong arm; covers all three cd app-arm branches.
#[test]
fn test_par_reduces_p_app_dev_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_app_dev")
        .expect("par_reduces_p_app_dev should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_app_dev should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_app_dev should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_app_dev should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_app_dev should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_app_dev should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src
            .contains("par_reduces_p env (KExpr.app f' a') (cd env (KExpr.app f a))"),
        "par_reduces_p_app_dev signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_app_dev should record deps");
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_app_dev must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// The cd_triangle beta-redex (kbeta) arm (#2859 Increment F+):
/// `par_reduces_p_beta_dev` — for a lam-headed source f = lam A body, the contracted
/// root beta reaches the development target (instantiate body' arg' ⇒_p cd (app (lam A
/// body) a)) from the post-IH developments body' ⇒_p cd body, arg' ⇒_p cd a — is a
/// DerivedProved closed term with an empty axiom closure. Built from par_subst_p +
/// cd_app_lam; non-circular.
#[test]
fn test_par_reduces_p_beta_dev_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_beta_dev")
        .expect("par_reduces_p_beta_dev should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_beta_dev should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_beta_dev should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_beta_dev should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_beta_dev should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_beta_dev should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains(
            "par_reduces_p env (instantiate body' arg') (cd env (KExpr.app (KExpr.lam A body) a))"
        ),
        "par_reduces_p_beta_dev signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_beta_dev should record deps");
    assert!(
        deps.contains("par_subst_p"),
        "par_reduces_p_beta_dev should consume the 1-step substitution lemma par_subst_p: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_beta_dev must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// L2 brick (#2859 Increment F+, confluence core): `par_reduces_p_strict_partial_no_iota`
/// — a recursor application whose spine length EQUALS its major boundary does not fire a
/// top-level iota (iota_reduct env f = none), PROVED (not assumed) from the boundary
/// identity — is a DerivedProved closed term with an empty axiom closure. The fact the
/// boundary inverter needs to conclude major = a in the kcong-sub of the kiota arm.
#[test]
fn test_par_reduces_p_strict_partial_no_iota_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_strict_partial_no_iota")
        .expect("par_reduces_p_strict_partial_no_iota should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_strict_partial_no_iota should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_strict_partial_no_iota should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_strict_partial_no_iota should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_strict_partial_no_iota should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_strict_partial_no_iota should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src
            .contains("Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)"),
        "par_reduces_p_strict_partial_no_iota signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_strict_partial_no_iota should record deps");
    assert!(
        deps.contains("list_head_drop_some_le_succ") && deps.contains("le_succ_self_empty"),
        "par_reduces_p_strict_partial_no_iota should consume the boundary-window bricks: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_strict_partial_no_iota must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// #2859 Increment F++ keystone: `par_reduces_p_preserves_head_const_below_boundary`
/// — the HEAD-side companion of the below-boundary spine congruence. Under the
/// below-boundary recursor guard, a const-headed `f ⇒_p f'` preserves the head const
/// (`head f' = some nm`). Reuses the spine congruence's AndType-product recursor
/// (projecting the head box) — the p-side analogue of the c-side
/// `par_reduces_c_preserves_head_const_nr` (whose not-redex guard does not port).
/// A DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_preserves_head_const_below_boundary_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_preserves_head_const_below_boundary")
        .expect("par_reduces_p_preserves_head_const_below_boundary should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_preserves_head_const_below_boundary should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_preserves_head_const_below_boundary should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_preserves_head_const_below_boundary should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_preserves_head_const_below_boundary should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_preserves_head_const_below_boundary should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // Conclusion: head(kapp_fn f') = some nm.
    assert!(
        def.type_src
            .contains("par_reduces_p env f f' -> Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"),
        "par_reduces_p_preserves_head_const_below_boundary signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_preserves_head_const_below_boundary should record deps");
    assert!(
        deps.contains("iota_step_below_boundary_absurd")
            && deps.contains("HeadConstBox.rec")
            && deps.contains("AndType.rec"),
        "par_reduces_p_preserves_head_const_below_boundary should reuse the AndType recursor + project the head box: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_preserves_head_const_below_boundary must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// #2859 Increment F++ keystone: `par_reduces_p_preserves_head_const_no_recmeta` —
/// the HEAD-side companion of the no-recmeta (constructor-head) spine congruence. Under
/// the no-recmeta guard, a const-headed `f ⇒_p f'` preserves the head const
/// (`head f' = some nm`). Reuses the no-recmeta spine congruence's AndType-product
/// recursor (projecting the head box). A DerivedProved closed term with an empty axiom
/// closure.
#[test]
fn test_par_reduces_p_preserves_head_const_no_recmeta_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_preserves_head_const_no_recmeta")
        .expect("par_reduces_p_preserves_head_const_no_recmeta should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_preserves_head_const_no_recmeta should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_preserves_head_const_no_recmeta should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_preserves_head_const_no_recmeta should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_preserves_head_const_no_recmeta should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_preserves_head_const_no_recmeta should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src
            .contains("par_reduces_p env f f' -> Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"),
        "par_reduces_p_preserves_head_const_no_recmeta signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_preserves_head_const_no_recmeta should record deps");
    assert!(
        deps.contains("iota_step_no_recmeta_absurd")
            && deps.contains("HeadConstBox.rec")
            && deps.contains("AndType.rec"),
        "par_reduces_p_preserves_head_const_no_recmeta should reuse the AndType recursor + project the head box: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_preserves_head_const_no_recmeta must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// Step 1 of the marked-fuel `par_reduces_pL_reduct_cong` campaign (#2859
/// Increment F++, design §16): the c→p port `par_reduces_p_preserves_head_const`
/// (generic const-head preservation) is a DerivedProved closed term with an empty
/// axiom closure. The iota_p arm forwards the reduced-form fire into the kiota
/// continuation (unlike the _nr variant, design §11).
#[test]
fn test_par_reduces_p_preserves_head_const_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p_preserves_head_const")
        .expect("par_reduces_p_preserves_head_const should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_p_preserves_head_const should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_p_preserves_head_const should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_p_preserves_head_const should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_p_preserves_head_const should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_p_preserves_head_const should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains("par_reduces_p env e e'")
            && def.type_src.contains("iota_step env t1 t2 -> C"),
        "par_reduces_p_preserves_head_const signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_p_preserves_head_const should record deps");
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_p_preserves_head_const must not depend on church_rosser_whnf: {deps:?}"
    );
}

// ===========================================================================
// #2859 Increment F++ — the MARKED / fuel-counted parallel reduction
// par_reduces_pL (the Tait–Martin-Löf labeled-development crack of the
// confirmed-immovable double-iota wall). The fuel index COUNTS the contractions,
// giving the decreasing measure the unlabeled par_reduces_p provably lacks.
// ===========================================================================

/// The marked relation `par_reduces_pL` and its recursor are registered, with the
/// fuel-bearing Nat index — the spine of the marked-development approach.
#[test]
fn test_par_reduces_p_marked_inductive_registered() {
    let spec = build_par_test_spec();
    assert!(
        spec.definitions().contains_key("par_reduces_pL"),
        "par_reduces_pL marked inductive should be registered"
    );
    assert!(
        spec.definitions().contains_key("par_reduces_pL.rec"),
        "par_reduces_pL recursor should be registered"
    );
    // The fuel-bearing constructors are registered (the well-typedness of the Nat.succ /
    // Nat.add fuel arithmetic in the indices is checked by the kernel when the inductive
    // is admitted and again when par_reduces_pL_erase recurses over it). The constructor
    // type surfaces are placeholders, so registration is the introspectable invariant.
    assert!(
        spec.definitions().contains_key("par_reduces_pL.iota_p"),
        "par_reduces_pL.iota_p (the Nat.succ-fuel iota contraction) should be registered"
    );
    assert!(
        spec.definitions().contains_key("par_reduces_pL.app"),
        "par_reduces_pL.app (the Nat.add-fuel congruence) should be registered"
    );
}

/// All 8 marked constructors are present (mirror of par_reduces_p plus the fuel).
#[test]
fn test_par_reduces_p_marked_has_eight_constructors() {
    let spec = build_par_test_spec();
    for ctor in [
        "par_reduces_pL.refl",
        "par_reduces_pL.beta",
        "par_reduces_pL.app",
        "par_reduces_pL.lam",
        "par_reduces_pL.pi",
        "par_reduces_pL.forall_",
        "par_reduces_pL.let_",
        "par_reduces_pL.iota_p",
    ] {
        assert!(
            spec.definitions().contains_key(ctor),
            "marked constructor {ctor} should be registered"
        );
    }
}

/// ERASURE (#2859 Increment F++): `par_reduces_pL_erase` — every marked step is an
/// unlabeled `par_reduces_p` step (drop the fuel) — is a DerivedProved closed term with
/// an empty axiom closure. The labels-drop half of the marked→unlabeled diamond lift (L3).
#[test]
fn test_par_reduces_p_marked_erase_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_pL_erase")
        .expect("par_reduces_pL_erase should be registered");
    assert!(!def.is_axiom, "par_reduces_pL_erase should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_pL_erase should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_pL_erase should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_pL_erase should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_pL_erase should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src
            .contains("par_reduces_pL env n e e' -> par_reduces_p env e e'"),
        "par_reduces_pL_erase signature surface drift: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_pL_erase should record deps");
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_pL_erase must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// The marked refl seed `par_reduces_pL_refl0` (fuel-0 reflexive marked step) is a
/// DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_marked_refl0_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_pL_refl0")
        .expect("par_reduces_pL_refl0 should be registered");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_pL_refl0 should be DerivedProved"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_pL_refl0 should have an empty axiom closure: {:?}",
        def.axiom_deps
    );
}

/// TARGET 2 (#2859 Increment F++) — the MEASURE on marked reduction. Every
/// fuel-decrease brick and the well-founded recursion scaffold are DerivedProved
/// closed terms with empty axiom closures. These ARE the decreasing measure the
/// unlabeled cd_triangle iota arm provably lacks.
#[test]
fn test_par_reduces_p_marked_measure_bricks_are_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in [
        // THE WALL-CASE decrease — the iota_p premise fuel strictly drops.
        "par_reduces_pL_iota_premise_lt",
        // The beta/let contraction's substituted-arg premise drops (kbeta-sub).
        "par_reduces_pL_beta_arg_premise_lt",
        // The congruence-arm premises are bounded by the threading successor.
        "par_reduces_pL_app_fst_premise_lt_succ",
        "par_reduces_pL_app_snd_premise_lt_succ",
        // The well-founded recursion scaffold on marked fuel (the termination cert).
        "par_reduces_pL_fuel_rec",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record deps"));
        assert!(
            !deps.iter().any(|d| d.contains("church_rosser")),
            "{name} must not depend on church_rosser_whnf: {deps:?}"
        );
    }
}

/// The well-founded recursion scaffold `par_reduces_pL_fuel_rec` has the strong-Nat-
/// induction shape (fuel-indexed motive, decrease hypothesis), i.e. it really is the
/// termination certificate, and consumes the landed `nat_strong_rec`.
#[test]
fn test_par_reduces_p_marked_fuel_rec_shape() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_pL_fuel_rec")
        .expect("par_reduces_pL_fuel_rec should be registered");
    assert!(
        def.type_src.contains("forall (Q : Nat -> Type)") && def.type_src.contains("Lt j k -> Q j"),
        "par_reduces_pL_fuel_rec should be strong-induction on marked fuel: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_pL_fuel_rec should record deps");
    assert!(
        deps.contains("nat_strong_rec"),
        "par_reduces_pL_fuel_rec should reuse the landed nat_strong_rec measure primitive: {deps:?}"
    );
}

/// TARGET 3 (#2859 Increment F++) — THE MARKED TRIANGLE SCAFFOLD, the crux.
/// `par_reduces_pL_triangle_scaffold` proves `e ⇒L_n e' → e' ⇒_p cd e` by structural
/// recursion on the marked derivation, with all seven non-iota arms closed by the
/// landed development bricks and the iota arm (the immovable double-iota wall) isolated
/// to the single hypothesis `iota_join`, FED its development from the recursor's
/// structural IH — the development the unlabeled cd_triangle provably could not obtain.
/// A DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_marked_triangle_scaffold_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_pL_triangle_scaffold")
        .expect("par_reduces_pL_triangle_scaffold should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_pL_triangle_scaffold should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_pL_triangle_scaffold should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_pL_triangle_scaffold should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_pL_triangle_scaffold should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_pL_triangle_scaffold should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // The conclusion is the marked triangle: e ⇒L_n e' -> e' ⇒_p cd e.
    assert!(
        def.type_src
            .contains("par_reduces_pL env n e e' -> par_reduces_p env e' (cd env e)"),
        "par_reduces_pL_triangle_scaffold should conclude the marked triangle: {}",
        def.type_src
    );
    // The wall is isolated as the iota_join hypothesis (and nothing else).
    assert!(
        def.type_src.contains("par_reduces_p env r (cd env e0)"),
        "par_reduces_pL_triangle_scaffold should isolate the iota arm as iota_join: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_pL_triangle_scaffold should record deps");
    assert!(
        deps.contains("par_reduces_pL.rec")
            && deps.contains("cd_refl")
            && deps.contains("par_reduces_p_app_dev")
            && deps.contains("par_reduces_p_beta_dev")
            && deps.contains("par_reduces_pL_erase"),
        "par_reduces_pL_triangle_scaffold should consume the landed development bricks: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_pL_triangle_scaffold must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// THE marked-fuel keystone (#2859 Increment F++, design §16):
/// `par_reduces_pL_reduct_cong` — the MARKED SYMMETRIC reduct congruence. Proves
/// that if `e` MARKED-reduces to `m` and both endpoints are iota redexes (`e -> r`,
/// `m -> rm`), the reducts join in `par_reduces_p_star`, by recursing on the marked
/// FUEL (the decreasing measure the unlabeled relation lacks). The iota_p arm — the
/// double-iota wall §14/§16 — is CLOSED by the fuel recursion (NOT a hypothesis);
/// only the structural app-args reduct congruence is isolated as `happ`. A
/// DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_marked_reduct_cong_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_pL_reduct_cong")
        .expect("par_reduces_pL_reduct_cong should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_pL_reduct_cong should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_pL_reduct_cong should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_pL_reduct_cong should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_pL_reduct_cong should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_pL_reduct_cong should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // The conclusion is the STAR-valued symmetric reduct congruence.
    assert!(
        def.type_src.contains(
            "par_reduces_pL env n e m -> iota_step env e r -> iota_step env m rm -> \
             par_reduces_p_star env r rm"
        ),
        "par_reduces_pL_reduct_cong should conclude the marked symmetric reduct congruence: {}",
        def.type_src
    );
    // The MINIMAL app case is now discharged INTERNALLY: the keystone threads the
    // faithful disjointness interface RecEnvCtorNoRecMeta (NOT an axiom) and consumes
    // par_reduces_p_app_reduct_cong_minimal; only the OVER-APPLICATION residual happ_over
    // remains as an explicit hypothesis (guarded by iota_reduct env f = some f1).
    assert!(
        def.type_src.contains("RecEnvCtorNoRecMeta env ->"),
        "par_reduces_pL_reduct_cong should thread the RecEnvCtorNoRecMeta interface: {}",
        def.type_src
    );
    assert!(
        def.type_src
            .contains("Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) ->"),
        "par_reduces_pL_reduct_cong should isolate the OVER-APPLICATION residual happ_over (guarded by iota_reduct env f = some f1): {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_pL_reduct_cong should record deps");
    // The CRUX: it consumes the FUEL recursion + the determinism + the star-trans
    // join + the iota-redex-to-reduct step — the fuel-driven double-iota close — AND
    // discharges the minimal app arm via par_reduces_p_app_reduct_cong_minimal.
    assert!(
        deps.contains("par_reduces_pL_fuel_rec")
            && deps.contains("par_reduces_pL.rec")
            && deps.contains("iota_step_deterministic")
            && deps.contains("par_reduces_p_star_trans")
            && deps.contains("par_reduces_p_iota_redex_to_reduct")
            && deps.contains("lt_succ_self")
            && deps.contains("par_reduces_p_app_reduct_cong_minimal")
            && deps.contains("RecEnvCtorNoRecMeta"),
        "par_reduces_pL_reduct_cong should drive the fuel recursion + the double-iota join + the internal minimal-app discharge: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_pL_reduct_cong must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// STEP 2 (#2859 Increment F++, design §17) — THE STAR-VALUED MARKED TRIANGLE.
/// `par_reduces_pL_triangle_star` proves `e ⇒L_n e' → e' ⇒*_p cd e` by structural
/// recursion on the marked derivation with the STAR motive
/// `M n a b _ := par_reduces_p_star env b (cd env a)`. The seven non-iota arms close
/// UNCONDITIONALLY by lifting the landed single-step development bricks to the star
/// motive via the new `par_reduces_p_star_{app,lam,pi,forall}` / `par_subst_p_star`
/// congruences; the iota arm (the fire-vs-development local-confluence join) is isolated
/// to the single faithful STAR hypothesis `iota_join_star`, FED its development from the
/// recursor's structural STAR IH. A DerivedProved closed term with an empty axiom closure.
#[test]
fn test_par_reduces_p_marked_triangle_star_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_pL_triangle_star")
        .expect("par_reduces_pL_triangle_star should be registered");
    assert!(
        !def.is_axiom,
        "par_reduces_pL_triangle_star should not be an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "par_reduces_pL_triangle_star should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "par_reduces_pL_triangle_star should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.value_src.is_some(),
        "par_reduces_pL_triangle_star should carry a closed proof term"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "par_reduces_pL_triangle_star should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    // The conclusion is the STAR-valued marked triangle: e ⇒L_n e' -> e' ⇒*_p cd e.
    assert!(
        def.type_src
            .contains("par_reduces_pL env n e e' -> par_reduces_p_star env e' (cd env e)"),
        "par_reduces_pL_triangle_star should conclude the STAR-valued marked triangle: {}",
        def.type_src
    );
    // The wall is isolated as the STAR iota_join hypothesis (e2 ⇒*_p cd e0 -> fire -> r ⇒*_p cd e0).
    assert!(
        def.type_src
            .contains("par_reduces_p_star env e2 (cd env e0) -> iota_step env e2 r -> ")
            && def.type_src.contains("par_reduces_p_star env r (cd env e0)"),
        "par_reduces_pL_triangle_star should isolate the iota arm as the STAR iota_join hypothesis: {}",
        def.type_src
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_reduces_pL_triangle_star should record deps");
    // The seven non-iota arms consume the NEW star congruences + the landed app dev brick.
    assert!(
        deps.contains("par_reduces_pL.rec")
            && deps.contains("par_reduces_p_star_app")
            && deps.contains("par_reduces_p_star_lam")
            && deps.contains("par_reduces_p_star_pi")
            && deps.contains("par_reduces_p_star_forall")
            && deps.contains("par_subst_p_star")
            && deps.contains("par_subsumes_par_p_star")
            && deps.contains("par_reduces_p_star_trans")
            && deps.contains("par_reduces_p_app_dev")
            && deps.contains("cd_refl")
            && deps.contains("cd_app_lam"),
        "par_reduces_pL_triangle_star should lift the development bricks to star via the new congruences: {deps:?}"
    );
    assert!(
        !deps.iter().any(|d| d.contains("church_rosser")),
        "par_reduces_pL_triangle_star must not depend on church_rosser_whnf: {deps:?}"
    );
}

/// Increment G (#2859, literal-scrutinee development): the `par_reduces_p0`
/// inductive (the in-tree analogue of the blueprint `Par0`) is registered with its
/// recursor and all EIGHT constructors (refl/beta/app/lam/pi/forall_/let_/iota_0),
/// where iota_0 is the LITERAL-scrutinee iota that fires on the source redex.
#[test]
fn test_par_reduces_p0_inductive_registered() {
    let spec = build_par_test_spec();
    assert!(
        spec.definitions().contains_key("par_reduces_p0"),
        "par_reduces_p0 inductive should be registered"
    );
    assert!(
        spec.definitions().contains_key("par_reduces_p0.rec"),
        "par_reduces_p0 recursor should be registered"
    );
    for ctor in [
        "refl", "beta", "app", "lam", "pi", "forall_", "let_", "iota_0",
    ] {
        let name = format!("par_reduces_p0.{ctor}");
        assert!(
            spec.definitions().contains_key(&name),
            "par_reduces_p0 constructor {name} should be registered"
        );
    }
    // The iota_0 constructor must gate on the LITERAL source redex (app f a) and
    // fire on the developed redex (app f' a'). The inductive's type_src is stored as
    // "Type" (the inductive's own type); the literal-scrutinee design is recorded in
    // the registered description, which is the stable queryable surface.
    let ind = spec
        .definitions()
        .get("par_reduces_p0")
        .expect("par_reduces_p0 should be registered");
    assert!(
        ind.description.contains("gate iota_step env (app f a) r0")
            && ind.description.contains("fire iota_step env (app f' a') r"),
        "par_reduces_p0.iota_0 must gate on the literal (app f a) and fire on the developed (app f' a'): {}",
        ind.description
    );
}

/// Increment G (#2859): the `par_reduces_p0` lift/subst substrate and the forward
/// bridge to `par_reduces_p` are DerivedProved closed terms with empty axiom
/// closures (genuine 0-axiom, FOUNDATIONAL only). These are the blueprint's
/// `par0_lift` / `par0_subst` and the `Par0 ⊆ Par` embedding the development
/// triangle is built on.
#[test]
fn test_par_reduces_p0_substrate_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in ["par_reduces_p0_subsumes_par_p", "par0_lift", "par0_subst"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
        // None of the par0 substrate may lean on the false church_rosser_whnf axiom.
        if let Some(deps) = def.dependencies.as_ref() {
            assert!(
                !deps.iter().any(|d| d.contains("church_rosser")),
                "{name} must not depend on church_rosser_whnf: {deps:?}"
            );
        }
    }
    // par0_lift / par0_subst must be stated over par_reduces_p0 (not par_reduces_p).
    let lift = spec.definitions().get("par0_lift").expect("par0_lift");
    assert!(
        lift.type_src
            .contains("par_reduces_p0 env (lift_at e c a) (lift_at e' c a)"),
        "par0_lift signature surface drift: {}",
        lift.type_src
    );
    let subst = spec.definitions().get("par0_subst").expect("par0_subst");
    assert!(
        subst
            .type_src
            .contains("par_reduces_p0 env (instantiate_at e v d) (instantiate_at e' v d)"),
        "par0_subst signature surface drift: {}",
        subst.type_src
    );
}

/// Increment G (#2859): the lam inversion `par_reduces_p0_lam_inv` and the triangle's
/// reflexive base `dev0_refl` (`par_reduces_p0 e (dev0 e)`) are DerivedProved closed
/// terms with empty axiom closures (genuine 0-axiom). `dev0_refl` is the cd_refl
/// analogue for the literal-scrutinee developer; its iota arm reaches
/// par_reduces_p0.iota_0 through dev0's nested LITERAL gate convoy with NO redex
/// reconstruction (the over-application wall is sidestepped).
#[test]
fn test_dev0_refl_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in ["par_reduces_p0_lam_inv", "dev0_refl"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
        if let Some(deps) = def.dependencies.as_ref() {
            assert!(
                !deps.iter().any(|d| d.contains("church_rosser")),
                "{name} must not depend on church_rosser_whnf: {deps:?}"
            );
        }
    }
    let refl = spec.definitions().get("dev0_refl").expect("dev0_refl");
    assert!(
        refl.type_src.contains("par_reduces_p0 env e (dev0 env e)"),
        "dev0_refl signature surface drift: {}",
        refl.type_src
    );
    // dev0_refl consumes the literal-scrutinee iota_0 and the par_reduces_p0 lam inversion.
    let deps = refl
        .dependencies
        .as_ref()
        .expect("dev0_refl should record deps");
    assert!(
        deps.contains("par_reduces_p0.iota_0") && deps.contains("par_reduces_p0_lam_inv"),
        "dev0_refl should reach iota_0 via the literal gate and use par_reduces_p0_lam_inv: {deps:?}"
    );
}

/// Increment G (#2859): the two-sided substitution tower for par_reduces_p0
/// (par_subst_refl_p0_full + par_subst_p0, the blueprint's par0_subst) is
/// DerivedProved 0-axiom. par_subst_p0 reduces BOTH the body and the substituted
/// value in a single par0-step — the substrate dev0_triangle's beta arm needs.
#[test]
fn test_par_subst_p0_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in ["par_subst_refl_p0_full", "par_subst_p0"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(def.value_src.is_some(), "{name} closed proof term");
        assert!(
            def.axiom_deps.is_empty(),
            "{name} empty axiom closure: {:?}",
            def.axiom_deps
        );
        if let Some(deps) = def.dependencies.as_ref() {
            assert!(
                !deps.iter().any(|d| d.contains("church_rosser")),
                "{name} must not depend on church_rosser_whnf: {deps:?}"
            );
        }
    }
    let subst = spec
        .definitions()
        .get("par_subst_p0")
        .expect("par_subst_p0");
    assert!(
        subst
            .type_src
            .contains("par_reduces_p0 env (instantiate_at e v d) (instantiate_at e' v' d)"),
        "par_subst_p0 must be two-sided (e=>e', v=>v'): {}",
        subst.type_src
    );
}

/// Increment G (#2859): the dev0_triangle app-arm BOUNDARY gate
/// `par_reduces_p0_redex_preserved_boundary` is DerivedProved 0-axiom. A minimal/
/// boundary iota redex (iota_reduct env f = none) is preserved under par0-reduction
/// of its spine: app f' a' is still a redex (iota_reduct env (app f' a') = some _).
/// This reuses the c/p-track par_reduces_p_app_redex through the
/// par_reduces_p0_subsumes_par_p bridge.
#[test]
fn test_par_reduces_p0_redex_preserved_boundary_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_reduces_p0_redex_preserved_boundary")
        .expect("par_reduces_p0_redex_preserved_boundary should be registered");
    assert!(!def.is_axiom, "should not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(def.value_src.is_some(), "should carry a closed proof term");
    assert!(
        def.axiom_deps.is_empty(),
        "should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    if let Some(deps) = def.dependencies.as_ref() {
        assert!(
            !deps.iter().any(|d| d.contains("church_rosser")),
            "must not depend on church_rosser_whnf: {deps:?}"
        );
    }
    // The boundary gate must be stated over the developed spine (app f' a') being a redex,
    // gated on the boundary guard iota_reduct env f = none.
    assert!(
        def.type_src
            .contains("Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)")
            && def.type_src.contains("iota_reduct env (KExpr.app f' a')"),
        "boundary gate signature surface drift: {}",
        def.type_src
    );
}

/// Stage 2 (#2859 Increment F+++): the full `par_reduces_p` diamond chain
/// (`topIotaStar` developer port) lands 0-axiom DerivedProved — `app_redex_tri` (the
/// over-application crux), `iota_redex_tri` (closes the iota arm via derivation
/// induction), `dev_triangle` (the Takahashi triangle), and the BREAKTHROUGH brick
/// `par_diamond` (the strong single-step diamond). Each must be a closed,
/// kernel-checked term with empty axiom closure and must not depend on
/// `church_rosser_whnf` (the relation it retires).
#[test]
fn test_par_reduces_p_diamond_chain_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    // The `dev` developer itself is a recursive `def` (not a proved lemma); it is
    // exercised below via dev_self / dev_triangle. The list here is the proved bricks.
    for name in [
        "topIotaStar_fix",
        "dev_self",
        "dev_iotaReduct_none",
        "topIotaStar_dev",
        "app_redex_tri",
        "iota_redex_tri_aux",
        "iota_redex_tri",
        "dev_kbeta",
        "dev_kcong",
        "dev_triangle",
        "par_diamond",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
        if let Some(deps) = def.dependencies.as_ref() {
            assert!(
                !deps.iter().any(|d| d.contains("church_rosser")),
                "{name} must not depend on church_rosser_whnf: {deps:?}"
            );
        }
    }

    // The `dev` developer (recursive def) underpins the whole chain.
    assert!(
        spec.definitions().contains_key("dev"),
        "the dev developer should be registered"
    );

    // The breakthrough brick par_diamond joins both legs at the complete development
    // dev e via dev_triangle (the strong single-step diamond).
    let par_diamond = spec
        .definitions()
        .get("par_diamond")
        .expect("par_diamond should be registered");
    let pd_deps = par_diamond
        .dependencies
        .as_ref()
        .expect("par_diamond should record deps");
    assert!(
        pd_deps.contains("dev_triangle") && pd_deps.contains("dev"),
        "par_diamond should join both legs at dev e via dev_triangle: {pd_deps:?}"
    );

    // iota_redex_tri_aux closes the open iota_p arm by DERIVATION induction: the
    // app-congruence case delegates to app_redex_tri (replacing the marked fuel), and
    // the iota cascade telescopes via topIotaStar_step.
    let aux = spec
        .definitions()
        .get("iota_redex_tri_aux")
        .expect("iota_redex_tri_aux should be registered");
    let aux_deps = aux
        .dependencies
        .as_ref()
        .expect("iota_redex_tri_aux should record deps");
    assert!(
        aux_deps.contains("app_redex_tri") && aux_deps.contains("topIotaStar_step"),
        "iota_redex_tri_aux should delegate the app arm to app_redex_tri and absorb the cascade via topIotaStar_step: {aux_deps:?}"
    );

    // app_redex_tri (the over-application crux) reuses the keystone reduct congruence
    // and the (app f' a')-side reconstruction — NOT the marked-fuel keystone.
    let crux = spec
        .definitions()
        .get("app_redex_tri")
        .expect("app_redex_tri should be registered");
    let crux_deps = crux
        .dependencies
        .as_ref()
        .expect("app_redex_tri should record deps");
    assert!(
        crux_deps.contains("par_reduces_p_reduct_cong")
            && crux_deps.contains("par_reduces_p_app_redex")
            && crux_deps.contains("iota_reduct_app_some"),
        "app_redex_tri should reuse par_reduces_p_reduct_cong + par_reduces_p_app_redex + iota_reduct_app_some: {crux_deps:?}"
    );
    assert!(
        !crux_deps.iter().any(|d| d.contains("par_reduces_pL")),
        "app_redex_tri must NOT route through the marked-fuel keystone (the derivation IH replaces the fuel): {crux_deps:?}"
    );
}

/// Stage 3 (#2859 Increment F+++): the Tait–Martin-Löf lift of the strong
/// single-step diamond `par_diamond` to full Church–Rosser confluence. The strip
/// lemma `par_strips_p_star_strip`, the multi-step diamond
/// `par_reduces_p_star_diamond` (= `par_reduces_p_star` CR), the sandwiched
/// `par_reduces_c_star_diamond` (= `par_reduces_c_star` CR, the result that makes
/// `church_rosser_whnf` deletable), and the two star-level sandwich bridges. Each
/// must be a closed, kernel-checked term with empty axiom closure and must not
/// depend on `church_rosser_whnf` (the relation it retires). The four faithful
/// interfaces are carried as HYPOTHESES (parameters in each lemma type), never
/// discharged here.
#[test]
fn test_par_reduces_p_star_confluence_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in [
        "par_reduces_c_star_subsumes_par_p_star",
        "par_reduces_p_star_subsumes_par_c_star",
        "par_strips_p_star_strip",
        "par_reduces_p_star_diamond",
        "par_reduces_c_star_diamond",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
        if let Some(deps) = def.dependencies.as_ref() {
            assert!(
                !deps.iter().any(|d| d.contains("church_rosser")),
                "{name} must not depend on church_rosser_whnf: {deps:?}"
            );
        }
    }

    // The strip lemma joins via the STRONG single-step diamond par_diamond (CPS),
    // closing the single-step side through par_reduces_p_star_trans.
    let strip = spec
        .definitions()
        .get("par_strips_p_star_strip")
        .expect("par_strips_p_star_strip should be registered");
    let strip_deps = strip
        .dependencies
        .as_ref()
        .expect("par_strips_p_star_strip should record deps");
    assert!(
        strip_deps.contains("par_diamond") && strip_deps.contains("par_reduces_p_star_trans"),
        "par_strips_p_star_strip should tile par_diamond and re-close via par_reduces_p_star_trans: {strip_deps:?}"
    );

    // par_reduces_p_star_diamond (par_reduces_p_star CR) strips each head step via
    // par_strips_p_star_strip.
    let pdiam = spec
        .definitions()
        .get("par_reduces_p_star_diamond")
        .expect("par_reduces_p_star_diamond should be registered");
    let pdiam_deps = pdiam
        .dependencies
        .as_ref()
        .expect("par_reduces_p_star_diamond should record deps");
    assert!(
        pdiam_deps.contains("par_strips_p_star_strip"),
        "par_reduces_p_star_diamond should strip head steps via par_strips_p_star_strip: {pdiam_deps:?}"
    );

    // par_reduces_c_star_diamond (par_reduces_c_star CR — the church_rosser_whnf
    // retirement target) rides the star-level sandwich on par_reduces_p_star_diamond.
    let cdiam = spec
        .definitions()
        .get("par_reduces_c_star_diamond")
        .expect("par_reduces_c_star_diamond should be registered");
    let cdiam_deps = cdiam
        .dependencies
        .as_ref()
        .expect("par_reduces_c_star_diamond should record deps");
    assert!(
        cdiam_deps.contains("par_reduces_p_star_diamond")
            && cdiam_deps.contains("par_reduces_c_star_subsumes_par_p_star")
            && cdiam_deps.contains("par_reduces_p_star_subsumes_par_c_star"),
        "par_reduces_c_star_diamond should sandwich par_reduces_p_star_diamond between the two star bridges: {cdiam_deps:?}"
    );
}

// ===========================================================================
// #2859 Increment H: the δ-extended computational parallel reduction
// par_reduces_cd and the 3-way (β+ι+δ) cross-joins (par_reduces_cd.rs).
// ===========================================================================

/// `RedEnv` product carrier + `red_rec` / `red_def` projections registered.
#[test]
fn test_red_env_and_projections_registered() {
    let spec = build_par_test_spec();
    for name in ["RedEnv", "RedEnv.mk", "RedEnv.rec", "red_rec", "red_def"] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered (RedEnv = RecEnv × DefEnv carrier)"
        );
    }
}

/// `RecEnvDefEnvDisjoint` faithful interface + its projector are registered, and
/// the projector `recenv_defenv_disjoint_recmeta` is a DerivedProved closed term
/// with an empty axiom closure (FOUNDATIONAL only). The δ analogue of
/// `recenv_ctor_rec_disjoint_major`: a defined const is never a recursor.
#[test]
fn test_recenv_defenv_disjoint_recmeta_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    for name in ["RecEnvDefEnvDisjoint", "RecEnvDefEnvDisjoint.rec"] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered (δ name-disjointness interface)"
        );
    }
    let def = spec
        .definitions()
        .get("recenv_defenv_disjoint_recmeta")
        .expect("recenv_defenv_disjoint_recmeta should be registered");
    assert!(
        !def.is_axiom,
        "recenv_defenv_disjoint_recmeta is not an axiom"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(def.proof_status, ProofStatus::DerivedProved);
    assert!(def.value_src.is_some());
    assert!(
        def.axiom_deps.is_empty(),
        "recenv_defenv_disjoint_recmeta should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    assert!(
        def.type_src.contains(
            "Eq (OptionType RecMeta) (recmeta_for (red_rec env) dname) (OptionType.none RecMeta)"
        ),
        "recenv_defenv_disjoint_recmeta should conclude recmeta_for (red_rec env) dname = none: {}",
        def.type_src
    );
}

/// `par_reduces_cd` (the δ-extended relation) is registered with all 9
/// constructors (refl/beta/app/lam/pi/forall_/let_/iota/delta), and its join
/// witness `par_strips_witness_cd` is registered.
#[test]
fn test_par_reduces_cd_has_nine_constructors() {
    let spec = build_par_test_spec();
    assert!(spec.definitions().contains_key("par_reduces_cd"));
    assert!(spec.definitions().contains_key("par_reduces_cd.rec"));
    for ctor in [
        "refl", "beta", "app", "lam", "pi", "forall_", "let_", "iota", "delta",
    ] {
        let name = format!("par_reduces_cd.{ctor}");
        assert!(
            spec.definitions().contains_key(&name),
            "par_reduces_cd.{ctor} constructor should be registered"
        );
    }
    for name in ["par_strips_witness_cd", "par_strips_witness_cd.intro"] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered"
        );
    }
}

/// The (δ,δ) cross-join `par_strips_delta_delta_cd` is a DerivedProved closed term
/// with an empty axiom closure — closed by `delta_step_deterministic` ALONE. The δ
/// mirror of `par_strips_iota_iota_c`.
#[test]
fn test_par_strips_delta_delta_cd_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    let def = spec
        .definitions()
        .get("par_strips_delta_delta_cd")
        .expect("par_strips_delta_delta_cd should be registered");
    assert!(!def.is_axiom, "par_strips_delta_delta_cd is not an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(def.proof_status, ProofStatus::DerivedProved);
    assert!(def.value_src.is_some());
    assert!(
        def.axiom_deps.is_empty(),
        "par_strips_delta_delta_cd should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("par_strips_delta_delta_cd should record deps");
    assert!(
        deps.contains("delta_step_deterministic") && deps.contains("par_reduces_cd.refl"),
        "par_strips_delta_delta_cd should close via determinism + refl: {deps:?}"
    );
}

/// Helper: a DerivedProved closed term with an empty axiom closure.
fn assert_zero_axiom_derived_proved(spec: &Specification, name: &str) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(!def.is_axiom, "{name} should not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma, "{name} category");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(def.value_src.is_some(), "{name} should carry a proof term");
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should have an empty axiom closure (FOUNDATIONAL only): {:?}",
        def.axiom_deps
    );
}

/// The (δ,β) head-disjointness primitive `delta_step_beta_redex_absurd` — a delta
/// step on a beta redex is impossible — is zero-axiom DerivedProved.
#[test]
fn test_delta_step_beta_redex_absurd_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    assert_zero_axiom_derived_proved(&spec, "delta_step_beta_redex_absurd");
}

/// The (δ,ι) head-disjointness primitive `delta_iota_disjoint_absurd` — a delta
/// step and an iota step on the same source are impossible together, via the
/// `RecEnvDefEnvDisjoint` name-disjointness interface — is zero-axiom DerivedProved.
#[test]
fn test_delta_iota_disjoint_absurd_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    assert_zero_axiom_derived_proved(&spec, "delta_iota_disjoint_absurd");
    let def = spec
        .definitions()
        .get("delta_iota_disjoint_absurd")
        .expect("registered");
    let deps = def.dependencies.as_ref().expect("deps");
    assert!(
        deps.contains("recenv_defenv_disjoint_recmeta")
            && deps.contains("delta_reduct_some_inv")
            && deps.contains("iota_reduct_some_inv"),
        "delta_iota_disjoint_absurd should consume the disjointness interface + both inverters: {deps:?}"
    );
}

/// The embedding `par_reduces_c_subsumes_cd` — every β+ι computational par-step
/// (over red_rec env) lifts into the δ-extended par_reduces_cd — is zero-axiom
/// DerivedProved.
#[test]
fn test_par_reduces_c_subsumes_cd_is_zero_axiom_derived_proved() {
    let spec = build_par_test_spec();
    assert_zero_axiom_derived_proved(&spec, "par_reduces_c_subsumes_cd");
}
