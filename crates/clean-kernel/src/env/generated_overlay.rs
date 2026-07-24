// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated namespace overlay for #1444.
//!
//! This module loads namespace payload artifacts from `env/generated/` and
//! registers them in bulk via `extend_constants_unchecked`.
//!
//! Payload artifacts can be refreshed with:
//! `cargo run -p clean-olean --bin generate_namespace_overlay -- ...`

// Always-compiled: topology_topological_space (live production path)
use crate::env::generated::topology_topological_space;
use crate::env::types::ConstantInfo;
use crate::env::{EnvError, Environment};

pub(crate) const TOPOLOGICAL_SPACE_NAMESPACE: &str = topology_topological_space::NAMESPACE;

// All other generated overlay imports/constants are test/feature-gated
#[cfg(any(test, feature = "math-overlays"))]
use crate::env::generated::{
    topology_characteristic, topology_cobordism, topology_connection, topology_contractible,
    topology_coproduct, topology_covering_space, topology_cw, topology_derham, topology_embedding,
    topology_fiber_bundle, topology_filtration, topology_fundamental_group,
    topology_higher_homotopy, topology_homology, topology_homotopy_equivalence, topology_kahler,
    topology_ktheory, topology_lie_group, topology_manifold, topology_morse,
    topology_path_connected, topology_principal_bundle, topology_product, topology_quotient,
    topology_retract, topology_scheme, topology_sheaf, topology_simplicial,
    topology_simply_connected, topology_spectral, topology_spin, topology_subspace,
    topology_suspension, topology_symplectic, topology_vector_bundle,
};

#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_MANIFOLD_NAMESPACE: &str = topology_manifold::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_LIE_GROUP_NAMESPACE: &str = topology_lie_group::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE: &str = topology_principal_bundle::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_CONNECTION_NAMESPACE: &str = topology_connection::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SYMPLECTIC_NAMESPACE: &str = topology_symplectic::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_KAHLER_NAMESPACE: &str = topology_kahler::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SPIN_NAMESPACE: &str = topology_spin::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_QUOTIENT_NAMESPACE: &str = topology_quotient::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SUBSPACE_NAMESPACE: &str = topology_subspace::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_EMBEDDING_NAMESPACE: &str = topology_embedding::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_PRODUCT_NAMESPACE: &str = topology_product::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_FIBER_BUNDLE_NAMESPACE: &str = topology_fiber_bundle::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_FILTRATION_NAMESPACE: &str = topology_filtration::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_HIGHER_HOMOTOPY_NAMESPACE: &str = topology_higher_homotopy::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_MORSE_NAMESPACE: &str = topology_morse::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SPECTRAL_NAMESPACE: &str = topology_spectral::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_CHARACTERISTIC_NAMESPACE: &str = topology_characteristic::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_COBORDISM_NAMESPACE: &str = topology_cobordism::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SHEAF_NAMESPACE: &str = topology_sheaf::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SCHEME_NAMESPACE: &str = topology_scheme::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_CW_NAMESPACE: &str = topology_cw::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SIMPLICIAL_NAMESPACE: &str = topology_simplicial::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_HOMOLOGY_NAMESPACE: &str = topology_homology::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_DERHAM_NAMESPACE: &str = topology_derham::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_KTHEORY_NAMESPACE: &str = topology_ktheory::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_COPRODUCT_NAMESPACE: &str = topology_coproduct::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SUSPENSION_NAMESPACE: &str = topology_suspension::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_VECTOR_BUNDLE_NAMESPACE: &str = topology_vector_bundle::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_PATH_CONNECTED_NAMESPACE: &str = topology_path_connected::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_SIMPLY_CONNECTED_NAMESPACE: &str = topology_simply_connected::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_CONTRACTIBLE_NAMESPACE: &str = topology_contractible::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_COVERING_SPACE_NAMESPACE: &str = topology_covering_space::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_FUNDAMENTAL_GROUP_NAMESPACE: &str = topology_fundamental_group::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_HOMOTOPY_EQUIVALENCE_NAMESPACE: &str =
    topology_homotopy_equivalence::NAMESPACE;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) const TOPOLOGY_RETRACT_NAMESPACE: &str = topology_retract::NAMESPACE;

#[cfg(any(test, feature = "math-overlays"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NamespaceSourcePolicy {
    GeneratedOverlayFirst,
    HandwrittenOnly,
}

#[cfg(any(test, feature = "math-overlays"))]
pub(crate) fn namespace_source_policy(namespace: &str) -> NamespaceSourcePolicy {
    if namespace == TOPOLOGICAL_SPACE_NAMESPACE {
        return NamespaceSourcePolicy::GeneratedOverlayFirst;
    }
    if is_gated_overlay_namespace(namespace) {
        return NamespaceSourcePolicy::GeneratedOverlayFirst;
    }
    NamespaceSourcePolicy::HandwrittenOnly
}

#[cfg(any(test, feature = "math-overlays"))]
fn is_gated_overlay_namespace(namespace: &str) -> bool {
    namespace == TOPOLOGY_MANIFOLD_NAMESPACE
        || namespace == TOPOLOGY_LIE_GROUP_NAMESPACE
        || namespace == TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE
        || namespace == TOPOLOGY_CONNECTION_NAMESPACE
        || namespace == TOPOLOGY_SYMPLECTIC_NAMESPACE
        || namespace == TOPOLOGY_KAHLER_NAMESPACE
        || namespace == TOPOLOGY_SPIN_NAMESPACE
        || namespace == TOPOLOGY_QUOTIENT_NAMESPACE
        || namespace == TOPOLOGY_SUBSPACE_NAMESPACE
        || namespace == TOPOLOGY_EMBEDDING_NAMESPACE
        || namespace == TOPOLOGY_PRODUCT_NAMESPACE
        || namespace == TOPOLOGY_FIBER_BUNDLE_NAMESPACE
        || namespace == TOPOLOGY_FILTRATION_NAMESPACE
        || namespace == TOPOLOGY_HIGHER_HOMOTOPY_NAMESPACE
        || namespace == TOPOLOGY_MORSE_NAMESPACE
        || namespace == TOPOLOGY_SPECTRAL_NAMESPACE
        || namespace == TOPOLOGY_CHARACTERISTIC_NAMESPACE
        || namespace == TOPOLOGY_COBORDISM_NAMESPACE
        || namespace == TOPOLOGY_SHEAF_NAMESPACE
        || namespace == TOPOLOGY_SCHEME_NAMESPACE
        || namespace == TOPOLOGY_CW_NAMESPACE
        || namespace == TOPOLOGY_SIMPLICIAL_NAMESPACE
        || namespace == TOPOLOGY_HOMOLOGY_NAMESPACE
        || namespace == TOPOLOGY_DERHAM_NAMESPACE
        || namespace == TOPOLOGY_KTHEORY_NAMESPACE
        || namespace == TOPOLOGY_COPRODUCT_NAMESPACE
        || namespace == TOPOLOGY_SUSPENSION_NAMESPACE
        || namespace == TOPOLOGY_VECTOR_BUNDLE_NAMESPACE
        || namespace == TOPOLOGY_PATH_CONNECTED_NAMESPACE
        || namespace == TOPOLOGY_SIMPLY_CONNECTED_NAMESPACE
        || namespace == TOPOLOGY_CONTRACTIBLE_NAMESPACE
        || namespace == TOPOLOGY_COVERING_SPACE_NAMESPACE
        || namespace == TOPOLOGY_FUNDAMENTAL_GROUP_NAMESPACE
        || namespace == TOPOLOGY_HOMOTOPY_EQUIVALENCE_NAMESPACE
        || namespace == TOPOLOGY_RETRACT_NAMESPACE
}

#[cfg(any(test, feature = "math-overlays"))]
pub(crate) fn build_topology_manifold_payload() -> Vec<ConstantInfo> {
    topology_manifold::payload()
}

#[cfg(any(test, feature = "math-overlays"))]
fn build_topology_lie_group_payload() -> Vec<ConstantInfo> {
    topology_lie_group::payload()
}

fn build_namespace_payload(namespace: &str) -> Result<Vec<ConstantInfo>, EnvError> {
    // TopologicalSpace is always available (live production path)
    if namespace == TOPOLOGICAL_SPACE_NAMESPACE {
        return Ok(topology_topological_space::payload());
    }

    // All other namespaces require the math-overlays feature
    #[cfg(any(test, feature = "math-overlays"))]
    if let Some(payload) = build_gated_namespace_payload(namespace) {
        return Ok(payload);
    }

    Err(EnvError::UnsupportedGeneratedNamespace {
        namespace: namespace.to_owned(),
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn build_gated_namespace_payload(namespace: &str) -> Option<Vec<ConstantInfo>> {
    Some(match namespace {
        ns if ns == TOPOLOGY_MANIFOLD_NAMESPACE => build_topology_manifold_payload(),
        ns if ns == TOPOLOGY_LIE_GROUP_NAMESPACE => build_topology_lie_group_payload(),
        ns if ns == TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE => topology_principal_bundle::payload(),
        ns if ns == TOPOLOGY_CONNECTION_NAMESPACE => topology_connection::payload(),
        ns if ns == TOPOLOGY_SYMPLECTIC_NAMESPACE => topology_symplectic::payload(),
        ns if ns == TOPOLOGY_KAHLER_NAMESPACE => topology_kahler::payload(),
        ns if ns == TOPOLOGY_SPIN_NAMESPACE => topology_spin::payload(),
        ns if ns == TOPOLOGY_QUOTIENT_NAMESPACE => topology_quotient::payload(),
        ns if ns == TOPOLOGY_SUBSPACE_NAMESPACE => topology_subspace::payload(),
        ns if ns == TOPOLOGY_EMBEDDING_NAMESPACE => topology_embedding::payload(),
        ns if ns == TOPOLOGY_PRODUCT_NAMESPACE => topology_product::payload(),
        ns if ns == TOPOLOGY_FIBER_BUNDLE_NAMESPACE => topology_fiber_bundle::payload(),
        ns if ns == TOPOLOGY_FILTRATION_NAMESPACE => topology_filtration::payload(),
        ns if ns == TOPOLOGY_HIGHER_HOMOTOPY_NAMESPACE => topology_higher_homotopy::payload(),
        ns if ns == TOPOLOGY_MORSE_NAMESPACE => topology_morse::payload(),
        ns if ns == TOPOLOGY_SPECTRAL_NAMESPACE => topology_spectral::payload(),
        ns if ns == TOPOLOGY_CHARACTERISTIC_NAMESPACE => topology_characteristic::payload(),
        ns if ns == TOPOLOGY_COBORDISM_NAMESPACE => topology_cobordism::payload(),
        ns if ns == TOPOLOGY_SHEAF_NAMESPACE => topology_sheaf::payload(),
        ns if ns == TOPOLOGY_SCHEME_NAMESPACE => topology_scheme::payload(),
        ns if ns == TOPOLOGY_CW_NAMESPACE => topology_cw::payload(),
        ns if ns == TOPOLOGY_SIMPLICIAL_NAMESPACE => topology_simplicial::payload(),
        ns if ns == TOPOLOGY_HOMOLOGY_NAMESPACE => topology_homology::payload(),
        ns if ns == TOPOLOGY_DERHAM_NAMESPACE => topology_derham::payload(),
        ns if ns == TOPOLOGY_KTHEORY_NAMESPACE => topology_ktheory::payload(),
        ns if ns == TOPOLOGY_COPRODUCT_NAMESPACE => topology_coproduct::payload(),
        ns if ns == TOPOLOGY_SUSPENSION_NAMESPACE => topology_suspension::payload(),
        ns if ns == TOPOLOGY_VECTOR_BUNDLE_NAMESPACE => topology_vector_bundle::payload(),
        ns if ns == TOPOLOGY_PATH_CONNECTED_NAMESPACE => topology_path_connected::payload(),
        ns if ns == TOPOLOGY_SIMPLY_CONNECTED_NAMESPACE => topology_simply_connected::payload(),
        ns if ns == TOPOLOGY_CONTRACTIBLE_NAMESPACE => topology_contractible::payload(),
        ns if ns == TOPOLOGY_COVERING_SPACE_NAMESPACE => topology_covering_space::payload(),
        ns if ns == TOPOLOGY_FUNDAMENTAL_GROUP_NAMESPACE => topology_fundamental_group::payload(),
        ns if ns == TOPOLOGY_HOMOTOPY_EQUIVALENCE_NAMESPACE => {
            topology_homotopy_equivalence::payload()
        }
        ns if ns == TOPOLOGY_RETRACT_NAMESPACE => topology_retract::payload(),
        _ => return None,
    })
}

pub(crate) fn load_generated_namespace_overlay(
    env: &mut Environment,
    namespace: &str,
) -> Result<usize, EnvError> {
    // Wrap payload construction in stack_safe: generated payload functions
    // construct large Expr trees with massive stack frames (25-50KB each).
    // Without this, chained init calls that each build payloads can overflow
    // the default 8MB thread stack when invoked outside cargo (which sets
    // RUST_MIN_STACK via .cargo/config.toml). See #1483.
    let payload = crate::expr::stack_safe(|| build_namespace_payload(namespace))?;
    load_namespace_overlay(env, payload)
}

/// Load a generated namespace overlay into the environment.
///
/// Registers pre-built `ConstantInfo` records via `extend_constants_unchecked`,
/// skipping per-declaration type checking.
pub(crate) fn load_namespace_overlay(
    env: &mut Environment,
    payload: Vec<ConstantInfo>,
) -> Result<usize, EnvError> {
    let count = payload.len();
    for info in &payload {
        if env.get_const(&info.name).is_some() {
            return Err(EnvError::DuplicateName(info.name.clone()));
        }
    }
    // SOUNDNESS (Pillar-1 G4 — CLOSED): this is the PRIMARY, genuinely
    // trust-bearing registration of the generated overlay declarations into the
    // trusted env. It now routes through `extend_constants_checked`, which runs
    // the EXACT kernel machinery `add_decl(Declaration::Axiom)` would:
    //   * `infer_sort(type_)` on every record — each axiom's declared type is a
    //     well-formed Sort (no leaked fvar/mvar, all Level::Params in scope);
    //   * `check_type(value, type_)` on every VALUE-bearing record — closing the
    //     one shape `add_decl` cannot mint: a `kind:Axiom` record carrying a
    //     `Reducible` value (`Function.Injective`) whose body the reducer would
    //     otherwise δ-unfold UNCHECKED during def-eq.
    // Records are inserted then re-checked against the complete env (overlay
    // namespaces are mutually-referencing); any record the kernel rejects makes
    // this return `Err`, and the caller discards the partially-built env
    // (fail-closed). Unresolved sibling/base references (a legitimate forward /
    // external overlay dependency) are TOLERATED — still fully structurally
    // checked, re-typecheckable once the full env is assembled. This drops the
    // overlay lane out of the unchecked-production ratchet
    // (`data/unchecked_decl_ratchet.json` extend_constants block). The records
    // still enlarge the trusted AXIOM base (their TRUTH is governed by the C2
    // golden-pin + data/axiom_audit.json), but they are no longer trusted
    // WELL-FORMED / WELL-TYPED on the generator's authority — the kernel
    // re-derives that here.
    env.extend_constants_checked(payload.into_iter())
        .map_err(|(_name, e)| e)?;
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name::Name;

    fn payload_names(payload: &[ConstantInfo]) -> Vec<String> {
        payload.iter().map(|c| c.name.to_string()).collect()
    }

    #[test]
    fn test_payload_has_29_declarations() {
        let payload = build_topology_manifold_payload();
        assert_eq!(payload.len(), topology_manifold::DECL_COUNT);
        assert_eq!(payload.len(), 29);
        assert_eq!(
            payload_names(&payload),
            topology_manifold::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lie_group_payload_has_20_declarations() {
        let payload = build_topology_lie_group_payload();
        assert_eq!(payload.len(), topology_lie_group::DECL_COUNT);
        assert_eq!(payload.len(), 20);
        assert_eq!(
            payload_names(&payload),
            topology_lie_group::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_generated_payload_types_are_closed() {
        let all_payloads: Vec<(&str, Vec<ConstantInfo>)> = vec![
            ("Manifold", build_topology_manifold_payload()),
            ("LieGroup", build_topology_lie_group_payload()),
            ("PrincipalBundle", topology_principal_bundle::payload()),
            ("Connection", topology_connection::payload()),
            ("Symplectic", topology_symplectic::payload()),
            ("Kahler", topology_kahler::payload()),
            ("Spin", topology_spin::payload()),
            ("Quotient", topology_quotient::payload()),
            ("Subspace", topology_subspace::payload()),
            ("Embedding", topology_embedding::payload()),
            ("Product", topology_product::payload()),
            ("FiberBundle", topology_fiber_bundle::payload()),
            ("Filtration", topology_filtration::payload()),
            ("Morse", topology_morse::payload()),
            ("Spectral", topology_spectral::payload()),
            ("Characteristic", topology_characteristic::payload()),
            ("Cobordism", topology_cobordism::payload()),
            ("Sheaf", topology_sheaf::payload()),
            ("Scheme", topology_scheme::payload()),
            ("CW", topology_cw::payload()),
            ("Simplicial", topology_simplicial::payload()),
            ("Homology", topology_homology::payload()),
            ("DeRham", topology_derham::payload()),
            ("KTheory", topology_ktheory::payload()),
            ("Coproduct", topology_coproduct::payload()),
            ("Suspension", topology_suspension::payload()),
            ("VectorBundle", topology_vector_bundle::payload()),
            ("PathConnected", topology_path_connected::payload()),
            ("SimplyConnected", topology_simply_connected::payload()),
            ("Contractible", topology_contractible::payload()),
            ("CoveringSpace", topology_covering_space::payload()),
            ("FundamentalGroup", topology_fundamental_group::payload()),
            (
                "HomotopyEquivalence",
                topology_homotopy_equivalence::payload(),
            ),
            ("Retract", topology_retract::payload()),
            ("TopologicalSpace", topology_topological_space::payload()),
        ];
        for (ns, payload) in all_payloads {
            for info in payload {
                assert!(
                    !info.type_.has_fvar_quick(),
                    "{ns}/{}: type contains leaked FVars",
                    info.name
                );
            }
        }
    }

    #[test]
    fn test_simple_axiom_payload_counts() {
        assert_eq!(topology_principal_bundle::payload().len(), 16);
        assert_eq!(topology_connection::payload().len(), 20);
        assert_eq!(topology_symplectic::payload().len(), 27);
        assert_eq!(topology_kahler::payload().len(), 37);
        assert_eq!(topology_spin::payload().len(), 72);
        assert_eq!(
            topology_fiber_bundle::payload().len(),
            topology_fiber_bundle::DECL_COUNT
        );
        assert_eq!(topology_fiber_bundle::payload().len(), 17);
        assert_eq!(
            payload_names(&topology_fiber_bundle::payload()),
            topology_fiber_bundle::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_quotient_payload_has_15_declarations() {
        let payload = topology_quotient::payload();
        assert_eq!(payload.len(), topology_quotient::DECL_COUNT);
        assert_eq!(payload.len(), 15);
        assert_eq!(
            payload_names(&payload),
            topology_quotient::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_subspace_payload_has_7_declarations() {
        let payload = topology_subspace::payload();
        assert_eq!(payload.len(), topology_subspace::DECL_COUNT);
        assert_eq!(payload.len(), 7);
        assert_eq!(
            payload_names(&payload),
            topology_subspace::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_payload_loads_via_init_topology_manifold() {
        let mut env = Environment::new();
        env.init_topology_manifold()
            .expect("init_topology_manifold should succeed");

        let payload = build_topology_manifold_payload();
        for info in &payload {
            let loaded = env
                .get_const(&info.name)
                .unwrap_or_else(|| panic!("missing after init: {}", info.name));
            assert_eq!(
                info.type_, loaded.type_,
                "{}: payload type differs from loaded",
                info.name
            );
            assert_eq!(
                info.level_params, loaded.level_params,
                "{}: payload level_params differ from loaded",
                info.name
            );
        }
    }

    #[test]
    fn test_load_namespace_overlay_registers_declarations() {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_nat().expect("init_nat");
        env.init_fin().expect("init_fin");
        env.init_rat().expect("init_rat");
        env.init_list().expect("init_list");
        env.init_eq().expect("init_eq");
        env.init_exists().expect("init_exists");
        env.init_true_false().expect("init_true_false");
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topology_homeomorphism()
            .expect("init_topology_homeomorphism");
        env.init_add_comm_group().expect("init_add_comm_group");

        let payload = build_topology_manifold_payload();
        let count = load_namespace_overlay(&mut env, payload).expect("overlay load should succeed");
        assert_eq!(count, topology_manifold::DECL_COUNT);

        for name in topology_manifold::DECL_NAMES {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "missing declaration: {name}"
            );
        }
    }

    #[test]
    fn test_load_namespace_overlay_rejects_duplicates() {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_nat().expect("init_nat");
        env.init_fin().expect("init_fin");
        env.init_rat().expect("init_rat");
        env.init_list().expect("init_list");
        env.init_eq().expect("init_eq");
        env.init_exists().expect("init_exists");
        env.init_true_false().expect("init_true_false");
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topology_homeomorphism()
            .expect("init_topology_homeomorphism");
        env.init_add_comm_group().expect("init_add_comm_group");

        let payload = build_topology_manifold_payload();
        load_namespace_overlay(&mut env, payload).expect("first load");

        let payload2 = build_topology_manifold_payload();
        let err = load_namespace_overlay(&mut env, payload2)
            .expect_err("second load should fail with duplicate");
        match err {
            EnvError::DuplicateName(name) => {
                assert!(
                    name.to_string().starts_with(TOPOLOGY_MANIFOLD_NAMESPACE),
                    "duplicate name should come from Topology.Manifold namespace"
                );
            }
            other => panic!("expected DuplicateName, got: {other:?}"),
        }
    }

    #[test]
    fn test_namespace_source_policy_defaults() {
        for ns in [
            TOPOLOGY_MANIFOLD_NAMESPACE,
            TOPOLOGY_LIE_GROUP_NAMESPACE,
            TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE,
            TOPOLOGY_CONNECTION_NAMESPACE,
            TOPOLOGY_SYMPLECTIC_NAMESPACE,
            TOPOLOGY_KAHLER_NAMESPACE,
            TOPOLOGY_SPIN_NAMESPACE,
            TOPOLOGY_QUOTIENT_NAMESPACE,
            TOPOLOGY_SUBSPACE_NAMESPACE,
            TOPOLOGY_EMBEDDING_NAMESPACE,
            TOPOLOGY_PRODUCT_NAMESPACE,
            TOPOLOGY_FIBER_BUNDLE_NAMESPACE,
            TOPOLOGY_FILTRATION_NAMESPACE,
            TOPOLOGY_MORSE_NAMESPACE,
            TOPOLOGY_SPECTRAL_NAMESPACE,
            TOPOLOGY_CHARACTERISTIC_NAMESPACE,
            TOPOLOGY_COBORDISM_NAMESPACE,
            TOPOLOGY_SHEAF_NAMESPACE,
            TOPOLOGY_SCHEME_NAMESPACE,
            TOPOLOGY_CW_NAMESPACE,
            TOPOLOGY_SIMPLICIAL_NAMESPACE,
            TOPOLOGY_HOMOLOGY_NAMESPACE,
            TOPOLOGY_DERHAM_NAMESPACE,
            TOPOLOGY_KTHEORY_NAMESPACE,
            TOPOLOGY_PATH_CONNECTED_NAMESPACE,
            TOPOLOGY_SIMPLY_CONNECTED_NAMESPACE,
            TOPOLOGY_CONTRACTIBLE_NAMESPACE,
            TOPOLOGY_COVERING_SPACE_NAMESPACE,
            TOPOLOGY_FUNDAMENTAL_GROUP_NAMESPACE,
            TOPOLOGY_HOMOTOPY_EQUIVALENCE_NAMESPACE,
            TOPOLOGY_RETRACT_NAMESPACE,
        ] {
            assert_eq!(
                namespace_source_policy(ns),
                NamespaceSourcePolicy::GeneratedOverlayFirst,
                "{ns} should be GeneratedOverlayFirst"
            );
        }
        assert_eq!(
            namespace_source_policy("Topology.Unknown"),
            NamespaceSourcePolicy::HandwrittenOnly
        );
    }

    #[test]
    fn test_load_generated_namespace_overlay_loads_topology_manifold() {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_nat().expect("init_nat");
        env.init_fin().expect("init_fin");
        env.init_rat().expect("init_rat");
        env.init_list().expect("init_list");
        env.init_eq().expect("init_eq");
        env.init_exists().expect("init_exists");
        env.init_true_false().expect("init_true_false");
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topology_homeomorphism()
            .expect("init_topology_homeomorphism");
        env.init_add_comm_group().expect("init_add_comm_group");

        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_MANIFOLD_NAMESPACE)
            .expect("namespace overlay load should succeed");
        assert_eq!(count, topology_manifold::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.Manifold.Chart"))
            .is_some());
    }

    #[test]
    fn test_load_generated_namespace_overlay_loads_topology_lie_group() {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_nat().expect("init_nat");
        env.init_rat().expect("init_rat");
        env.init_eq().expect("init_eq");
        env.init_topology_manifold()
            .expect("init_topology_manifold");
        env.init_group().expect("init_group");
        env.init_add_comm_group().expect("init_add_comm_group");

        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_LIE_GROUP_NAMESPACE)
            .expect("lie-group namespace overlay load should succeed");
        assert_eq!(count, topology_lie_group::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.LieGroup.LieAlgebraHom"))
            .is_some());
    }

    #[test]
    fn test_load_generated_namespace_overlay_loads_topology_subspace_cluster() {
        let mut env = Environment::new();
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_subtype().expect("init_subtype");
        env.init_eq().expect("init_eq");
        env.init_exists().expect("init_exists");

        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_SUBSPACE_NAMESPACE)
            .expect("subspace namespace overlay load should succeed");
        assert_eq!(count, topology_subspace::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.SubspaceTopology"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("Topology.inclusion_continuous"))
            .is_some());
    }

    #[test]
    fn test_load_generated_namespace_overlay_rejects_unknown_namespace() {
        let mut env = Environment::new();
        let unknown = "Topology.Unknown";
        let err = load_generated_namespace_overlay(&mut env, unknown)
            .expect_err("unknown generated namespace should fail");
        match err {
            EnvError::UnsupportedGeneratedNamespace { namespace } => {
                assert_eq!(namespace, unknown);
            }
            other => panic!("expected UnsupportedGeneratedNamespace, got: {other:?}"),
        }
    }

    #[test]
    fn test_load_simple_axiom_namespaces_via_overlay() {
        let mut env = Environment::new();
        // Set up all dependencies needed by topology_diff init functions
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_nat().expect("init_nat");
        env.init_eq().expect("init_eq");

        // PrincipalBundle
        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE)
            .expect("principal bundle overlay");
        assert_eq!(count, topology_principal_bundle::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string(
                "Topology.PrincipalBundle.PrincipalBundle"
            ))
            .is_some());

        // Connection
        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_CONNECTION_NAMESPACE)
            .expect("connection overlay");
        assert_eq!(count, topology_connection::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.Connection.LeviCivita"))
            .is_some());

        // Symplectic
        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_SYMPLECTIC_NAMESPACE)
            .expect("symplectic overlay");
        assert_eq!(count, topology_symplectic::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.Symplectic.PoissonBracket"))
            .is_some());

        // Kahler
        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_KAHLER_NAMESPACE)
            .expect("kahler overlay");
        assert_eq!(count, topology_kahler::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.Kahler.CalabiYau"))
            .is_some());

        // Spin
        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_SPIN_NAMESPACE)
            .expect("spin overlay");
        assert_eq!(count, topology_spin::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.Spin.DiracOperator"))
            .is_some());
    }

    #[test]
    fn test_embedding_payload_has_11_declarations() {
        let payload = topology_embedding::payload();
        assert_eq!(payload.len(), topology_embedding::DECL_COUNT);
        assert_eq!(payload.len(), 11);
        assert_eq!(
            payload_names(&payload),
            topology_embedding::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_embedding_function_injective_has_value() {
        let payload = topology_embedding::payload();
        let injective = payload
            .iter()
            .find(|c| c.name.to_string() == "Function.Injective")
            .expect("Function.Injective should be in embedding payload");
        assert!(
            injective.value.is_some(),
            "Function.Injective should be a definition with a value"
        );
        assert!(
            injective.is_reducible,
            "Function.Injective should be reducible"
        );
        assert_eq!(injective.level_params.len(), 2, "should have [u, v] levels");
    }

    #[test]
    fn test_load_generated_namespace_overlay_loads_embedding_cluster() {
        let mut env = Environment::new();
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_subtype().expect("init_subtype");
        env.init_eq().expect("init_eq");
        env.init_exists().expect("init_exists");

        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_EMBEDDING_NAMESPACE)
            .expect("embedding namespace overlay load should succeed");
        assert_eq!(count, topology_embedding::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.IsEmbedding"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("Function.Injective"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("Topology.IsOpenEmbedding"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string(
                "Topology.closed_embedding_of_closed_inclusion"
            ))
            .is_some());
    }

    #[test]
    fn test_product_payload_has_16_declarations() {
        let payload = topology_product::payload();
        assert_eq!(payload.len(), topology_product::DECL_COUNT);
        assert_eq!(payload.len(), 16);
        assert_eq!(
            payload_names(&payload),
            topology_product::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_product_dual_universe_declarations() {
        let payload = topology_product::payload();
        // First 5 declarations should have [u, v] level params
        for info in &payload[..5] {
            assert_eq!(
                info.level_params.len(),
                2,
                "{} should have [u, v] levels",
                info.name
            );
        }
        // Remaining 11 should have [u] level params
        for info in &payload[5..] {
            assert_eq!(
                info.level_params.len(),
                1,
                "{} should have [u] level",
                info.name
            );
        }
    }

    #[test]
    fn test_load_generated_namespace_overlay_loads_product_cluster() {
        let mut env = Environment::new();
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_prod().expect("init_prod");
        env.init_eq().expect("init_eq");

        let count = load_generated_namespace_overlay(&mut env, TOPOLOGY_PRODUCT_NAMESPACE)
            .expect("product namespace overlay load should succeed");
        assert_eq!(count, topology_product::DECL_COUNT);
        assert!(env
            .get_const(&Name::from_string("Topology.ProductTopology"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string(
                "Topology.ProductTopology.fst_continuous"
            ))
            .is_some());
        assert!(env
            .get_const(&Name::from_string(
                "Topology.ProductTopology.diagonal_closed"
            ))
            .is_some());
    }

    #[test]
    fn test_characteristic_payload_has_50_declarations() {
        let payload = topology_characteristic::payload();
        assert_eq!(payload.len(), topology_characteristic::DECL_COUNT);
        assert_eq!(payload.len(), 50);
        assert_eq!(
            payload_names(&payload),
            topology_characteristic::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_cobordism_payload_has_40_declarations() {
        let payload = topology_cobordism::payload();
        assert_eq!(payload.len(), topology_cobordism::DECL_COUNT);
        assert_eq!(payload.len(), 40);
        assert_eq!(
            payload_names(&payload),
            topology_cobordism::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_filtration_payload_has_18_declarations() {
        let payload = topology_filtration::payload();
        assert_eq!(payload.len(), topology_filtration::DECL_COUNT);
        assert_eq!(payload.len(), 18);
        assert_eq!(
            payload_names(&payload),
            topology_filtration::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_morse_payload_has_26_declarations() {
        let payload = topology_morse::payload();
        assert_eq!(payload.len(), topology_morse::DECL_COUNT);
        assert_eq!(payload.len(), 26);
        assert_eq!(
            payload_names(&payload),
            topology_morse::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_sheaf_payload_has_40_declarations() {
        let payload = topology_sheaf::payload();
        assert_eq!(payload.len(), topology_sheaf::DECL_COUNT);
        assert_eq!(payload.len(), 40);
        assert_eq!(
            payload_names(&payload),
            topology_sheaf::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_scheme_payload_has_35_declarations() {
        let payload = topology_scheme::payload();
        assert_eq!(payload.len(), topology_scheme::DECL_COUNT);
        assert_eq!(payload.len(), 35);
        assert_eq!(
            payload_names(&payload),
            topology_scheme::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_cw_payload_has_15_declarations() {
        let payload = topology_cw::payload();
        assert_eq!(payload.len(), topology_cw::DECL_COUNT);
        assert_eq!(payload.len(), 15);
        assert_eq!(
            payload_names(&payload),
            topology_cw::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_simplicial_payload_has_16_declarations() {
        let payload = topology_simplicial::payload();
        assert_eq!(payload.len(), topology_simplicial::DECL_COUNT);
        assert_eq!(payload.len(), 16);
        assert_eq!(
            payload_names(&payload),
            topology_simplicial::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_homology_payload_has_22_declarations() {
        let payload = topology_homology::payload();
        assert_eq!(payload.len(), topology_homology::DECL_COUNT);
        assert_eq!(payload.len(), 22);
        assert_eq!(
            payload_names(&payload),
            topology_homology::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_derham_payload_has_27_declarations() {
        let payload = topology_derham::payload();
        assert_eq!(payload.len(), topology_derham::DECL_COUNT);
        assert_eq!(payload.len(), 27);
        assert_eq!(
            payload_names(&payload),
            topology_derham::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_ktheory_payload_has_30_declarations() {
        let payload = topology_ktheory::payload();
        assert_eq!(payload.len(), topology_ktheory::DECL_COUNT);
        assert_eq!(payload.len(), 30);
        assert_eq!(
            payload_names(&payload),
            topology_ktheory::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_topological_space_payload_has_12_declarations() {
        let payload = topology_topological_space::payload();
        assert_eq!(payload.len(), topology_topological_space::DECL_COUNT);
        assert_eq!(payload.len(), 12);
        assert_eq!(
            payload_names(&payload),
            topology_topological_space::DECL_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_payload_loads_via_init_topological_space() {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space should succeed");

        let payload = topology_topological_space::payload();
        for info in &payload {
            let loaded = env
                .get_const(&info.name)
                .unwrap_or_else(|| panic!("missing after init: {}", info.name));
            assert_eq!(
                info.type_, loaded.type_,
                "{}: payload type differs from loaded",
                info.name
            );
            assert_eq!(
                info.level_params, loaded.level_params,
                "{}: payload level_params differ from loaded",
                info.name
            );
        }
    }

    #[test]
    fn test_topological_space_namespace_uses_generated_overlay_policy() {
        assert_eq!(
            namespace_source_policy(TOPOLOGICAL_SPACE_NAMESPACE),
            NamespaceSourcePolicy::GeneratedOverlayFirst
        );
    }

    #[test]
    fn test_manifold_overlay_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_topology_manifold()
            .expect("init_topology_manifold");
        let tc = TypeChecker::new(&env);

        // Verify key manifold constants type-check after overlay load
        for name in &[
            "Topology.Manifold.Chart",
            "Topology.Manifold.SmoothManifold",
            "Topology.Manifold.TangentBundle",
        ] {
            let n = Name::from_string(name);
            let ci = env.get_const(&n).expect(name);
            let levels: Vec<Level> = ci.level_params.iter().map(|_| Level::zero()).collect();
            let expr = crate::expr::Expr::const_(n, levels);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            // All manifold declarations are Pi types or Sorts
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
                "{name}: expected Sort or Pi type, got {ty:?}"
            );
        }
    }
}
