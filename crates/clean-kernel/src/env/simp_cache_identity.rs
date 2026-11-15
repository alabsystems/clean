// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Process-local identity for derived simp structures, never proof evidence.

use std::sync::Arc;

/// An environment's origin and exact simp-registry mutation snapshot.
///
/// Fresh and deserialized environments get distinct origins. Clones share an
/// origin, but each registry mutation gets a distinct snapshot, even when two
/// clones register the same names with different declarations. Holding the
/// tokens keeps their allocations alive, so allocator address reuse cannot
/// produce a cache hit. Neither token is serialized or read by the checker.
#[derive(Clone, Debug)]
pub struct SimpCacheIdentity {
    origin: Arc<()>,
    registry: Arc<()>,
}

impl Default for SimpCacheIdentity {
    fn default() -> Self {
        Self {
            origin: Arc::new(()),
            registry: Arc::new(()),
        }
    }
}

impl PartialEq for SimpCacheIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.shares_origin(other) && Arc::ptr_eq(&self.registry, &other.registry)
    }
}

impl Eq for SimpCacheIdentity {}

impl SimpCacheIdentity {
    /// Whether closed-pattern path reuse belongs to the same environment
    /// lineage. This alone does not authorize reusing a collected lemma set.
    #[must_use]
    pub fn shares_origin(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.origin, &other.origin)
    }

    pub(super) fn registry_changed(&mut self) {
        self.registry = Arc::new(());
    }
}

#[cfg(test)]
mod tests {
    use crate::env::{Declaration, Environment, SimpPriority};
    use crate::{Expr, Name};

    #[test]
    fn fresh_environments_and_registry_branches_have_distinct_identities() {
        let env = Environment::new();
        let original = env.simp_cache_identity();
        assert_ne!(original, Environment::new().simp_cache_identity());
        let mut first = env.clone();
        let mut second = env;
        assert_eq!(original, first.simp_cache_identity());
        for branch in [&mut first, &mut second] {
            branch.register_simp_lemma(Name::from_string("same"), SimpPriority::Default);
        }
        let left = first.simp_cache_identity();
        let right = second.simp_cache_identity();
        assert_eq!(
            first.simp_registry_revision(),
            second.simp_registry_revision()
        );
        assert_ne!(left, right);
        assert!(original.shares_origin(&left) && left.shares_origin(&right));
    }

    #[test]
    fn append_only_declarations_preserve_the_registry_snapshot() {
        let mut env = Environment::new();
        let original = env.simp_cache_identity();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("P"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("well-typed proposition declaration");
        assert_eq!(original, env.simp_cache_identity());
    }

    #[test]
    fn registry_churn_invalidates_but_missing_removal_preserves_identity() {
        let mut env = Environment::new();
        let name = Name::from_string("same");
        env.register_simp_lemma(name.clone(), SimpPriority::Default);
        let registered = env.simp_cache_identity();
        assert!(!env.unregister_simp_lemma(&Name::from_string("absent")));
        assert_eq!(registered, env.simp_cache_identity());
        assert!(env.unregister_simp_lemma(&name));
        let removed = env.simp_cache_identity();
        assert_ne!(registered, removed);
        env.register_simp_lemma(name, SimpPriority::Default);
        assert_ne!(registered, env.simp_cache_identity());
        assert_ne!(removed, env.simp_cache_identity());
    }

    #[test]
    fn identity_is_not_serialized_and_restoration_gets_a_fresh_origin() {
        // `new` installs three built-in constants in a randomized HashMap.
        // Its legacy bincode order can change on restoration. Use the truly
        // empty fixture for exact round-trip bytes, and check a populated
        // environment separately with only its transient identity changed.
        let env = Environment::default();
        let bytes = env.to_bincode().expect("serialize empty environment");
        let restored = Environment::from_bincode(&bytes).expect("restore environment");
        assert_ne!(env.simp_cache_identity(), restored.simp_cache_identity());
        assert!(!env
            .simp_cache_identity()
            .shares_origin(&restored.simp_cache_identity()));
        assert_eq!(bytes, restored.to_bincode().expect("reserialize"));
        assert!(!serde_json::to_string(&env)
            .expect("serialize JSON")
            .contains("simp_cache_identity"));
        let dag = env.to_dag_bincode().expect("serialize DAG environment");
        let restored = Environment::from_dag_bincode(&dag).expect("restore DAG environment");
        assert!(!env
            .simp_cache_identity()
            .shares_origin(&restored.simp_cache_identity()));
        assert_eq!(dag, restored.to_dag_bincode().expect("reserialize DAG"));

        let populated = Environment::new();
        let mut retagged = populated.clone();
        retagged.simp_cache_identity = Default::default();
        assert_ne!(
            populated.simp_cache_identity(),
            retagged.simp_cache_identity()
        );
        assert_eq!(
            populated
                .to_bincode()
                .expect("serialize populated environment"),
            retagged
                .to_bincode()
                .expect("serialize retagged environment")
        );
        assert_eq!(
            populated.to_dag_bincode().expect("serialize populated DAG"),
            retagged.to_dag_bincode().expect("serialize retagged DAG")
        );
    }
}
