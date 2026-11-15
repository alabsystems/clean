// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Module definition exposure for source attribute validation. Kernel checking
//! and runtime compilation retain the original definition values.
use super::{
    register_persistent_ext, EnvExtensionEntry, EnvExtensionEntryData, Environment, ExtensionIdx,
    PersistentExtEntry, PersistentExtState,
};
use crate::Name;
use std::collections::BTreeMap;
use std::sync::{Arc, OnceLock};

#[derive(Clone, Debug)]
enum Entry {
    Definition(Name, bool),
    Invalid,
}
impl PersistentExtEntry for Entry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        match self {
            Self::Definition(name, exposed) => EnvExtensionEntry {
                name: name.clone(),
                data: EnvExtensionEntryData::Scalar(u64::from(*exposed)),
            },
            Self::Invalid => EnvExtensionEntry {
                name: Name::anon(),
                data: EnvExtensionEntryData::Scalar(2),
            },
        }
    }
    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        Some(match entry.data {
            EnvExtensionEntryData::Scalar(value @ 0..=1) if !entry.name.is_anon() => {
                Self::Definition(entry.name.clone(), value == 1)
            }
            _ => Self::Invalid,
        })
    }
}
#[derive(Clone, Debug, Default)]
struct State {
    definitions: Arc<BTreeMap<Name, bool>>,
    invalid: bool,
}
impl PersistentExtState for State {
    type Entry = Entry;
    fn add_entry(&mut self, entry: &Entry) {
        match entry {
            Entry::Definition(name, exposed) => {
                Arc::make_mut(&mut self.definitions).insert(name.clone(), *exposed);
            }
            Entry::Invalid => self.invalid = true,
        }
    }
    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        let mut entries: Vec<_> = self
            .definitions
            .iter()
            .map(|(name, exposed)| Entry::Definition(name.clone(), *exposed).to_env_entry())
            .collect();
        if self.invalid {
            entries.push(Entry::Invalid.to_env_entry());
        }
        entries
    }
}
fn index() -> ExtensionIdx {
    static INDEX: OnceLock<ExtensionIdx> = OnceLock::new();
    *INDEX.get_or_init(|| {
        register_persistent_ext::<State>(Name::from_string("Clean.module.definitionExposure"))
    })
}
/// Record a module-system definition's export visibility, independently of its
/// logical value and compiler implementation.
pub fn record(env: &mut Environment, name: Name, exposed: bool) {
    env.add_ext_entry::<State>(index(), &Entry::Definition(name, exposed));
}
/// Recorded module definitions, in stable name order. Legacy definitions have
/// no exposure restriction and need no entry.
pub fn definitions(env: &Environment) -> Vec<(Name, bool)> {
    env.get_ext_state::<State>(index())
        .map(|s| s.definitions.iter().map(|(n, e)| (n.clone(), *e)).collect())
        .unwrap_or_default()
}
/// A source attribute's exporting view, never a replacement for the runtime or
/// kernel environment. Removing values drops verification stamps in this clone.
pub fn exporting_view(env: &Environment) -> Result<Environment, &'static str> {
    let mut view = env.clone();
    if let Some(state) = env.get_ext_state::<State>(index()) {
        if state.invalid {
            return Err("malformed module exposure metadata");
        }
        for (name, exposed) in state.definitions.iter() {
            if !exposed {
                view.forget_value(name);
            }
        }
    }
    Ok(view)
}

#[cfg(test)]
mod tests {
    use super::super::{
        ConstantInfo, ConstantKind, ConstantOrigin, ConstantSource, Declaration,
        DeclarationVerification, Reducibility,
    };
    use super::*;
    use crate::{BinderInfo, Expr, Level};
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Debug)]
    struct Source(ConstantInfo);
    impl ConstantSource for Source {
        fn get(&self, name: &Name) -> Option<&ConstantInfo> {
            (name == &self.0.name).then_some(&self.0)
        }
        fn contains(&self, name: &Name) -> bool {
            name == &self.0.name
        }
        fn names(&self) -> Vec<Name> {
            vec![self.0.name.clone()]
        }
    }

    #[test]
    fn exporting_view_hides_eager_and_lazy_bodies_without_mutating_original() {
        let eager = Name::from_string("eager");
        let lazy = Name::from_string("lazy");
        let exposed = Name::from_string("exposed");
        let info = |name| ConstantInfo::new(name, vec![], Expr::prop(), Some(Expr::prop()), true);
        let mut env = Environment::new();
        env.constants.insert(eager.clone(), info(eager.clone()));
        env.constants.insert(exposed.clone(), info(exposed.clone()));
        env.set_constant_source(Arc::new(Source(info(lazy.clone()))));
        record(&mut env, eager.clone(), false);
        record(&mut env, lazy.clone(), false);
        record(&mut env, exposed.clone(), true);
        let mut view = exporting_view(&env).expect("valid metadata");
        view.refresh_constant_source_cache();
        for name in [&eager, &lazy] {
            assert!(env.get_const(name).expect("original").value.is_some());
            let hidden = view.get_const(name).expect("exporting view");
            assert!(hidden.value.is_none());
            assert_eq!(hidden.reducibility, Reducibility::Opaque);
        }
        assert!(view.get_const(&exposed).expect("exposed").value.is_some());
        assert_eq!(view.lazy_source_names(), vec![lazy]);
    }

    #[derive(Clone, Debug)]
    struct RefreshingSource {
        packets: Arc<BTreeMap<Name, ConstantInfo>>,
        withheld: Name,
        refreshes: Arc<AtomicUsize>,
    }
    impl ConstantSource for RefreshingSource {
        fn get(&self, name: &Name) -> Option<&ConstantInfo> {
            if name == &self.withheld {
                None
            } else {
                self.packets.get(name)
            }
        }
        fn contains(&self, name: &Name) -> bool {
            self.packets.contains_key(name)
        }
        fn names(&self) -> Vec<Name> {
            self.packets.keys().cloned().collect()
        }
        fn fresh(&self) -> Option<Arc<dyn ConstantSource>> {
            self.refreshes.fetch_add(1, Ordering::SeqCst);
            Some(Arc::new(self.clone()))
        }
    }

    fn stripped(mut info: ConstantInfo) -> ConstantInfo {
        info.value = None;
        info.reducibility = Reducibility::Opaque;
        info.is_reducible = false;
        info
    }

    #[test]
    fn lazy_elision_preserves_packets_and_survives_real_refreshes() {
        let mut env = Environment::new();
        let eager = Name::from_string("hidden.eager");
        let lazy = Name::from_string("hidden.lazy");
        let theorem = Name::from_string("hidden.theorem");
        let exposed_eager = Name::from_string("exposed.eager");
        let exposed_lazy = Name::from_string("exposed.lazy");
        let withheld = Name::from_string("indexed.but.withheld");
        let missing = Name::from_string("absent");
        let u = Name::from_string("u");
        for name in [&eager, &lazy, &exposed_eager, &exposed_lazy, &withheld] {
            env.add_decl(Declaration::Definition {
                name: name.clone(),
                level_params: vec![u.clone()],
                type_: Expr::sort(Level::succ(Level::param(u.clone()))),
                value: Expr::sort(Level::param(u.clone())),
                is_reducible: true,
            })
            .expect("checked polymorphic fixture");
        }
        env.add_decl(Declaration::Theorem {
            name: theorem.clone(),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        })
        .expect("checked theorem fixture");
        let origin = ConstantOrigin::olean_import(Some("ExposureFixture".into()));
        assert!(env.set_constant_origin(lazy.clone(), origin));
        let originals: BTreeMap<_, _> = env
            .constants()
            .map(|info| (info.name.clone(), info.clone()))
            .collect();
        let mut packets = BTreeMap::new();
        for name in [&lazy, &theorem, &exposed_lazy, &withheld] {
            packets.insert(
                name.clone(),
                env.constants.remove(name).expect("move to source"),
            );
        }
        // A source entry with the same name must never defeat the eager packet.
        let mut shadowed_source_packet = stripped(originals[&eager].clone());
        shadowed_source_packet.kind = ConstantKind::Axiom;
        packets.insert(eager.clone(), shadowed_source_packet);
        let refreshes = Arc::new(AtomicUsize::new(0));
        env.set_constant_source(Arc::new(RefreshingSource {
            packets: Arc::new(packets),
            withheld: withheld.clone(),
            refreshes: Arc::clone(&refreshes),
        }));
        for name in [&eager, &lazy, &theorem, &withheld, &missing] {
            record(&mut env, name.clone(), false);
        }
        for name in [&exposed_eager, &exposed_lazy] {
            record(&mut env, name.clone(), true);
        }
        let eager_count = env.num_constants();
        let generation = env.generation();
        let source_names = env.lazy_source_names();
        let stamps = env.declaration_verification.clone();
        let origins = env.constant_origins.clone();
        assert_eq!(env.get_const(&eager), Some(&originals[&eager]));
        assert!(env
            .lazy_source
            .as_ref()
            .expect("source")
            .contains(&withheld));
        assert!(env.get_const(&withheld).is_none());

        let mut view = exporting_view(&env).expect("valid metadata");
        assert_eq!(view.num_constants(), eager_count + 2);
        assert!(view.generation() > generation);
        assert_eq!(view.constant_origins, origins);
        for _ in 0..2 {
            view.refresh_constant_source_cache();
            for name in [&eager, &lazy, &theorem] {
                assert_eq!(
                    view.get_const(name),
                    Some(&stripped(originals[name].clone()))
                );
                assert_eq!(view.declaration_verification(name), None);
                assert_eq!(env.get_const(name), Some(&originals[name]));
                assert_eq!(
                    env.declaration_verification(name),
                    Some(DeclarationVerification::FullKernelCheck)
                );
            }
            for name in [&exposed_eager, &exposed_lazy] {
                assert_eq!(view.get_const(name), Some(&originals[name]));
                assert_eq!(
                    view.declaration_verification(name),
                    Some(DeclarationVerification::FullKernelCheck)
                );
            }
            assert!(view.get_const(&withheld).is_none());
            assert!(view.get_const(&missing).is_none());
            assert_eq!(view.lazy_source_names(), source_names);
        }
        assert_eq!(refreshes.load(Ordering::SeqCst), 2, "real source refreshes");
        assert_eq!(env.num_constants(), eager_count);
        assert_eq!(env.generation(), generation);
        assert_eq!(env.declaration_verification, stamps);
        assert_eq!(env.constant_origins, origins);

        let count = view.num_constants();
        let generation = view.generation();
        let stamps = view.declaration_verification.clone();
        for name in [&eager, &lazy, &theorem] {
            assert!(view.forget_value(name), "already elided name still exists");
        }
        for name in [&missing, &withheld] {
            assert!(!view.forget_value(name), "unavailable name stays absent");
            assert!(!view.constants.contains_key(name));
        }
        assert_eq!(view.num_constants(), count);
        assert_eq!(
            view.generation(),
            generation,
            "idempotent and missing no-ops"
        );
        assert_eq!(view.declaration_verification, stamps);
        assert_eq!(view.constant_origins, origins);

        // Materialized shadows persist bodyless; serialization grants no stamp.
        let restored = Environment::from_bincode(&view.to_bincode().expect("serialize view"))
            .expect("restore view");
        for name in [&eager, &lazy, &theorem] {
            assert_eq!(
                restored.get_const(name),
                Some(&stripped(originals[name].clone()))
            );
            assert_eq!(restored.declaration_verification(name), None);
        }
        assert_eq!(
            restored.get_constant_origin(&lazy),
            env.get_constant_origin(&lazy)
        );
    }

    #[test]
    fn bodyless_lazy_materialization_changes_generation_once() {
        let mut env = Environment::new();
        let name = Name::from_string("already.opaque");
        let info = ConstantInfo::new_with_reducibility(
            name.clone(),
            vec![],
            Expr::prop(),
            None,
            Reducibility::Opaque,
            ConstantKind::Axiom,
        );
        env.set_constant_source(Arc::new(Source(info.clone())));
        let generation = env.generation();
        let count = env.num_constants();
        assert!(env.forget_value(&name));
        assert_eq!(env.get_const(&name), Some(&info));
        assert_eq!(env.num_constants(), count + 1);
        assert!(
            env.generation() > generation,
            "materialization invalidates generation readers"
        );
        let generation = env.generation();
        assert!(env.forget_value(&name));
        assert_eq!(env.generation(), generation);
        assert_eq!(env.declaration_verification(&name), None);
    }

    #[test]
    fn forget_value_invalidates_warm_native_fold_authority_at_same_count() {
        let mut env = Environment::with_prelude();
        let add = Name::from_string("Nat.add");
        let mul = Name::from_string("Nat.mul");
        for name in [&add, &mul] {
            assert!(
                env.native_fold_verdict(name).is_ok(),
                "warm canonical {name}"
            );
        }
        let sum = Expr::apps(
            Expr::const_(add.clone(), vec![]),
            [Expr::nat_lit(2), Expr::nat_lit(3)],
        );
        assert!(crate::TypeChecker::new(&env).is_def_eq(&sum, &Expr::nat_lit(5)));
        let count = env.num_constants();
        let generation = env.generation();
        assert!(env.forget_value(&add));
        assert_eq!(env.num_constants(), count, "eager elision keeps the count");
        assert!(env.get_const(&add).expect("retained name").value.is_none());
        let cold = env.clone();
        for name in [&add, &mul] {
            eprintln!(
                "{name}: warm={:?}; cold={:?}",
                env.native_fold_verdict(name),
                cold.native_fold_verdict(name)
            );
        }
        for name in [&add, &mul] {
            let expected = cold.native_fold_verdict(name);
            assert!(expected.is_err(), "cold verdict must refuse {name}");
            assert_eq!(
                env.native_fold_verdict(name),
                expected,
                "warm verdict must follow the removed body's cold verdict for {name}"
            );
        }
        assert!(env.generation() > generation);
        assert!(!crate::TypeChecker::new(&env).is_def_eq(&sum, &Expr::nat_lit(5)));
    }

    #[test]
    fn malformed_metadata_cannot_produce_an_exporting_view() {
        let mut env = Environment::new();
        let malformed = EnvExtensionEntry {
            name: Name::from_string("bad"),
            data: EnvExtensionEntryData::Scalar(7),
        };
        let entry = Entry::from_env_entry(&malformed).expect("invalid sentinel");
        env.add_ext_entry::<State>(index(), &entry);
        assert!(exporting_view(&env).is_err());
    }
}
