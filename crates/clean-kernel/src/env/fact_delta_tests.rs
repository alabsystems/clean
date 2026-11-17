// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The local fact delta replays exactly what an elaboration did, carries the
//! producing check's stamps, refuses what it cannot replay, and refuses to
//! apply to an environment its key does not name.

use super::*;
use crate::env::{Declaration, DeclarationVerification};
use crate::expr::Expr;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// The serde-skipped fields of [`Environment`], which `transplant_heavy`
/// moves by hand.
const TRANSIENT_FIELDS: &[&str] = &[
    "lazy_source",
    "declaration_verification",
    "codata_origins",
    "codata_carriers",
    "cumulative_ever",
    "native_reducers",
    "kernel_theory",
    "native_fold_cache",
    "prelude_aliases",
    "simp_cache_identity",
];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn enumeration(ty: &str, ctors: &[&str]) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n(ty),
            type_: Expr::type_(),
            constructors: ctors
                .iter()
                .map(|ctor| Constructor {
                    name: n(&format!("{ty}.{ctor}")),
                    type_: c(ty),
                })
                .collect(),
        }],
    }
}

fn def(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("`{name}` is well-typed: {e:?}"));
}

/// The macro emits this inventory from the same fields and attributes as
/// `Environment`; formatting or wrapping the field table cannot hide a skip.
fn serde_skipped_fields(fields: &[(&str, &[&str])]) -> Vec<String> {
    fields
        .iter()
        .filter_map(|(field, attributes)| {
            let mut skipped = false;
            for attribute in *attributes {
                let compact: String = attribute.chars().filter(|ch| !ch.is_whitespace()).collect();
                if compact.starts_with("serde(") {
                    match compact.as_str() {
                        "serde(skip)" => skipped = true,
                        "serde(default)" => {}
                        other => panic!("unmodeled serde field attribute on `{field}`: {other}"),
                    }
                }
            }
            skipped.then(|| (*field).to_string())
        })
        .collect()
}

fn transient_field_census_matches(fields: &[(&str, &[&str])]) -> bool {
    let mut in_declaration = serde_skipped_fields(fields);
    in_declaration.sort();
    let mut handled: Vec<String> = TRANSIENT_FIELDS.iter().map(|s| (*s).to_string()).collect();
    handled.sort();
    in_declaration == handled
}

#[test]
fn transient_fields_are_exactly_the_serde_skipped_ones() {
    assert!(
        transient_field_census_matches(crate::env::ENVIRONMENT_FIELD_ATTRIBUTES),
        "a serde-skipped Environment field must be moved by `transplant_heavy`, or a replay \
         silently resets it"
    );
}

#[test]
fn every_typed_component_is_a_serialized_field() {
    let capture = OrderedCapture::capture(&Environment::new()).expect("capture");
    let seen: Vec<&str> = capture.fields.iter().map(|(field, _)| *field).collect();
    for field in DELTA_TYPED_FIELDS {
        assert!(
            seen.contains(field),
            "`{field}` is not a serialized Environment field"
        );
    }
    // And the generic capture still records the rest (the prelude flags).
    assert!(
        capture
            .fields
            .iter()
            .filter(|(_, bytes)| bytes.is_some())
            .count()
            > 100
    );
}

#[test]
fn every_effect_component_is_a_delta_component() {
    for field in super::super::effect::TYPED_FIELDS {
        assert!(
            DELTA_TYPED_FIELDS.contains(field),
            "`{field}` is compared by an effect but not carried as a typed delta component"
        );
    }
}

#[test]
fn an_unchanged_environment_has_an_empty_delta() {
    let env = Environment::with_prelude();
    let delta = env.local_fact_delta_since(&env.clone()).expect("delta");
    assert_eq!(delta.changed_entries(), 0);
    let mut replayed = env.clone();
    replayed.apply_local_fact_delta(&delta).expect("apply");
    assert_eq!(replayed.local_fact_difference(&env), None);
}

#[test]
fn registry_delta_replay_refreshes_the_snapshot_for_entries_and_churn() {
    let mut env = Environment::new();
    let name = n("deltaSimpProposition");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("checked proposition declaration");
    for action in 0..3 {
        let mut produced = env.clone();
        match action {
            0 => produced.register_simp_lemma(name.clone(), super::super::SimpPriority::Default),
            1 => assert!(produced.unregister_simp_lemma(&name)),
            _ => {
                produced.register_simp_lemma(name.clone(), super::super::SimpPriority::Default);
                assert!(produced.unregister_simp_lemma(&name));
            }
        }
        let delta = produced
            .local_fact_delta_since(&env)
            .expect("registry delta");
        assert!(delta.scalars.is_empty(), "exercise registry-only replay");
        assert!(delta.counter_steps[1] > 0);
        if action == 2 {
            assert!(delta.simp_lemmas.changed.is_empty(), "net-neutral churn");
        }
        let identity = env.simp_cache_identity();
        env.apply_local_fact_delta(&delta)
            .expect("apply registry delta");
        assert_ne!(identity, env.simp_cache_identity());
        assert!(identity.shares_origin(&env.simp_cache_identity()));
        assert_eq!(env.local_fact_difference(&produced), None);
    }
    let empty = env.local_fact_delta_since(&env).expect("empty delta");
    let identity = env.simp_cache_identity();
    env.apply_local_fact_delta(&empty)
        .expect("apply empty delta");
    assert_eq!(identity, env.simp_cache_identity());
}

#[test]
fn scalar_delta_replay_resets_the_simp_cache_origin() {
    let mut env = Environment::new();
    let mut produced = env.clone();
    produced.set_cumulative(true);
    let delta = produced.local_fact_delta_since(&env).expect("scalar delta");
    assert!(!delta.scalars.is_empty(), "exercise scalar reconstruction");
    let identity = env.simp_cache_identity();
    env.apply_local_fact_delta(&delta)
        .expect("apply scalar delta");
    assert!(!identity.shares_origin(&env.simp_cache_identity()));
    assert_eq!(env.local_fact_difference(&produced), None);
}

#[test]
fn a_checked_declaration_replays_with_its_stamp_and_no_check() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    after
        .add_inductive(enumeration("TgSix", &["a", "b"]))
        .expect("inductive");
    def(&mut after, "tgSixPick", c("TgSix"), c("TgSix.b"));
    let delta = after.local_fact_delta_since(&before).expect("delta");
    assert!(delta
        .changed_constant_names()
        .iter()
        .any(|name| **name == n("tgSixPick")));

    let bytes = delta.encode().expect("encode");
    let decoded = EnvFactDelta::decode(&bytes).expect("decode");
    let mut replayed = before.clone();
    replayed.apply_local_fact_delta(&decoded).expect("apply");
    assert_eq!(replayed.local_fact_difference(&after), None);
    for name in ["TgSix", "TgSix.a", "TgSix.rec", "tgSixPick"] {
        assert_eq!(
            replayed.declaration_verification(&n(name)),
            Some(DeclarationVerification::FullKernelCheck),
            "`{name}` carries the producing check's stamp"
        );
    }
    assert!(replayed.inductives.contains_key(&n("TgSix")));
}

/// TG6 measurement (astream-broker): a `def` whose value is a `∀` records
/// its binder names, which a later named argument reads. The delta carries
/// them, so an elaboration that wrote them stores a fact, and a replay leaves
/// the table a real elaboration leaves.
#[test]
fn value_binder_names_replay_and_are_part_of_the_elaboration_record() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    def(
        &mut after,
        "tgSixAll",
        Expr::type_(),
        Expr::pi(crate::expr::BinderInfo::Default, c("Nat"), Expr::prop()),
    );
    let record = |env: &mut Environment, binder: &str| {
        env.record_value_forall_binder_names(n("tgSixAll"), 0, vec![n(binder)]);
    };
    record(&mut after, "x");
    let delta = after
        .local_fact_delta_since(&before)
        .expect("binder names are replayable");
    let mut replayed = before.clone();
    replayed
        .apply_local_fact_delta(
            &EnvFactDelta::decode(&delta.encode().expect("encode")).expect("decode"),
        )
        .expect("apply");
    assert_eq!(replayed.local_fact_difference(&after), None);
    assert_eq!(
        replayed.get_value_forall_binder_names(&n("tgSixAll")),
        after.get_value_forall_binder_names(&n("tgSixAll"))
    );
    assert!(replayed
        .get_value_forall_binder_names(&n("tgSixAll"))
        .is_some());

    // A replay that lost them, or recorded others, is a difference, and the
    // elaboration record of the name sees which names were recorded.
    let mut without = before.clone();
    def(
        &mut without,
        "tgSixAll",
        Expr::type_(),
        Expr::pi(crate::expr::BinderInfo::Default, c("Nat"), Expr::prop()),
    );
    assert!(without.local_fact_difference(&after).is_some());
    let mut renamed = without.clone();
    record(&mut renamed, "y");
    assert!(renamed.local_fact_difference(&after).is_some());
    assert_ne!(
        renamed.elaboration_record_digest(&n("tgSixAll")),
        after.elaboration_record_digest(&n("tgSixAll"))
    );
    assert_ne!(
        without.elaboration_record_digest(&n("tgSixAll")),
        after.elaboration_record_digest(&n("tgSixAll"))
    );
}

#[test]
fn a_lazy_initialisation_flag_replays_through_the_generic_capture() {
    let before = Environment::new();
    let mut after = before.clone();
    after.init_nat().expect("init nat");
    assert_ne!(before.nat_init, after.nat_init);
    let delta = after.local_fact_delta_since(&before).expect("delta");
    assert!(delta
        .scalars
        .iter()
        .any(|(field, _, _)| field == "nat_init"));
    let mut replayed = before.clone();
    replayed.apply_local_fact_delta(&delta).expect("apply");
    assert!(replayed.nat_init);
    assert_eq!(replayed.local_fact_difference(&after), None);
}

/// NEGATIVE CONTROL: a delta applied to an environment that is not the one
/// its key names refuses, rather than silently overwriting.
#[test]
fn a_delta_refuses_an_environment_it_does_not_fit() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    def(&mut after, "tgSixOne", c("Nat"), Expr::nat_lit(1));
    let delta = after.local_fact_delta_since(&before).expect("delta");
    let mut twice = after.clone();
    assert!(matches!(
        twice.apply_local_fact_delta(&delta),
        Err(FactDeltaError::BaseMismatch(_))
    ));
}

/// NEGATIVE CONTROL: the comparison a replay is checked with sees a changed
/// declaration body.
#[test]
fn a_changed_body_is_a_difference() {
    let base = Environment::with_prelude();
    let mut one = base.clone();
    def(&mut one, "tgSixK", c("Nat"), Expr::nat_lit(1));
    let mut two = base.clone();
    def(&mut two, "tgSixK", c("Nat"), Expr::nat_lit(2));
    assert!(one.local_fact_difference(&two).is_some());
}

/// NEGATIVE CONTROL: what a delta cannot replay refuses at construction.
#[test]
fn a_kernel_theory_change_is_unrepresentable() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    after.set_kernel_theory(crate::env::KernelTheory::Lean);
    assert!(matches!(
        after.local_fact_delta_since(&before),
        Err(FactDeltaError::Unrepresentable(_))
    ));
}

#[test]
fn a_foreign_format_does_not_decode() {
    let env = Environment::with_prelude();
    let mut delta = env.local_fact_delta_since(&env.clone()).expect("delta");
    delta.format = "clean_kernel.local_fact_delta.v0".to_string();
    let bytes = delta.encode().expect("encode");
    assert!(EnvFactDelta::decode(&bytes).is_err());
}

/// A fact applied to an environment that has counted further (an unrelated
/// declaration added since the fact's base) moves the registration counters
/// FORWARD by the fact's own steps, never back to the producer's values.
#[test]
fn counters_move_forward_by_the_facts_steps() {
    let base = Environment::with_prelude();
    let mut produced = base.clone();
    def(&mut produced, "tgSixFact", c("Nat"), Expr::nat_lit(3));
    let delta = produced.local_fact_delta_since(&base).expect("delta");

    let mut target = base.clone();
    def(&mut target, "tgSixUnrelated", c("Nat"), Expr::nat_lit(4));
    let before = target.generation();
    target
        .apply_local_fact_delta(&delta)
        .expect("an unrelated addition does not block the fact");
    assert_eq!(
        target.generation(),
        before + (produced.generation() - base.generation())
    );
    assert!(target.generation() > produced.generation());
    assert!(target.get_const(&n("tgSixFact")).is_some());
    assert!(target.get_const(&n("tgSixUnrelated")).is_some());
}

/// NEGATIVE CONTROL: an entry the fact CHANGES must hold the producer's
/// before value here; a different value refuses instead of being overwritten.
#[test]
fn a_changed_entry_with_a_different_before_value_refuses() {
    let base = Environment::with_prelude();
    let mut one = base.clone();
    one.options
        .insert("tgSix.option".to_string(), Some("one".to_string()));
    let mut produced = one.clone();
    produced
        .options
        .insert("tgSix.option".to_string(), Some("two".to_string()));
    let delta = produced.local_fact_delta_since(&one).expect("delta");
    let mut other = base.clone();
    other
        .options
        .insert("tgSix.option".to_string(), Some("other".to_string()));
    assert!(matches!(
        other.apply_local_fact_delta(&delta),
        Err(FactDeltaError::BaseMismatch(_))
    ));
}

/// The dependency digest sees a changed body under the same name, and the
/// references name what a declaration's kernel check reads.
#[test]
fn the_kernel_record_digest_sees_a_body_and_references_name_the_callees() {
    let base = Environment::with_prelude();
    let mut one = base.clone();
    def(&mut one, "tgSixBody", c("Nat"), Expr::nat_lit(1));
    def(&mut one, "tgSixUser", c("Nat"), c("tgSixBody"));
    let mut two = base.clone();
    def(&mut two, "tgSixBody", c("Nat"), Expr::nat_lit(2));
    let body = n("tgSixBody");
    assert!(one.kernel_record_digest(&body).is_some());
    assert_ne!(
        one.kernel_record_digest(&body),
        two.kernel_record_digest(&body)
    );
    assert_eq!(one.kernel_record_digest(&n("tgSixAbsent")), None);
    assert!(one.kernel_references(&n("tgSixUser")).contains(&body));
    assert!(one.kernel_references(&n("tgSixUser")).contains(&n("Nat")));
}

/// A test-only typed extension state that exports nothing.
#[derive(Clone, Default)]
struct SessionNote(Vec<Name>);

#[derive(Clone)]
struct SessionNoteEntry(Name);

impl crate::env::persistent_ext::PersistentExtEntry for SessionNoteEntry {
    fn to_env_entry(&self) -> crate::env::EnvExtensionEntry {
        crate::env::EnvExtensionEntry {
            name: self.0.clone(),
            data: crate::env::EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &crate::env::EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl crate::env::persistent_ext::PersistentExtState for SessionNote {
    type Entry = SessionNoteEntry;

    fn add_entry(&mut self, entry: &SessionNoteEntry) {
        self.0.push(entry.0.clone());
    }

    fn export_entries(&self) -> Vec<crate::env::EnvExtensionEntry> {
        Vec::new()
    }
}

/// TG6 review: the `@[implemented_by]` ORDER record exports nothing, yet
/// every compiled lane reads it, so a delta that dropped it would hand those
/// lanes an environment whose refusal had vanished. It refuses instead.
#[test]
fn an_implemented_by_order_record_is_unrepresentable() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    after.record_compiled_before(vec![(
        n("tgSixCaller"),
        crate::env::CompiledBefore {
            rebound: n("tgSixSlow"),
            via: n("tgSixSlow"),
        },
    )]);
    assert!(after.compiled_before_record().is_some());
    let refused = after.local_fact_delta_since(&before);
    assert!(
        matches!(&refused, Err(FactDeltaError::Unrepresentable(why))
            if why.contains("Clean.compiler.implementedByOrder")),
        "{refused:?}"
    );
}

/// An elaboration-private state is left out (a later elaboration rebuilds
/// it); any OTHER unexported state refuses (NEGATIVE CONTROL: the same write
/// under a name not on the list).
#[test]
fn only_elaboration_private_extension_writes_are_left_out() {
    use crate::env::persistent_ext::register_persistent_ext;
    let private = register_persistent_ext::<SessionNote>(n("Clean.olean.scopedInstances"));
    let other = register_persistent_ext::<SessionNote>(n("CleanKernelTest.factDeltaSessionNote"));
    let before = Environment::with_prelude();
    let mut after = before.clone();
    after.add_ext_entry::<SessionNote>(private, &SessionNoteEntry(n("tgSix")));
    after
        .local_fact_delta_since(&before)
        .expect("an elaboration-private write is left out");
    after.add_ext_entry::<SessionNote>(other, &SessionNoteEntry(n("tgSix")));
    let refused = after.local_fact_delta_since(&before);
    assert!(
        matches!(&refused, Err(FactDeltaError::Unrepresentable(why))
            if why.contains("factDeltaSessionNote")),
        "{refused:?}"
    );
}

/// The typed components keyed by a declaration name that the elaboration
/// record does NOT digest, each with the reason.
const OUTSIDE_THE_ELABORATION_RECORD: &[(&str, &str)] = &[
    ("constants", "a kernel record (`kernel_record_digest`)"),
    ("inductives", "a kernel record"),
    ("constructors", "a kernel record"),
    ("recursors", "a kernel record"),
    ("quotients", "a kernel record"),
    (
        "constant_origins",
        "Trust digests the origin beside the record",
    ),
    (
        "persistent_extensions",
        "keyed by extension, not by declaration",
    ),
    (
        "options",
        "keyed by option name: session state, never per declaration",
    ),
    ("aesop_rule_sets", "keyed by rule set: session state"),
    ("aesop_target_index", "keyed by index head: session state"),
    ("aesop_hyps_index", "keyed by index head: session state"),
    ("aesop_rules", "one list for the session"),
    ("aesop_unindexed_rules", "one list for the session"),
    ("grind_lemmas", "one list for the session"),
    (
        "instance_seqs",
        "positions every replay relocates: compared, never counted",
    ),
    (
        "extension_states",
        "not a table: a write outside the private list refuses the delta",
    ),
];

/// The per-name tables a delta carries as extension states
/// ([`DELTA_CARRIED_EXTENSIONS`]), by the name the elaboration record digests
/// them under.
const CARRIED_EXTENSION_TABLES: &[&str] =
    &["value_forall_binder_names", "csimp_compiled", "attr_tags"];

#[test]
fn every_carried_extension_is_digested_per_name() {
    use crate::env::content_digest::ELABORATION_RECORD_TABLES;
    assert_eq!(
        DELTA_CARRIED_EXTENSIONS,
        &[
            super::super::value_binder_names::VALUE_BINDER_NAMES_EXTENSION,
            super::super::csimp::CSIMP_SOURCE_EXTENSION,
            super::super::ext_attr::ATTR_EXT_NAME,
        ]
    );
    assert_eq!(
        DELTA_CARRIED_EXTENSIONS.len(),
        CARRIED_EXTENSION_TABLES.len()
    );
    for table in CARRIED_EXTENSION_TABLES {
        assert!(ELABORATION_RECORD_TABLES.contains(table), "`{table}`");
    }
}

/// Every typed component is either digested per name by
/// `elaboration_record_digest` or listed above with a reason, so a table
/// added to the environment cannot silently escape a fact's dependencies.
#[test]
fn every_typed_component_is_in_the_elaboration_record_or_excluded() {
    use crate::env::content_digest::ELABORATION_RECORD_TABLES;
    for field in DELTA_TYPED_FIELDS {
        let digested = ELABORATION_RECORD_TABLES.contains(field);
        let excluded = OUTSIDE_THE_ELABORATION_RECORD
            .iter()
            .any(|(name, _)| name == field);
        assert!(
            digested != excluded,
            "`{field}` must be either digested per name or excluded with a reason (digested: \
             {digested}, excluded: {excluded})"
        );
    }
    for table in ELABORATION_RECORD_TABLES {
        assert!(
            DELTA_TYPED_FIELDS.contains(table)
                || TRANSIENT_FIELDS.contains(table)
                || CARRIED_EXTENSION_TABLES.contains(table),
            "`{table}` is not an Environment table"
        );
    }
}

/// The session tables are exactly the excluded ones that are not kernel
/// records, origins or extension states: an admission window may change
/// none of them.
#[test]
fn a_session_table_change_is_named_and_a_per_name_one_is_not() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    def(&mut after, "tgSixAdmitted", c("Nat"), Expr::nat_lit(1));
    let delta = after.local_fact_delta_since(&before).expect("delta");
    assert_eq!(delta.changed_session_table(), None);
    after.set_option("tgSix.option".to_string(), Some("1".to_string()));
    let delta = after.local_fact_delta_since(&before).expect("delta");
    assert_eq!(delta.changed_session_table(), Some("options"));
}

/// TG6 review: two same-typed fields swapped or renamed change only the field
/// table, which no kernel record carries; the elaboration record sees it.
#[test]
fn the_elaboration_record_sees_a_field_table_the_kernel_record_does_not() {
    let pair = n("TgSixPair");
    let nat = || c("Nat");
    let structure = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: n("TgSixPair.mk"),
                type_: Expr::arrow(nat(), Expr::arrow(nat(), c("TgSixPair"))),
            }],
        }],
    };
    let mut base = Environment::with_prelude();
    base.add_inductive(structure).expect("inductive");
    let fields = |names: &[&str]| {
        let mut env = base.clone();
        env.register_structure_fields(pair.clone(), names.iter().map(|f| n(f)).collect())
            .expect("fields");
        env
    };
    let (one, swapped, renamed) = (
        fields(&["width", "height"]),
        fields(&["height", "width"]),
        fields(&["w", "height"]),
    );
    assert_eq!(
        one.kernel_record_digest(&pair),
        swapped.kernel_record_digest(&pair)
    );
    let record = one.elaboration_record_digest(&pair);
    assert!(record.is_some());
    assert_ne!(record, swapped.elaboration_record_digest(&pair));
    assert_ne!(record, renamed.elaboration_record_digest(&pair));
    assert_eq!(
        record,
        fields(&["width", "height"]).elaboration_record_digest(&pair)
    );
    assert_eq!(base.elaboration_record_digest(&n("tgSixAbsent")), None);
}

/// A csimp rule over two fresh `Nat` constants, registered as a global rule.
fn csimp_rule(env: &mut Environment, tag: &str) {
    let (from, to, theorem) = (format!("{tag}From"), format!("{tag}To"), format!("{tag}Eq"));
    def(env, &from, c("Nat"), Expr::nat_lit(1));
    def(env, &to, c("Nat"), Expr::nat_lit(1));
    env.add_decl(Declaration::Axiom {
        name: n(&theorem),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(n("Eq"), vec![crate::Level::succ(crate::Level::zero())]),
            [c("Nat"), c(&from), c(&to)],
        ),
    })
    .expect("the equality is well-typed");
    assert!(crate::env::csimp::register(env, &n(&theorem)));
}

/// Clean 21233e7751 records a csimp compilation point for every elaborated
/// declaration, which changes the csimp state's exported snapshot; a delta
/// that refused it stored no fact for any island (Trust TG6). The point is
/// carried and replays exactly, in a fresh copy of the environment the key
/// names; a second record of the same name changes nothing.
#[test]
fn a_csimp_compilation_point_is_carried_and_replays_exactly() {
    use crate::env::csimp;
    let mut before = Environment::with_prelude();
    csimp_rule(&mut before, "tgSixSeen");
    let mut after = before.clone();
    def(&mut after, "tgSixCompiled", c("Nat"), Expr::nat_lit(1));
    csimp::record_compiled(&mut after, [n("tgSixCompiled")]);
    csimp::record_compiled(&mut after, [n("tgSixCompiled")]);
    let delta = after.local_fact_delta_since(&before).expect("carried");
    assert_eq!(delta.csimp_compiled.len(), 1);
    assert_eq!(
        delta.csimp_compiled[0].1.len(),
        1,
        "the rule visible at the point"
    );
    let decoded = EnvFactDelta::decode(&delta.encode().expect("encodes")).expect("decodes");
    let mut replayed = before.clone();
    replayed.apply_local_fact_delta(&decoded).expect("fits");
    assert_eq!(replayed.local_fact_difference(&after), None);
    assert_eq!(
        csimp::recorded_body_rules(&replayed, &n("tgSixCompiled")),
        csimp::recorded_body_rules(&after, &n("tgSixCompiled")),
    );
    assert!(csimp::recorded_body_rules(&before, &n("tgSixCompiled")).is_none());
    assert_ne!(
        before.elaboration_record_digest(&n("tgSixCompiled")),
        replayed.elaboration_record_digest(&n("tgSixCompiled")),
        "the record digests the compilation point"
    );
}

/// NEGATIVE CONTROL: every csimp change other than a compilation point still
/// refuses, alone or beside one.
#[test]
fn a_csimp_rule_event_is_still_unrepresentable() {
    use crate::env::csimp;
    let before = Environment::with_prelude();
    let refused = |after: &Environment| {
        let refused = after.local_fact_delta_since(&before);
        assert!(
            matches!(&refused, Err(FactDeltaError::Unrepresentable(why))
                if why.contains("more than compilation points")),
            "{refused:?}"
        );
    };
    let mut global = before.clone();
    csimp_rule(&mut global, "tgSixGlobal");
    refused(&global);
    csimp::record_compiled(&mut global, [n("tgSixGlobalFrom")]);
    refused(&global);
    let mut local = before.clone();
    csimp_rule(&mut local, "tgSixLocal");
    let base = local.clone();
    let token = csimp::register_local(&mut local, &n("tgSixLocalEq")).expect("a rule");
    let delta = local.local_fact_delta_since(&base);
    assert!(
        matches!(&delta, Err(FactDeltaError::Unrepresentable(_))),
        "{delta:?}"
    );
    csimp::retire_local(&mut local, token);
    let delta = local.local_fact_delta_since(&base);
    assert!(
        matches!(&delta, Err(FactDeltaError::Unrepresentable(_))),
        "{delta:?}"
    );
    let mut scoped = before.clone();
    csimp_rule(&mut scoped, "tgSixScoped");
    let base = scoped.clone();
    assert!(csimp::define_scoped(
        &mut scoped,
        &n("TgSix"),
        &n("tgSixScopedEq")
    ));
    let delta = scoped.local_fact_delta_since(&base);
    assert!(
        matches!(&delta, Err(FactDeltaError::Unrepresentable(_))),
        "{delta:?}"
    );
}

/// A carried compilation point applies only where it resolves to the rules
/// the producing elaboration saw, and only once: an environment with another
/// visible rule, or with the point already recorded, is not the one the
/// fact's key names, and is left unchanged.
#[test]
fn a_csimp_compilation_point_refuses_a_different_base() {
    use crate::env::csimp;
    let before = Environment::with_prelude();
    let mut after = before.clone();
    def(&mut after, "tgSixCompiled", c("Nat"), Expr::nat_lit(1));
    csimp::record_compiled(&mut after, [n("tgSixCompiled")]);
    let delta = after.local_fact_delta_since(&before).expect("carried");

    let mut other_rules = before.clone();
    csimp_rule(&mut other_rules, "tgSixOther");
    let untouched = other_rules.clone();
    let refused = other_rules.apply_local_fact_delta(&delta);
    assert!(
        matches!(&refused, Err(FactDeltaError::BaseMismatch(why)) if why.contains("csimp")),
        "{refused:?}"
    );
    assert_eq!(other_rules.local_fact_difference(&untouched), None);

    let mut already = before.clone();
    csimp::record_compiled(&mut already, [n("tgSixCompiled")]);
    let refused = already.apply_local_fact_delta(&delta);
    assert!(
        matches!(&refused, Err(FactDeltaError::BaseMismatch(why))
            if why.contains("already has a csimp compilation point")),
        "{refused:?}"
    );
}

fn tag(env: &mut Environment, decl: &str, attr: &str) {
    use crate::env::{attr_ext_idx, AttrExtEntry, AttrExtState};
    env.add_ext_entry::<AttrExtState>(
        attr_ext_idx(),
        &AttrExtEntry {
            decl_name: n(decl),
            attr_name: n(attr),
            priority: 0,
        },
    );
}

/// Clean 493d4c3aac tags a theorem proved by bare `rfl` with `defeq` and
/// `backward_defeq` in the exported attribute extension, which refused the
/// delta of every such island. Appended registrations are carried, in an
/// order that rebuilds both indexes, whatever order the declarations were
/// tagged in, and the record digests them per name.
#[test]
fn appended_attribute_tags_are_carried_and_replay_exactly() {
    use crate::env::ext_attr;
    let mut before = Environment::with_prelude();
    def(&mut before, "tgSixOld", c("Nat"), Expr::nat_lit(1));
    tag(&mut before, "tgSixOld", "backward_defeq");
    let mut after = before.clone();
    for name in ["tgSixZ", "tgSixA", "tgSixM"] {
        def(&mut after, name, c("Nat"), Expr::nat_lit(1));
        tag(&mut after, name, "defeq");
        tag(&mut after, name, "backward_defeq");
    }
    tag(&mut after, "tgSixOld", "defeq");
    let delta = after.local_fact_delta_since(&before).expect("carried");
    assert_eq!(delta.attr_tags.len(), 7);
    let decoded = EnvFactDelta::decode(&delta.encode().expect("encodes")).expect("decodes");
    let mut replayed = before.clone();
    replayed.apply_local_fact_delta(&decoded).expect("fits");
    assert_eq!(replayed.local_fact_difference(&after), None);
    assert!(ext_attr::same_registrations(&replayed, &after));
    assert_eq!(
        replayed.export_extension_states(),
        after.export_extension_states(),
        "equal states export equally, however they were built"
    );
    assert!(!ext_attr::same_registrations(&replayed, &before));
    assert_ne!(
        before.elaboration_record_digest(&n("tgSixOld")),
        after.elaboration_record_digest(&n("tgSixOld")),
        "the record digests a declaration's tags"
    );
    // A base whose touched declaration holds other tags is refused, unchanged.
    let mut other = before.clone();
    tag(&mut other, "tgSixOld", "simp");
    let untouched = other.clone();
    let refused = other.apply_local_fact_delta(&decoded);
    assert!(
        matches!(&refused, Err(FactDeltaError::BaseMismatch(why)) if why.contains("tgSixOld")),
        "{refused:?}"
    );
    assert_eq!(other.local_fact_difference(&untouched), None);
}

/// NEGATIVE CONTROL: `local_fact_difference` still sees an attribute tag one
/// side lacks, so a hit that dropped one disagrees with real elaboration.
#[test]
fn a_missing_attribute_tag_is_a_difference() {
    let before = Environment::with_prelude();
    let mut after = before.clone();
    def(&mut after, "tgSixTagged", c("Nat"), Expr::nat_lit(1));
    let untagged = after.clone();
    tag(&mut after, "tgSixTagged", "defeq");
    let difference = untagged.local_fact_difference(&after);
    assert!(
        difference
            .as_deref()
            .is_some_and(|why| why.contains("attrExtension")),
        "{difference:?}"
    );
}

#[test]
fn transient_field_inventory_rejects_missing_and_extra_skipped_rows() {
    let fields = crate::env::ENVIRONMENT_FIELD_ATTRIBUTES;
    assert!(transient_field_census_matches(fields));
    let omitted: Vec<_> = fields
        .iter()
        .copied()
        .filter(|(name, _)| *name != "lazy_source")
        .collect();
    assert_eq!(omitted.len() + 1, fields.len());
    assert!(!transient_field_census_matches(&omitted));
    let mut extra = fields.to_vec();
    extra.push(("unhandled_transient_control", &["serde(skip)"]));
    assert!(!transient_field_census_matches(&extra));
}
