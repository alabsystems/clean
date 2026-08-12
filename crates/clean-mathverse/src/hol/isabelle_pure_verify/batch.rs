// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! In-memory batch closure-replay driver: `import_proven_theorems` plus the
//! shared per-theorem `verify_one` verifier.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::env::is_foundational_axiom;
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, Level};

use super::super::isabelle_bridge::discharge_value;
use super::super::isabelle_pure::IsaProvenTheorem;
use super::super::isabelle_pure_translate::{
    bnf_combinator_definition_decls, bnf_opaque_combinator_definition_decls,
    concludes_registered_class_membership, connective_definition_decls, eq_tower_applicable,
    extremum_definition_decls, fun_combinator_definition_decls, fun_comp_definition_decl,
    fun_id_definition_decl, hol_if_definition_decl, hol_the_definition_decl,
    nonempty_erase_applicable, pointfree_definition_decls, pure_meta_definition_decls,
    register_datatype_inductives, root_lane_applicable, thm_spine_root_applicable,
    translate_theorem_with_meta_lane, wo_the_definition_decls, ClassMembership, ClassRegistry,
    Closure, ClosureEntry, InstanceEmbed, InstanceOpRegistry, ListFnRegistry, MethodEmbed,
    MethodRegistry, PolyInstRegistry, RootLane, TranslateError, TranslatedMeta,
};
use super::super::opentheory_shard::lower_kernel_expr;
use super::register::{
    register_classes_superclass_first, register_instance_ops, register_list_fns, register_methods,
    register_poly_insts, topological_order,
};
use super::{
    ledger_enabled, translate_error_tag, LedgerEntry, PureVerifiedImport, WrittenConstant,
    LEDGER_AXIOM_PREFIX,
};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// Diagnostic-only master mode-attempt instrumentation (P2 step-2 lever
/// baseline). [`MODE_ATTEMPTS`] counts the total kernel `add_decl` mode attempts
/// summed over every verified line; [`MODE_LINES`] counts the lines that reached
/// the escalation loop. Their ratio is the average per-line mode-attempt count —
/// the cost the step-2 worker pre-check aims to cut from ~5–14 to ~1–2. Both are
/// [`Ordering::Relaxed`] increments on the single master thread (cost dwarfed by a
/// kernel `add_decl`); they are pure telemetry and NEVER gate a verdict. A driver
/// prints the ratio only when `ISA_MODE_ATTEMPT_STATS` is set.
pub(super) static MODE_ATTEMPTS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Lines that reached the escalation loop — see [`MODE_ATTEMPTS`].
pub(super) static MODE_LINES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// `(total_mode_attempts, lines)` snapshot of the master mode-attempt counters.
pub(super) fn mode_attempt_stats() -> (u64, u64) {
    use std::sync::atomic::Ordering::Relaxed;
    (MODE_ATTEMPTS.load(Relaxed), MODE_LINES.load(Relaxed))
}

// ---------------------------------------------------------------------------
// Cross-lane KERNEL BRIDGE discharge (opt-in, `ISA_BRIDGE_DISCHARGE=<manifest>`).
//
// A blocked Isabelle line whose embedded statement bridges — via a foundational
// connective iso — to a NAMED Mathlib-KV witness already present in the
// accumulating environment is discharged as `KernelBridged` (never
// `KernelVerified`). The manifest is the curated Isabelle↔Mathlib alias table:
// it maps an Isabelle theorem name (or serial) to the Mathlib witness constant
// name whose kernel-checked value the bridge composes against. Default OFF ⇒
// byte-identical to the historical two-tier lane.
// ---------------------------------------------------------------------------

/// The Isabelle→Mathlib witness manifest driving [`try_bridge_discharge`]. Keys
/// resolve a blocked Isabelle line to the Mathlib-KV *witness constant name* the
/// bridge discharges against.
#[derive(Debug, Default, serde::Deserialize)]
pub(crate) struct BridgeManifest {
    /// Isabelle theorem name → Mathlib witness constant name.
    #[serde(default)]
    by_name: BTreeMap<String, String>,
    /// Isabelle proof-term serial (as a decimal string) → Mathlib witness
    /// constant name. Consulted only when [`Self::by_name`] misses.
    #[serde(default)]
    by_serial: BTreeMap<String, String>,
}

impl BridgeManifest {
    /// Load a manifest from a JSON file. Returns `None` on any read/parse error
    /// (the bridge simply stays inert — an unreadable manifest never blocks or
    /// mis-verifies a line).
    fn load(path: &Path) -> Option<Self> {
        let bytes = std::fs::read(path).ok()?;
        serde_json::from_slice(&bytes).ok()
    }

    /// The Mathlib witness constant name for `thm`, if the manifest names one
    /// (by theorem name first, then by serial).
    fn witness_for(&self, thm: &IsaProvenTheorem) -> Option<&str> {
        if let Some(w) = self.by_name.get(&thm.name) {
            return Some(w.as_str());
        }
        if thm.serial != 0 {
            if let Some(w) = self.by_serial.get(&thm.serial.to_string()) {
                return Some(w.as_str());
            }
        }
        None
    }

    /// Every distinct Mathlib witness constant name the manifest can resolve to —
    /// the set the witness sourcer ([`super::bridge_witness::load_bridge_witnesses`])
    /// tries to load (type + value) into the replay env.
    fn witness_names(&self) -> BTreeSet<String> {
        self.by_name
            .values()
            .chain(self.by_serial.values())
            .cloned()
            .collect()
    }
}

/// The process-wide bridge manifest, loaded once from `ISA_BRIDGE_DISCHARGE`.
/// `None` when the env var is unset (the default) OR the file cannot be
/// read/parsed — in every such case the bridge lane is inert.
static BRIDGE_MANIFEST: std::sync::OnceLock<Option<BridgeManifest>> = std::sync::OnceLock::new();

/// The loaded bridge manifest, or `None` when the bridge lane is disabled/inert.
/// Read once and cached; subsequent calls are a pointer load.
fn bridge_manifest() -> Option<&'static BridgeManifest> {
    BRIDGE_MANIFEST
        .get_or_init(|| {
            let path = std::env::var_os("ISA_BRIDGE_DISCHARGE")?;
            BridgeManifest::load(Path::new(&path))
        })
        .as_ref()
}

/// The directory of Mathlib-KV `.mathverse` shards the witness sourcer reads
/// (`ISA_BRIDGE_WITNESS_SHARDS`). `None` when unset — the witness-loading step is
/// then skipped entirely, so a bridge run without it is byte-identical to the
/// pre-witness lane (the discharge simply finds no resident witness and declines,
/// exactly as before this brick). Loaded once and cached.
static BRIDGE_WITNESS_SHARDS: std::sync::OnceLock<Option<PathBuf>> = std::sync::OnceLock::new();

/// The witness-shard directory, or `None` when witness sourcing is disabled.
fn bridge_witness_shards() -> Option<&'static Path> {
    BRIDGE_WITNESS_SHARDS
        .get_or_init(|| {
            std::env::var_os("ISA_BRIDGE_WITNESS_SHARDS")
                .map(PathBuf::from)
                .filter(|p| p.is_dir())
        })
        .as_deref()
}

/// Verify a batch of Pure-proof theorems via closure replay and write the
/// kernel-verified ones to `writer` as `KernelVerified`.
#[must_use]
pub fn import_proven_theorems(
    theorems: &[IsaProvenTheorem],
    writer: &mut ShardWriter,
) -> PureVerifiedImport {
    // Install THIS run's verify config (parsed once from env) for the whole
    // batch, so translate/verify reads resolve against an explicit per-run value
    // rather than a process-global first-wins `OnceLock`. See
    // [`super::super::isabelle_verify_config`].
    let _cfg = crate::hol::isabelle_verify_config::VerifyConfig::from_env().install();
    let mut out = PureVerifiedImport::default();
    // One accumulating environment: later PThm references resolve against the
    // clean theorems added by earlier iterations (the closure replay).
    let mut env = Environment::with_prelude();
    // Register the monomorphic HOL connectives (True/False/Not/conj/disj) as
    // clean `Definition`s up front, in dependency order. `embed_term` emits each
    // connective occurrence as that definition's const (`isabelle.def.HOL.conj`,
    // …) rather than inlining its encoding, so abstract and concrete occurrences
    // share one defeq-unfolding head symbol — fixing the conjI/disjI/notI
    // fold/unfold asymmetry. A registration failure here is non-fatal; the
    // connective `_def` proofs simply fail to resolve their const and are
    // honestly rejected.
    for decl in connective_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register the point-free HOL logical constants (`HOL.Uniq`/`Ex1`/`Let`/
    // `induct_forall`/`induct_equal`/`NO_MATCH`) as faithful polymorphic
    // `Definition`s (bodies built from the `∀`/`→`/`@Eq`/`∃`/`∧`/`True` encodings —
    // pure λ, no axiom content). A single shared def-const head makes each
    // constant's point-free `…_def_raw` axiom verify reflexively and every
    // occurrence δ-consistent. Registered AFTER the connective def-consts (their
    // `True`/`conj` dependencies), so the δ-unfolding chain closes. Non-fatal.
    for decl in pointfree_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register HOL's if-then-else `HOL.If` as a faithful polymorphic `Definition`
    // (`ite` over a classical `Decidable` instance; foundational closure). Every
    // `HOL.If` occurrence then unfolds to this one head, so the `…_def` bodies of
    // the recursive list/option functions that branch with `if` close and verify
    // reflexively. Non-fatal: an `if`-using `_def` simply stays unmapped on failure.
    let _ = env.add_decl(hol_if_definition_decl());
    // Register HOL's definite description `HOL.The` (`THE x. P x`) as a faithful
    // polymorphic `Definition` — clean's classical epsilon threaded with an explicit
    // `Nonempty α` (foundational `Classical.choice` closure). Every routed `HOL.The`
    // occurrence unfolds to this one head, so `the_eq_trivial` and the `The`-defined
    // `Least`/`Greatest` characterisations become provable. Non-fatal: a `The`-using
    // node simply stays unmapped on failure.
    let _ = env.add_decl(hol_the_definition_decl());
    // Register HOL's `The`-defined order extrema `Orderings.ord.Least` /
    // `Orderings.order.Greatest` as faithful polymorphic `Definition`s (each
    // δ-unfolding to `THE x. P x ∧ (∀y. P y → x ≼ y)`), so their defining axioms
    // (`Least_def`/`Greatest_def`) verify reflexively against the epsilon `The`.
    // Registered AFTER `isabelle.def.HOL.The`/`isabelle.def.HOL.conj` (their bodies'
    // dependencies). Non-fatal.
    for decl in extremum_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register HOL's function composition `Fun.comp` (`λf g x. f (g x)`, three type
    // vars) and identity `Fun.id` (`λx. x`) as faithful polymorphic `Definition`s.
    // `comp`/`id` are PERVASIVE across HOL — `foldr_def` and countless list/function
    // lemmas mention `comp f g`/`id` on a RHS or as a dep. A single shared
    // defeq-unfolding head makes `comp_def`/`id_def` reflexive and every consumer
    // δ-consistent. Pure λ (no axiom content) → consumers stay foundational.
    // Non-fatal: a `comp`/`id`-using node simply stays unmapped on failure.
    let _ = env.add_decl(fun_comp_definition_decl());
    let _ = env.add_decl(fun_id_definition_decl());
    // Register the `Fun.*` combinators (`fcomp`/`inj_on`/`bij_betw`/`fun_upd`/
    // `monotone_on`) as faithful polymorphic `Definition`s — bodies built from the
    // shared `Ball`/`image`/`If`/`conj`/`@Eq` encodings, so each constant's
    // `…_def`/`…_def_raw` axiom verifies reflexively and every occurrence is
    // δ-consistent. Registered AFTER the connective + `HOL.If` def-consts (their
    // bodies' dependencies), in internal dependency order (`inj_on` before
    // `bij_betw`). Non-fatal.
    for decl in fun_combinator_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register the BNF (Bounded Natural Functor) datatype-package combinators
    // (`convol`/`rel_fun`/`rel_set`/`eq_onp`/`vimage2p`/`Grp`/`Gr`/`csquare`/
    // `id_bnf`) as faithful polymorphic `Definition`s — bodies built from the same
    // `∀`/`Ball`/`Bex`/`∃`/`∧`/`@Eq`/`Prod.mk` encodings, so each constant's
    // `…_def`/`…_def_raw` axiom verifies reflexively and every occurrence is
    // δ-consistent. Registered AFTER the connective def-consts. Non-fatal.
    for decl in bnf_combinator_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register the BNF leaf combinators whose bodies reference OPAQUE HOL
    // constants (`cinfinite`/`cfinite`/`pick_middlep`/`fstOp`/`sndOp`) as faithful
    // polymorphic `Definition`s with the opaque constants (`Field`/`finite`/`Eps`/
    // prod-selectors) abstracted as leading value binders and supplied at each
    // use-site by re-embedding the actual HOL constant. Registered AFTER the closed
    // BNF combinators (`pick_middlep` precedes `fstOp`/`sndOp`, which reference its
    // def-const). The two-`Field` cardinal `+`/`*`/`^`/`Csum` family is deferred
    // (see `connectives/bnf_cardinal.rs`). Non-fatal.
    for decl in bnf_opaque_combinator_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register the `wo_rel` `The`-threaded constants (`minim`/`supr`/`suc`) as
    // faithful polymorphic `Definition`s (`minim r A = THE b. isMinim r A b`; `supr`/
    // `suc` = `minim r (Above/AboveS r A)`). Registered AFTER `HOL.The`, `isMinim`
    // and the `Above`/`AboveS` opaque combinators their bodies depend on, in internal
    // dependency order (`minim` before `supr`/`suc`). Non-fatal.
    for decl in wo_the_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register Pure's judgement marker `Pure.term` as a faithful polymorphic
    // `Definition` (`λ_. ∀A. A → A`, the meta-truth its `_def` body denotes; no
    // axiom content). A single shared defeq-unfolding head makes `Pure.term_def`
    // reflexive and every `Pure.term` use-site δ-consistent (`Pure.sort_constraint`
    // is an erased sort constraint proved by a dedicated `propext` bridge, so it
    // needs no def-const). Non-fatal: a marker-using node stays unmapped on failure.
    for decl in pure_meta_definition_decls() {
        let _ = env.add_decl(decl);
    }
    // Register the HOL datatypes clean's prelude lacks (currently `Num.num`) as
    // faithful clean inductives, so their constructors/recursor map to real kernel
    // declarations (see `register_datatype_inductives`). `Nat` is already in the
    // prelude. Idempotent and non-fatal.
    register_datatype_inductives(&mut env);
    let mut closure: Closure = BTreeMap::new();
    // Structured type classes registered so far. When a `…c_class_def` axiom is
    // reached, its class predicate is registered as a clean polymorphic
    // `Definition` and recorded here (in dependency order — the topo sort puts a
    // class's def-axiom before any consumer of its `OFCLASS` premise). Threaded
    // into `translate_theorem` so consumer proofs see the real membership
    // proposition `c_class α ops` rather than the vacuous `True`.
    // Cross-lane KERNEL BRIDGE (opt-in): when a discharge manifest is loaded,
    // register the Mathlib inductive `Iff`/`Or`/`Exists` the connective bridge
    // composes with, so a bridged discharge term (built from `Iff.intro`/`Iff.mpr`/
    // `Or.rec`/`Exists.rec`) kernel-checks. GUARDED by `bridge_manifest()` being
    // `Some` so an OFF run (the default) never sees these extra decls ⇒
    // byte-identical. Non-fatal (a failed init just makes the bridge decline).
    if let Some(manifest) = bridge_manifest() {
        let _ = env.init_iff();
        let _ = env.init_or();
        let _ = env.init_exists();
        // WITNESS SOURCING (opt-in, `ISA_BRIDGE_WITNESS_SHARDS=<dir>`): load the
        // manifest-named Mathlib-KV witness constants (type + VALUE) from the
        // Mathlib import lane's `.mathverse` shards into this replay env, so the
        // phase-2 discharge finds them resident and the minted `Iff.mpr bridge
        // witness` proof closes foundationally. Gated behind the shards dir being
        // set (and a real directory), so a bridge run WITHOUT it is byte-identical
        // to the pre-witness lane. `init_classical` supplies the foundational
        // `Classical.em`/`Or`/`False` base the logical alias witnesses reference.
        if let Some(dir) = bridge_witness_shards() {
            let _ = env.init_classical();
            let stats = super::bridge_witness::load_bridge_witnesses(
                &mut env,
                dir,
                &manifest.witness_names(),
            );
            if std::env::var_os("ISA_BRIDGE_WITNESS_STATS").is_some() {
                eprintln!(
                    "isa-bridge-witness: requested={} present={} candidates={} loaded={} \
                     skipped(not_kv={} no_value={} polymorphic={} kernel_reject={} \
                     non_foundational={}) from {}",
                    stats.requested,
                    stats.present,
                    stats.candidates,
                    stats.loaded,
                    stats.skipped_not_kv,
                    stats.skipped_no_value,
                    stats.skipped_polymorphic,
                    stats.skipped_kernel_reject,
                    stats.skipped_non_foundational,
                    dir.display(),
                );
            }
        }
    }
    let mut class_registry: ClassRegistry = BTreeMap::new();
    // Register all structured type-class definitions up front in superclass-first
    // order. The `…c_class_def` axioms have no inter-dependencies the topo sort
    // can see (bare `PAxm` leaves), so registering them here — superclass before
    // subclass — guarantees each class's membership proposition contains the real
    // (recursively unfolded) superclass axioms rather than an erased `True`. The
    // def-axiom theorems themselves are then re-verified faithfully by
    // reflexivity in the main loop (their LHS `c_class α ops` δ-unfolds to the
    // registered body).
    register_classes_superclass_first(theorems, &mut env, &mut class_registry);
    // Overloaded class methods registered so far. Their `…_dict` dictionary axioms
    // appear only inside consumer proofs (never standalone), so we scan the whole
    // batch up front and register each method as a clean `Definition` before
    // translating consumers — making every overloaded-method occurrence unfold to
    // its dictionary form and the `…_dict` axiom verify reflexively.
    let mut method_registry: MethodRegistry = BTreeMap::new();
    register_methods(theorems, &mut env, &mut method_registry);
    // Monomorphic ground-type instance operations (the recursive-arithmetic
    // `…_nat_def`/`…_num_def` definitions) registered up front in serial (=
    // dependency) order, so every nat/num operation occurrence unfolds to its
    // def-const and the recursive `…_def` axiom verifies reflexively.
    let mut instance_op_registry: InstanceOpRegistry = BTreeMap::new();
    register_instance_ops(theorems, &mut env, &mut instance_op_registry);
    // Plain polymorphic list-datatype functions (`List.append`, `List.rev`,
    // `List.map`, …) registered up front in serial (= dependency) order, so every
    // list-function occurrence unfolds to its def-const and the recursive
    // `List.*_def` axiom verifies reflexively.
    let mut list_fn_registry: ListFnRegistry = BTreeMap::new();
    register_list_fns(
        theorems,
        &mut env,
        &mut list_fn_registry,
        &instance_op_registry,
        &method_registry,
    );
    // Polymorphic instance operations (`Int.power_int`, … — `'a`-generic constants
    // whose `_def` body uses overloaded class operations) registered up front in
    // serial (= dependency) order, so every occurrence unfolds to its def-const and
    // the `_def` axiom verifies reflexively.
    let mut poly_inst_registry: PolyInstRegistry = BTreeMap::new();
    register_poly_insts(
        theorems,
        &mut env,
        &mut poly_inst_registry,
        &method_registry,
        &instance_op_registry,
        &list_fn_registry,
    );

    // Opaque proof-value elision (env-gated, default off): after each theorem is
    // KernelVerified, drop its resident proof VALUE so peak memory stays bounded
    // on the full corpus. See [`super::elide_proofs_enabled`] and `verify_one`.
    let elide = super::elide_proofs_enabled();
    for &i in &topological_order(theorems) {
        let thm = &theorems[i];
        verify_one(
            thm,
            i,
            &mut env,
            &mut closure,
            &class_registry,
            &method_registry,
            &instance_op_registry,
            &list_fn_registry,
            &poly_inst_registry,
            writer,
            &mut out,
            elide,
        );
    }

    super::streaming::report_mode_attempt_stats();
    out
}

/// Verify a single Pure-proof theorem against the accumulating `env` / `closure`
/// / `class_registry` and, on success, write it to `writer` as `KernelVerified`
/// and record its closure entry.
///
/// `index` is the theorem's position in its source ordering — used only as a
/// fallback kernel-name component for the rare anonymous node whose serial is `0`
/// (real exported nodes carry a stable serial). The verification logic is
/// identical for the batch ([`import_proven_theorems`]) and streaming
/// ([`import_proven_theorems_streaming`]) drivers, so it lives here once.
///
/// When `elide` is `true`, the theorem's resident proof VALUE is dropped
/// (`env.forget_value`) immediately AFTER it has been stamped `KernelVerified`
/// (see [`super::elide_proofs_enabled`]). This keeps only the theorem's TYPE in
/// the accumulating environment, so later `PThm` references — which are opaque,
/// by-name-only (Isabelle never δ-unfolds a `PThm`/`ZConstp(ZThm)`) — still
/// resolve, while peak memory stays bounded on the multi-GB corpus.
///
/// SOUNDNESS: `elide` is applied ONLY after the kernel has already accepted
/// `value : type` and the foundational-axiom-closure check has passed — the
/// `KernelVerified` verdict is fully earned before the value is dropped. Dropping
/// it (and forcing the constant `Opaque`) only REMOVES a potential δ-reduction
/// rule, which can never turn an unequal pair equal or admit a false proof
/// (`Environment::forget_value` contract), so it is verdict-neutral for every
/// later theorem. The verdict-neutrality is additionally validated empirically
/// (identical KernelVerified set with elision on vs. off) by the scale-run gate.
///
/// Soundness is otherwise unchanged: nothing is stamped verified that the kernel
/// did not accept with a foundational-only axiom closure.
#[allow(clippy::too_many_arguments)]
/// The per-mode translation results for one theorem line, in the exact
/// escalation order [`escalation_modes`] returns — the worker-side half of the
/// parallel driver's split. Entry `i` is what `translate_theorem_with_meta`
/// returned for mode `i`. Pure data: safe to compute on any thread whose
/// closure view contains the theorem's (final) dependencies.
pub(super) type ModeTranslations = Vec<Result<(Declaration, TranslatedMeta), TranslateError>>;

/// The escalating translate-mode order for one theorem — extracted from
/// [`verify_one`] so the parallel driver's workers compute translations in
/// EXACTLY the order the master consumes them. See [`verify_one`]'s comments
/// for why the set and the `Real`-first reorder exist.
pub(super) fn escalation_modes(
    thm: &IsaProvenTheorem,
    class_registry: &ClassRegistry,
) -> Vec<(ClassMembership, MethodEmbed, InstanceEmbed, RootLane)> {
    let modes = [
        (
            ClassMembership::Erase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
            RootLane::Off,
        ),
        (
            ClassMembership::Real,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
            RootLane::Off,
        ),
        (
            ClassMembership::Real,
            MethodEmbed::DictUnfold,
            InstanceEmbed::Opaque,
            RootLane::Off,
        ),
        (
            ClassMembership::Real,
            MethodEmbed::DictUnfold,
            InstanceEmbed::Unfold,
            RootLane::Off,
        ),
        (
            ClassMembership::Erase,
            MethodEmbed::DictUnfold,
            InstanceEmbed::Unfold,
            RootLane::Off,
        ),
    ];
    let mut ordered: Vec<_> = if concludes_registered_class_membership(thm, class_registry) {
        let (real, erase): (Vec<_>, Vec<_>) = modes
            .into_iter()
            .partition(|(m, _, _, _)| *m == ClassMembership::Real);
        real.into_iter().chain(erase).collect()
    } else {
        modes.into_iter().collect()
    };
    // **Namespace-crossed root lane** trailing modes (binder-order round): the
    // lane re-solves a leading sort-`AbsP` chain over a generic reference
    // expectation-pinned, which can build a DIFFERENT (occasionally wrong)
    // value than the plain path — so it runs ONLY after every historical mode
    // above kernel-rejected (strictly additive: a node any historical mode
    // verified is stored exactly as before; the lane can only recover nodes
    // that were rejects). Appended only for structural candidates
    // ([`root_lane_applicable`]) so non-candidates pay no extra translation.
    let fallback_modes: Vec<_> = ordered
        .iter()
        .map(|&(m, me, ie, _)| (m, me, ie, RootLane::StmtFallback))
        .collect();
    if root_lane_applicable(&thm.proof) {
        ordered.extend([
            (
                ClassMembership::Real,
                MethodEmbed::Opaque,
                InstanceEmbed::Opaque,
                RootLane::On,
            ),
            (
                ClassMembership::Real,
                MethodEmbed::DictUnfold,
                InstanceEmbed::Opaque,
                RootLane::On,
            ),
            (
                ClassMembership::Real,
                MethodEmbed::DictUnfold,
                InstanceEmbed::Unfold,
                RootLane::On,
            ),
        ]);
    }
    // **Statement-fallback** trailing modes ([`RootLane::StmtFallback`]), one
    // per historical mode in the same order: skip the recorded proof and run
    // only the statement-level fallback arms — exactly what the historical
    // pipeline did when a recorded proof failed to translate. A node whose
    // reference to a newly-recovered dependency now translates-but-rejects
    // (at HEAD the unresolved reference errored and the fallback verified)
    // still lands on the identical fallback derivation, so recovering a new
    // dependency can only ADD verifications, never displace one.
    ordered.extend(fallback_modes);
    // **Recursive expectation-propagation** trailing modes
    // ([`RootLane::BidirEqTower`]) — appended LAST, after every historical mode
    // and the `On`/`StmtFallback` lanes. The lane translates the recorded proof
    // ROOT bidirectionally against the embedded statement so the expectation
    // propagates recursively down every interior `equal_elim`/`transitive`/
    // `symmetric`/`combination`/`reflexive`/`AbsP`/`Abst`/`AppT`/`AppP` node,
    // pinning each operand by its EXPECTED TYPE rather than the recorded
    // (crossed-namespace) instantiation table (the operand-desync the reject
    // census decoded). Running last keeps it strictly additive: a node any
    // earlier mode verified is stored exactly as before; the lane only recovers
    // former rejects. Appended only for structural candidates
    // ([`eq_tower_applicable`]) so non-candidates pay no extra translation. The
    // membership/dict/inst embeddings are escalated exactly like the other lanes
    // (a tower whose operands mention a registered method/instance needs the
    // unfold embedding to embed both sides consistently).
    // The `thm_spine_root_applicable` disjunct (bidir stage 2) extends the same
    // trailing lane to the non-equational Thm-spine / proof-redex roots under
    // leading premises (the discharge-chain twins): the routing in
    // [`translate_theorem`](super::super::isabelle_pure_translate) sends those
    // through [`Ctx::translate_proof_expecting`] on the statement instead of the
    // Isabelle-level eq-tower channel. Same strictly-additive, kernel-re-checked
    // discipline — appended only where the lane could fire.
    if eq_tower_applicable(&thm.proof) || thm_spine_root_applicable(&thm.proof) {
        ordered.extend([
            (
                ClassMembership::Real,
                MethodEmbed::Opaque,
                InstanceEmbed::Opaque,
                RootLane::BidirEqTower,
            ),
            (
                ClassMembership::Real,
                MethodEmbed::DictUnfold,
                InstanceEmbed::Opaque,
                RootLane::BidirEqTower,
            ),
            (
                ClassMembership::Real,
                MethodEmbed::DictUnfold,
                InstanceEmbed::Unfold,
                RootLane::BidirEqTower,
            ),
            (
                ClassMembership::Erase,
                MethodEmbed::Opaque,
                InstanceEmbed::Opaque,
                RootLane::BidirEqTower,
            ),
        ]);
    }
    // **NonemptyErase** trailing mode (the faithfulness-restoring erasure) — appended
    // LAST, strictly after every historical mode and every other trailing lane
    // kernel-rejected. It re-spells the leading `OFCLASS` sort premises as
    // `Nonempty α` instead of the vacuous `True`, which supplies the quantifier
    // witness `Classical.choice` needs for the vacuous-`∀`/`∃` and `∧`-miniscoping
    // simp leaves of the conjunction bundles (`simp_thms`/`all_simps`) — leaves that
    // are false-as-embedded under `True`-erasure over a possibly-empty Clean sort.
    // Strictly additive: a line any earlier mode verified is stored (byte-identical)
    // as before; this mode changes the stored statement (the premise becomes
    // `Nonempty α`) ONLY for lines no historical mode accepted, so no previously
    // stored statement is disturbed. Gated on the theorem carrying an `OFCLASS`
    // premise and concluding EITHER a `Pure.conjunction` bundle OR a single
    // quantifier simp equation (`(∀x. …) = …` / `(∃x. …) = …`, routed through
    // [`prove_nonempty_single_leaf`]), so non-candidates pay no extra translation.
    // The kernel re-checks the assembled proof against the `Nonempty`-spelled
    // statement, so a wrong witness is rejected — never miscounted.
    if nonempty_erase_applicable(thm) {
        ordered.push((
            ClassMembership::NonemptyErase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
            RootLane::Off,
        ));
    }
    ordered
}

/// Worker-side half of the parallel replay: translate `thm` under EVERY
/// escalation mode (the serial path stops at the first kernel accept, but the
/// kernel verdict is master-side, so a worker must precompute all of them).
/// Resets the per-line translation budget exactly as [`verify_one`] does, so
/// mode `i`'s budget state is identical to the serial run for every mode the
/// master actually consumes (later modes may burn residual budget the serial
/// run never spent — their results are discarded on early accept, so this is
/// wasted work, never a verdict change). Translation is a pure function of
/// (thm, closure entries of its deps, frozen registries) — it never touches
/// the kernel [`Environment`].
#[allow(clippy::too_many_arguments)]
pub(super) fn translate_all_modes(
    thm: &IsaProvenTheorem,
    closure: &Closure,
    class_registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
) -> ModeTranslations {
    super::super::isabelle_pure_translate::reset_translate_steps();
    escalation_modes(thm, class_registry)
        .into_iter()
        .map(|(membership, method_embed, instance_embed, root_lane)| {
            translate_theorem_with_meta_lane(
                thm,
                closure,
                class_registry,
                method_registry,
                instance_op_registry,
                list_fn_registry,
                poly_inst_registry,
                membership,
                method_embed,
                instance_embed,
                root_lane,
            )
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn verify_one(
    thm: &IsaProvenTheorem,
    index: usize,
    env: &mut Environment,
    closure: &mut Closure,
    class_registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
) {
    verify_one_with_translations(
        thm,
        index,
        None,
        env,
        closure,
        class_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        writer,
        out,
        elide,
    );
}

/// [`verify_one`] with optionally PRECOMPUTED per-mode translations (the
/// parallel driver's master path). `pre: None` = translate inline exactly as
/// the historical serial driver (byte-identical). `pre: Some(v)` = `v[i]` is
/// used verbatim where mode `i` would have translated — the kernel `add_decl`
/// loop, honest-reject bucketing, foundational gate, closure insert, shard
/// write and elision all run HERE, unchanged, so the kernel remains the sole
/// verdict mint regardless of which thread translated.
#[allow(clippy::too_many_arguments)]
pub(super) fn verify_one_with_translations(
    thm: &IsaProvenTheorem,
    index: usize,
    pre: Option<&ModeTranslations>,
    env: &mut Environment,
    closure: &mut Closure,
    class_registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
) {
    // Fresh per-LINE translation node budget (`ISA_TRANSLATE_NODE_BUDGET`):
    // the counter is thread-local so it spans ALL escalating translate modes
    // below — a pathological recorded proof gets ONE budget for the whole
    // line, not one per mode. No-op when the budget env is unset. (With
    // precomputed translations the budget was reset and spent on the WORKER
    // thread by [`translate_all_modes`]; nothing translate-side runs here.)
    if pre.is_none() {
        super::super::isabelle_pure_translate::reset_translate_steps();
    }
    // **Two-tier trusted-ledger** lane (env-gated `ISA_TRUSTED_LEDGER`, default
    // OFF). Read once per line. When OFF, phase 2 ([`try_ledger_tier2`]) is never
    // entered, so this whole function is byte-identical to HEAD.
    //
    // **Phase 1 is the entire body up to the KernelVerified write.** It resolves
    // `PThm` references against the KV `closure` ONLY — never the ledger closure
    // (`out.ledger_closure`) — so it is byte-for-byte the historical single-tier
    // importer. A line is `KernelVerified` iff phase 1 accepts it foundationally,
    // EXACTLY as a no-ledger run ⇒ `KernelVerified` is invariant ON vs OFF. Only
    // a line phase 1 could NOT verify falls through to phase 2 below.
    let ledger_on = ledger_enabled();
    // Kernel identity is the (unique) proof-term serial, decoupled from the
    // human name: Isabelle's closure contains anonymous nodes (empty names)
    // and promoted duplicates (several serials sharing one name), both of
    // which would collide as kernel declarations. PThm references resolve by
    // serial, so this is exactly the right key.
    let kernel_name = if thm.serial != 0 {
        format!("isabelle.s{}", thm.serial)
    } else {
        format!("isabelle.anon.{index}")
    };

    // Two-pass class-membership translation: first treat each `OFCLASS`
    // premise as the vacuous `True` (`Erase` — the historical behaviour that
    // most theorems verify with), and ONLY if the kernel rejects that do we
    // retry treating the structured-class premises as real membership
    // propositions (`Real` — needed by the `c_class.super`/`.axioms`/`.assoc`
    // projections). This keeps the membership model strictly additive: no
    // erasure-verified theorem is lost, and the genuinely axiom-using ones are
    // recovered. The accumulating env re-checks `value : type` either way.
    // Translate each theorem in escalating passes. The first two keep methods
    // OPAQUE (the exact historical embedding — every previously-verified theorem
    // still verifies); the next pass UNFOLDS registered overloaded methods to
    // their dictionary def-consts, which the `…_dict`-axiom-using nodes need but
    // which changes how `c_class.method` embeds everywhere; the FINAL pass also
    // UNFOLDS registered ground-type instance operations to their def-consts
    // (`Nat.plus_nat` → `isabelle.inst.…`, `0::nat` → `Nat.zero`, …), which the
    // recursive-arithmetic `…_def` axioms and their nat/num consumers need. Each
    // escalation is a strictly additive fallback (a later mode runs only after the
    // earlier ones kernel-reject), so it never displaces an earlier success.
    // The escalating mode set + `Real`-first reorder for membership-concluding
    // nodes — shared with the parallel driver's workers so precomputed
    // translations line up index-for-index. See [`escalation_modes`].
    let modes = escalation_modes(thm, class_registry);
    // Master mode-attempt telemetry (diagnostic; see [`MODE_ATTEMPTS`]): one line
    // reaching the escalation loop.
    MODE_LINES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut accepted: Option<(Expr, Expr, TranslatedMeta)> = None;
    let mut last_translate_err: Option<TranslateError> = None;
    // **Opt-in** kernel-reject diagnostics: when `ISA_DUMP_REJECTS` is set, we
    // keep the last mode's `add_decl` `EnvError` so a genuine kernel-reject (a
    // translated-but-not-accepted theorem) can be clustered by its
    // expected-vs-got type heads below. `None` (the default) — nothing kept, no
    // cost, no behaviour change.
    let dump_target = super::dump::dump_target();
    let mut last_kernel_err: Option<clean_kernel::env::EnvError> = None;
    // The **honest origin error** of a FABRICATED-reflexivity fallback that the
    // kernel then rejected (see [`TranslatedMeta::fallback_origin`]). When the
    // recorded proof failed to translate (commonly an unresolved dependency) the
    // translator short-circuits an equation-shaped statement to `Eq.refl LHS`; the
    // kernel accepts that ONLY when the equation is genuinely reflexive. If it is
    // rejected, the *honest* reason is this recorded-proof failure — not a genuine
    // "kernel refused our reconstruction". Bucketing by it (below) stops a
    // dependency cascade from being mis-counted as `kernel-reject`.
    let mut last_fallback_origin: Option<TranslateError> = None;
    // TRUE when some escalation mode translated a REAL (non-fabricated) proof —
    // the recorded proof or a structurally-valid statement-level arm, i.e.
    // `fallback_origin` is `None` — and the kernel rejected it. The honest
    // primary reject reason is then the KERNEL's: an earlier, weaker mode's
    // fabricated-fallback origin (`UnmappedAxiom`, `UnresolvedThm`, …) describes
    // that mode's failure, not this one's. Without this, a node whose final
    // escalation genuinely reaches the kernel is mis-bucketed under the stale
    // earlier-mode origin (e.g. `unmapped-axiom: …max_dict` for a node whose
    // DictUnfold pass translated the whole recorded chain).
    let mut real_proof_kernel_reject = false;
    // **Debug-only, opt-in** per-mode outcome trace (`ISA_DUMP_MODES`): records
    // each escalation mode's translate/kernel error for one matched theorem and
    // prints them on the reject path. `None` (the default) — nothing recorded.
    let mut mode_trace: Option<Vec<String>> =
        super::dump::mode_trace_wanted(&thm.name, thm.serial).then(Vec::new);
    for (mode_idx, (membership, method_embed, instance_embed, root_lane)) in
        modes.into_iter().enumerate()
    {
        // Mode `i`'s translation: precomputed by a worker ([`translate_all_modes`],
        // same order, same per-line budget semantics) or inline (serial path).
        let translated = match pre {
            Some(v) => v
                .get(mode_idx)
                .cloned()
                .unwrap_or(Err(TranslateError::Unsupported(
                    "missing precomputed mode translation",
                ))),
            None => translate_theorem_with_meta_lane(
                thm,
                closure,
                class_registry,
                method_registry,
                instance_op_registry,
                list_fn_registry,
                poly_inst_registry,
                membership,
                method_embed,
                instance_embed,
                root_lane,
            ),
        };
        let (decl, meta) = match translated {
            Ok(d) => d,
            Err(e) => {
                if let Some(tr) = mode_trace.as_mut() {
                    tr.push(format!(
                        "mode {mode_idx} ({membership:?},{method_embed:?},{instance_embed:?},{root_lane:?}): translate error: {e:?}"
                    ));
                }
                // A statement-fallback mode's synthetic "skip the recorded
                // proof" error must not displace the honest earlier-mode
                // translate error the reject would otherwise bucket under.
                if root_lane != RootLane::StmtFallback {
                    last_translate_err = Some(e);
                }
                continue;
            }
        };
        let fallback_origin = meta.fallback_origin.clone();
        let Declaration::Theorem { type_, value, .. } = &decl else {
            continue;
        };
        let (ty, proof_value) = (type_.clone(), value.clone());
        let kdecl = Declaration::Theorem {
            name: Name::from_string(&kernel_name),
            level_params: Vec::new(),
            type_: ty.clone(),
            value: proof_value.clone(),
        };
        // Master mode-attempt telemetry (diagnostic; see [`MODE_ATTEMPTS`]): one
        // kernel `add_decl` attempt — the cost the step-2 pre-check aims to cut.
        MODE_ATTEMPTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        match env.add_decl(kdecl) {
            Ok(()) => {
                if let Some(tr) = mode_trace.as_mut() {
                    tr.push(format!(
                        "mode {mode_idx} ({membership:?},{method_embed:?},{instance_embed:?}): ACCEPTED"
                    ));
                }
                accepted = Some((ty, proof_value, meta));
                break;
            }
            Err(e) => {
                if let Some(tr) = mode_trace.as_mut() {
                    tr.push(format!(
                        "mode {mode_idx} ({membership:?},{method_embed:?},{instance_embed:?}): kernel reject: {} (fallback_origin={fallback_origin:?})",
                        super::dump::env_error_signature(&e)
                    ));
                    // Per-mode full expected-vs-got dump for a node that a later
                    // mode may still accept (`ISA_DUMP_FULL`-gated, trace-only).
                    super::dump::maybe_dump_full(&thm.name, thm.serial, &e);
                }
                // A rejected FABRICATED-reflexivity fallback carries the honest
                // recorded-proof failure — remember it so the final reject path can
                // bucket by it instead of `kernel-reject` (the whole point of the
                // fabricating-fallback fix). Always tracked (bucketing is not
                // diagnostics-gated); the clone is on the reject cold path only.
                if fallback_origin.is_some() {
                    // (Not from a statement-fallback mode: its origin is the
                    // synthetic "skip the recorded proof" sentinel, which
                    // must not displace an honest earlier-mode origin.)
                    if root_lane != RootLane::StmtFallback {
                        last_fallback_origin = fallback_origin;
                    }
                } else {
                    real_proof_kernel_reject = true;
                }
                // Keep the reject reason only when diagnostics are on (cold path,
                // and only allocates the error we would have dropped anyway).
                if dump_target.is_some() {
                    last_kernel_err = Some(e);
                }
            }
        }
    }
    if let Some(tr) = &mode_trace {
        super::dump::print_mode_trace(&thm.name, thm.serial, tr);
    }
    let Some((ty, proof_value, meta)) = accepted else {
        // A real (non-fabricated) proof that reached the kernel and was rejected
        // buckets as `kernel-reject` — see `real_proof_kernel_reject` above.
        let origin = if real_proof_kernel_reject {
            None
        } else {
            last_translate_err.or(last_fallback_origin)
        };
        // **Phase 2** (flag ON): phase 1 could not KernelVerify this line against
        // the KV closure. Re-resolve it against the KV closure UNIONED with the
        // ledger closure. If the kernel now accepts, it is tier-2
        // (`KernelCheckedConditional`) — its verification REQUIRED the ledger, so
        // it is never KV. If it still proves nothing but its STATEMENT embeds, it
        // becomes a trusted-ledger `Axiom` (`isabelle.trusted.s<serial>`) so its
        // downstream cascade can resolve + kernel-check. Returns `true` when it
        // took ownership of the verdict (tier-2 or ledger); otherwise fall
        // through to the unchanged honest reject.
        if ledger_on {
            let reason = origin
                .as_ref()
                .map_or("kernel-reject", |e| translate_error_tag(e));
            if try_ledger_tier2(
                thm,
                index,
                &*closure,
                class_registry,
                method_registry,
                instance_op_registry,
                list_fn_registry,
                poly_inst_registry,
                reason,
                env,
                writer,
                out,
                elide,
            ) {
                return;
            }
        }
        match origin {
            Some(e) => out.reject_with_specific(translate_error_tag(&e), &e),
            None => {
                out.reject("kernel-reject");
                // **Opt-in** cluster dump: append this genuine kernel-reject's
                // normalized signature (EnvError kind + expected-vs-got type
                // heads + failing proof-node kind) when `ISA_DUMP_REJECTS` is set.
                // Inert (and this whole block skipped) when unset.
                if let (Some(target), Some(err)) = (&dump_target, &last_kernel_err) {
                    super::dump::append_reject(
                        target,
                        "kernel-reject",
                        &thm.name,
                        thm.serial,
                        err,
                        &thm.proof,
                    );
                    super::dump::maybe_dump_full(&thm.name, thm.serial, err);
                }
            }
        }
        return;
    };

    let name = Name::from_string(&kernel_name);
    let foundational = match env.axiom_deps(&name) {
        Some(deps) => deps.iter().all(is_foundational_axiom),
        None => false,
    };
    if !foundational {
        // Phase 1 resolved only KV-closure entries (no ledger axioms are ever
        // in that closure), so a non-foundational closure here is a REAL domain
        // axiom — a genuine reject in both a ledger and a no-ledger run. (A line
        // that is only provable VIA the ledger fails phase-1 translation and is
        // handled by phase 2 above, never here.)
        out.reject("non-foundational-axiom");
        return;
    }

    // Verified: record in the closure (by serial), lower, stamp the shard.
    // The verified clean type is kept so later `PThm` references can
    // reconstruct the implicit leading type/sort arguments the Isabelle
    // proof spine omits (see `Ctx::apply_thm`), and the leading type-param keys
    // so a fully-typed (`zproof`) reference carrying an explicit `tyinst` table
    // can specialize this theorem directly (see `Ctx::apply_thm_explicit`).
    if thm.serial != 0 {
        closure.insert(
            thm.serial,
            ClosureEntry {
                name: kernel_name.clone(),
                ty: ty.clone(),
                type_param_keys: meta.type_param_keys,
                term_param_keys: meta.term_param_keys,
            },
        );
    }

    // The shard stores the human-readable name (or the kernel name when the
    // node is anonymous), keeping the catalog readable.
    let shard_name = if thm.name.is_empty() {
        &kernel_name
    } else {
        &thm.name
    };
    let name_idx = writer.add_string(shard_name);
    let type_idx = lower_kernel_expr(&ty, writer);
    let value_idx = lower_kernel_expr(&proof_value, writer);
    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile(0),
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    let shard_idx = writer.add_constant(header);
    out.kernel_verified += 1;
    out.names.push(thm.name.clone());
    // On a ledger run, record every written constant (here: tier-1 KV) so the
    // publish step can stamp provenance at the right shard index even when the
    // shard also holds tier-2 / ledger constants. Empty (untouched) when OFF.
    if ledger_on {
        out.written_constants.push(WrittenConstant {
            name: shard_name.clone(),
            shard_idx,
            confidence: ImportConfidence::KernelVerified as u8,
            ledger_note: None,
        });
    }
    // **Opt-in, env-gated** KernelVerified-name dump (`ISA_DUMP_KV=<file>`):
    // append one `name\tserial` line per verified theorem, the KV-side twin of
    // `ISA_DUMP_REJECTS`. Two runs' dumps diff to the exact former-KV losses /
    // new-KV gains of a translator change (bucket totals alone cannot
    // distinguish a loss masked by a larger gain). Inert when unset; reached
    // only on the (rare) accept path; nothing here can mint or block a verdict.
    if let Ok(kv_dump) = std::env::var("ISA_DUMP_KV") {
        if !kv_dump.is_empty() {
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&kv_dump)
            {
                use std::io::Write as _;
                let _ = writeln!(f, "{}\t{}", thm.name, thm.serial);
            }
        }
    }

    // Opaque proof-value elision (env-gated): the `KernelVerified` verdict is now
    // fully earned (kernel-accepted + foundational closure), and this theorem is
    // henceforth referenced only BY NAME (opaque `PThm`/`ZConstp(ZThm)`, never
    // δ-unfolded). Drop its resident proof VALUE to bound peak memory on the
    // full corpus, keeping only its TYPE for later references. Verdict-neutral:
    // `forget_value` removes a δ-reduction rule (and the value the shard already
    // holds), never adds an accept — see this fn's SOUNDNESS note. The lowered
    // `value_idx` above is already written to the shard, so the shard's stored
    // proof value is unaffected; only the in-memory env value is freed.
    if elide {
        env.forget_value(&name);
    }
}

/// **Phase 2** of the two-tier lane, entered only for a line phase 1 could NOT
/// `KernelVerify` and only when `ISA_TRUSTED_LEDGER` is set. Re-resolves the
/// line's `PThm` references against the KV closure UNIONED with the ledger
/// closure (`out.ledger_closure`), then:
///
/// - if the kernel now accepts a translated proof → **tier-2**
///   ([`ImportConfidence::KernelCheckedConditional`]): the verification REQUIRED
///   the ledger (phase 1, which sees only the KV closure, already declined it),
///   so it is recorded in the ledger closure + shard and counted — NEVER KV;
/// - else if the STATEMENT still embeds cleanly → a **trusted-ledger axiom**
///   ([`register_ledger_axiom`]);
/// - else → returns `false` and the caller emits the unchanged honest reject.
///
/// SOUNDNESS: this function never touches the KV closure and is never reached for
/// a line phase 1 verified, so `KernelVerified` is byte-identical ON vs OFF.
#[allow(clippy::too_many_arguments)]
fn try_ledger_tier2(
    thm: &IsaProvenTheorem,
    index: usize,
    kv_closure: &Closure,
    class_registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    reason: &str,
    env: &mut Environment,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
) -> bool {
    let kernel_name = if thm.serial != 0 {
        format!("isabelle.s{}", thm.serial)
    } else {
        format!("isabelle.anon.{index}")
    };
    // The ledger closure is owned by `out`; take it out so we can borrow it
    // mutably alongside `out`'s counters without aliasing (put back before every
    // return). `mem::take` on a `BTreeMap` is O(1).
    let mut ledger_closure = std::mem::take(&mut out.ledger_closure);
    // Merged mini-closure: exactly this line's dependency entries, KV first then
    // ledger (a serial lives in at most one). This is the union view phase 1 was
    // deliberately denied.
    let mut deps = Vec::new();
    thm.proof.thm_deps(&mut deps);
    deps.sort_unstable();
    deps.dedup();
    let merged: Closure = deps
        .iter()
        .filter_map(|s| {
            kv_closure
                .get(s)
                .or_else(|| ledger_closure.get(s))
                .map(|e| (*s, e.clone()))
        })
        .collect();
    // Fresh per-line translation budget for this second attempt.
    super::super::isabelle_pure_translate::reset_translate_steps();
    let modes = escalation_modes(thm, class_registry);
    let mut ledger_candidate: Option<(Expr, Vec<String>, Vec<String>)> = None;
    let mut accepted: Option<(Expr, Expr, TranslatedMeta)> = None;
    for (membership, method_embed, instance_embed, root_lane) in modes {
        let translated = translate_theorem_with_meta_lane(
            thm,
            &merged,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            membership,
            method_embed,
            instance_embed,
            root_lane,
        );
        let (decl, meta) = match translated {
            Ok(d) => d,
            Err(_) => continue,
        };
        let Declaration::Theorem { type_, value, .. } = &decl else {
            continue;
        };
        let (ty, proof_value) = (type_.clone(), value.clone());
        if ledger_candidate.is_none() {
            ledger_candidate = Some((
                ty.clone(),
                meta.type_param_keys.clone(),
                meta.term_param_keys.clone(),
            ));
        }
        let kdecl = Declaration::Theorem {
            name: Name::from_string(&kernel_name),
            level_params: Vec::new(),
            type_: ty.clone(),
            value: proof_value.clone(),
        };
        if env.add_decl(kdecl).is_ok() {
            accepted = Some((ty, proof_value, meta));
            break;
        }
    }
    if let Some((ty, proof_value, meta)) = accepted {
        let name = Name::from_string(&kernel_name);
        // Classify the phase-2 accept. A line reaches phase 2 only because phase 1
        // (KV-closure-only) declined it; the merged (KV ∪ ledger) closure supplied
        // the missing dependency. Two disjoint provenances for a merged-closure
        // accept, discriminated by the transitive axiom closure:
        //
        //  • FOUNDATIONAL closure AND the line references a BRIDGED serial ⇒
        //    **inherited KernelBridged**. Its own native Isabelle proof term WAS
        //    kernel-re-checked, and NO trusted-ledger axiom is in its closure
        //    (foundational) — trust is KV-grade — but it routes through a
        //    cross-lane bridged constant, so the bridged PROVENANCE propagates
        //    transitively. Ranked immediately below KV; NEVER counted as native KV
        //    (which stays byte-identical ON vs OFF: a bridged serial never lives in
        //    the KV closure, so no phase-1-KV line can reference one).
        //  • otherwise ⇒ **tier-2** (KernelCheckedConditional): its closure
        //    contains a trusted-ledger `Axiom` (non-foundational), so it is
        //    conditional on the ledger.
        //
        // A foundational phase-2 accept MUST reference a bridged serial (a ledger
        // axiom would make it non-foundational, and a purely-KV-closure line would
        // have been accepted in phase 1), so the two branches are exhaustive; the
        // explicit `refs_bridged` guard makes the intent legible and keeps a
        // (never-reached) foundational-but-unbridged accept on the conservative
        // tier-2 under-claim rather than mis-minting KernelBridged.
        let foundational = env
            .axiom_deps(&name)
            .is_some_and(|d| d.iter().all(is_foundational_axiom));
        let refs_bridged = deps.iter().any(|s| out.bridged_serials.contains(s));
        if phase2_accept_is_inherited_bridged(foundational, refs_bridged) {
            record_bridged_dependent(
                thm,
                &kernel_name,
                &ty,
                &proof_value,
                &meta,
                env,
                &mut ledger_closure,
                writer,
                out,
                elide,
            );
            out.ledger_closure = ledger_closure;
            return true;
        }
        // Tier-2: name the trusted-ledger dependence for the provenance note —
        // the ledger axioms actually in the kernel `axiom_deps`, or (when the
        // reference was eliminated) the referenced ledger-closure serials.
        let mut ledger_deps: Vec<String> = env
            .axiom_deps(&name)
            .map(|d| {
                d.iter()
                    .map(ToString::to_string)
                    .filter(|s| s.starts_with(LEDGER_AXIOM_PREFIX))
                    .collect()
            })
            .unwrap_or_default();
        ledger_deps.sort();
        if ledger_deps.is_empty() {
            ledger_deps = deps
                .iter()
                .filter(|s| ledger_closure.contains_key(s))
                .map(|s| format!("s{s}"))
                .collect();
        }
        record_tier2(
            thm,
            &kernel_name,
            &ty,
            &proof_value,
            &meta,
            &ledger_deps,
            env,
            &mut ledger_closure,
            writer,
            out,
            elide,
        );
        out.ledger_closure = ledger_closure;
        return true;
    }
    // No proof accepted. BEFORE ledgering (registering a trusted-ledger axiom
    // restatement), try the opt-in cross-lane KERNEL BRIDGE: if the manifest
    // names a Mathlib-KV witness for this line and this line's embedded statement
    // bridges to that witness's type via a foundational connective iso, mint a
    // real `KernelBridged` proof instead. Byte-identical when `ISA_BRIDGE_DISCHARGE`
    // is unset (`bridge_manifest()` is `None`, so the block is skipped) — the
    // same OFF-invariance the ledger lane guarantees.
    if let (Some(manifest), Some((stmt_ty, tpk, tmpk))) =
        (bridge_manifest(), ledger_candidate.as_ref())
    {
        if try_bridge_discharge(
            thm,
            index,
            stmt_ty,
            tpk,
            tmpk,
            manifest,
            reason,
            env,
            &mut ledger_closure,
            writer,
            out,
            elide,
        ) {
            out.ledger_closure = ledger_closure;
            return true;
        }
    }
    // No proof accepted; register the embedded statement as a ledger axiom if
    // some mode produced a well-formed TYPE.
    let handled = if let Some((stmt_ty, tpk, tmpk)) = ledger_candidate {
        register_ledger_axiom(
            thm,
            index,
            stmt_ty,
            tpk,
            tmpk,
            reason,
            env,
            &mut ledger_closure,
            writer,
            out,
        )
    } else {
        false
    };
    out.ledger_closure = ledger_closure;
    handled
}

/// **Cross-lane kernel-bridge discharge** (opt-in, `ISA_BRIDGE_DISCHARGE`).
///
/// Given a line phase 1 could NOT verify, its embedded statement TYPE
/// (`isa_stmt`), and the loaded [`BridgeManifest`], attempt to discharge it
/// against a NAMED Mathlib-KV witness constant already resident in `env`:
///
/// 1. resolve the witness constant name from the manifest (by theorem name, then
///    serial); decline if none;
/// 2. require the witness to be present in `env`, **level-monomorphic** (the
///    connective composer works over ground `Prop`s), and to have a
///    **foundational-only** transitive axiom closure (Mathlib-KV grade);
/// 3. compose the foundational connective bridge and mint
///    `@Iff.mpr isa_stmt witness_type bridge witness : isa_stmt`
///    ([`discharge_value`]);
/// 4. `add_decl` the theorem `isabelle.s<serial> : isa_stmt := <that term>`; the
///    kernel re-checks the whole proof — a mis-shaped bridge is a rejection,
///    never a silent pass;
/// 5. re-assert the minted theorem's transitive axiom closure is
///    foundational-only (the [`ImportConfidence::KernelBridged`] minting floor);
/// 6. write it to the shard as `KernelBridged` and count it in
///    [`PureVerifiedImport::kernel_bridged`].
///
/// Returns `true` iff the line was minted `KernelBridged` (the caller then owns
/// the verdict and never ledgers it). Any decline returns `false` and the caller
/// falls through to the unchanged ledger/reject path.
///
/// SOUNDNESS: the verdict is minted **only by the kernel** (`add_decl` + the
/// foundational-closure re-check), never at manifest-load time — the manifest is
/// a *candidate feeder*, exactly like the alias table, and cannot by itself mint
/// trust. The witness's own value is a `KernelVerified` proof and the bridge is
/// foundational, so `KernelBridged` is a real end-to-end Clean proof of the
/// Isabelle statement — but it is NEVER `KernelVerified` (the statement arrived
/// via the bridge; the discharge writes a distinct tier).
///
/// **Non-terminal (this round).** The minted decl `isabelle.s<serial>` IS a real
/// kernel-checked constant in `env`, so — exactly as an accepted tier-2 line does
/// — its [`ClosureEntry`] is inserted into the LEDGER closure and its serial is
/// recorded in [`PureVerifiedImport::bridged_serials`]. A dependent that
/// references it therefore resolves the serial (in phase 2, against the merged
/// closure), re-checks its own native proof against the real bridged value, and
/// is classified `KernelBridged` (inherited) by the phase-2 classifier — the
/// bridged provenance propagating transitively, trust staying foundational.
///
/// **Level-poly witnesses** are monomorphized at `Prop` (level 0): see the
/// witness-resolution block below.
#[allow(clippy::too_many_arguments)]
fn try_bridge_discharge(
    thm: &IsaProvenTheorem,
    index: usize,
    isa_stmt: &Expr,
    type_param_keys: &[String],
    term_param_keys: &[String],
    manifest: &BridgeManifest,
    reason: &str,
    env: &mut Environment,
    ledger_closure: &mut Closure,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
) -> bool {
    let witness_name = match manifest.witness_for(thm) {
        Some(w) => w.to_string(),
        None => return false,
    };
    let witness_ident = Name::from_string(&witness_name);
    // Resolve the witness's type + a reference term, MONOMORPHIZING a
    // level-polymorphic witness at `Prop` (level 0). A Mathlib-KV witness
    // `w.{u..} : T(u..)` specializes to `@w.{0..} : T(0..)` — a genuine instance
    // the kernel re-checks. `Sort 0 = Prop` is a valid universe specialization of
    // ANY level parameter (levels are bounded below by 0), so the instantiation
    // is always well-typed and SOUND: it can only produce a MORE specific,
    // still-provable statement of the same constant. The composer and the
    // `add_decl` re-check below are the arbiters — if the `Prop` instance is not
    // the bridged propositional skeleton (e.g. a param fed a carrier-tower `Type`
    // slot the composer does not cover), the composition declines honestly
    // (`IsaMismatch`/`CarrierMismatch`) or the kernel rejects, and no unsound
    // "bridge" is ever minted. Capture what we need, then drop the immutable
    // borrow before mutating `env`.
    let (witness_type, witness_ref) = match env.get_const(&witness_ident) {
        Some(ci) if ci.level_params.is_empty() => {
            (ci.type_.clone(), Expr::const_str(&witness_name))
        }
        Some(ci) => {
            let zeros: Vec<Level> = vec![Level::zero(); ci.level_params.len()];
            let mono_type = ci
                .type_
                .instantiate_level_params_direct(&ci.level_params, &zeros);
            (mono_type, Expr::const_str_levels(&witness_name, zeros))
        }
        None => return false,
    };
    // Witness must itself be Mathlib-KV grade (foundational-only closure), else
    // the composition could smuggle a domain axiom into a "bridged" verdict.
    // (Axiom deps are level-independent, so the base constant's closure governs
    // every `Prop`-monomorphized instantiation.)
    match env.axiom_deps(&witness_ident) {
        Some(deps) if deps.iter().all(is_foundational_axiom) => {}
        _ => return false,
    }
    // Compose the connective bridge and mint the discharge value. An out-of-scope
    // statement / carrier mismatch / isa-mismatch declines honestly.
    let value = match discharge_value(isa_stmt, &witness_type, witness_ref) {
        Ok(v) => v,
        Err(_) => return false,
    };
    let kernel_name = if thm.serial != 0 {
        format!("isabelle.s{}", thm.serial)
    } else {
        format!("isabelle.anon.{index}")
    };
    let name = Name::from_string(&kernel_name);
    let decl = Declaration::Theorem {
        name: name.clone(),
        level_params: Vec::new(),
        type_: isa_stmt.clone(),
        value: value.clone(),
    };
    if env.add_decl(decl).is_err() {
        return false;
    }
    // Minting floor: the kernel is the sole arbiter of the foundational closure.
    // The witness pre-check + foundational isos make this hold, but we re-assert
    // it here — a non-foundational closure is NEVER KernelBridged.
    let foundational = match env.axiom_deps(&name) {
        Some(deps) => deps.iter().all(is_foundational_axiom),
        None => false,
    };
    if !foundational {
        return false;
    }
    let shard_name = if thm.name.is_empty() {
        &kernel_name
    } else {
        &thm.name
    };
    let name_idx = writer.add_string(shard_name);
    let type_idx = lower_kernel_expr(isa_stmt, writer);
    let value_idx = lower_kernel_expr(&value, writer);
    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::KernelBridged as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile(0),
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    let shard_idx = writer.add_constant(header);
    out.kernel_bridged += 1;
    out.written_constants.push(WrittenConstant {
        name: shard_name.clone(),
        shard_idx,
        confidence: ImportConfidence::KernelBridged as u8,
        ledger_note: Some(format!(
            "cross-lane KernelBridged discharge of Isabelle '{}' serial {} via Mathlib-KV \
             witness '{witness_name}' + foundational connective bridge (was: {reason})",
            thm.name, thm.serial
        )),
    });
    // NON-TERMINAL: the minted decl is a real kernel-checked constant in `env`, so
    // record its LEDGER-closure entry (keyed by serial, exactly as a tier-2 accept
    // does) and mark the serial bridged. A dependent then resolves it in phase 2
    // and is classified inherited-`KernelBridged` (see the phase-2 classifier).
    if thm.serial != 0 {
        ledger_closure.insert(
            thm.serial,
            ClosureEntry {
                name: kernel_name.clone(),
                ty: isa_stmt.clone(),
                type_param_keys: type_param_keys.to_vec(),
                term_param_keys: term_param_keys.to_vec(),
            },
        );
        out.bridged_serials.insert(thm.serial);
    }
    if elide {
        env.forget_value(&name);
    }
    true
}

/// Register the embedded STATEMENT of a line that failed every reconstruction /
/// reprove arm as a **trusted-ledger kernel `Axiom`** (`isabelle.trusted.s<serial>`),
/// insert its entry into the LEDGER closure so downstream lines resolve the
/// dependency (in phase 2 only), and write it to the shard as
/// [`ImportConfidence::Axiomatized`]. Returns `true` when the axiom was
/// registered (the line is then accounted tier-LEDGER, NOT rejected). Returns
/// `false` (caller falls back to the honest reject) when the kernel refuses the
/// axiom TYPE.
///
/// SOUNDNESS: the ledger axiom is a **restatement**, never a proof — the kernel
/// checks only that the embedded statement TYPE is well-formed (it re-checks no
/// proof). It is counted in `ledger_size` and NOWHERE in any proved/verified
/// metric (CLAUDE.md: `Theorem` wrapping `Axiom` is NOT a proof). Its entry goes
/// into the LEDGER closure, never the KV closure, so a dependent that references
/// it fails phase-1 (KV-closure-only) verification and is routed to phase 2 —
/// tier-2, never tier-1 `KernelVerified`.
#[allow(clippy::too_many_arguments)]
fn register_ledger_axiom(
    thm: &IsaProvenTheorem,
    index: usize,
    stmt_ty: Expr,
    type_param_keys: Vec<String>,
    term_param_keys: Vec<String>,
    reason: &str,
    env: &mut Environment,
    ledger_closure: &mut Closure,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
) -> bool {
    let axiom_name = if thm.serial != 0 {
        format!("{LEDGER_AXIOM_PREFIX}s{}", thm.serial)
    } else {
        format!("{LEDGER_AXIOM_PREFIX}anon.{index}")
    };
    // The kernel checks the TYPE is well-formed (a valid Sort); no proof value.
    let decl = Declaration::Axiom {
        name: Name::from_string(&axiom_name),
        level_params: Vec::new(),
        type_: stmt_ty.clone(),
    };
    if env.add_decl(decl).is_err() {
        return false;
    }
    // Dependents resolve this line's serial to the ledger axiom in PHASE 2 (the
    // entry lives only in the ledger closure), so their recorded proofs
    // kernel-check against it there → tier-2.
    if thm.serial != 0 {
        ledger_closure.insert(
            thm.serial,
            ClosureEntry {
                name: axiom_name.clone(),
                ty: stmt_ty.clone(),
                type_param_keys,
                term_param_keys,
            },
        );
    }
    let shard_name = if thm.name.is_empty() {
        &axiom_name
    } else {
        &thm.name
    };
    let name_idx = writer.add_string(shard_name);
    let type_idx = lower_kernel_expr(&stmt_ty, writer);
    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Axiom as u8,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    let shard_idx = writer.add_constant(header);
    let theory = thm.name.split('.').next().unwrap_or_default().to_string();
    out.ledger.push(LedgerEntry {
        serial: thm.serial,
        isabelle_name: thm.name.clone(),
        theory,
        reject_reason: reason.to_string(),
        axiom_name: axiom_name.clone(),
    });
    out.ledger_size += 1;
    out.written_constants.push(WrittenConstant {
        name: shard_name.clone(),
        shard_idx,
        confidence: ImportConfidence::Axiomatized as u8,
        ledger_note: Some(format!(
            "trusted-ledger restatement (tier-LEDGER) of Isabelle '{}' serial {}; \
             failed all reconstruction/reprove arms (reject reason: {reason})",
            thm.name, thm.serial
        )),
    });
    true
}

/// Record a **tier-2** ([`ImportConfidence::KernelCheckedConditional`]) line: in
/// phase 2 the kernel accepted `value : type` against the ledger-augmented
/// closure, so its verification required the trusted ledger (`ledger_deps`).
/// Insert its entry into the LEDGER closure (so ITS dependents cascade in phase
/// 2 too), write it to the shard with a provenance note naming the ledger
/// dependence, and count it. NEVER `KernelVerified`.
#[allow(clippy::too_many_arguments)]
fn record_tier2(
    thm: &IsaProvenTheorem,
    kernel_name: &str,
    ty: &Expr,
    proof_value: &Expr,
    meta: &TranslatedMeta,
    ledger_deps: &[String],
    env: &mut Environment,
    ledger_closure: &mut Closure,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
) {
    if thm.serial != 0 {
        ledger_closure.insert(
            thm.serial,
            ClosureEntry {
                name: kernel_name.to_string(),
                ty: ty.clone(),
                type_param_keys: meta.type_param_keys.clone(),
                term_param_keys: meta.term_param_keys.clone(),
            },
        );
    }
    let shard_name = if thm.name.is_empty() {
        kernel_name
    } else {
        thm.name.as_str()
    };
    let name_idx = writer.add_string(shard_name);
    let type_idx = lower_kernel_expr(ty, writer);
    let value_idx = lower_kernel_expr(proof_value, writer);
    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::KernelCheckedConditional as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    let shard_idx = writer.add_constant(header);
    out.kernel_checked_ledger += 1;
    out.written_constants.push(WrittenConstant {
        name: shard_name.to_string(),
        shard_idx,
        confidence: ImportConfidence::KernelCheckedConditional as u8,
        ledger_note: Some(format!(
            "tier-2 (KernelCheckedConditional): kernel re-checked, conditional on \
             the trusted ledger via {} dependence(s): {}",
            ledger_deps.len(),
            ledger_deps.join(", ")
        )),
    });
    // Elide the resident proof value exactly as the KV path does: the tier-2
    // verdict is fully earned before the drop, so it is verdict-neutral.
    if elide {
        env.forget_value(&Name::from_string(kernel_name));
    }
}

/// Classify a **phase-2 accept** by its axiom-closure facts: `true` ⇒ inherited
/// [`ImportConfidence::KernelBridged`], `false` ⇒ tier-2
/// ([`ImportConfidence::KernelCheckedConditional`]).
///
/// The honest argument, from the closure facts:
/// - A line reaches phase 2 only because its KV closure was insufficient, so the
///   accept was made possible by a serial that lives ONLY in the ledger closure —
///   either a trusted-ledger `Axiom` or a bridged constant.
/// - `foundational_closure` ⇒ NO trusted-ledger axiom is in the transitive
///   closure (a ledger axiom is non-foundational by construction). Combined with
///   `references_bridged`, the only merged-closure dependency it rests on is a
///   BRIDGED constant, whose own closure is foundational. So the line's trust is
///   KV-grade (`⊆ FOUNDATIONAL_AXIOMS`), but its statement is proved *through* a
///   cross-lane bridge — bridged PROVENANCE that must propagate. ⇒ inherited
///   `KernelBridged`.
/// - Otherwise the closure contains a trusted-ledger axiom (non-foundational) ⇒
///   tier-2 (conditional on the ledger). The `references_bridged` guard also keeps
///   a (never-reached) foundational-but-unbridged accept on the conservative
///   tier-2 under-claim rather than mis-minting `KernelBridged`.
#[inline]
fn phase2_accept_is_inherited_bridged(
    foundational_closure: bool,
    references_bridged: bool,
) -> bool {
    foundational_closure && references_bridged
}

/// Record an **inherited `KernelBridged`** line: a phase-2 accept whose own
/// native Isabelle proof term the kernel re-checked (`value : type` accepted) and
/// whose transitive axiom closure is **foundational-only**, but which references a
/// BRIDGED serial — so its statement is proved, transitively, *through* a
/// cross-lane bridge. Its provenance is therefore bridged (propagated), even
/// though its trust is KV-grade (foundational).
///
/// Insert its entry into the LEDGER closure and mark its serial bridged (so ITS
/// dependents cascade + inherit too), write it to the shard as
/// [`ImportConfidence::KernelBridged`], and count it in
/// [`PureVerifiedImport::kernel_bridged`] alongside the direct discharges.
///
/// SOUNDNESS: this is a real kernel-re-checked proof (`add_decl` already accepted
/// it against the merged closure in [`try_ledger_tier2`]) with a foundational
/// closure — the discharge writes a distinct tier ONLY to record the bridged
/// provenance, never to weaken or strengthen the kernel's verdict. It is NEVER
/// `KernelVerified` (that tier is byte-invariant ON vs OFF, and a bridged serial
/// never enters the KV closure, so this line could not have been phase-1 KV).
#[allow(clippy::too_many_arguments)]
fn record_bridged_dependent(
    thm: &IsaProvenTheorem,
    kernel_name: &str,
    ty: &Expr,
    proof_value: &Expr,
    meta: &TranslatedMeta,
    env: &mut Environment,
    ledger_closure: &mut Closure,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
) {
    if thm.serial != 0 {
        ledger_closure.insert(
            thm.serial,
            ClosureEntry {
                name: kernel_name.to_string(),
                ty: ty.clone(),
                type_param_keys: meta.type_param_keys.clone(),
                term_param_keys: meta.term_param_keys.clone(),
            },
        );
        out.bridged_serials.insert(thm.serial);
    }
    let shard_name = if thm.name.is_empty() {
        kernel_name
    } else {
        thm.name.as_str()
    };
    let name_idx = writer.add_string(shard_name);
    let type_idx = lower_kernel_expr(ty, writer);
    let value_idx = lower_kernel_expr(proof_value, writer);
    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::KernelBridged as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile(0),
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    let shard_idx = writer.add_constant(header);
    out.kernel_bridged += 1;
    out.written_constants.push(WrittenConstant {
        name: shard_name.to_string(),
        shard_idx,
        confidence: ImportConfidence::KernelBridged as u8,
        ledger_note: Some(format!(
            "inherited KernelBridged: kernel re-checked this line's own native proof, \
             foundational closure, but it cascades through a bridged dependency of \
             Isabelle '{}' serial {}",
            thm.name, thm.serial
        )),
    });
    // Elide the resident proof value exactly as the KV/tier-2 paths do: the
    // verdict is fully earned before the drop, so it is verdict-neutral. Dependents
    // reference this by NAME (opaque `PThm`), so dropping the δ-value keeps the
    // closure entry (name + type) usable for the cascade.
    if elide {
        env.forget_value(&Name::from_string(kernel_name));
    }
}

#[cfg(test)]
mod bridge_discharge_tests {
    use super::*;
    use crate::hol::isabelle_pure::{parse_proven_theorem, IsaProvenTheorem};
    use crate::shard::ShardReader;
    use clean_kernel::{BinderInfo, Level};

    /// A prelude env with the Mathlib inductive `Iff` the bridge composes with.
    fn env_with_iff() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_iff().expect("init_iff");
        env
    }

    /// The exact impredicative `isaTrue` embedding the composer expects:
    /// `(λx:Prop. x) = (λx:Prop. x)`.
    fn isa_true() -> Expr {
        let id = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [Expr::arrow(Expr::prop(), Expr::prop()), id.clone(), id],
        )
    }

    fn synthetic_thm(name: &str, serial: i64) -> IsaProvenTheorem {
        // prop/proof are placeholders — try_bridge_discharge takes the statement
        // Expr directly and keys the manifest by name/serial, never re-translating.
        let json = format!(
            r#"{{"name":"{name}","serial":{serial},"prop":{{"k":"Free","n":"p","t":{{"k":"Type","n":"HOL.bool","a":[]}}}},"proof":{{"k":"min"}}}}"#
        );
        parse_proven_theorem(&json).expect("parse synthetic thm")
    }

    fn manifest(pairs: &[(&str, &str)]) -> BridgeManifest {
        BridgeManifest {
            by_name: pairs
                .iter()
                .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
                .collect(),
            by_serial: BTreeMap::new(),
        }
    }

    #[test]
    fn bridge_discharge_flips_line_to_kernel_bridged_foundational() {
        let mut env = env_with_iff();
        let thm = synthetic_thm("Demo.true_thm", 9001);
        let m = manifest(&[("Demo.true_thm", "True.intro")]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();

        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_true(),
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );

        assert!(took, "bridge should discharge isaTrue against True.intro");
        assert_eq!(out.kernel_bridged, 1);
        assert_eq!(out.written_constants.len(), 1);
        assert_eq!(
            out.written_constants[0].confidence,
            ImportConfidence::KernelBridged as u8
        );

        // NON-TERMINAL: the bridged serial is recorded in the ledger closure (so a
        // dependent can resolve it) AND in the bridged-serial provenance frontier.
        assert!(
            ledger_closure.contains_key(&9001),
            "bridged serial must be inserted into the replay (ledger) closure"
        );
        assert_eq!(
            ledger_closure[&9001].name, "isabelle.s9001",
            "closure entry names the minted kernel decl"
        );
        assert!(
            out.bridged_serials.contains(&9001),
            "bridged serial recorded in the provenance frontier"
        );

        // The minted proof really is in the kernel env with a foundational closure.
        let name = Name::from_string("isabelle.s9001");
        let deps = env.axiom_deps(&name).expect("minted theorem in env");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "closure must be foundational: {deps:?}"
        );

        // Shard round-trips as KernelBridged with a stored proof value.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        let (_, hdr) = reader
            .lookup_name("Demo.true_thm")
            .expect("bridged name present");
        assert_eq!(hdr.import_confidence, ImportConfidence::KernelBridged as u8);
        assert_ne!(hdr.value_idx, NO_VALUE, "bridged proof value stored");
    }

    #[test]
    fn bridge_discharge_inert_when_manifest_has_no_witness() {
        // OFF-equivalent: an empty manifest names no witness => no mint, no env
        // mutation, no shard write — byte-identical to the historical reject path.
        let mut env = env_with_iff();
        let thm = synthetic_thm("Demo.true_thm", 9002);
        let m = manifest(&[]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();

        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_true(),
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );

        assert!(!took, "no witness => decline");
        assert_eq!(out.kernel_bridged, 0);
        assert!(out.written_constants.is_empty());
        assert!(
            ledger_closure.is_empty(),
            "declined bridge must not touch the replay closure"
        );
        assert!(
            out.bridged_serials.is_empty(),
            "declined bridge must not record a bridged serial"
        );
        assert!(
            env.axiom_deps(&Name::from_string("isabelle.s9002"))
                .is_none(),
            "declined bridge must not mutate the env"
        );
    }

    #[test]
    fn bridge_discharge_declines_when_witness_absent_from_env() {
        // Witness named but not resident (not a KV constant here) => decline, inert.
        let mut env = env_with_iff();
        let thm = synthetic_thm("Demo.true_thm", 9003);
        let m = manifest(&[("Demo.true_thm", "Mathlib.not_in_env")]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();

        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_true(),
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );
        assert!(!took);
        assert_eq!(out.kernel_bridged, 0);
        assert!(ledger_closure.is_empty());
    }

    // ---------------------------------------------------------------------
    // END-TO-END: a REAL alias row (`excluded_middle` ↔ Mathlib `em`)
    // discharged `KernelBridged` with the witness loaded from a REAL on-disk
    // `.mathverse` artifact via the production witness sourcer.
    // ---------------------------------------------------------------------

    /// Write a one-constant KV `.mathverse` shard `<name>.mathverse` into `dir` —
    /// the exact bytes the Mathlib import lane (`clean mathverse stamp-verified`)
    /// emits for one KernelVerified constant, values included.
    fn write_kv_witness_shard(dir: &Path, name: &str, type_: &Expr, value: &Expr) {
        let mut w = ShardWriter::new();
        let name_idx = w.add_string(name);
        let type_idx = lower_kernel_expr(type_, &mut w);
        let value_idx = lower_kernel_expr(value, &mut w);
        w.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::Logic as u8,
            decl_kind: DeclKind::Theorem as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        let mut buf = Vec::new();
        w.write(&mut buf).expect("serialize witness shard");
        std::fs::write(dir.join(format!("{name}.mathverse")), &buf).expect("write shard file");
    }

    /// The Isabelle/HOL importer's impredicative embedding of `excluded_middle`
    /// (`∀ P, P ∨ ¬P`): `∀ (P:Prop), isaDisj P (isaNot P)` — exactly what the
    /// connective composer derives from the Mathlib `em` type, hand-built here to
    /// prove the REAL alias row discharges (not the composer's own output fed back).
    fn isa_excluded_middle() -> Expr {
        use clean_kernel::FVarId;
        // isaFalse ≡ ∀ (R:Prop), R
        let isa_false = || Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        // isaNot P ≡ P → isaFalse
        let isa_not = |p: Expr| Expr::arrow(p, isa_false());
        // isaDisj P Q ≡ ∀ (C:Prop), (P → C) → (Q → C) → C
        let isa_disj = |p: Expr, q: Expr| {
            let cfv = FVarId::new(0x5000_0001);
            let cc = Expr::fvar(cfv);
            let body = Expr::arrow(
                Expr::arrow(p, cc.clone()),
                Expr::arrow(Expr::arrow(q, cc.clone()), cc),
            );
            Expr::pi(BinderInfo::Default, Expr::prop(), body.abstract_fvar(cfv))
        };
        let pfv = FVarId::new(0x5000_0002);
        let p = Expr::fvar(pfv);
        let body = isa_disj(p.clone(), isa_not(p));
        Expr::pi(BinderInfo::Default, Expr::prop(), body.abstract_fvar(pfv))
    }

    #[test]
    fn end_to_end_excluded_middle_bridged_from_real_shard_witness() {
        use super::super::bridge_witness::load_bridge_witnesses;

        // (0) A replay env carrying the foundational witness base.
        let mut env = Environment::with_prelude();
        env.init_iff().expect("init_iff");
        env.init_or().expect("init_or");
        env.init_exists().expect("init_exists");
        env.init_classical().expect("init_classical");

        // (1) Build a REAL on-disk KV `.mathverse` shard for the Mathlib witness
        // `em := Classical.em` (Mathlib's `em` re-exports `Classical.em`). Its type
        // is Classical.em's own type — `∀ (p:Prop), p ∨ ¬p` — so the composer sees
        // exactly the Mathlib spelling.
        let em_ty = env
            .get_const(&Name::from_string("Classical.em"))
            .expect("Classical.em resident")
            .type_
            .clone();
        let dir = tempfile::tempdir().expect("tempdir");
        write_kv_witness_shard(dir.path(), "em", &em_ty, &Expr::const_str("Classical.em"));

        // (2) Load the witness (type + value) from the real artifact into the env.
        let wanted: BTreeSet<String> = ["em".to_string()].into_iter().collect();
        let stats = load_bridge_witnesses(&mut env, dir.path(), &wanted);
        assert_eq!(stats.loaded, 1, "em must load from the shard: {stats:?}");
        assert!(
            env.get_const(&Name::from_string("em")).is_some(),
            "witness resident after load"
        );

        // (3) Discharge the Isabelle `excluded_middle` statement KernelBridged
        // against the loaded witness.
        let thm = synthetic_thm("HOL.excluded_middle", 9100);
        let m = manifest(&[("HOL.excluded_middle", "em")]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();
        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_excluded_middle(),
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );
        assert!(took, "excluded_middle must bridge against the em witness");
        assert!(
            ledger_closure.contains_key(&9100) && out.bridged_serials.contains(&9100),
            "excluded_middle bridged serial is non-terminal (in the replay closure)"
        );
        assert_eq!(out.kernel_bridged, 1);
        assert_eq!(
            out.written_constants[0].confidence,
            ImportConfidence::KernelBridged as u8
        );

        // (4) The minted proof is genuinely in the kernel env with a foundational
        // closure — an end-to-end Clean proof of the Isabelle statement.
        let minted = Name::from_string("isabelle.s9100");
        let deps = env.axiom_deps(&minted).expect("minted theorem in env");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "bridged closure must be foundational: {deps:?}"
        );

        // (5) Shard round-trips as KernelBridged with a stored proof value.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        let (_, hdr) = reader
            .lookup_name("HOL.excluded_middle")
            .expect("bridged name present");
        assert_eq!(hdr.import_confidence, ImportConfidence::KernelBridged as u8);
        assert_ne!(hdr.value_idx, NO_VALUE, "bridged proof value stored");
    }

    // ---------------------------------------------------------------------
    // END-TO-END (REAL IMPORT EMBED): a corpus line whose `prop` embeds through
    // the ACTUAL importer path (`Ctx::embed_term`) — producing the connective
    // DEFINITION-CONST spelling (`isabelle.def.HOL.disj`/`.Not`), NOT the
    // impredicative encoding — is discharged `KernelBridged` against a manifest
    // witness. Before the def-const pre-normalization brick the composer could not
    // consume this spelling (it walks only the impredicative encoding), so this
    // family was deliberately raw-encoding-only.
    // ---------------------------------------------------------------------

    /// `HOL.bool` object type.
    fn ty_bool() -> crate::hol::isabelle_pure::IsaType {
        crate::hol::isabelle_pure::IsaType::Type {
            n: "HOL.bool".into(),
            a: vec![],
        }
    }

    /// `a ⇒ b` HOL function type.
    fn ty_fun(
        a: crate::hol::isabelle_pure::IsaType,
        b: crate::hol::isabelle_pure::IsaType,
    ) -> crate::hol::isabelle_pure::IsaType {
        crate::hol::isabelle_pure::IsaType::Type {
            n: "fun".into(),
            a: vec![a, b],
        }
    }

    /// Embed `∀ P::bool. P ∨ ¬P` through the REAL importer path
    /// (`Ctx::embed_term`), yielding the def-const-spelled statement type a corpus
    /// line's `translate` produces: `∀ (P:Prop), isabelle.def.HOL.disj P
    /// (isabelle.def.HOL.Not P)`.
    fn embed_real_excluded_middle() -> Expr {
        use crate::hol::isabelle_pure::IsaTerm;
        use crate::hol::isabelle_pure_translate::{Binder, Ctx};
        let b2b = ty_fun(ty_bool(), ty_bool());
        let b2b2b = ty_fun(ty_bool(), b2b.clone());
        // body = HOL.disj (Bound 0) (HOL.Not (Bound 0))
        let body = IsaTerm::App {
            f: Box::new(IsaTerm::App {
                f: Box::new(IsaTerm::Const {
                    n: "HOL.disj".into(),
                    t: b2b2b,
                }),
                a: Box::new(IsaTerm::Bound { i: 0 }),
            }),
            a: Box::new(IsaTerm::App {
                f: Box::new(IsaTerm::Const {
                    n: "HOL.Not".into(),
                    t: b2b.clone(),
                }),
                a: Box::new(IsaTerm::Bound { i: 0 }),
            }),
        };
        // HOL.All (λP::bool. body), typed `(bool⇒bool)⇒bool`.
        let all = IsaTerm::App {
            f: Box::new(IsaTerm::Const {
                n: "HOL.All".into(),
                t: ty_fun(b2b, ty_bool()),
            }),
            a: Box::new(IsaTerm::Abs {
                n: "P".into(),
                t: ty_bool(),
                b: Box::new(body),
            }),
        };
        // Trueprop-wrapped (stripped as an identity coercion by embed_term).
        let prop = IsaTerm::App {
            f: Box::new(IsaTerm::Const {
                n: "HOL.Trueprop".into(),
                t: ty_fun(
                    ty_bool(),
                    crate::hol::isabelle_pure::IsaType::Type {
                        n: "prop".into(),
                        a: vec![],
                    },
                ),
            }),
            a: Box::new(all),
        };
        let mut ctx = Ctx::default();
        let mut binders: Vec<Binder> = Vec::new();
        ctx.embed_term(&prop, &mut binders)
            .expect("embed excluded_middle statement through the real importer path")
    }

    #[test]
    fn end_to_end_excluded_middle_bridged_from_real_import_embed() {
        // (0) Env: prelude + the inductive `Iff`/`Or`/`Exists` the composer needs,
        // `Classical` (for the `em` witness), AND the connective def-consts the REAL
        // importer emits — registered exactly as `import_proven_theorems` does up
        // front, so the discharge's `Iff.mpr` re-check can δ-unfold
        // `isabelle.def.HOL.*` to the impredicative encoding the bridge is stated
        // over. This is the production wiring, not a fixture shortcut.
        let mut env = Environment::with_prelude();
        env.init_iff().expect("init_iff");
        env.init_or().expect("init_or");
        env.init_exists().expect("init_exists");
        env.init_classical().expect("init_classical");
        for decl in connective_definition_decls() {
            env.add_decl(decl).expect("connective def-const registers");
        }

        // (1) The REAL importer embedding of `∀ P. P ∨ ¬P` — connectives spelled
        // with the def-consts, exactly what a corpus line's `translate/embed_term`
        // yields (and precisely the spelling the pre-fix composer rejected).
        let isa_stmt = embed_real_excluded_middle();
        // Structurally confirm the importer produced the def-const spelling: the
        // statement is `∀ (P:Prop), isabelle.def.HOL.disj P (isabelle.def.HOL.Not P)`
        // — the disjunction head is the DEFINITION const, not the impredicative
        // encoding (the spelling the pre-fix composer could not consume).
        let disj_head = match isa_stmt.kind() {
            clean_kernel::expr::ExprKind::Pi(_, _, body) => body.get_app_fn().clone(),
            other => panic!("expected an outer ∀ binder, got {other:?}"),
        };
        assert!(
            matches!(
                disj_head.kind(),
                clean_kernel::expr::ExprKind::Const(n, _)
                    if n.to_string() == "isabelle.def.HOL.disj"
            ),
            "embedded statement must carry the importer def-const spelling, got head {disj_head:?}"
        );

        // (2) Witness `em := Classical.em : ∀ p, p ∨ ¬p` (Mathlib's `em` re-exports
        // `Classical.em`), foundational KV grade — the named constant the manifest
        // resolves to, referenced by name exactly as production does.
        let em_ty = env
            .get_const(&Name::from_string("Classical.em"))
            .expect("Classical.em resident")
            .type_
            .clone();
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("em"),
            level_params: Vec::new(),
            type_: em_ty,
            value: Expr::const_str("Classical.em"),
        })
        .expect("em witness kernel-checks");

        // (3) Discharge the REAL def-const-spelled statement KernelBridged.
        let thm = synthetic_thm("HOL.excluded_middle", 9110);
        let m = manifest(&[("HOL.excluded_middle", "em")]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();
        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_stmt,
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );
        assert!(
            took,
            "real-import def-const-spelled excluded_middle must bridge against em"
        );
        assert_eq!(out.kernel_bridged, 1);
        assert_eq!(
            out.written_constants[0].confidence,
            ImportConfidence::KernelBridged as u8
        );
        // Non-terminal (in the replay closure + bridged frontier).
        assert!(ledger_closure.contains_key(&9110) && out.bridged_serials.contains(&9110));

        // (4) The minted proof — of the DEF-CONST-spelled statement type — is a
        // genuine kernel-checked constant with a foundational closure.
        let minted = Name::from_string("isabelle.s9110");
        let deps = env.axiom_deps(&minted).expect("minted theorem in env");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "bridged closure must be foundational: {deps:?}"
        );

        // (5) Shard round-trips as KernelBridged with a stored proof value.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        let (_, hdr) = reader
            .lookup_name("HOL.excluded_middle")
            .expect("bridged name present");
        assert_eq!(hdr.import_confidence, ImportConfidence::KernelBridged as u8);
        assert_ne!(hdr.value_idx, NO_VALUE, "bridged proof value stored");
    }

    // ---------------------------------------------------------------------
    // FOLLOW-UP (1): non-terminal bridged lines + honest cascade classification.
    // ---------------------------------------------------------------------

    /// The phase-2 accept classifier is exactly `foundational ∧ references_bridged`
    /// — the honest decision table argued from the axiom-closure facts. Both
    /// cases: a foundational accept that references a bridged serial inherits
    /// `KernelBridged`; anything with a trusted-ledger axiom in its closure
    /// (non-foundational) — or that references no bridged serial — stays tier-2.
    #[test]
    fn phase2_classifier_decision_table() {
        // Case A — dependent proves against a BRIDGED dep, foundational closure ⇒
        // inherited KernelBridged.
        assert!(phase2_accept_is_inherited_bridged(true, true));
        // Case B — closure contains a trusted-ledger axiom (non-foundational) even
        // though it references a bridged serial ⇒ tier-2 (the ledger claim
        // dominates; a non-foundational closure is never KernelBridged).
        assert!(!phase2_accept_is_inherited_bridged(false, true));
        // Foundational but references no bridged serial (never reached in practice)
        // ⇒ conservative tier-2 under-claim, never a mis-minted KernelBridged.
        assert!(!phase2_accept_is_inherited_bridged(true, false));
        // Pure trusted-ledger accept ⇒ tier-2.
        assert!(!phase2_accept_is_inherited_bridged(false, false));
    }

    /// A dependent whose OWN proof term the kernel re-checks **against a bridged
    /// constant** is recorded inherited-`KernelBridged`: foundational closure
    /// (trust is KV-grade) but bridged provenance (never native KV), non-terminal
    /// (its serial re-enters the replay closure + the bridged frontier so ITS
    /// dependents cascade), and it round-trips on the shard as `KernelBridged`.
    #[test]
    fn inherited_bridged_dependent_is_kernel_bridged_and_non_terminal() {
        let mut env = env_with_iff();
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();

        // (0) Bridge-discharge a primary `isaTrue` (serial 9001) so it is resident,
        // in the replay closure, and on the bridged frontier.
        let primary = synthetic_thm("Demo.true_primary", 9001);
        let m = manifest(&[("Demo.true_primary", "True.intro")]);
        assert!(try_bridge_discharge(
            &primary,
            0,
            &isa_true(),
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        ));
        assert_eq!(out.kernel_bridged, 1);
        assert!(out.bridged_serials.contains(&9001));

        // (1) SOUNDNESS CORE: a dependent's own native proof re-checks against the
        // bridged constant *like any other constant*. Here the dependent
        // `isabelle.s9500 : isaTrue` is proved BY the bridged constant
        // `isabelle.s9001` — the kernel accepts it, proving the bridged decl is a
        // usable dependency (not a terminal dead-end).
        let dep_name = Name::from_string("isabelle.s9500");
        env.add_decl(Declaration::Theorem {
            name: dep_name.clone(),
            level_params: Vec::new(),
            type_: isa_true(),
            value: Expr::const_str("isabelle.s9001"),
        })
        .expect("dependent proof re-checks against the bridged constant");

        // (2) Its transitive axiom closure is FOUNDATIONAL (the bridged dep
        // contributes only foundational axioms) and it references bridged serial
        // 9001 — so the classifier routes it to inherited KernelBridged.
        let dep_deps = env.axiom_deps(&dep_name).expect("dependent in env");
        let foundational = dep_deps.iter().all(is_foundational_axiom);
        assert!(foundational, "dependent-of-bridged closure is foundational");
        let refs_bridged = out.bridged_serials.contains(&9001);
        assert!(phase2_accept_is_inherited_bridged(
            foundational,
            refs_bridged
        ));

        // (3) Record it exactly as the phase-2 classifier does.
        let dep_thm = synthetic_thm("Demo.dependent", 9500);
        record_bridged_dependent(
            &dep_thm,
            "isabelle.s9500",
            &isa_true(),
            &Expr::const_str("isabelle.s9001"),
            &TranslatedMeta::default(),
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );

        // KernelBridged (not KV), counted alongside the direct discharge.
        assert_eq!(out.kernel_bridged, 2);
        assert!(
            out.names.is_empty(),
            "an inherited-bridged dependent is NEVER counted native KernelVerified"
        );
        // NON-TERMINAL: the dependent's own serial re-enters the replay closure +
        // frontier, so ITS dependents cascade + inherit too (transitive propagation).
        assert!(ledger_closure.contains_key(&9500));
        assert_eq!(ledger_closure[&9500].name, "isabelle.s9500");
        assert!(out.bridged_serials.contains(&9500));
        // Shard round-trip: KernelBridged with a stored proof value.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        let (_, hdr) = reader
            .lookup_name("Demo.dependent")
            .expect("dependent present");
        assert_eq!(hdr.import_confidence, ImportConfidence::KernelBridged as u8);
        assert_ne!(hdr.value_idx, NO_VALUE, "inherited-bridged value stored");
    }

    // ---------------------------------------------------------------------
    // FOLLOW-UP (2): level-polymorphic witness monomorphization at Prop (0).
    // ---------------------------------------------------------------------

    /// A level-POLYMORPHIC Mathlib-KV witness discharges after monomorphization at
    /// `Prop` (level 0): `w.{u} : True` is referenced as `@w.{0}` and its type is
    /// instantiated to the ground `True` the composer bridges `isaTrue ↔ True`
    /// against. (Prior to this brick the composer required a level-monomorphic
    /// witness and declined `w` outright.)
    #[test]
    fn level_poly_witness_monomorphized_at_prop_discharges() {
        let mut env = env_with_iff();
        // A genuinely level-polymorphic witness `w.{u} : True := True.intro`.
        let u = Name::from_string("u");
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("w"),
            level_params: vec![u],
            type_: Expr::const_str("True"),
            value: Expr::const_str("True.intro"),
        })
        .expect("level-poly witness kernel-checks");

        let thm = synthetic_thm("Demo.poly_true", 9200);
        let m = manifest(&[("Demo.poly_true", "w")]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();
        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_true(),
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );
        assert!(
            took,
            "level-poly witness must discharge after Prop-monomorphization"
        );
        assert_eq!(out.kernel_bridged, 1);
        // The minted proof references `@w.{0}` and closes foundationally.
        let minted = Name::from_string("isabelle.s9200");
        let deps = env.axiom_deps(&minted).expect("minted theorem in env");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "Prop-monomorphized bridge closure must be foundational: {deps:?}"
        );
        assert!(ledger_closure.contains_key(&9200));
    }

    /// A level-poly witness whose `Prop`-monomorphized type is NOT the bridged
    /// skeleton declines honestly (no mint, no env mutation): `w.{u} : True`
    /// cannot bridge the `isaFalse` statement (`IsaMismatch`), and the
    /// monomorphization does not paper over the mismatch.
    #[test]
    fn level_poly_witness_declines_honestly_on_shape_mismatch() {
        let mut env = env_with_iff();
        let u = Name::from_string("u");
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("w"),
            level_params: vec![u],
            type_: Expr::const_str("True"),
            value: Expr::const_str("True.intro"),
        })
        .expect("level-poly witness kernel-checks");

        // isaFalse ≡ ∀ (R:Prop), R — a different skeleton than the witness's True.
        let isa_false = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        let thm = synthetic_thm("Demo.poly_false", 9300);
        let m = manifest(&[("Demo.poly_false", "w")]);
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut ledger_closure = Closure::new();
        let took = try_bridge_discharge(
            &thm,
            0,
            &isa_false,
            &[],
            &[],
            &m,
            "kernel-reject",
            &mut env,
            &mut ledger_closure,
            &mut writer,
            &mut out,
            false,
        );
        assert!(
            !took,
            "shape mismatch must decline even for a level-poly witness"
        );
        assert_eq!(out.kernel_bridged, 0);
        assert!(ledger_closure.is_empty());
        assert!(
            env.axiom_deps(&Name::from_string("isabelle.s9300"))
                .is_none(),
            "declined bridge must not mutate the env"
        );
    }
}
