// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Graduation intake gate — the sole producer of `SourceSystem::Cake` shards.
//!
//! [`graduate`] performs, in order, for every candidate:
//!
//! 1. **Kernel re-check** — the declaration is replayed into a *fresh*
//!    prelude environment via the real `Environment::add_decl` path. The only
//!    way to earn `KernelVerdict::KernelVerified` is for the kernel to
//!    type-check the candidate **with its proof value**. Project-side
//!    certificates are cross-checked (proof-hash identity) but never trusted
//!    as a verdict.
//! 2. **Axiom closure** — `Environment::proof_quality` in the recheck
//!    environment. Anything other than `ProofQuality::Constructive`
//!    (transitive closure ⊆ `FOUNDATIONAL_AXIOMS`) is rejected under the
//!    fixed `min_trust = kernel_verified` policy; non-foundational closures
//!    are recorded as `AxiomDependent`, never laundered.
//! 3. **Novelty** — `name + statement-hash` dedup against the pinned
//!    baseline corpus AND against earlier accepted candidates from the same
//!    run (the run's accepted set is corpus-to-be; without the intra-run
//!    check a single run could append statement-duplicates). Honest label;
//!    defeq-grade matching is roadmap.
//! 4. **Shard write** — accepted theorems, preceded by the carried
//!    definitions they require (dependency order), are flattened through
//!    `KernelShardBuilder` with `SourceSystem::Cake`, axiom profiles are
//!    closed in-shard, and every constant's provenance record carries the
//!    digest-bound graduation note. The record (`<stem>.graduation.json`)
//!    and shard are mutually digest-bound; see
//!    [`crate::shard_verify::cake_gate`] for the unbypassable verify side.
//!
//! v2 scope: candidates must be theorems whose proofs reference only prelude
//! constants, earlier candidates in the same run, axioms (which are seeded
//! into the recheck environment so the closure check can observe — and
//! reject — them), or **definitions, which are carried**: every
//! definition-valued dependency is kernel re-checked EXACTLY like a theorem
//! (`Environment::add_decl` with its defining value, in dependency order,
//! definitions before their users) and recorded in the graduation record's
//! `carried_definitions` section. A definition whose value fails the kernel
//! re-check kills every dependent candidate (`carried-definition-failed`),
//! never downgrades silently. A theorem's transitive axiom closure includes
//! its carried definitions' closures (the kernel's `axiom_deps` walks
//! through definition values), so an axiom smuggled through a carried
//! definition still rejects the theorem as `axiom-dependent`. Only
//! definitions required by at least one accepted theorem are written into
//! the shard — which the cake gate replays self-contained-against-prelude,
//! definitions first.
//!
//! v3.1 scope: **theorem-valued dependencies are carried too**, under the
//! exact same `add_decl`-with-proof-value discipline, recorded in the
//! record's `carried_theorems` section. A carried theorem is supporting
//! material, never a graduating candidate: it does not enter
//! `result.accepted`, and the `on_duplicate` policy does NOT apply to it —
//! its baseline novelty is recorded honestly (a carried mathlib lemma is
//! expected to be `duplicate`) but never used to reject. Closure composition
//! is unchanged: `axiom_deps` walks carried proof values, so an axiom
//! smuggled through a carried theorem still rejects every dependent
//! candidate. Opaque-valued external dependencies remain rejected.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprVisitor, LevelVec, Name};

use super::intake_family::{carry_inductive_family, inductive_family_root, CarriedFamilyState};
use super::recheck::recheck_and_classify;
use super::record::{
    blake3_digest, expr_canonical_digest, graduation_record_path, AxiomClosure, CarriedDefinition,
    CarriedInductive, CarriedInductiveMember, CarriedTheorem, CorpusPin, EnvProvenance,
    EvidenceClass, GateInfo, GraduatedTheorem, GraduationRecord, GraduationResult, KernelFacts,
    KernelVerdict, NoveltyFacts, NoveltyMatchKind, NoveltyVerdict, OnDuplicate, PolicyInfo,
    ProjectInfo, RunProvenance, SemanticIdentityRecord, GRADUATION_GATE_VERSION,
    GRADUATION_MIN_TRUST, GRADUATION_SCHEMA_VERSION,
};
use crate::error::{MathverseError, MathverseResult};
use crate::export::kernel_export::{InductiveFamilyMemberExport, KernelShardBuilder};
use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;
use crate::types::{DeclKind, SourceSystem};

/// Project-side certificate identity used for cross-checking only — the
/// intake re-derives every verdict and merely corroborates that the project
/// is talking about the same proof term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateCrossCheck {
    pub theorem: String,
    /// Expected `blake3:<hex>` canonical proof-value digest.
    pub proof_hash: String,
}

/// Caller-supplied graduation request (everything except the candidates,
/// the source environment, and the baseline corpus).
#[derive(Clone, Debug)]
pub struct GraduationRequest {
    pub project_name: String,
    pub manifest_kind: String,
    /// `blake3:<hex>` digest of the project manifest bytes.
    pub manifest_digest: String,
    pub certificate_schema: Option<String>,
    pub certificate_cross_checks: Vec<CertificateCrossCheck>,
    /// Label of the pinned novelty baseline (e.g. `mathverse-v1.2.0`).
    pub mathverse_release: String,
    pub on_duplicate: OnDuplicate,
    pub attempt_id: Option<String>,
    pub replay_archive_sha256: Option<String>,
    pub engine: Option<String>,
    pub seed: Option<String>,
    pub evidence_class: EvidenceClass,
    /// Mandatory honesty field (may be `"none-known"`).
    pub residual_risk: String,
    /// `git` commit of the deciding Clean build, when known.
    pub clean_commit: Option<String>,
    /// Shard filename override; defaults to `<project>-graduated.mathverse`.
    pub shard_filename: Option<String>,
    /// Pinned decision time (epoch seconds) for reproducible-by-content shards.
    /// `None` reads the wall clock (normal runs). To reproduce a prior shard
    /// byte-for-byte (verify-by-digest / attestation replay), pin this to the
    /// `decided_at_epoch_s` recorded in that shard's graduation record: the
    /// decision time is the only nondeterministic input to shard bytes (it
    /// feeds per-record `import_timestamp` + the record's `binding_digest`
    /// provenance note, which zstd then amplifies into the header length).
    pub decided_at_epoch_s: Option<u64>,
    /// Cake build-provenance fingerprint of the source `.olean` environment, when
    /// freshness was checked (`--olean-source-root`). `None` ⇒ omitted from the
    /// record (byte-for-byte determinism preserved).
    pub env_provenance: Option<EnvProvenance>,
    /// Compute + bind each candidate's Cake semantic identity (`--score`). Off by
    /// default so records stay byte-identical (the semantic-identity field is omitted).
    /// This is the FAST path: only the env-free `structural_rewrite_digest` (no kernel
    /// normalisation), which is the corpus key + the intra-run probe key.
    pub score_identity: bool,
    /// Additionally compute the EXPENSIVE defeq Tier-1 identity (`--score-defeq`): runs the
    /// kernel normaliser (`whnf`) on the statement type. Bounded but can be slow on heavy
    /// mathlib-Real statements; off by default. Requires `score_identity`.
    pub score_defeq: bool,
}

// ---------------------------------------------------------------------------
// Baseline corpus
// ---------------------------------------------------------------------------

/// Pinned novelty baseline: declaration names and canonical statement hashes
/// extracted from one or more `.mathverse` shards — either scanned directly
/// ([`GraduationBaseline::load`]) or served from a prebuilt `MVBIDX01` index
/// ([`GraduationBaseline::from_index`], built by
/// [`super::baseline_index::build_baseline_index`]). Both backends answer
/// the same `name + statement-hash` question with the same hash primitive.
#[derive(Debug)]
pub struct GraduationBaseline {
    digest: String,
    backend: BaselineBackend,
}

#[derive(Debug)]
enum BaselineBackend {
    InMemory {
        names: HashSet<String>,
        /// statement-hash -> first declaration name carrying it.
        statement_hashes: HashMap<String, String>,
        /// Cake env-free Tier-1.5 rewrite-canonical digest -> first declaration
        /// name carrying it. The "same object, different form" corpus key, kept
        /// in parity with the `MVBIDX01` index's semantic table.
        semantic_hashes: HashMap<String, String>,
    },
    Index(super::baseline_index::BaselineIndex),
}

impl Default for GraduationBaseline {
    fn default() -> Self {
        Self::empty()
    }
}

impl GraduationBaseline {
    /// Empty baseline (every candidate is `new`). Digest is the blake3 of
    /// zero bytes so the corpus pin stays well-formed.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            digest: blake3_digest(&[]),
            backend: BaselineBackend::InMemory {
                names: HashSet::new(),
                statement_hashes: HashMap::new(),
                semantic_hashes: HashMap::new(),
            },
        }
    }

    /// Load a baseline from a single `.mathverse` shard file or a directory
    /// tree of shards. The baseline digest is blake3 over every shard's
    /// bytes in sorted-path order.
    pub fn load(path: &Path) -> MathverseResult<Self> {
        let shard_paths = collect_shard_paths(path)?;
        let mut hasher = blake3::Hasher::new();
        let mut baseline = Self::empty();
        for shard_path in &shard_paths {
            let bytes = std::fs::read(shard_path).map_err(MathverseError::Io)?;
            hasher.update(&bytes);
            let reader = ShardReader::from_bytes(&bytes)?;
            baseline.index_reader(&reader);
        }
        baseline.digest = format!("blake3:{}", hasher.finalize().to_hex());
        Ok(baseline)
    }

    /// Load a baseline from a prebuilt `MVBIDX01` index file (seconds for
    /// the full 5.77M-declaration release, vs ≥16h for [`Self::load`]).
    ///
    /// The corpus-pin digest comes from the index header and is the same
    /// blake3-over-shard-bytes digest `load` would have computed; the index
    /// loader fail-closes on any corruption before a single lookup.
    pub fn from_index(path: &Path) -> MathverseResult<Self> {
        let index = super::baseline_index::BaselineIndex::load(path)?;
        Ok(Self {
            digest: index.corpus_digest().to_string(),
            backend: BaselineBackend::Index(index),
        })
    }

    /// Index every constant of `reader` for name + statement-hash dedup.
    ///
    /// Statement-hash indexing is best-effort: a baseline constant whose
    /// type fails reconstruction still participates in exact-name dedup.
    fn index_reader(&mut self, reader: &ShardReader) {
        let BaselineBackend::InMemory {
            names,
            statement_hashes,
            semantic_hashes,
        } = &mut self.backend
        else {
            // `index_reader` is only reachable from `load`, which always
            // constructs the in-memory backend.
            return;
        };
        for header in &reader.constants {
            let Some(name) = reader.strings.get(header.name_idx as usize) else {
                continue;
            };
            names.insert(name.clone());
            let Ok(type_) = reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                header.type_idx,
            ) else {
                continue;
            };
            // Both tables are gated on the SAME condition as `build_baseline_index`
            // (statement-hash success): a type that fails `expr_canonical_digest` is
            // name-only in BOTH the Index and the InMemory backend, so the semantic table
            // stays in lockstep parity by CONSTRUCTION — not by an external shard invariant.
            if let Ok(hash) = expr_canonical_digest(&type_) {
                statement_hashes.entry(hash).or_insert_with(|| name.clone());
                // Semantic key: env-free Tier-1.5 rewrite-canonical digest of the SAME type.
                let sem = clean_cake::identity::structural_rewrite_digest(&type_);
                semantic_hashes.entry(sem).or_insert_with(|| name.clone());
            }
        }
    }

    /// `blake3:<hex>` digest over the baseline shard bytes.
    #[must_use]
    pub fn digest(&self) -> &str {
        &self.digest
    }

    fn contains_name(&self, name: &str) -> bool {
        match &self.backend {
            BaselineBackend::InMemory { names, .. } => names.contains(name),
            BaselineBackend::Index(index) => index.contains_name(name),
        }
    }

    fn statement_match(&self, statement_hash: &str) -> Option<&str> {
        match &self.backend {
            BaselineBackend::InMemory {
                statement_hashes, ..
            } => statement_hashes.get(statement_hash).map(String::as_str),
            BaselineBackend::Index(index) => index.lookup_statement_hash(statement_hash),
        }
    }

    /// Corpus lookup of a candidate's Cake env-free Tier-1.5 rewrite-canonical
    /// digest — "is this the same object in a different form?". Always misses
    /// against a v1 index (no semantic table).
    fn semantic_match(&self, semantic_digest: &str) -> Option<&str> {
        match &self.backend {
            BaselineBackend::InMemory {
                semantic_hashes, ..
            } => semantic_hashes.get(semantic_digest).map(String::as_str),
            BaselineBackend::Index(index) => index.lookup_semantic(semantic_digest),
        }
    }

    /// Novelty against the baseline corpus. Priority: exact name, then structural
    /// statement-hash — these are CONFIRMED duplicates (`Duplicate`, blocking). Then,
    /// when the candidate supplies its env-free Tier-1.5 `semantic_digest` (under
    /// `--score`), an UNCONFIRMED SEMANTIC bucket match — "same object, different form".
    ///
    /// A semantic-digest hit is reported as **`New`** with `matched_name` + `SemanticDigest`
    /// as an *informational, non-blocking* alternate-form annotation — NOT a `Duplicate`.
    /// The corpus index stores only digest prefixes, so no `same_object` arbiter can confirm
    /// it (the Tier-1.5 digest collapses commutative reorderings like `a = b` / `b = a`,
    /// which are distinct statements). Treating it as a blocking duplicate would suppress a
    /// genuinely-novel theorem; instead the candidate stays novel-by-exact-identity and the
    /// alternate form is recorded for search/uniqueness. `semantic_digest = None` skips the
    /// probe entirely, so default runs are byte-identical regardless of the baseline's table.
    fn novelty_of(
        &self,
        name: &str,
        statement_hash: &str,
        semantic_digest: Option<&str>,
    ) -> NoveltyFacts {
        if self.contains_name(name) {
            return NoveltyFacts {
                method: novelty_method(Some(NoveltyMatchKind::Name)),
                verdict: NoveltyVerdict::Duplicate,
                matched_name: Some(name.to_string()),
                match_kind: Some(NoveltyMatchKind::Name),
            };
        }
        if let Some(matched) = self.statement_match(statement_hash) {
            return NoveltyFacts {
                method: novelty_method(Some(NoveltyMatchKind::StatementHash)),
                verdict: NoveltyVerdict::Duplicate,
                matched_name: Some(matched.to_string()),
                match_kind: Some(NoveltyMatchKind::StatementHash),
            };
        }
        if let Some(matched) = semantic_digest.and_then(|d| self.semantic_match(d)) {
            // Unconfirmed Tier-1.5 bucket: New (novel by exact identity) with the alternate
            // form recorded. Never blocks — see the doc above and `evaluate_candidate` Step 3.
            return NoveltyFacts {
                method: novelty_method(Some(NoveltyMatchKind::SemanticDigest)),
                verdict: NoveltyVerdict::New,
                matched_name: Some(matched.to_string()),
                match_kind: Some(NoveltyMatchKind::SemanticDigest),
            };
        }
        NoveltyFacts {
            method: novelty_method(None),
            verdict: NoveltyVerdict::New,
            matched_name: None,
            match_kind: None,
        }
    }
}

/// The novelty-method label. A `SemanticDigest` match additionally applied the env-free
/// Tier-1.5 rewrite-canonical primitive; every other branch used only `name+statement-hash`
/// (so default, no-`--score` runs — which never reach the semantic branch — keep the exact
/// historical string, preserving binding-digest determinism).
fn novelty_method(kind: Option<NoveltyMatchKind>) -> String {
    match kind {
        Some(NoveltyMatchKind::SemanticDigest) => {
            "name+statement-hash+tier1.5-rewrite-canonical".to_string()
        }
        _ => "name+statement-hash".to_string(),
    }
}

pub(crate) fn collect_shard_paths(path: &Path) -> MathverseResult<Vec<PathBuf>> {
    if path.is_file() {
        return Ok(vec![path.to_path_buf()]);
    }
    let mut out = Vec::new();
    collect_shards_recursive(path, &mut out)?;
    out.sort();
    Ok(out)
}

fn collect_shards_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> MathverseResult<()> {
    for entry in std::fs::read_dir(dir).map_err(MathverseError::Io)? {
        let path = entry.map_err(MathverseError::Io)?.path();
        if path.is_dir() {
            collect_shards_recursive(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "mathverse") {
            out.push(path);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Expression helpers
// ---------------------------------------------------------------------------

/// Collect every constant name referenced by `expr`.
///
/// Beyond `Const` nodes this includes the two implicit reference forms the
/// kernel resolves by name during type checking — both of which a
/// dependency-closure walk must therefore treat as references:
/// - `Proj(struct_name, …)`: projection typing looks up `struct_name`'s
///   inductive + constructor in the environment;
/// - `Lit(Nat …)` / `Lit(String …)`: literal inference types them at
///   `Const(Nat)` / `Const(String)`.
pub(crate) fn collect_constant_refs(expr: &Expr) -> HashSet<String> {
    struct ConstCollector;

    impl ExprVisitor for ConstCollector {
        type Result = HashSet<String>;

        fn combine(&self, mut a: Self::Result, b: Self::Result) -> Self::Result {
            a.extend(b);
            a
        }

        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
            HashSet::from([name.to_string()])
        }

        fn visit_lit(&mut self, lit: &clean_kernel::expr::Literal) -> Self::Result {
            match lit {
                clean_kernel::expr::Literal::Nat(_) => HashSet::from(["Nat".to_string()]),
                clean_kernel::expr::Literal::String(_) => HashSet::from(["String".to_string()]),
            }
        }
    }

    let mut refs = ConstCollector.visit_expr(expr);
    collect_proj_struct_names(expr, &mut refs);
    refs
}

/// Collect every `Proj` struct name in `expr` (the visitor's main dispatch
/// only descends into the projected term, dropping the head name).
fn collect_proj_struct_names(expr: &Expr, out: &mut HashSet<String>) {
    use clean_kernel::expr::ExprKind;
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Proj(struct_name, _, inner) => {
                out.insert(struct_name.to_string());
                stack.push(inner);
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) => stack.push(inner),
            _ => {}
        }
    }
}

/// Rewrite every fully-applied kernel-transparent annotation gadget to its
/// underlying type, everywhere in `expr`: `autoParam α tac` / `optParam α
/// default` → `α`, `outParam α` / `semiOutParam α` → `α`.
///
/// Lean's gadgets are definitionally transparent (`autoParam α tac := α`),
/// so the rewrite is defeq-preserving — the kernel accepts the erased
/// object wherever it accepted the annotated one. The gate erases them from
/// every CARRIED constant (type and value) for the same reason the v3
/// family carry erases telescopes: the payloads (`*._autoParam :
/// Lean.Syntax` tactic defaults) would otherwise drag the nested
/// out-of-fence `Lean.Syntax` family — pure elaborator metadata — into the
/// carry closure of ordinary mathlib/toolchain proofs (`Lean.Omega.*`).
/// Partial gadget applications are left untouched (fail-closed: the gadget
/// constant itself then resolves like any dependency).
pub(crate) fn erase_annotation_gadgets(expr: &Expr) -> Expr {
    use clean_kernel::expr::ExprKind;
    fn gadget_target(e: &Expr) -> Option<&Expr> {
        let head = e.get_app_fn();
        let ExprKind::Const(name, _) = head.kind() else {
            return None;
        };
        let arity = match name.to_string().as_str() {
            "autoParam" | "optParam" => 2,
            "outParam" | "semiOutParam" => 1,
            _ => return None,
        };
        let args = e.get_app_args();
        (args.len() == arity).then(|| args[0])
    }
    fn go(e: &Expr) -> Expr {
        if let Some(target) = gadget_target(e) {
            return go(target);
        }
        match e.kind() {
            ExprKind::App(f, a) => Expr::app(go(f), go(a)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, go(ty), go(body)),
            ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, go(ty), go(body)),
            ExprKind::Let(n, ty, val, body, nd) => {
                Expr::let_named(n.clone(), go(ty), go(val), go(body), *nd)
            }
            ExprKind::Proj(n, i, inner) => Expr::proj(n.clone(), *i, go(inner)),
            _ => e.clone(),
        }
    }
    go(expr)
}

// ---------------------------------------------------------------------------
// Gate state (v2 definitions + v3 inductive families)
// ---------------------------------------------------------------------------

/// A definition-valued dependency that passed its own kernel re-check and is
/// available for carrying into the shard.
struct CarriedDefState {
    entry: CarriedDefinition,
    decl: Declaration,
    /// Sorted constant refs of the definition's type + value (closure walks).
    refs: Vec<String>,
}

/// A theorem-valued dependency that passed its own kernel re-check (WITH its
/// proof value) and is available for carrying into the shard (v3.1).
struct CarriedThmState {
    entry: CarriedTheorem,
    decl: Declaration,
    /// Sorted constant refs of the theorem's type + value (closure walks).
    refs: Vec<String>,
}

/// One carried dependency: a kernel re-checked definition (v2), a kernel
/// re-checked inductive family (v3), or a kernel re-checked theorem (v3.1).
/// Insertion order is dependency order for all three — an item's
/// dependencies are always carried before it.
enum CarriedItem {
    Definition(CarriedDefState),
    Family(CarriedFamilyState),
    Theorem(CarriedThmState),
}

impl CarriedItem {
    /// Key under which the item is appended to the shard write list (the
    /// definition/theorem name / the family root).
    fn key(&self) -> &str {
        match self {
            Self::Definition(def) => &def.entry.name,
            Self::Family(fam) => &fam.root,
            Self::Theorem(thm) => &thm.entry.name,
        }
    }

    fn refs(&self) -> &[String] {
        match self {
            Self::Definition(def) => &def.refs,
            Self::Family(fam) => &fam.refs,
            Self::Theorem(thm) => &thm.refs,
        }
    }

    fn required_by_mut(&mut self) -> &mut Vec<String> {
        match self {
            Self::Definition(def) => &mut def.entry.required_by,
            Self::Family(fam) => &mut fam.entry.required_by,
            Self::Theorem(thm) => &mut thm.entry.required_by,
        }
    }
}

/// One shard-bound write entry, in write order.
enum ShardEntry {
    /// A carried definition or an accepted theorem.
    Decl { name: String, decl: Declaration },
    /// A carried inductive family (index into `GateState::carried`); its
    /// member constants are emitted at write time, after the run's full
    /// referenced-name set is known.
    Family { carried_idx: usize },
}

/// Recheck-environment base for one graduation run (v3.2).
///
/// The recheck environment satisfies dependencies BY NAME: any constant
/// already present silently shadows the source spelling. The base therefore
/// determines what can be shadowed — and the 2026-06-12 kernel-parity sweep
/// showed Clean's prelude shadows the Lean toolchain with dozens of
/// non-Lean-faithful objects (overlay `Monoid`, Opaque `Nat.mod`, …). See
/// [`super::shadow`] for the fail-closed guard either base runs under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecheckBase {
    /// `Environment::with_prelude()` — Clean's native prelude. Correct when
    /// the source environment derives from the same prelude (the
    /// `--env native` lane), where name-identity implies object-identity.
    CleanPrelude,
    /// Shadow-free Lean-core base: kernel builtins only (Quot primitives +
    /// native literal reducers; no prelude constants). Everything else is
    /// carried from the source environment through the checked add paths —
    /// the base for `.olean`-sourced runs, where the source of truth is the
    /// imported toolchain, not Clean's prelude.
    LeanCore,
}

impl RecheckBase {
    /// Label recorded in the graduation record (and selecting the cake-gate
    /// replay base).
    #[must_use]
    pub fn record_label(self) -> &'static str {
        match self {
            Self::CleanPrelude => "clean-prelude",
            Self::LeanCore => "lean-core",
        }
    }

    /// Replay one inductive family against `env` under this base's
    /// generated-member policy: the Lean-core lane uses the kernel-
    /// certificate-only replay (`add_inductive_core`) so the SOURCE
    /// spellings of the generated convenience definitions (`noConfusionType`
    /// etc.) carry as ordinary checked definitions instead of being shadowed
    /// by Clean's non-Lean-faithful twins; the Clean-prelude lane keeps the
    /// full generation (native content may reference Clean's spellings).
    ///
    /// # Errors
    ///
    /// Propagates the kernel's `add_inductive` rejection.
    pub(crate) fn add_family(
        self,
        env: &mut Environment,
        decl: clean_kernel::inductive::InductiveDecl,
    ) -> Result<(), clean_kernel::KernelEnvError> {
        match self {
            Self::CleanPrelude => env.add_inductive(decl),
            Self::LeanCore => env.add_inductive_core(decl),
        }
    }

    /// Build the recheck environment for this base.
    pub(crate) fn build(self) -> Environment {
        match self {
            Self::CleanPrelude => Environment::with_prelude(),
            Self::LeanCore => {
                use clean_kernel::env::TrustedEnvExt as _;
                let mut env = Environment::default();
                env.init_quot();
                env.init_native_reducers();
                env.init_arith_native_reducers();
                // The deterministic re-check budget stays at the kernel
                // default. Known wall (kernel-parity sweep, 2026-06-12):
                // `Lean.Omega.tidy_sat` / `Nat.Linear.Poly.*cancelAux`
                // exceed any practical budget under Clean's current
                // whnf/def-eq (a 100x budget burned gigabytes and minutes
                // before the same fail-closed verdict; an unlimited probe
                // did not finish in 40 minutes) — a kernel PERFORMANCE
                // parity divergence, recorded as such, never laundered.
                env
            }
        }
    }
}

/// In-flight state of one graduation run: the fresh recheck environment plus
/// everything the gate has learned about candidates and carried dependencies.
pub(super) struct GateState {
    pub(super) recheck: Environment,
    /// Which base `recheck` was built from (recorded; selects replay base
    /// and the family replay's generated-member policy).
    pub(super) base: RecheckBase,
    /// Memoized shadow-faithfulness verdicts (v3.2; see [`super::shadow`]).
    shadow: super::shadow::ShadowChecks,
    rejected_names: HashSet<String>,
    /// statement-hash -> name of the earlier ACCEPTED candidate carrying it
    /// (intra-run half of the novelty dedup; see module doc, step 3).
    run_statements: HashMap<String, String>,
    /// Tier-1.5 rewrite-canonical digest -> name of the earlier ACCEPTED
    /// candidate carrying it. The SEMANTIC intra-run dedup: catches "same
    /// object, different form" within a run. Populated only under `--score`.
    run_semantic: HashMap<String, String>,
    /// Kernel-rechecked carried items in `recheck`-insertion (dependency)
    /// order.
    carried: Vec<CarriedItem>,
    /// name -> index into `carried`. Definitions map their own name; carried
    /// families map the root AND every member `add_inductive` generated, so
    /// a reference to any member finds its family.
    pub(super) carried_idx: HashMap<String, usize>,
    /// Definitions whose kernel re-check failed: name -> reject reason.
    /// Cached so every later dependent fails fast with the same audit trail.
    failed_defs: HashMap<String, String>,
    /// Theorems whose kernel re-check failed: name -> reject reason (the
    /// v3.1 mirror of `failed_defs`).
    failed_theorems: HashMap<String, String>,
    /// Inductive families whose carry failed: family root -> reject reason
    /// (the v3 mirror of `failed_defs`; fence rejections cache here too).
    pub(super) failed_families: HashMap<String, String>,
    /// Declarations destined for the shard, in write order (each carried
    /// item strictly precedes its first user).
    shard_decls: Vec<ShardEntry>,
    /// Carried-item keys already pushed into `shard_decls`.
    appended: HashSet<String>,
    /// Every constant name referenced by accepted shard-bound content
    /// (theorem types/values plus all carried items' refs). Decides which
    /// generated recursor members each carried family writes into the shard.
    referenced: HashSet<String>,
}

impl GateState {
    pub(super) fn new(base: RecheckBase) -> Self {
        Self {
            recheck: base.build(),
            base,
            shadow: super::shadow::ShadowChecks::default(),
            rejected_names: HashSet::new(),
            run_statements: HashMap::new(),
            run_semantic: HashMap::new(),
            carried: Vec::new(),
            carried_idx: HashMap::new(),
            failed_defs: HashMap::new(),
            failed_theorems: HashMap::new(),
            failed_families: HashMap::new(),
            shard_decls: Vec::new(),
            appended: HashSet::new(),
            referenced: HashSet::new(),
        }
    }

    /// v3.1: register a candidate that was rejected ONLY by the duplicate
    /// novelty policy as carried supporting material.
    ///
    /// Such a candidate is already in the recheck environment through its
    /// own checked `add_decl` (step 1) with a foundational-only closure
    /// (step 2) — the kernel facts are real; only the CANDIDATE policy said
    /// no. Without this registration the constant would satisfy later
    /// dependency resolution from the recheck env while never reaching the
    /// shard — an incomplete-shard hole the cake gate would fail-close on.
    /// With it, dependents graduate and the duplicate enters the shard as a
    /// carried theorem whose honest `duplicate` novelty travels into the
    /// record's `carried_theorems` section.
    fn register_duplicate_candidate_as_carried(
        &mut self,
        entry: &GraduatedTheorem,
        refs: Vec<String>,
        decl: Declaration,
    ) {
        let carried_entry = CarriedTheorem {
            name: entry.name.clone(),
            decl_kind: entry.decl_kind.clone(),
            statement_hash: entry.statement_hash.clone(),
            proof_hash: entry.proof_hash.clone(),
            kernel: KernelFacts {
                verdict: KernelVerdict::KernelVerified,
                value_typechecked: true,
                family_checked: false,
                checker: format!("clean-kernel {}", env!("CARGO_PKG_VERSION")),
            },
            // Step 2 just verified the foundational-only closure.
            axiom_closure: entry.axiom_closure.clone(),
            // The candidate evaluation's honest duplicate verdict (baseline
            // or intra-run) — carried as-is, never re-laundered to `new`.
            novelty: entry.novelty.clone(),
            required_by: Vec::new(),
        };
        self.carried_idx
            .insert(entry.name.clone(), self.carried.len());
        self.carried.push(CarriedItem::Theorem(CarriedThmState {
            entry: carried_entry,
            decl,
            refs,
        }));
    }

    /// Register a successfully re-checked inductive family: every member
    /// name maps to the family's carried index for closure walks.
    pub(super) fn register_family(&mut self, family: CarriedFamilyState) {
        let idx = self.carried.len();
        self.carried_idx.insert(family.root.clone(), idx);
        for member in &family.member_names {
            self.carried_idx.insert(member.clone(), idx);
        }
        self.carried.push(CarriedItem::Family(family));
    }

    /// Carried-item indices transitively reachable from `refs`, ascending
    /// (= dependency order, since `carried` is insertion-ordered and an
    /// item's dependencies were carried before it).
    fn carried_closure(&self, refs: &[String]) -> Vec<usize> {
        let mut seen: HashSet<usize> = HashSet::new();
        let mut queue: Vec<&str> = refs.iter().map(String::as_str).collect();
        while let Some(dep) = queue.pop() {
            if let Some(&idx) = self.carried_idx.get(dep) {
                if seen.insert(idx) {
                    queue.extend(self.carried[idx].refs().iter().map(String::as_str));
                }
            }
        }
        let mut indices: Vec<usize> = seen.into_iter().collect();
        indices.sort_unstable();
        indices
    }

    /// Record an accepted theorem: append its not-yet-written carried items
    /// (dependency order) and then the theorem itself to the shard write
    /// list, stamping `required_by` on each item and accumulating the
    /// referenced-name set that drives family member emission.
    fn accept(
        &mut self,
        name: &str,
        refs: &[String],
        statement_hash: &str,
        rewrite_digest: Option<&str>,
        decl: Declaration,
    ) {
        self.referenced.extend(refs.iter().cloned());
        for idx in self.carried_closure(refs) {
            let item = &mut self.carried[idx];
            item.required_by_mut().push(name.to_string());
            self.referenced.extend(item.refs().iter().cloned());
            let key = item.key().to_string();
            if self.appended.insert(key.clone()) {
                let entry = match &self.carried[idx] {
                    CarriedItem::Definition(def) => ShardEntry::Decl {
                        name: key,
                        decl: def.decl.clone(),
                    },
                    CarriedItem::Family(_) => ShardEntry::Family { carried_idx: idx },
                    CarriedItem::Theorem(thm) => ShardEntry::Decl {
                        name: key,
                        decl: thm.decl.clone(),
                    },
                };
                self.shard_decls.push(entry);
            }
        }
        self.run_statements
            .entry(statement_hash.to_string())
            .or_insert_with(|| name.to_string());
        if let Some(rd) = rewrite_digest {
            self.run_semantic
                .entry(rd.to_string())
                .or_insert_with(|| name.to_string());
        }
        self.shard_decls.push(ShardEntry::Decl {
            name: name.to_string(),
            decl,
        });
    }

    /// The carried-definition record section: entries for exactly the
    /// definitions written into the shard, in shard order.
    fn carried_record_entries(&self) -> Vec<CarriedDefinition> {
        self.carried
            .iter()
            .filter_map(|item| match item {
                CarriedItem::Definition(def) if self.appended.contains(&def.entry.name) => {
                    Some(def.entry.clone())
                }
                _ => None,
            })
            .collect()
    }

    /// The carried-theorem record section (v3.1): entries for exactly the
    /// theorems written into the shard, in shard order, each stamped with
    /// its HONEST novelty (informational; never a reject verdict —
    /// `on_duplicate` governs candidates, not carried supporting material).
    /// Dependency-carried theorems are evaluated against the baseline here;
    /// duplicate-rejected candidates re-registered as carried keep the
    /// (stronger) verdict their candidate evaluation already earned.
    fn carried_theorem_record_entries(&self, baseline: &GraduationBaseline) -> Vec<CarriedTheorem> {
        self.carried
            .iter()
            .filter_map(|item| match item {
                CarriedItem::Theorem(thm) if self.appended.contains(&thm.entry.name) => {
                    let mut entry = thm.entry.clone();
                    if entry.novelty.verdict == NoveltyVerdict::Unevaluated {
                        // Carried supporting material carries no Cake semantic digest, so the
                        // semantic probe is skipped (name + statement-hash only).
                        entry.novelty =
                            baseline.novelty_of(&entry.name, &entry.statement_hash, None);
                    }
                    Some(entry)
                }
                _ => None,
            })
            .collect()
    }

    /// The shard-bound members of an appended family, in shard order: the
    /// root, every constructor, then exactly the generated recursors the
    /// accepted content references.
    fn family_shard_members(&self, family: &CarriedFamilyState) -> Vec<(String, DeclKind)> {
        let mut members = vec![(family.root.clone(), DeclKind::Inductive)];
        members.extend(
            family
                .ctor_names
                .iter()
                .map(|name| (name.clone(), DeclKind::Constructor)),
        );
        members.extend(
            family
                .recursor_names
                .iter()
                .filter(|name| self.referenced.contains(*name))
                .map(|name| (name.clone(), DeclKind::Recursor)),
        );
        members
    }

    /// The carried-inductive record section: entries for exactly the
    /// families written into the shard, in shard order, with their
    /// `members_in_shard` finalized against the recheck environment.
    fn carried_family_record_entries(&self) -> MathverseResult<Vec<CarriedInductive>> {
        let mut entries = Vec::new();
        for item in &self.carried {
            let CarriedItem::Family(family) = item else {
                continue;
            };
            if !self.appended.contains(&family.root) {
                continue;
            }
            let mut entry = family.entry.clone();
            entry.members_in_shard = self
                .family_shard_members(family)
                .into_iter()
                .map(|(name, kind)| {
                    let info = self
                        .recheck
                        .get_const(&Name::from_string(&name))
                        .ok_or_else(|| {
                            MathverseError::TrustViolation(format!(
                                "graduation internal invariant violated: carried family \
                                 member `{name}` missing from the recheck environment"
                            ))
                        })?;
                    Ok(CarriedInductiveMember {
                        name,
                        decl_kind: family_member_kind_label(kind).to_string(),
                        statement_hash: expr_canonical_digest(&info.type_)?,
                    })
                })
                .collect::<MathverseResult<Vec<_>>>()?;
            entries.push(entry);
        }
        Ok(entries)
    }
}

fn family_member_kind_label(kind: DeclKind) -> &'static str {
    match kind {
        DeclKind::Inductive => "inductive",
        DeclKind::Constructor => "constructor",
        DeclKind::Recursor => "recursor",
        _ => "unsupported",
    }
}

// ---------------------------------------------------------------------------
// graduate()
// ---------------------------------------------------------------------------

/// Run the graduation gate over `candidates` from the live `env`, writing a
/// `SourceSystem::Cake` shard plus its digest-bound `mathverse-graduation-v2`
/// record into `out_dir`.
///
/// Candidates are evaluated in order; a candidate may reference earlier
/// candidates from the same run. Both accepted and rejected candidates are
/// recorded in the returned [`GraduationRecord`].
///
/// # Errors
///
/// Returns an error only for infrastructure failures (I/O, serialization,
/// shard write). Per-candidate failures are *not* errors — they are recorded
/// as rejections so the audit trail stays complete.
pub fn graduate(
    env: &Environment,
    candidates: &[Name],
    req: &GraduationRequest,
    baseline: &GraduationBaseline,
    out_dir: &Path,
) -> MathverseResult<GraduationRecord> {
    graduate_with_base(
        env,
        candidates,
        req,
        baseline,
        out_dir,
        RecheckBase::CleanPrelude,
    )
}

/// [`graduate`] with an explicit recheck base (v3.2): `--env olean` runs use
/// [`RecheckBase::LeanCore`] so the imported toolchain can never be silently
/// shadowed by a non-Lean-faithful prelude object.
///
/// # Errors
///
/// Returns an error only for infrastructure failures (I/O, serialization,
/// shard write); per-candidate failures are recorded as rejections.
pub fn graduate_with_base(
    env: &Environment,
    candidates: &[Name],
    req: &GraduationRequest,
    baseline: &GraduationBaseline,
    out_dir: &Path,
    base: RecheckBase,
) -> MathverseResult<GraduationRecord> {
    graduate_with_base_keep_env(env, candidates, req, baseline, out_dir, base)
        .map(|(record, _recheck)| record)
}

/// As [`graduate_with_base`], but also returns the gate's populated recheck
/// environment — the one in which every accepted candidate and every carried
/// dependency already passed the real `Environment::add_decl` /
/// `add_inductive` kernel re-check this run.
///
/// This is the ENV-FUSION hook: the CLI verb pairs it with
/// [`crate::shard_verify::cake_gate::verify_cake_shard_fused`] so the
/// mandatory verify-side gate discharges its per-constant kernel clause from
/// THIS already-completed pass (via a round-trip oracle against the shard
/// bytes) instead of re-running the identical, dominant-cost kernel work a
/// second time in the same process.
pub fn graduate_with_base_keep_env(
    env: &Environment,
    candidates: &[Name],
    req: &GraduationRequest,
    baseline: &GraduationBaseline,
    out_dir: &Path,
    base: RecheckBase,
) -> MathverseResult<(GraduationRecord, Environment)> {
    let mut state = GateState::new(base);
    let mut seen: HashSet<String> = HashSet::new();
    let mut entries: Vec<GraduatedTheorem> = Vec::new();

    for name in candidates {
        let name_str = name.to_string();
        if !seen.insert(name_str.clone()) {
            entries.push(rejected_entry(
                &name_str,
                "unknown",
                "duplicate-candidate-name",
            ));
            state.rejected_names.insert(name_str);
            continue;
        }
        let entry = evaluate_candidate(env, &mut state, baseline, req, name);
        if !entry.accepted {
            state.rejected_names.insert(entry.name.clone());
        }
        entries.push(entry);
    }

    let record = write_outputs(req, baseline, entries, &state, out_dir)?;
    Ok((record, state.recheck))
}

/// Fuel bound for the opt-in `--score-defeq` kernel normalisation. Far below the
/// `clean_cake::identity` default (200k) so even the expensive defeq path cannot hang for
/// minutes on a heavy mathlib-Real statement; the digest is honestly marked incomplete when
/// the bound is hit.
const SCORE_DEFEQ_FUEL: u32 = 16_384;

/// Evaluate one candidate. On acceptance the theorem (and any newly required
/// carried definitions) are appended to the gate state's shard write list.
fn evaluate_candidate(
    source: &Environment,
    state: &mut GateState,
    baseline: &GraduationBaseline,
    req: &GraduationRequest,
    name: &Name,
) -> GraduatedTheorem {
    let name_str = name.to_string();

    let Some(info) = source.get_const(name) else {
        return rejected_entry(&name_str, "unknown", "missing-from-environment");
    };
    let kind_str = constant_kind_label(info.kind);
    if info.kind != ConstantKind::Theorem {
        return rejected_entry(&name_str, kind_str, "not-a-theorem");
    }
    let Some(value) = info.value.clone() else {
        // A `Theorem` without a stored proof value is `Unchecked` — there is
        // no kernel certificate to re-check, so it can never graduate.
        return rejected_entry(
            &name_str,
            kind_str,
            "missing-proof-value: no kernel certificate to re-check",
        );
    };

    let (statement_hash, proof_hash) = match (
        expr_canonical_digest(&info.type_),
        expr_canonical_digest(&value),
    ) {
        (Ok(s), Ok(p)) => (s, p),
        (Err(e), _) | (_, Err(e)) => {
            return rejected_entry(&name_str, kind_str, &format!("hash-failed: {e}"));
        }
    };

    // Cake semantic identity of the statement, bound under `--score`. The FAST path computes
    // ONLY the env-free `structural_rewrite_digest` (no kernel `whnf`) — the corpus key and
    // the intra-run probe key. The EXPENSIVE defeq Tier-1 identity (kernel normalisation, which
    // can hang for minutes on a heavy mathlib-Real statement) is opt-in via `--score-defeq` and
    // bounded. This split is what makes `--score` viable at olean/mathlib scale.
    let semantic_identity = if req.score_identity {
        let structural_rewrite_digest =
            clean_cake::identity::structural_rewrite_digest(&info.type_);
        let (canonical_digest, rewrite_digest, complete) = if req.score_defeq {
            let tc = clean_kernel::tc::TypeChecker::new(source);
            let sid = clean_cake::identity::defeq_canonical_digest_fueled(
                &tc,
                &info.type_,
                SCORE_DEFEQ_FUEL,
            );
            (
                Some(sid.canonical_digest),
                Some(sid.rewrite_digest),
                Some(sid.complete),
            )
        } else {
            (None, None, None)
        };
        Some(SemanticIdentityRecord {
            structural_rewrite_digest,
            canonical_digest,
            rewrite_digest,
            complete,
        })
    } else {
        None
    };

    // Baseline dedup first — name, then structural statement-hash (CONFIRMED duplicates,
    // blocking), then (under `--score`) an UNCONFIRMED SEMANTIC alternate-form match against
    // the whole corpus (recorded as `New` + `SemanticDigest`, non-blocking — see `novelty_of`).
    // When the baseline is silent, dedup against earlier candidates from THIS run: an exact
    // statement-hash match is a CONFIRMED duplicate (blocking); an intra-run SEMANTIC match
    // (the env-DEPENDENT defeq `rewrite_digest`, stronger than the corpus key since the run's
    // env is available, but still a commutative-collapse heuristic without a same_object
    // arbiter wired in) is likewise recorded as a non-blocking `New` alternate-form note.
    let semantic_corpus_key = semantic_identity
        .as_ref()
        .map(|s| s.structural_rewrite_digest.as_str());
    let mut novelty = baseline.novelty_of(&name_str, &statement_hash, semantic_corpus_key);
    // A confirmed intra-run statement-hash duplicate blocks (and overrides any corpus
    // semantic annotation); only consider it when the baseline did not already confirm a dup.
    if novelty.verdict != NoveltyVerdict::Duplicate {
        if let Some(earlier) = state.run_statements.get(&statement_hash) {
            novelty = NoveltyFacts {
                method: novelty_method(Some(NoveltyMatchKind::StatementHash)),
                verdict: NoveltyVerdict::Duplicate,
                matched_name: Some(earlier.clone()),
                match_kind: Some(NoveltyMatchKind::StatementHash),
            };
        }
    }
    // Intra-run semantic alternate form: only when still novel-by-exact-identity and no
    // alternate form is already recorded. Non-blocking (`New`), like the corpus probe.
    if novelty.verdict == NoveltyVerdict::New && novelty.match_kind.is_none() {
        if let Some(sid) = semantic_identity.as_ref() {
            if let Some(earlier) = state.run_semantic.get(&sid.structural_rewrite_digest) {
                novelty = NoveltyFacts {
                    method: novelty_method(Some(NoveltyMatchKind::SemanticDigest)),
                    verdict: NoveltyVerdict::New,
                    matched_name: Some(earlier.clone()),
                    match_kind: Some(NoveltyMatchKind::SemanticDigest),
                };
            }
        }
    }

    let mut entry = GraduatedTheorem {
        name: name_str.clone(),
        decl_kind: kind_str.to_string(),
        statement_hash,
        proof_hash,
        kernel: rejected_kernel_facts(),
        axiom_closure: empty_axiom_closure(false),
        novelty,
        accepted: false,
        reject_reason: None,
        carried_definitions: Vec::new(),
        carried_inductives: Vec::new(),
        carried_theorems: Vec::new(),
        semantic_identity,
    };

    // Certificate cross-check (corroboration only — never a verdict).
    if let Some(check) = req
        .certificate_cross_checks
        .iter()
        .find(|c| c.theorem == name_str)
    {
        if check.proof_hash != entry.proof_hash {
            entry.reject_reason = Some(format!(
                "certificate-mismatch: project claims proof_hash {} but intake recomputed {}",
                check.proof_hash, entry.proof_hash
            ));
            return entry;
        }
    }

    // v3.1: a candidate that an EARLIER candidate already pulled in as a
    // carried dependency cannot graduate in this run — it is already in the
    // recheck environment as supporting material. Fail closed with guidance
    // (list a theorem before its users to graduate it) rather than letting
    // the kernel's duplicate-declaration error masquerade as a proof defect.
    if state.carried_idx.contains_key(&name_str) {
        entry.reject_reason = Some(format!(
            "already-carried: `{name_str}` was already carried into this run as a dependency \
             of an earlier candidate — order it before its users in the candidate list to \
             graduate it"
        ));
        return entry;
    }

    // Dependency policy: seed axioms, kernel re-check + carry definitions.
    let mut set = collect_constant_refs(&info.type_);
    set.extend(collect_constant_refs(&value));
    let mut refs: Vec<String> = set.into_iter().collect();
    refs.sort();
    if let Err(reason) = resolve_dependencies(source, state, &refs) {
        entry.reject_reason = Some(reason);
        return entry;
    }
    // The carried-dependency set is well-defined once resolution succeeded;
    // record it even when a later step rejects the theorem (audit value).
    for idx in state.carried_closure(&refs) {
        match &state.carried[idx] {
            CarriedItem::Definition(def) => {
                entry.carried_definitions.push(def.entry.name.clone());
            }
            CarriedItem::Family(fam) => entry.carried_inductives.push(fam.root.clone()),
            CarriedItem::Theorem(thm) => entry.carried_theorems.push(thm.entry.name.clone()),
        }
    }
    entry.carried_definitions.sort();
    entry.carried_inductives.sort();
    entry.carried_theorems.sort();

    // Steps 1+2: kernel re-check with the proof value (the only honest path
    // to a KernelVerified verdict) and the transitive axiom closure in the
    // recheck environment — the single shared verdict (see
    // [`super::recheck::recheck_and_classify`]). Carried definitions are
    // present WITH their values, so the closure walks through them: a
    // theorem's closure includes its carried definitions' closures, and an
    // axiom smuggled through a definition is caught here.
    let decl = Declaration::Theorem {
        name: name.clone(),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
        value,
    };
    let verdict = match recheck_and_classify(&mut state.recheck, decl.clone()) {
        Ok(verdict) => verdict,
        Err(e) => {
            entry.reject_reason = Some(e.reject_reason());
            return entry;
        }
    };
    entry.kernel.value_typechecked = verdict.kernel.value_typechecked;
    if verdict.is_foundational() {
        entry.axiom_closure = empty_axiom_closure(true);
    } else {
        entry.axiom_closure = AxiomClosure {
            foundational_only: false,
            domain_axioms: verdict.domain_axioms.clone(),
            axiom_profile_bits: 0,
        };
        entry.reject_reason = Some(format!(
            "axiom-dependent: transitive closure contains non-foundational axioms [{}] — \
             cannot claim {GRADUATION_MIN_TRUST}",
            verdict.domain_axioms.join(", ")
        ));
        return entry;
    }

    // Step 3: novelty policy (candidates only — carried theorems record
    // their baseline novelty honestly but are never rejected by it).
    if entry.novelty.verdict == NoveltyVerdict::Duplicate {
        let matched = entry.novelty.matched_name.clone().unwrap_or_default();
        let scope = if state
            .run_statements
            .get(&entry.statement_hash)
            .is_some_and(|earlier| *earlier == matched)
        {
            if state.carried_idx.contains_key(matched.as_str()) {
                "theorem carried earlier in this run"
            } else {
                "co-graduated candidate"
            }
        } else {
            "baseline"
        };
        let note = match req.on_duplicate {
            OnDuplicate::Reject => String::new(),
            OnDuplicate::AcceptIfSharper => {
                " (accept-if-sharper requested, but sharper detection is not \
                 implemented in graduation v2 — treated as reject)"
                    .to_string()
            }
        };
        entry.reject_reason = Some(format!("duplicate: matches {scope} `{matched}`{note}"));
        // v3.1: the rejection above is pure CANDIDATE policy — the kernel
        // facts (checked add_decl, foundational-only closure) are real and
        // the constant stays in the recheck environment. Register it as
        // carried supporting material so later dependents can graduate over
        // it (see `register_duplicate_candidate_as_carried`).
        state.register_duplicate_candidate_as_carried(&entry, refs, decl);
        return entry;
    }

    entry.kernel.verdict = KernelVerdict::KernelVerified;
    entry.accepted = true;
    // Register the env-free structural key for the intra-run semantic probe (the same key
    // `run_semantic` is queried with above) — cheap, and present under plain `--score`.
    let semantic_key = entry
        .semantic_identity
        .as_ref()
        .map(|s| s.structural_rewrite_digest.as_str());
    state.accept(&name_str, &refs, &entry.statement_hash, semantic_key, decl);
    entry
}

/// Enforce the v3.1 dependency policy against the recheck environment.
///
/// Every referenced constant must be (a) already present in the recheck
/// environment (prelude, an earlier candidate, or an already-carried
/// dependency) and not previously rejected, (b) an axiom in the source
/// environment, which is seeded so the closure check can observe it, (c) a
/// value-bearing definition in the source environment, which is **carried**:
/// its own dependencies are resolved first, then the definition is kernel
/// re-checked with its defining value (`Environment::add_decl`) — a failed
/// re-check fails this candidate and is cached so every later dependent
/// fails too, (d) a member of a kernel-checked **inductive family** in
/// the source environment's side tables, whose whole family is carried
/// through the checked `add_inductive` replay (v3; single-type non-nested
/// fence — see [`super::intake_family`]), or (e) a value-bearing **theorem**
/// in the source environment, which is **carried** (v3.1) under the exact
/// candidate discipline — `add_decl` with the proof value, dependency order,
/// honest baseline novelty recorded but never policy-rejected. Opaque
/// dependencies absent from the recheck environment remain external and
/// rejected — they could never be replayed by the cake gate.
fn resolve_dependencies(
    source: &Environment,
    state: &mut GateState,
    refs: &[String],
) -> Result<(), String> {
    // Rejected candidates kill their dependents — EXCEPT those re-registered
    // as carried supporting material (duplicate-policy rejections, v3.1):
    // those are kernel-verified shard-bound content a dependent may use.
    let rejected_refs: Vec<&str> = refs
        .iter()
        .filter(|r| {
            state.rejected_names.contains(r.as_str()) && !state.carried_idx.contains_key(r.as_str())
        })
        .map(String::as_str)
        .collect();
    if !rejected_refs.is_empty() {
        return Err(format!(
            "rejected-dependency: references candidate(s) already rejected by this gate: {}",
            rejected_refs.join(", ")
        ));
    }

    let mut in_progress: Vec<String> = Vec::new();
    for dep in refs {
        resolve_dependency(source, state, dep, &mut in_progress)?;
    }
    Ok(())
}

/// Depth-first resolution of one dependency (dependencies before users).
pub(super) fn resolve_dependency(
    source: &Environment,
    state: &mut GateState,
    dep: &str,
    in_progress: &mut Vec<String>,
) -> Result<(), String> {
    let dep_name = Name::from_string(dep);
    if state.carried_idx.contains_key(dep) {
        // Already-carried items (including duplicate-policy-rejected
        // candidates re-registered as carried) are shard-bound: dependents
        // may resolve against them.
        return Ok(());
    }
    if state.rejected_names.contains(dep) {
        return Err(format!(
            "rejected-dependency: references candidate(s) already rejected by this gate: {dep}"
        ));
    }
    if state.recheck.get_const(&dep_name).is_some() {
        // v3.2 shadow guard: a recheck-present constant silently SUBSTITUTES
        // for the source spelling — honest only when the two are the same
        // kernel object. Fail closed otherwise (memoized; see shadow.rs).
        let GateState {
            shadow, recheck, ..
        } = state;
        return shadow.guard(source, recheck, dep);
    }
    if let Some(reason) = state.failed_defs.get(dep) {
        return Err(format!(
            "carried-definition-failed: definition `{dep}` already failed its kernel \
             re-check in this run ({reason})"
        ));
    }
    if let Some(reason) = state.failed_theorems.get(dep) {
        return Err(format!(
            "carried-theorem-failed: theorem `{dep}` already failed its kernel re-check \
             in this run ({reason})"
        ));
    }
    if in_progress.iter().any(|n| n == dep) {
        return Err(format!(
            "dependency-cycle: `{dep}` participates in a reference cycle ({})",
            in_progress.join(" -> ")
        ));
    }
    let Some(dep_info) = source.get_const(&dep_name) else {
        return Err(format!(
            "unknown-constant: `{dep}` is neither in the prelude nor the source environment"
        ));
    };

    // v3: inductive-family members (the source env's side tables are the
    // discriminator — `ConstantInfo` alone shows a value-less Definition).
    // The whole family is carried via the checked `add_inductive` replay.
    if let Some(root) = inductive_family_root(source, &dep_name) {
        carry_inductive_family(source, state, &root, in_progress)?;
        if state.recheck.get_const(&dep_name).is_some() {
            return Ok(());
        }
        // v3.2: the kernel-certificate-only family replay (lean-core lane)
        // regenerates types, constructors, and `rec` — NOT the value-bearing
        // eliminator definitions Lean stores (`casesOn`, `recOn`; the
        // importer registers them in the recursor side table for direct
        // iota, but in Lean they are definitions that delta-unfold to
        // `rec`, and replayed proofs need exactly that unfolding). A
        // value-bearing source member therefore falls through and carries
        // as an ORDINARY definition/theorem below; only a value-LESS member
        // missing from the regeneration is a family-replay defect.
        if dep_info.value.is_none() {
            return Err(format!(
                "carried-inductive-failed: family `{root}` was carried but member `{dep}` \
                 was not regenerated by the checked add_inductive replay"
            ));
        }
    }

    match dep_info.kind {
        ConstantKind::Axiom => {
            let dep_type = erase_annotation_gadgets(&dep_info.type_);
            in_progress.push(dep.to_string());
            let result = resolve_refs_of(source, state, &dep_type, None, in_progress);
            in_progress.pop();
            result?;
            state
                .recheck
                .add_decl(Declaration::Axiom {
                    name: dep_name,
                    level_params: dep_info.level_params.clone(),
                    type_: dep_type,
                })
                .map_err(|e| format!("dependency-failed-recheck: axiom `{dep}`: {e}"))
        }
        ConstantKind::Definition => {
            let Some(dep_value) = dep_info.value.as_ref() else {
                return Err(format!(
                    "external-dependency: definition `{dep}` has no stored value — there is \
                     no kernel certificate to re-check, so it cannot be carried"
                ));
            };
            // v3.2: kernel-transparent annotation gadgets are erased from
            // every carried object (see `erase_annotation_gadgets`).
            let dep_type = erase_annotation_gadgets(&dep_info.type_);
            let dep_value = erase_annotation_gadgets(dep_value);
            in_progress.push(dep.to_string());
            let result = resolve_refs_of(source, state, &dep_type, Some(&dep_value), in_progress);
            in_progress.pop();
            result?;
            // Resolving the definition's own refs may have carried an
            // inductive family whose `add_inductive` already regenerated a
            // constant of this name (e.g. a source-side `noConfusion`
            // definition for a family carried via its root). The dependent
            // is then checked against the regenerated constant; re-adding
            // would be a duplicate.
            if state.recheck.get_const(&dep_name).is_some() {
                return Ok(());
            }
            carry_definition(state, dep, dep_info, dep_type, dep_value)
        }
        // v3.1: theorem-valued dependencies are CARRIED under the exact same
        // kernel discipline as candidates — `add_decl` with the proof value
        // in dependency order. A carried theorem is supporting material: it
        // never enters `result.accepted` and the on-duplicate policy does
        // not apply to it (its baseline novelty is recorded honestly in the
        // record's `carried_theorems` section instead).
        ConstantKind::Theorem => {
            let Some(dep_value) = dep_info.value.as_ref() else {
                return Err(format!(
                    "external-dependency: theorem `{dep}` has no stored proof value — there \
                     is no kernel certificate to re-check, so it cannot be carried"
                ));
            };
            let dep_type = erase_annotation_gadgets(&dep_info.type_);
            let dep_value = erase_annotation_gadgets(dep_value);
            in_progress.push(dep.to_string());
            let result = resolve_refs_of(source, state, &dep_type, Some(&dep_value), in_progress);
            in_progress.pop();
            result?;
            // Same regeneration guard as definitions: resolving the
            // theorem's own refs may have carried a family that regenerated
            // a constant of this name.
            if state.recheck.get_const(&dep_name).is_some() {
                return Ok(());
            }
            carry_theorem(state, dep, dep_info, dep_type, dep_value)
        }
        // v3.2: opaque dependencies are CARRIED under the same add_decl
        // discipline (Lean stores a kernel-checked consistency witness as
        // the opaque's value; `Declaration::Opaque` preserves the
        // never-delta-unfold semantics, so recheck defeq matches Lean's).
        // mathlib's `irreducible_def` wrappers (`Real.wrapped.*`,
        // `String.Internal.append`) are exactly this shape.
        ConstantKind::Opaque => {
            let Some(dep_value) = dep_info.value.as_ref() else {
                return Err(format!(
                    "external-dependency: `{dep}` (opaque) has no stored value — there is \
                     no kernel certificate to re-check, so it cannot be carried"
                ));
            };
            let dep_type = erase_annotation_gadgets(&dep_info.type_);
            let dep_value = erase_annotation_gadgets(dep_value);
            in_progress.push(dep.to_string());
            let result = resolve_refs_of(source, state, &dep_type, Some(&dep_value), in_progress);
            in_progress.pop();
            result?;
            if state.recheck.get_const(&dep_name).is_some() {
                return Ok(());
            }
            carry_opaque(state, dep, dep_info, dep_type, dep_value)
        }
    }
}

/// Resolve every constant referenced by `type_` (and `value`, when given).
fn resolve_refs_of(
    source: &Environment,
    state: &mut GateState,
    type_: &Expr,
    value: Option<&Expr>,
    in_progress: &mut Vec<String>,
) -> Result<(), String> {
    let mut inner_refs = collect_constant_refs(type_);
    if let Some(value) = value {
        inner_refs.extend(collect_constant_refs(value));
    }
    let mut inner_refs: Vec<String> = inner_refs.into_iter().collect();
    inner_refs.sort();
    for inner in &inner_refs {
        resolve_dependency(source, state, inner, in_progress)?;
    }
    Ok(())
}

/// Kernel re-check a definition with its value and register it as carried.
///
/// Fail-closed: a definition whose value the kernel rejects is cached in
/// `failed_defs` (killing every dependent), never downgraded.
fn carry_definition(
    state: &mut GateState,
    dep: &str,
    dep_info: &clean_kernel::ConstantInfo,
    dep_type: Expr,
    dep_value: Expr,
) -> Result<(), String> {
    let (statement_hash, value_hash) = match (
        expr_canonical_digest(&dep_type),
        expr_canonical_digest(&dep_value),
    ) {
        (Ok(s), Ok(v)) => (s, v),
        (Err(e), _) | (_, Err(e)) => {
            let reason = format!("hash-failed: {e}");
            state.failed_defs.insert(dep.to_string(), reason.clone());
            return Err(format!(
                "carried-definition-failed: definition `{dep}`: {reason}"
            ));
        }
    };
    let mut set = collect_constant_refs(&dep_type);
    set.extend(collect_constant_refs(&dep_value));
    let mut refs: Vec<String> = set.into_iter().collect();
    refs.sort();
    let decl = Declaration::Definition {
        name: Name::from_string(dep),
        level_params: dep_info.level_params.clone(),
        type_: dep_type,
        value: dep_value,
        is_reducible: dep_info.is_reducible,
    };
    // Kernel re-check + honest closure via the single shared verdict (see
    // [`super::recheck::recheck_and_classify`]): `domain_axioms` is the
    // non-foundational axioms in the definition's transitive closure (type +
    // value). A carried definition RECORDS its closure (never rejects on it) —
    // the dependent candidate's own foundational-only check does the rejecting.
    let verdict = match recheck_and_classify(&mut state.recheck, decl.clone()) {
        Ok(verdict) => verdict,
        Err(e) => {
            let reason = e.reject_reason();
            state.failed_defs.insert(dep.to_string(), reason.clone());
            return Err(format!(
                "carried-definition-failed: definition `{dep}` did not pass its kernel \
                 re-check ({reason})"
            ));
        }
    };
    let domain_axioms = verdict.domain_axioms;
    let entry = CarriedDefinition {
        name: dep.to_string(),
        decl_kind: constant_kind_label(ConstantKind::Definition).to_string(),
        statement_hash,
        value_hash,
        is_reducible: dep_info.is_reducible,
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified,
            value_typechecked: true,
            family_checked: false,
            checker: format!("clean-kernel {}", env!("CARGO_PKG_VERSION")),
        },
        axiom_closure: AxiomClosure {
            foundational_only: domain_axioms.is_empty(),
            domain_axioms,
            axiom_profile_bits: 0,
        },
        required_by: Vec::new(),
    };
    state
        .carried_idx
        .insert(dep.to_string(), state.carried.len());
    state.carried.push(CarriedItem::Definition(CarriedDefState {
        entry,
        decl,
        refs,
    }));
    Ok(())
}

/// Kernel re-check an opaque constant with its stored consistency witness
/// and register it as carried (v3.2). `Declaration::Opaque` preserves Lean's
/// never-delta-unfold semantics, so recheck-environment defeq matches the
/// source kernel's. Recorded in `carried_definitions` with `decl_kind:
/// "opaque"`; fail-closed caching mirrors `carry_definition`.
fn carry_opaque(
    state: &mut GateState,
    dep: &str,
    dep_info: &clean_kernel::ConstantInfo,
    dep_type: Expr,
    dep_value: Expr,
) -> Result<(), String> {
    let (statement_hash, value_hash) = match (
        expr_canonical_digest(&dep_type),
        expr_canonical_digest(&dep_value),
    ) {
        (Ok(s), Ok(v)) => (s, v),
        (Err(e), _) | (_, Err(e)) => {
            let reason = format!("hash-failed: {e}");
            state.failed_defs.insert(dep.to_string(), reason.clone());
            return Err(format!(
                "carried-definition-failed: opaque `{dep}`: {reason}"
            ));
        }
    };
    let mut set = collect_constant_refs(&dep_type);
    set.extend(collect_constant_refs(&dep_value));
    let mut refs: Vec<String> = set.into_iter().collect();
    refs.sort();
    let decl = Declaration::Opaque {
        name: Name::from_string(dep),
        level_params: dep_info.level_params.clone(),
        type_: dep_type,
        value: dep_value,
    };
    if let Err(e) = state.recheck.add_decl(decl.clone()) {
        let reason = format!("kernel-rejected: {e}");
        state.failed_defs.insert(dep.to_string(), reason.clone());
        return Err(format!(
            "carried-definition-failed: opaque `{dep}` did not pass its kernel \
             re-check ({reason})"
        ));
    }
    let mut domain_axioms: Vec<String> = state
        .recheck
        .axiom_deps(&Name::from_string(dep))
        .map(|axioms| axioms.iter().map(Name::to_string).collect())
        .unwrap_or_default();
    domain_axioms.sort();
    let entry = CarriedDefinition {
        name: dep.to_string(),
        decl_kind: constant_kind_label(ConstantKind::Opaque).to_string(),
        statement_hash,
        value_hash,
        is_reducible: false,
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified,
            value_typechecked: true,
            family_checked: false,
            checker: format!("clean-kernel {}", env!("CARGO_PKG_VERSION")),
        },
        axiom_closure: AxiomClosure {
            foundational_only: domain_axioms.is_empty(),
            domain_axioms,
            axiom_profile_bits: 0,
        },
        required_by: Vec::new(),
    };
    state
        .carried_idx
        .insert(dep.to_string(), state.carried.len());
    state.carried.push(CarriedItem::Definition(CarriedDefState {
        entry,
        decl,
        refs,
    }));
    Ok(())
}

/// Kernel re-check a theorem WITH its proof value and register it as carried
/// (v3.1) — the exact `add_decl` discipline candidates go through.
///
/// Fail-closed: a theorem whose proof the kernel rejects is cached in
/// `failed_theorems` (killing every dependent), never downgraded. The
/// entry's `novelty` stays `Unevaluated` here and is stamped with the honest
/// baseline verdict at record-write time (informational only — a carried
/// corpus duplicate is FINE; the on-duplicate policy governs candidates).
fn carry_theorem(
    state: &mut GateState,
    dep: &str,
    dep_info: &clean_kernel::ConstantInfo,
    dep_type: Expr,
    dep_value: Expr,
) -> Result<(), String> {
    let (statement_hash, proof_hash) = match (
        expr_canonical_digest(&dep_type),
        expr_canonical_digest(&dep_value),
    ) {
        (Ok(s), Ok(p)) => (s, p),
        (Err(e), _) | (_, Err(e)) => {
            let reason = format!("hash-failed: {e}");
            state
                .failed_theorems
                .insert(dep.to_string(), reason.clone());
            return Err(format!("carried-theorem-failed: theorem `{dep}`: {reason}"));
        }
    };
    let mut set = collect_constant_refs(&dep_type);
    set.extend(collect_constant_refs(&dep_value));
    let mut refs: Vec<String> = set.into_iter().collect();
    refs.sort();
    let decl = Declaration::Theorem {
        name: Name::from_string(dep),
        level_params: dep_info.level_params.clone(),
        type_: dep_type,
        value: dep_value,
    };
    if let Err(e) = state.recheck.add_decl(decl.clone()) {
        let reason = format!("kernel-rejected: {e}");
        state
            .failed_theorems
            .insert(dep.to_string(), reason.clone());
        return Err(format!(
            "carried-theorem-failed: theorem `{dep}` did not pass its kernel re-check \
             ({reason})"
        ));
    }

    // Honest closure contribution: `axiom_deps` walks the proof value, so
    // closure composition is transitive — a dependent candidate's closure
    // includes this theorem's closure, and an axiom smuggled through a
    // carried proof still rejects the candidate as `axiom-dependent`.
    let mut domain_axioms: Vec<String> = state
        .recheck
        .axiom_deps(&Name::from_string(dep))
        .map(|axioms| axioms.iter().map(Name::to_string).collect())
        .unwrap_or_default();
    domain_axioms.sort();
    let entry = CarriedTheorem {
        name: dep.to_string(),
        decl_kind: constant_kind_label(ConstantKind::Theorem).to_string(),
        statement_hash: statement_hash.clone(),
        proof_hash,
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified,
            value_typechecked: true,
            family_checked: false,
            checker: format!("clean-kernel {}", env!("CARGO_PKG_VERSION")),
        },
        axiom_closure: AxiomClosure {
            foundational_only: domain_axioms.is_empty(),
            domain_axioms,
            axiom_profile_bits: 0,
        },
        novelty: NoveltyFacts {
            method: novelty_method(None),
            verdict: NoveltyVerdict::Unevaluated,
            matched_name: None,
            match_kind: None,
        },
        required_by: Vec::new(),
    };
    // Intra-run statement dedup: the carried statement is corpus-to-be, so a
    // LATER candidate restating it is a duplicate (best-effort — same scope
    // as the accepted-candidate half; see module doc, step 3).
    state
        .run_statements
        .entry(statement_hash)
        .or_insert_with(|| dep.to_string());
    state
        .carried_idx
        .insert(dep.to_string(), state.carried.len());
    state
        .carried
        .push(CarriedItem::Theorem(CarriedThmState { entry, decl, refs }));
    Ok(())
}

// ---------------------------------------------------------------------------
// Shard + record assembly
// ---------------------------------------------------------------------------

fn write_outputs(
    req: &GraduationRequest,
    baseline: &GraduationBaseline,
    entries: Vec<GraduatedTheorem>,
    state: &GateState,
    out_dir: &Path,
) -> MathverseResult<GraduationRecord> {
    let carried_entries = state.carried_record_entries();
    let carried_family_entries = state.carried_family_record_entries()?;
    let carried_theorem_entries = state.carried_theorem_record_entries(baseline);
    // Defense-in-depth (should be unreachable): a carried item can only be
    // appended via an ACCEPTED theorem, whose foundational-only closure
    // subsumes the item's — and carried families fail closed on a
    // non-foundational union closure at carry time. Refuse to write a shard
    // that would contradict either invariant rather than emitting it.
    if let Some(bad) = carried_entries
        .iter()
        .find(|c| !c.axiom_closure.foundational_only)
    {
        return Err(MathverseError::TrustViolation(format!(
            "graduation internal invariant violated: carried definition `{}` with \
             non-foundational closure reached the shard write path",
            bad.name
        )));
    }
    if let Some(bad) = carried_family_entries
        .iter()
        .find(|c| !c.axiom_closure.foundational_only || !c.kernel.family_checked)
    {
        return Err(MathverseError::TrustViolation(format!(
            "graduation internal invariant violated: carried inductive family `{}` \
             without a foundational-only family-checked certificate reached the shard \
             write path",
            bad.name
        )));
    }
    if let Some(bad) = carried_theorem_entries
        .iter()
        .find(|c| !c.axiom_closure.foundational_only || !c.kernel.value_typechecked)
    {
        return Err(MathverseError::TrustViolation(format!(
            "graduation internal invariant violated: carried theorem `{}` without a \
             foundational-only value-typechecked certificate reached the shard write path",
            bad.name
        )));
    }
    std::fs::create_dir_all(out_dir).map_err(MathverseError::Io)?;
    let shard_filename = req
        .shard_filename
        .clone()
        .unwrap_or_else(|| format!("{}-graduated.mathverse", req.project_name));
    let decided_at = req.decided_at_epoch_s.unwrap_or_else(|| {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    });

    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let mut const_indices: Vec<(u32, String)> = Vec::new();
    for entry in &state.shard_decls {
        match entry {
            ShardEntry::Decl { name, decl } => {
                let idx = builder
                    .add_declaration(decl, &[])
                    .map_err(|e| e.constant_name(name))?;
                // `add_declaration` stamps name-heuristic content bits into the
                // profile (`FLOAT_APPROX | NN_ABSTRACTION` for `NNVerify.*` names).
                // Every accepted theorem just re-earned a foundational-only closure
                // (step 2) — and every carried definition/theorem in the write list
                // is foundational-only (checked above) — so the gate-derived profile
                // is NONE; heuristic bits would trip the cake gate's
                // `NonEmptyAxiomProfile` clause and contradict the record's
                // `axiom_profile_bits: 0`. Zero before the in-shard closure pass so
                // stale bits cannot propagate through dependencies.
                builder
                    .shard_writer_mut()
                    .set_constant_axiom_profile(idx, crate::types::AxiomProfile::NONE);
                const_indices.push((idx, name.clone()));
            }
            ShardEntry::Family { carried_idx } => {
                let CarriedItem::Family(family) = &state.carried[*carried_idx] else {
                    return Err(MathverseError::TrustViolation(
                        "graduation internal invariant violated: family shard entry \
                         points at a non-family carried item"
                            .to_string(),
                    ));
                };
                let members = state.family_shard_members(family);
                let mut exports = Vec::with_capacity(members.len());
                for (name, kind) in &members {
                    let info = state
                        .recheck
                        .get_const(&Name::from_string(name))
                        .ok_or_else(|| {
                            MathverseError::TrustViolation(format!(
                                "graduation internal invariant violated: carried family \
                                 member `{name}` missing from the recheck environment"
                            ))
                        })?;
                    exports.push(InductiveFamilyMemberExport {
                        name,
                        decl_kind: *kind,
                        level_params: &info.level_params,
                        type_: &info.type_,
                    });
                }
                let indices = builder.add_inductive_family(family.entry.num_params, &exports)?;
                for (idx, (name, _)) in indices.into_iter().zip(&members) {
                    const_indices.push((idx, name.clone()));
                }
            }
        }
    }
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = GraduationRecord {
        schema: GRADUATION_SCHEMA_VERSION.to_string(),
        gate: GateInfo {
            gate_version: GRADUATION_GATE_VERSION,
            clean_version: env!("CARGO_PKG_VERSION").to_string(),
            clean_commit: req
                .clean_commit
                .clone()
                .unwrap_or_else(|| "unknown".to_string()),
            decided_at_epoch_s: decided_at,
            recheck_base: state.base.record_label().to_string(),
        },
        project: ProjectInfo {
            name: req.project_name.clone(),
            manifest_kind: req.manifest_kind.clone(),
            manifest_digest: req.manifest_digest.clone(),
            certificate_schema: req.certificate_schema.clone(),
        },
        corpus_pin: CorpusPin {
            mathverse_release: req.mathverse_release.clone(),
            manifest_digest: baseline.digest().to_string(),
        },
        policy: PolicyInfo {
            min_trust: GRADUATION_MIN_TRUST.to_string(),
            on_duplicate: req.on_duplicate,
        },
        carried_definitions: carried_entries,
        carried_inductives: carried_family_entries,
        carried_theorems: carried_theorem_entries,
        provenance: RunProvenance {
            attempt_id: req.attempt_id.clone(),
            replay_archive_sha256: req.replay_archive_sha256.clone(),
            engine: req.engine.clone(),
            seed: req.seed.clone(),
            evidence_class: req.evidence_class,
            residual_risk: req.residual_risk.clone(),
            env_provenance: req.env_provenance.clone(),
        },
        result: GraduationResult {
            accepted: entries
                .iter()
                .filter(|e| e.accepted)
                .map(|e| e.name.clone())
                .collect(),
            rejected: entries
                .iter()
                .filter(|e| !e.accepted)
                .map(|e| e.name.clone())
                .collect(),
            shard_filename: shard_filename.clone(),
            shard_digest: String::new(),
        },
        theorems: entries,
    };

    // Bind the record into the shard's provenance, then the shard's digest
    // back into the record (see record.rs for why the order matters).
    let note = record.provenance_note()?;
    let mut sidecar = ProvenanceSidecar::new();
    for (const_idx, name) in &const_indices {
        let prov_record = ProvenanceBuilder::new(name)
            .module_path(&req.project_name)
            .source_version(&format!("clean {}", env!("CARGO_PKG_VERSION")))
            .import_timestamp(decided_at)
            .pipeline_version(GRADUATION_GATE_VERSION)
            .note(&note)
            .build();
        let (prov_idx, digest) = add_provenance(&mut sidecar, prov_record);
        builder
            .shard_writer_mut()
            .set_constant_provenance(*const_idx, prov_idx, digest);
    }
    if !sidecar.is_empty() {
        builder
            .shard_writer_mut()
            .set_provenance(sidecar.to_bytes()?);
    }

    let shard_path = out_dir.join(&shard_filename);
    builder.write_to_file(&shard_path)?;
    let shard_bytes = std::fs::read(&shard_path).map_err(MathverseError::Io)?;
    record.result.shard_digest = blake3_digest(&shard_bytes);
    record.write_to_file(&graduation_record_path(&shard_path))?;
    Ok(record)
}

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

fn constant_kind_label(kind: ConstantKind) -> &'static str {
    match kind {
        ConstantKind::Theorem => "theorem",
        ConstantKind::Definition => "definition",
        ConstantKind::Opaque => "opaque",
        ConstantKind::Axiom => "axiom",
    }
}

fn rejected_kernel_facts() -> KernelFacts {
    KernelFacts {
        verdict: KernelVerdict::Rejected,
        value_typechecked: false,
        family_checked: false,
        checker: format!("clean-kernel {}", env!("CARGO_PKG_VERSION")),
    }
}

fn empty_axiom_closure(foundational_only: bool) -> AxiomClosure {
    AxiomClosure {
        foundational_only,
        domain_axioms: Vec::new(),
        axiom_profile_bits: 0,
    }
}

fn rejected_entry(name: &str, decl_kind: &str, reason: &str) -> GraduatedTheorem {
    GraduatedTheorem {
        name: name.to_string(),
        decl_kind: decl_kind.to_string(),
        statement_hash: String::new(),
        proof_hash: String::new(),
        kernel: rejected_kernel_facts(),
        axiom_closure: empty_axiom_closure(false),
        novelty: NoveltyFacts {
            method: novelty_method(None),
            verdict: NoveltyVerdict::Unevaluated,
            matched_name: None,
            match_kind: None,
        },
        accepted: false,
        reject_reason: Some(reason.to_string()),
        carried_definitions: Vec::new(),
        carried_inductives: Vec::new(),
        carried_theorems: Vec::new(),
        semantic_identity: None,
    }
}
