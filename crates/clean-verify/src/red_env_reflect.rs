// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 2 (the_red_env discharge program): the REFLECTION GENERATOR.
//!
//! Mechanically reflects the FOUNDATION CORE of the real kernel environment —
//! the same allowlisted declarations `Specification::new()` builds — into a `RedEnv`
//! `value_src` literal (`kernel_core_red_env`), so the metatheory's reduction
//! environment contains the very inductives/definitions the metatheory itself
//! is written in (maximal self-reference). The same code path is the FIDELITY
//! GATE: a test regenerates the reflection from the live kernel env and
//! compares it 1:1 (structural definition and admitted rule levels)
//! against the committed generated artifacts; any drift fails.
//!
//! ## The three encoding TRUST EDGES (each named, each mechanical)
//!
//! 1. **Name interning** (`build_interning`). The spec models
//!    `Name = anonymous | str Name Nat` with a NAT tag (rec_env.rs); real
//!    kernel names are string-based hierarchical names. The generator builds
//!    an INJECTIVE interning table `real name string -> Name.str Name.anonymous
//!    <unary Nat tag>` (tags assigned by descending occurrence count, then
//!    lexicographic — deterministic); absent reserved literal builtin names
//!    are appended without renumbering encountered names. Equal strings map
//!    to the same tag and distinct strings to distinct tags. This is NOT yet
//!    an injectivity theorem for arbitrary structural kernel `Name` trees:
//!    display strings can conflate numeric and string components. This bounded
//!    batch retains the actual structural names, rejects any display collision
//!    or TSV-ambiguous key, and resolves dependency lookups with the saved Name,
//!    never by reparsing display strings. Canonical Nat/String are included.
//!    This runtime refusal is not a generic proved NameRep relation.
//! 2. **Structural universe image, bounded source branch**. Definition and
//!    recursor signatures/bodies preserve all five raw Level constructors through
//!    [`reflect_definition_expr`], with the same parameter-name identities used
//!    by ordered signatures. No smart constructors are invoked.
//!    Recursor rules are accepted ONLY when the actual immediate source RHS tag
//!    is Lambda, before transparent MData erasure, and the source layout is
//!    MajorAfterMinors. Other source reduction branches are refused, not inferred
//!    from an identical reflected image. The active guarded model then uses the
//!    looked-up signature and actual head universes to instantiate the stored RHS.
//!    The historical erased adapter remains solely for explicit legacy tests.
//!    Structural images do not prove Rust's smart max/imax substitution agrees
//!    with raw model instantiation. Typed admission, source execution/refinement,
//!    cache behavior, and the remaining reduction branches are still separate.
//! 3. **Coverage-with-skips** (the ledger). Everything outside the RecEnv/
//!    DefEnv model is SKIPPED WITH A REASON, lean_export-style, never
//!    silently weakened: Quot rules, K-like reduction (`is_k` recursors are
//!    reflected for their SYNTACTIC rules, with the unmodeled K-extension
//!    recorded), structural eta, native reducers, literal constructor
//!    normalization, and any `Expr` node with no reflected `KExpr` image
//!    (projections, fvars, mode extensions). `Let` is represented directly,
//!    `MData` is transparently erased, and a literal leaf is carried whole
//!    through the tagged literal codec ([`render_literal`]: `literal_nat n`,
//!    `literal_string (string_lit_code cs)`). A recursor/definition containing
//!    an unrepresentable node is skipped whole.
//!
//! ## What is reflected
//!
//! - Every allowlisted inductive's `<T>.rec` [`clean_kernel::RecursorVal`]
//!   becomes `RecEnv.addRec <interned name> (RecMeta.mk params motives minors
//!   indices major_after_minors signature k_flag) <rules>`, with the actual recursor's
//!   ordered universe parameters and schematic type stored as a `KConstSig`.
//!   Its separate ConstantInfo must agree on name, ordered parameters and type;
//!   missing or disagreeing signatures are refused. Each [`clean_kernel::RecursorRule`]
//!   becomes `RecRule.mk <interned ctor> <num_fields> <schematic rhs>` after
//!   immediate-source-Lambda and layout checks. RHS levels are structurally preserved.
//! - Every allowlisted definition becomes `DefEnv.addDef tail name
//!   (KDefSig.mk (KConstSig.mk params type) value)`. Ordered parameters, type,
//!   and value come from the SAME actual kernel constant. Type and value retain
//!   their structural universe levels and parameter occurrences.
//!   This allowlist accepts only [`ConstantKind::Definition`]; any other kind,
//!   including an opaque declaration with a stored value, is refused and
//!   recorded in the skip ledger. This is an intentional subset policy, not a
//!   claim that the kernel cannot unfold theorems: its full delta path unfolds
//!   definitions and theorems, but not opaque declarations. Transparency-aware
//!   elaboration has a separate reducibility policy. In particular,
//!   `is_reducible = false` does NOT make an ordinary definition opaque.
//!   This kind check neither inspects the environment's separate unsafe/partial
//!   registries nor proves declaration admission or full source fidelity.
//!
//! - A required four-entry Nat typing-data slice copies the actual
//!   ConstantInfo signatures of Nat, Nat.zero, Nat.succ, and Nat.rec, cross-checked
//!   against the same family's source metadata. These value-less Definition
//!   entries are not inserted into DefEnv. This emits a concrete KDeclEnv, not
//!   a formal soundness proof of the source validator: the builder checks
//!   metadata, rule payloads and the declaration before stamping generated
//!   recursors FullKernelCheck. Existing name tags stay fixed; any signature-only names
//!   append deterministically after the reduction-image table.
//! - Every allowlisted actual InductiveVal and its ordered ConstructorVals
//!   contributes a signature and projection-relevant metadata to IndCtorEnv,
//!   the third RedEnv field. Associated ConstantInfo types/ordered parameters,
//!   parent/order/count coherence and structural names are checked before
//!   capture. The final stored ordered `all_names` block is copied without
//!   sorting or deduplication, with source sibling consistency checks. Nested
//!   restoration can remove auxiliary families from that stored block; this
//!   image does not certify correspondence with the earlier transformed
//!   strict-validation context. The same signatures form kcre_ind_ctor_tenv. Omitted inductive
//!   flags, generic admission, projection reduction and Rust refinement are not
//!   certified by this image. A genuine source-checked ProdType application is
//!   emitted as data for a later checked typing consumer, not a theorem.
//!
//! ## Generated artifact shape (the measured parser constraint)
//!
//! The reflection is emitted as a DEF SCRIPT (one `def` per line): a
//! `kcre_nat_<k>` unary pool (depth 2 each), one
//! `def kcre_name_<tag> : Name := Name.str Name.anonymous kcre_nat_<tag>` per
//! interned name (depth 1), per-recursor signature and metadata atoms, then the
//! single `kernel_core_red_env : RedEnv` term whose leaves are those atoms.
//! This shape is forced by a MEASURED
//! constraint: the parser rejects expressions past `MAX_EXPR_DEPTH = 128`,
//! and the naive fully-inlined literal (unary tags in place) nests to paren
//! depth 163. The generator measures and validates every current line. The helper defs are
//! value-ful definitions (census-neutral), and the kernel's whnf delta-unfolds
//! them on demand during checker-fold evaluation.
//!
//! The emitter builds an artifact-independent seed containing exactly the
//! allowlisted source declarations, validates every rendered line against a
//! second fresh seed, then builds the complete `Specification` with the fresh
//! script injected in memory and checks all three rendered artifacts against
//! that complete live environment. Only then does it publish. This breaks the
//! otherwise circular dependency on successfully loading the old artifact
//! without weakening the final full-spec fidelity check.
//!
//! Consumed by the `red_env_reflect` bin (emits the generated artifacts under
//! `spec/core_spec/generated/`) and by the fidelity-gate tests
//! (`tests/kernel_core_red_env_fidelity.rs`).

use std::collections::BTreeMap;
use std::fmt::Write as _;

use clean_kernel::{
    ConstantInfo, ConstantKind, ConstructorVal, Environment, Expr, ExprKind, InductiveVal, Level,
    Name, RecursorArgOrder, RecursorVal, TypeChecker,
};

/// Committed generated foundation-core definition script.
pub const COMMITTED_DEF_SCRIPT: &str =
    include_str!("spec/core_spec/generated/kernel_core_red_env.defs.txt");
/// Committed semantic-name ↔ generated-tag table.
pub const COMMITTED_INTERNING_TSV: &str =
    include_str!("spec/core_spec/generated/kernel_core_red_env.interning.tsv");
/// Committed ledger of production constructs outside the reflected image.
pub const COMMITTED_SKIP_LEDGER: &str =
    include_str!("spec/core_spec/generated/kernel_core_red_env.skips.md");

/// Validation error for a generated semantic-name interning table.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum InterningTableError {
    /// The table is malformed or violates its injective contiguous-tag format.
    #[error("invalid kernel_core_red_env interning table: {0}")]
    Invalid(String),
    /// A semantic consumer requested a real name absent from the table.
    #[error("kernel_core_red_env interning table has no entry for {0}")]
    MissingName(String),
}

/// Parse and validate a generated interning TSV.
///
/// Validation is deliberately whole-table, not just lookup-local: every row
/// must have exactly two columns, tags must be canonical decimal `u64`s,
/// names and tags must both be unique, and tags must be contiguous from zero.
/// Semantic consumers therefore cannot silently agree on one usable row while
/// the rest of the committed trust-edge table is malformed.
///
/// # Errors
/// Returns [`InterningTableError`] on the first malformed row, duplicate,
/// non-canonical tag, gap, or empty table.
pub fn parse_interning_tsv(tsv: &str) -> Result<BTreeMap<String, u64>, InterningTableError> {
    let mut by_name = BTreeMap::new();
    let mut tags = std::collections::BTreeSet::new();

    for (line_index, line) in tsv.lines().enumerate() {
        let line_number = line_index + 1;
        let mut columns = line.split('\t');
        let Some(tag_text) = columns.next() else {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} has no tag column"
            )));
        };
        let Some(real_name) = columns.next() else {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} has fewer than two columns: {line:?}"
            )));
        };
        if columns.next().is_some() {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} has more than two columns: {line:?}"
            )));
        }
        if real_name.is_empty() {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} has an empty real-name column"
            )));
        }
        let tag = tag_text.parse::<u64>().map_err(|e| {
            InterningTableError::Invalid(format!(
                "line {line_number} has non-u64 tag {tag_text:?}: {e}"
            ))
        })?;
        if tag.to_string() != tag_text {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} has non-canonical tag {tag_text:?}"
            )));
        }
        if !tags.insert(tag) {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} duplicates tag {tag}"
            )));
        }
        if by_name.insert(real_name.to_string(), tag).is_some() {
            return Err(InterningTableError::Invalid(format!(
                "line {line_number} duplicates real name {real_name:?}"
            )));
        }
    }

    if by_name.is_empty() {
        return Err(InterningTableError::Invalid("table is empty".to_string()));
    }
    for (index, tag) in tags.into_iter().enumerate() {
        // `tags` is a `BTreeSet<u64>`, so the ascending index IS the expected tag.
        let expected = index as u64;
        if tag != expected {
            return Err(InterningTableError::Invalid(format!(
                "tags are not contiguous from zero: expected {expected}, found {tag}"
            )));
        }
    }
    Ok(by_name)
}

/// Resolve a real kernel name to its committed generated `kcre_name_<tag>`
/// atom after validating the entire interning table.
///
/// # Errors
/// Returns [`InterningTableError`] if the committed table is malformed or does
/// not contain `real_name`.
pub fn committed_name_atom(real_name: &str) -> Result<String, InterningTableError> {
    committed_name_tag(real_name).map(|tag| format!("kcre_name_{tag}"))
}

/// Resolve a semantic name to its tag without depending on the late-registered
/// `kcre_name_*` definitions. Early literal-model consumers use this same table.
///
/// # Errors
/// Returns [`InterningTableError`] if the table is malformed or the name absent.
fn committed_name_tag(real_name: &str) -> Result<u64, InterningTableError> {
    name_tag_in_table(COMMITTED_INTERNING_TSV, real_name)
}

/// Whole-table-validated lookup, also used while validating fresh artifacts
/// before publication. No missing builtin tag is guessed or defaulted.
///
/// # Errors
/// Returns [`InterningTableError`] if the table is malformed or the name absent.
pub(crate) fn name_tag_in_table(tsv: &str, real_name: &str) -> Result<u64, InterningTableError> {
    parse_interning_tsv(tsv)?
        .get(real_name)
        .copied()
        .ok_or_else(|| InterningTableError::MissingName(real_name.to_string()))
}

/// Canonical literal result names used by the real kernel. A name is reserved
/// even if no reflected reduction rule references it; reservation does not add
/// a String declaration, reduction rule, or environment-validity theorem.
pub const RESERVED_LITERAL_BUILTINS: &[&str] = &["Nat", "String"];

/// Foundation-core INDUCTIVE allowlist: the `<T>.rec` recursors reflected into
/// the `RecEnv` leg. This is the selected foundation/object-language family,
/// not the transitive closure of every current model datatype. In particular,
/// RedEnv's new IndCtorEnv field is represented in its signature, but the three
/// metadata carriers are not themselves added to this recursor allowlist.
/// The generated finite signature table therefore is not a claim of a closed,
/// fully admitted typing environment.
pub const REFLECT_INDUCTIVES: &[&str] = &[
    // foundation_types
    "Nat",
    "Bool",
    "Eq",
    "ProdType",
    "AndType",
    "Empty",
    "Lt",
    "Le",
    // expr_model
    "Name",
    "Level",
    "ListType",
    "KExpr",
    // rec_env / delta_step_core / add_red_env
    "OptionType",
    "RecRule",
    "RecRules",
    "RecMeta",
    "RecEnv",
    // shared declaration signatures consumed by universe-aware delta
    "KConstSig",
    "KDefSig",
    "DefEnv",
    "RedEnv",
];

/// Foundation-core DEFINITION allowlist: ordinary `ConstantKind::Definition`
/// declarations (regardless of their `is_reducible` hint) reflected into the
/// `DefEnv` leg — the modeled fragment's own function vocabulary (lookup folds,
/// spine surgery, de Bruijn operations, the closure checkers).
pub const REFLECT_DEFS: &[&str] = &[
    // foundation arithmetic + Bool glue
    "Nat.add",
    "Nat.sub",
    "Nat.pred",
    "Bool.and",
    // expr_model de Bruijn operations
    "lift_bvar_at",
    "lift_at",
    "instantiate_bvar_geq",
    "instantiate_bvar_at",
    "instantiate_at",
    "instantiate",
    "kapp_fn",
    // rec_env decidable equality + projectors + lookups
    "nat_is_zero",
    "nat_eqb",
    "name_eqb",
    "recrule_ctor_name",
    "recrule_num_fields",
    "recrule_rhs",
    "recmeta_num_params",
    "recmeta_num_motives",
    "recmeta_num_minors",
    "recmeta_num_indices",
    "recmeta_major_after_minors",
    "recmeta_signature",
    "opt_pick",
    "bool_pick",
    "recrule_in_rules",
    "recrules_for",
    "recmeta_for",
    "is_recursor",
    "recrule_for",
    // iota_step spine substrate + the reduct
    "opt_bind",
    "list_head",
    "list_tail",
    "list_drop",
    "list_take",
    "list_length",
    "list_append",
    "apply_spine",
    "kapp_args",
    "kexpr_const_name",
    "iota_reduct",
    // actual guarded iota contractum and signature-indexed RHS instance
    "iota_prefix_count",
    "iota_major_index",
    "iota_fields_ok",
    "iota_contractum",
    "iota_contractum_at",
    "recursor_rhs_instance",
    "recursor_rhs_at",
    // shared signature projections and raw universe-instantiation graph
    "kconst_params",
    "kconst_type",
    "kdef_signature",
    "kdef_value",
    "kdef_inst_value",
    "name_list_len",
    "level_list_len",
    "substL",
    "mapLL",
    "list_getD",
    "nameIdx",
    "paramSubstN",
    "instL",
    "instLevels",
    // delta_step_core
    "kdef_for",
    "defval_for",
    "kdef_guarded_value",
    "kdef_raw_value",
    "kdef_value_at",
    "kexpr_const_levels",
    "delta_reduct",
    // add_red_env projections
    "red_rec",
    "red_def",
    // de Bruijn ceiling + the Stage-1 closure checkers
    "bvar_ceiling",
    "rec_rules_closed_b",
    "rec_env_closed_b",
    "rec_env_lift_closed_b",
    "def_env_closed_b",
    "def_env_lift_closed_b",
];

/// Reflection failure (generator-level; the fidelity tests convert these into
/// test failures).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReflectError {
    /// The in-memory reflection cannot safely be emitted.
    #[error("invalid foundation-core reflection: {detail}")]
    InvalidReflection {
        /// The missing witness, malformed interning property, or uncovered
        /// semantic name.
        detail: String,
    },
    /// The rendered/committed artifacts differ (fidelity-gate drift).
    #[error("fidelity drift in {artifact}: {detail}")]
    Drift {
        /// Which emitted artifact drifted.
        artifact: &'static str,
        /// First observed divergence.
        detail: String,
    },
}

/// A kernel `Expr` node translated into the spec `KExpr` vocabulary.
/// Constants keep the REAL name string; interning tags are applied at render
/// time so the interning table can be frequency-ordered over the whole
/// reflection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecExpr {
    /// Structural level payload. Active definition/rule images preserve every
    /// constructor; the historical adapter remains an explicit legacy control.
    Sort(SpecLevel),
    /// `KExpr.bvar <nat>`.
    BVar(u32),
    /// `KExpr.app f a`.
    App(Box<SpecExpr>, Box<SpecExpr>),
    /// `KExpr.lam ty body` (binder name/info dropped; spec lam is anonymous).
    Lam(Box<SpecExpr>, Box<SpecExpr>),
    /// `KExpr.pi ty body`.
    Pi(Box<SpecExpr>, Box<SpecExpr>),
    /// `KExpr.const <interned name> <universe args>`.
    Const(String, Vec<SpecLevel>),
    /// `KExpr.let_ ty val body` (binder name/info and the non-dependent flag
    /// dropped; the seventh constructor in the live nine-constructor model).
    Let_(Box<SpecExpr>, Box<SpecExpr>, Box<SpecExpr>),
    /// A literal leaf, rendered through the tagged literal codec and the string
    /// payload decoding ([`render_literal`]): `literal_nat n` /
    /// `literal_string (string_lit_code cs)`.
    Lit(clean_kernel::Literal),
}

/// Structural image of a kernel [`Level`]. Parameter display keys are checked
/// against actual structural names across the complete reflected batch before
/// emission; this is not a generic Name representation theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecLevel {
    /// `Level.zero`
    Zero,
    /// `Level.succ l`
    Succ(Box<SpecLevel>),
    /// `Level.max a b`
    Max(Box<SpecLevel>, Box<SpecLevel>),
    /// `Level.imax a b`
    IMax(Box<SpecLevel>, Box<SpecLevel>),
    /// `Level.param <interned name>`.
    Param(String),
}

/// One reflected recursor rule (the structural image of a kernel
/// [`clean_kernel::RecursorRule`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedRule {
    /// Real constructor name (interned at render time).
    pub ctor: String,
    /// Kernel `num_fields`.
    pub num_fields: u32,
    /// The REAL schematic rule RHS with structural universe levels retained.
    pub rhs: SpecExpr,
}

/// One reflected recursor: structural signature and immediate-Lambda RHS images
/// from one [`RecursorVal`]. This bounded source branch is not typed recursor admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedRec {
    /// Real recursor name (e.g. `Nat.rec`; interned at render time).
    pub name: String,
    /// Ordered universe parameter names from the same source RecursorVal as
    /// type_, checked against that actual name's separate ConstantInfo.
    pub level_params: Vec<String>,
    /// The actual schematic recursor type with structural universe levels.
    pub type_: SpecExpr,
    /// Kernel `num_params`.
    pub num_params: u32,
    /// Kernel `num_motives`.
    pub num_motives: u32,
    /// Kernel `num_minors`.
    pub num_minors: u32,
    /// Kernel `num_indices`.
    pub num_indices: u32,
    /// `true` iff the kernel arg order is `MajorAfterMinors` (the only layout
    /// `iota_reduct` models; others are skipped, see the ledger).
    pub major_after_minors: bool,
    /// Kernel `is_k` flag (K-extension recorded in the ledger; syntactic
    /// rules still reflected).
    pub is_k: bool,
    /// One reflected rule per kernel rule, in kernel order.
    pub rules: Vec<ReflectedRule>,
}

/// A generated witness plan; the expected RHS is instantiated by the CHECKED
/// model at render time, not by a second handwritten SpecExpr substituter.
struct NatZeroWitness {
    redex: SpecExpr,
    rhs: SpecExpr,
    prefix: Vec<SpecExpr>,
    levels: Vec<SpecLevel>,
}

/// One reflected ordinary definition (not a theorem, opaque constant, or axiom).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedDef {
    /// Real definition name (interned at render time).
    pub name: String,
    /// Whether the kernel marks the constant reducible (recorded in the
    /// ledger, not used as the declaration-kind eligibility check).
    pub is_reducible: bool,
    /// Ordered universe parameter names from the same kernel constant as the
    /// type and value, using the same validated name keys as their occurrences.
    pub level_params: Vec<String>,
    /// The REAL schematic kernel type with structural universe levels retained.
    pub type_: SpecExpr,
    /// The REAL kernel value with structural universe levels retained.
    pub value: SpecExpr,
}

/// A skip-ledger entry: an allowlisted item (or a categorical model gap) that
/// is NOT reflected, with the reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkipEntry {
    /// Item name (or category name for model-level gaps).
    pub item: String,
    /// Why it is outside the reflection.
    pub reason: String,
}

/// Signature-only image of one actual ConstantInfo. Structural source names
/// are retained here as well as collision-checked at batch interning time.
/// This is not a formal soundness proof of the builder's metadata, rule-payload
/// and strict declaration checks; those checks precede its FullKernelCheck
/// stamp. Value-less Definition entries are intentionally supported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedConstSig {
    /// Actual source identity, never reconstructed by parsing its display text.
    pub name: Name,
    /// Exact ordered source universe parameters.
    pub level_params: Vec<Name>,
    /// Structural type image; no invented type or erased universe parameters.
    pub type_: SpecExpr,
}

/// Projection-relevant image of an actual inductive record, not its omitted
/// recursion, elimination or nesting flags. The ordered block is the final
/// stored metadata, not a certificate of the pre-restoration strict context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedInductive {
    /// Same-name ConstantInfo signature, checked against the source metadata.
    pub signature: ReflectedConstSig,
    /// Actual parameter prefix length.
    pub num_params: u32,
    /// Actual number of indices after the parameters.
    pub num_indices: u32,
    /// Actual ordered structural constructor identities.
    pub constructor_names: Vec<Name>,
    /// Exact final stored ordered block identities, including this family.
    /// Nested restoration may have removed auxiliary families before capture.
    pub all_names: Vec<Name>,
}

/// Projection-relevant image of an actual constructor record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedConstructor {
    /// Same-name ConstantInfo signature, checked against the source metadata.
    pub signature: ReflectedConstSig,
    /// Actual parent, checked against the containing inductive's ordered list.
    pub inductive_name: Name,
    /// Actual parameter prefix length.
    pub num_params: u32,
    /// Actual number of fields after the parameters.
    pub num_fields: u32,
    /// Actual position in the parent's ordered constructor list.
    pub constructor_idx: u32,
}

/// A concrete source-checked constructor application and its inferred type.
/// This finite execution receipt is not a general source-typing refinement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedProjectionWitness {
    /// Structural image of the genuine ProdType constructor application.
    pub value: SpecExpr,
    /// Structural image of its actual source-inferred type.
    pub type_: SpecExpr,
}

/// Required finite typing slice, in lookup-priority order.
const NAT_SIGNATURE_NAMES: [&str; 4] = ["Nat", "Nat.zero", "Nat.succ", "Nat.rec"];
const NAT_SIGNATURE_ATOMS: [&str; 4] = [
    "kcre_nat_type_signature",
    "kcre_nat_zero_signature",
    "kcre_nat_succ_signature",
    "kcre_nat_rec_signature",
];

/// The complete foundation-core reflection of a kernel environment.
#[derive(Debug, Clone, Default)]
pub struct Reflection {
    /// Reflected recursors, in `REFLECT_INDUCTIVES` order.
    pub recs: Vec<ReflectedRec>,
    /// Reflected definitions, in `REFLECT_DEFS` order.
    pub defs: Vec<ReflectedDef>,
    /// Four required source signatures, independent of the delta value allowlist.
    /// Empty after an explicitly ledgered capture refusal; emission then fails.
    pub nat_signatures: Vec<ReflectedConstSig>,
    /// Required projection metadata, in REFLECT_INDUCTIVES order.
    pub inductives: Vec<ReflectedInductive>,
    /// Required constructors, in inductive order then source constructor order.
    pub constructors: Vec<ReflectedConstructor>,
    /// Required nonempty source-checked constructor caller.
    pub projection_witness: Option<ReflectedProjectionWitness>,
    /// Interning table: real name -> unary Nat tag (trust edge 1).
    pub interning: Vec<(String, u64)>,
    /// Skip ledger (trust edge 3).
    pub skips: Vec<SkipEntry>,
}

/// Legacy iota ONLY: collapse a kernel [`Level`] to a numeric height for its
/// erased `KExpr.sort` payload (trust edge 2): `zero`→0, `succ`→+1,
/// `max`/`imax`→max, `param`→0. Rendering re-encodes the height as a spec
/// `Level.succ^n Level.zero`.
#[must_use]
fn erase_level_to_nat(l: &Level) -> u64 {
    match l {
        Level::Zero | Level::Param(_) => 0,
        Level::Succ(x) => erase_level_to_nat(x).saturating_add(1),
        Level::Max(a, b) | Level::IMax(a, b) => erase_level_to_nat(a).max(erase_level_to_nat(b)),
    }
}

/// Legacy iota ONLY: erase a kernel [`Level`] for `const` universe
/// arguments (trust edge 2): structural on `zero`/`succ`/`max`/`imax`,
/// `param`→`Level.zero`.
#[must_use]
fn erase_level_to_spec(l: &Level) -> SpecLevel {
    match l {
        Level::Zero | Level::Param(_) => SpecLevel::Zero,
        Level::Succ(x) => SpecLevel::Succ(Box::new(erase_level_to_spec(x))),
        Level::Max(a, b) => SpecLevel::Max(
            Box::new(erase_level_to_spec(a)),
            Box::new(erase_level_to_spec(b)),
        ),
        Level::IMax(a, b) => SpecLevel::IMax(
            Box::new(erase_level_to_spec(a)),
            Box::new(erase_level_to_spec(b)),
        ),
    }
}

/// Translate a definition or recursor signature's kernel [`Expr`] with faithful
/// structural universe levels, or report the first unrepresentable node. Parameter keys are checked
/// by the complete batch before publication. `MData` is unwrapped
/// transparently (the kernel type checker treats it as transparent).
///
/// # Errors
/// Returns the human-readable node description that has no `KExpr` image.
fn reflect_definition_expr(e: &Expr) -> Result<SpecExpr, String> {
    reflect_expr_with_policy(e, true)
}

/// Historical erased rule-RHS adapter, retained for explicit legacy controls.
/// The active reflection producer does not call this adapter.
/// Sorts retain the old numeric-height erasure; constant parameters become zero.
/// This image is intentionally NOT a faithful universe-preserving rule image.
///
/// # Errors
/// Returns the first expression node outside the represented iota fragment.
#[cfg(test)]
fn reflect_legacy_erased_iota_expr(e: &Expr) -> Result<SpecExpr, String> {
    reflect_expr_with_policy(e, false)
}

/// Preserve all five raw constructors without invoking smart constructors.
/// Parameter keys require the batch-level structural-name validation before
/// rendering; a standalone image is not an interning-fidelity certificate.
#[must_use]
fn reflect_level(l: &Level) -> SpecLevel {
    match l {
        Level::Zero => SpecLevel::Zero,
        Level::Succ(x) => SpecLevel::Succ(Box::new(reflect_level(x))),
        Level::Max(a, b) => SpecLevel::Max(Box::new(reflect_level(a)), Box::new(reflect_level(b))),
        Level::IMax(a, b) => {
            SpecLevel::IMax(Box::new(reflect_level(a)), Box::new(reflect_level(b)))
        }
        Level::Param(n) => SpecLevel::Param(n.to_string()),
    }
}

fn legacy_iota_sort_level(l: &Level) -> SpecLevel {
    let mut erased = SpecLevel::Zero;
    for _ in 0..erase_level_to_nat(l) {
        erased = SpecLevel::Succ(Box::new(erased));
    }
    erased
}

fn reflect_expr_with_policy(e: &Expr, preserve_levels: bool) -> Result<SpecExpr, String> {
    match e.kind() {
        ExprKind::BVar(i) => Ok(SpecExpr::BVar(*i)),
        ExprKind::Sort(l) => Ok(SpecExpr::Sort(if preserve_levels {
            reflect_level(l)
        } else {
            legacy_iota_sort_level(l)
        })),
        ExprKind::Const(n, ls) => Ok(SpecExpr::Const(
            n.to_string(),
            ls.iter()
                .map(if preserve_levels {
                    reflect_level
                } else {
                    erase_level_to_spec
                })
                .collect(),
        )),
        ExprKind::App(f, a) => Ok(SpecExpr::App(
            Box::new(reflect_expr_with_policy(f, preserve_levels)?),
            Box::new(reflect_expr_with_policy(a, preserve_levels)?),
        )),
        ExprKind::Lam(_, ty, b) => Ok(SpecExpr::Lam(
            Box::new(reflect_expr_with_policy(ty, preserve_levels)?),
            Box::new(reflect_expr_with_policy(b, preserve_levels)?),
        )),
        ExprKind::Pi(_, ty, b) => Ok(SpecExpr::Pi(
            Box::new(reflect_expr_with_policy(ty, preserve_levels)?),
            Box::new(reflect_expr_with_policy(b, preserve_levels)?),
        )),
        ExprKind::MData(_, inner) => reflect_expr_with_policy(inner, preserve_levels),
        ExprKind::Let(_, ty, val, body, _) => Ok(SpecExpr::Let_(
            Box::new(reflect_expr_with_policy(ty, preserve_levels)?),
            Box::new(reflect_expr_with_policy(val, preserve_levels)?),
            Box::new(reflect_expr_with_policy(body, preserve_levels)?),
        )),
        ExprKind::Lit(lit) => Ok(SpecExpr::Lit(lit.clone())),
        ExprKind::Proj(..) => {
            Err("proj node (struct projection/eta outside the RecEnv model)".to_string())
        }
        ExprKind::FVar(_) => Err("free variable (open term; no KExpr image)".to_string()),
        other => Err(format!("{other:?}-headed node (no KExpr image)")),
    }
}

/// Reflect the VALUE of one live definition into `KExpr` source text, every
/// constant and universe-parameter name rendered as `kcre_name_<tag>` through
/// `tag_of` (the validated interning table), every bound variable through the
/// `kcre_nat_<k>` pool, with the structural image the foundation core uses
/// ([`reflect_definition_expr`]) plus projection nodes, rendered as `KExpr.proj`
/// (the foundation core refuses them; a native-fold closure such as `Prod.fst`
/// needs them). At `zero_levels` universe arguments the value's level
/// parameters (exactly that many) are instantiated at `Level.zero` first, which
/// is the body the model's `kdef_value_at` returns for a head applied at those
/// levels. The E4d native-fold stage states each fold key's canonical body with
/// it, from the environment it is registered in, never from typed-in text.
///
/// # Errors
/// The name is absent, is not a [`ConstantKind::Definition`] with a value, its
/// level-parameter count is not `zero_levels`, its value has a node with no
/// `KExpr` image, or `tag_of` refuses a name.
pub(crate) fn reflect_definition_value_text_at<E>(
    env: &Environment,
    name: &str,
    zero_levels: usize,
    tag_of: impl Fn(&str) -> Result<u64, E>,
) -> Result<String, String>
where
    E: std::fmt::Display,
{
    let info = env
        .get_const(&Name::from_string(name))
        .ok_or_else(|| format!("{name}: absent from the environment"))?;
    if !matches!(info.kind, ConstantKind::Definition) {
        return Err(format!("{name}: a {:?}, not a definition", info.kind));
    }
    let value = info
        .value
        .as_ref()
        .ok_or_else(|| format!("{name}: a definition without a value"))?;
    if zero_levels > 0 || !info.level_params.is_empty() {
        if info.level_params.len() != zero_levels {
            return Err(format!(
                "{name}: {} universe parameters, instantiated at {zero_levels}",
                info.level_params.len()
            ));
        }
        let zeros = vec![Level::zero(); zero_levels];
        let value = value.instantiate_level_params_direct(&info.level_params, &zeros);
        let render_name = |n: &str| -> Result<String, String> {
            tag_of(n)
                .map(|tag| format!("kcre_name_{tag}"))
                .map_err(|e| format!("{name}: {e}"))
        };
        let mut out = String::new();
        render_kernel_expr(&value, &render_name, &mut out).map_err(|e| format!("{name}: {e}"))?;
        return Ok(out);
    }
    let render_name = |n: &str| -> Result<String, String> {
        tag_of(n)
            .map(|tag| format!("kcre_name_{tag}"))
            .map_err(|e| format!("{name}: {e}"))
    };
    let mut out = String::new();
    render_kernel_expr(value, &render_name, &mut out).map_err(|e| format!("{name}: {e}"))?;
    Ok(out)
}

/// Reflect the TYPE and ordered universe parameters of one live constant as
/// `KConstSig.mk <params> <type>` source text, names through `tag_of`, by the
/// same renderer as [`reflect_definition_value_text_at`]. The E4 String-literal
/// stage states the canonical `String.ofList` / `Char.ofNat` signatures with it.
///
/// # Errors
/// The name is absent, its type has a node with no `KExpr` image, or `tag_of`
/// refuses a name.
pub(crate) fn reflect_const_sig_text<E>(
    env: &Environment,
    name: &str,
    tag_of: impl Fn(&str) -> Result<u64, E>,
) -> Result<String, String>
where
    E: std::fmt::Display,
{
    let info = env
        .get_const(&Name::from_string(name))
        .ok_or_else(|| format!("{name}: absent from the environment"))?;
    let render_name = |n: &str| -> Result<String, String> {
        tag_of(n)
            .map(|tag| format!("kcre_name_{tag}"))
            .map_err(|e| format!("{name}: {e}"))
    };
    let mut params = String::from("(ListType.nil Name)");
    for param in info.level_params.iter().rev() {
        params = format!(
            "(ListType.cons Name {} {params})",
            render_name(&param.to_string())?
        );
    }
    let mut ty = String::new();
    render_kernel_expr(&info.type_, &render_name, &mut ty).map_err(|e| format!("{name}: {e}"))?;
    Ok(format!("(KConstSig.mk {params} {ty})"))
}

/// Reflect one live constructor's projection-relevant metadata as
/// `KCtorMeta.mk <signature> <parent> <params> <fields> <index>` source text
/// (the fields `IndCtorEnv` stores; `ind_ctor_env.rs`), names through `tag_of`
/// and counts as unary `Nat` terms.
///
/// # Errors
/// The name is not a constructor, its signature does not reflect, or `tag_of`
/// refuses a name.
pub(crate) fn reflect_ctor_meta_text<E>(
    env: &Environment,
    name: &str,
    tag_of: impl Fn(&str) -> Result<u64, E>,
) -> Result<String, String>
where
    E: std::fmt::Display,
{
    let ctor = env
        .get_constructor(&Name::from_string(name))
        .ok_or_else(|| format!("{name}: not a constructor"))?;
    let signature = reflect_const_sig_text(env, name, &tag_of)?;
    let parent = tag_of(&ctor.inductive_name.to_string())
        .map(|tag| format!("kcre_name_{tag}"))
        .map_err(|e| format!("{name}: {e}"))?;
    Ok(format!(
        "KCtorMeta.mk {signature} {parent} {} {} {}",
        render_nat(u64::from(ctor.num_params)),
        render_nat(u64::from(ctor.num_fields)),
        render_nat(u64::from(ctor.constructor_idx))
    ))
}

/// Render a kernel expression directly (the structural image of
/// [`reflect_definition_expr`] plus `Proj`), names through `rn`.
fn render_kernel_expr(
    e: &Expr,
    rn: &dyn Fn(&str) -> Result<String, String>,
    out: &mut String,
) -> Result<(), String> {
    fn lvl(l: &Level, rn: &dyn Fn(&str) -> Result<String, String>) -> Result<String, String> {
        Ok(match l {
            Level::Zero => "Level.zero".to_string(),
            Level::Succ(x) => format!("(Level.succ {})", lvl(x, rn)?),
            Level::Max(a, b) => format!("(Level.max {} {})", lvl(a, rn)?, lvl(b, rn)?),
            Level::IMax(a, b) => format!("(Level.imax {} {})", lvl(a, rn)?, lvl(b, rn)?),
            Level::Param(p) => format!("(Level.param {})", rn(&p.to_string())?),
        })
    }
    match e.kind() {
        ExprKind::BVar(i) => {
            let _ = write!(out, "(KExpr.bvar {})", nat_atom(u64::from(*i)));
        }
        ExprKind::Sort(l) => {
            let _ = write!(out, "(KExpr.sort {})", lvl(l, rn)?);
        }
        ExprKind::Const(n, ls) => {
            let mut levels = String::from("(ListType.nil Level)");
            for l in ls.iter().rev() {
                levels = format!("(ListType.cons Level {} {levels})", lvl(l, rn)?);
            }
            let _ = write!(out, "(KExpr.const {} {levels})", rn(&n.to_string())?);
        }
        ExprKind::App(f, a) => {
            out.push_str("(KExpr.app ");
            render_kernel_expr(f, rn, out)?;
            out.push(' ');
            render_kernel_expr(a, rn, out)?;
            out.push(')');
        }
        ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
            out.push_str(if matches!(e.kind(), ExprKind::Lam(..)) {
                "(KExpr.lam "
            } else {
                "(KExpr.pi "
            });
            render_kernel_expr(ty, rn, out)?;
            out.push(' ');
            render_kernel_expr(b, rn, out)?;
            out.push(')');
        }
        ExprKind::Let(_, ty, val, body, _) => {
            out.push_str("(KExpr.let_ ");
            render_kernel_expr(ty, rn, out)?;
            out.push(' ');
            render_kernel_expr(val, rn, out)?;
            out.push(' ');
            render_kernel_expr(body, rn, out)?;
            out.push(')');
        }
        ExprKind::MData(_, inner) => render_kernel_expr(inner, rn, out)?,
        ExprKind::Proj(s, i, sub) => {
            let _ = write!(
                out,
                "(KExpr.proj {} {} ",
                rn(&s.to_string())?,
                nat_atom(u64::from(*i))
            );
            render_kernel_expr(sub, rn, out)?;
            out.push(')');
        }
        ExprKind::Lit(lit) => out.push_str(&render_literal(lit)),
        other => return Err(format!("{other:?}-headed node (no KExpr image)")),
    }
    Ok(())
}

/// The model image of a kernel literal, through the tagged literal codec
/// (`literal_model`) and the string payload decoding (`literal_string_codec`):
/// `Literal::Nat(n)` is `(literal_nat n)` and `Literal::String(s)` is
/// `(literal_string (string_lit_code cs))` for `cs` the Unicode scalar values
/// of `s` in order -- the list the deployed `string_lit_to_constructor` walks
/// (`s.chars()`). Numerals are decimal, which the spec parser reads as kernel
/// `Nat` literals.
#[must_use]
pub(crate) fn render_literal(lit: &clean_kernel::Literal) -> String {
    match lit {
        clean_kernel::Literal::Nat(n) => format!("(literal_nat {})", bignat_decimal(n)),
        clean_kernel::Literal::String(s) => {
            let mut list = String::from("(ListType.nil Nat)");
            for c in s.chars().rev() {
                list = format!("(ListType.cons Nat {} {list})", u32::from(c));
            }
            format!("(literal_string (string_lit_code {list}))")
        }
    }
}

/// The same image as [`render_literal`], as a first-class kernel `Expr` over
/// the spec's own constants (for [`Reflection::kexpr_term`]).
fn literal_term(lit: &clean_kernel::Literal) -> Expr {
    match lit {
        clean_kernel::Literal::Nat(n) => {
            Expr::app(Expr::const_str("literal_nat"), Expr::bignat_lit(n.clone()))
        }
        clean_kernel::Literal::String(s) => {
            let mut list = Expr::app(Expr::const_str("ListType.nil"), Expr::const_str("Nat"));
            for c in s.chars().rev() {
                list = Expr::apps(
                    Expr::const_str("ListType.cons"),
                    [
                        Expr::const_str("Nat"),
                        Expr::nat_lit(u64::from(u32::from(c))),
                        list,
                    ],
                );
            }
            Expr::app(
                Expr::const_str("literal_string"),
                Expr::app(Expr::const_str("string_lit_code"), list),
            )
        }
    }
}

/// Decimal digits of a kernel `BigNat` (its `Display` renders `Big` in hex,
/// which the spec parser does not read).
fn bignat_decimal(n: &clean_kernel::BigNat) -> String {
    if let Some(small) = n.to_u64() {
        return small.to_string();
    }
    // Repeated long division of the little-endian limbs by 10^19.
    const CHUNK: u128 = 10_000_000_000_000_000_000;
    let mut limbs: Vec<u64> = n.limbs().to_vec();
    let mut chunks: Vec<u64> = Vec::new();
    while limbs.iter().any(|&l| l != 0) {
        let mut rem: u128 = 0;
        for limb in limbs.iter_mut().rev() {
            let cur = (rem << 64) | u128::from(*limb);
            // Quotient of a (< CHUNK * 2^64) value by CHUNK fits in 64 bits.
            *limb = u64::try_from(cur / CHUNK).unwrap_or(u64::MAX);
            rem = cur % CHUNK;
        }
        chunks.push(u64::try_from(rem).unwrap_or(u64::MAX));
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
    }
    let mut out = String::new();
    for (i, chunk) in chunks.iter().rev().enumerate() {
        if i == 0 {
            out.push_str(&chunk.to_string());
        } else {
            out.push_str(&format!("{chunk:019}"));
        }
    }
    if out.is_empty() {
        out.push('0');
    }
    out
}

/// A reflected recursor as `KExpr` source text: its `RecMeta.mk` (counts,
/// layout, signature, K flag) and one `(constructor, fields, rhs)` per rule,
/// through the same structural image and immediate-lambda / layout refusals
/// the foundation core applies ([`reflect_recursor`]). The E4d stage states
/// `Int.rec`'s canonical rules with it.
///
/// # Errors
/// The recursor or its signature is absent, its layout or a rule is outside the
/// reflected image, or `tag_of` refuses a name.
pub(crate) fn reflect_recursor_text<E>(
    env: &Environment,
    name: &str,
    tag_of: impl Fn(&str) -> Result<u64, E>,
) -> Result<(String, Vec<(String, u32, String)>), String>
where
    E: std::fmt::Display,
{
    let key = Name::from_string(name);
    let rv = env
        .get_recursor(&key)
        .ok_or_else(|| format!("{name}: no recursor"))?;
    let rec = reflect_recursor(rv, env.get_const(&key)).map_err(|e| format!("{name}: {e}"))?;
    let render_name = |n: &str| -> Result<String, String> {
        tag_of(n)
            .map(|tag| format!("kcre_name_{tag}"))
            .map_err(|e| format!("{name}: {e}"))
    };
    let mut params = String::from("(ListType.nil Name)");
    for param in rec.level_params.iter().rev() {
        params = format!("(ListType.cons Name {} {params})", render_name(param)?);
    }
    let meta = format!(
        "RecMeta.mk {} {} {} {} {} (KConstSig.mk {params} {}) {}",
        nat_atom(u64::from(rec.num_params)),
        nat_atom(u64::from(rec.num_motives)),
        nat_atom(u64::from(rec.num_minors)),
        nat_atom(u64::from(rec.num_indices)),
        if rec.major_after_minors {
            "Bool.true"
        } else {
            "Bool.false"
        },
        render_image(&rec.type_, &render_name)?,
        nat_atom(u64::from(rec.is_k)),
    );
    let rules = rec
        .rules
        .iter()
        .map(|rule| {
            Ok((
                render_name(&rule.ctor)?,
                rule.num_fields,
                render_image(&rule.rhs, &render_name)?,
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok((meta, rules))
}

/// Render a reflected image with every name through `rn`.
fn render_image(
    image: &SpecExpr,
    rn: &dyn Fn(&str) -> Result<String, String>,
) -> Result<String, String> {
    fn level(l: &SpecLevel, rn: &dyn Fn(&str) -> Result<String, String>) -> Result<String, String> {
        Ok(match l {
            SpecLevel::Zero => "Level.zero".to_string(),
            SpecLevel::Param(p) => format!("(Level.param {})", rn(p)?),
            SpecLevel::Succ(x) => format!("(Level.succ {})", level(x, rn)?),
            SpecLevel::Max(a, b) => format!("(Level.max {} {})", level(a, rn)?, level(b, rn)?),
            SpecLevel::IMax(a, b) => format!("(Level.imax {} {})", level(a, rn)?, level(b, rn)?),
        })
    }
    fn expr(
        e: &SpecExpr,
        rn: &dyn Fn(&str) -> Result<String, String>,
        out: &mut String,
    ) -> Result<(), String> {
        match e {
            SpecExpr::Sort(l) => {
                let _ = write!(out, "(KExpr.sort {})", level(l, rn)?);
            }
            SpecExpr::BVar(i) => {
                let _ = write!(out, "(KExpr.bvar {})", nat_atom(u64::from(*i)));
            }
            SpecExpr::Const(n, ls) => {
                let mut levels = String::from("(ListType.nil Level)");
                for l in ls.iter().rev() {
                    levels = format!("(ListType.cons Level {} {levels})", level(l, rn)?);
                }
                let _ = write!(out, "(KExpr.const {} {levels})", rn(n)?);
            }
            SpecExpr::App(f, a) | SpecExpr::Lam(f, a) | SpecExpr::Pi(f, a) => {
                out.push_str(match e {
                    SpecExpr::App(..) => "(KExpr.app ",
                    SpecExpr::Lam(..) => "(KExpr.lam ",
                    _ => "(KExpr.pi ",
                });
                expr(f, rn, out)?;
                out.push(' ');
                expr(a, rn, out)?;
                out.push(')');
            }
            SpecExpr::Let_(t, v, b) => {
                out.push_str("(KExpr.let_ ");
                expr(t, rn, out)?;
                out.push(' ');
                expr(v, rn, out)?;
                out.push(' ');
                expr(b, rn, out)?;
                out.push(')');
            }
            SpecExpr::Lit(lit) => out.push_str(&render_literal(lit)),
        }
        Ok(())
    }
    let mut out = String::new();
    expr(image, rn, &mut out)?;
    Ok(out)
}

/// Actual structural names behind each display key in this bounded batch.
/// This prevents both collisions and lossy reconstruction through from_string.
#[derive(Default)]
struct SourceNames {
    by_display: BTreeMap<String, Name>,
}

impl SourceNames {
    fn record(&mut self, name: &Name) -> Result<(), ReflectError> {
        let display = name.to_string();
        if display.is_empty() || display.contains(['\t', '\n', '\r']) {
            return Err(ReflectError::InvalidReflection {
                detail: format!("source name {name:?} has no unambiguous interning TSV key"),
            });
        }
        if let Some(existing) = self.by_display.get(&display) {
            if existing != name {
                return Err(ReflectError::InvalidReflection {
                    detail: format!(
                        "distinct structural source names share display key {display:?}: {existing:?} versus {name:?}"
                    ),
                });
            }
        } else {
            self.by_display.insert(display, name.clone());
        }
        Ok(())
    }

    fn level(&mut self, level: &Level) -> Result<(), ReflectError> {
        match level {
            Level::Zero => Ok(()),
            Level::Param(name) => self.record(name),
            Level::Succ(inner) => self.level(inner),
            Level::Max(left, right) | Level::IMax(left, right) => {
                self.level(left)?;
                self.level(right)
            }
        }
    }

    fn expression(&mut self, e: &Expr, preserve_levels: bool) -> Result<(), ReflectError> {
        match e.kind() {
            ExprKind::Sort(level) if preserve_levels => self.level(level),
            ExprKind::Const(name, levels) => {
                self.record(name)?;
                if preserve_levels {
                    for level in levels.iter() {
                        self.level(level)?;
                    }
                }
                Ok(())
            }
            ExprKind::App(left, right)
            | ExprKind::Lam(_, left, right)
            | ExprKind::Pi(_, left, right) => {
                self.expression(left, preserve_levels)?;
                self.expression(right, preserve_levels)
            }
            ExprKind::Let(_, type_, value, body, _) => {
                self.expression(type_, preserve_levels)?;
                self.expression(value, preserve_levels)?;
                self.expression(body, preserve_levels)
            }
            ExprKind::MData(_, inner) => self.expression(inner, preserve_levels),
            // Called only after the complete expression was representable.
            // Active rule universe parameters enter the same structural registry.
            _ => Ok(()),
        }
    }
}

/// Reflect the foundation core of `env` (see module docs). Deterministic:
/// allowlist order for items, frequency-then-lexicographic interning order.
///
/// # Errors
/// Rejects the complete batch if distinct represented structural source names
/// share a display key, or a key cannot be represented in the interning TSV.
pub fn reflect_foundation_core(env: &Environment) -> Result<Reflection, ReflectError> {
    let mut recs: Vec<ReflectedRec> = Vec::new();
    let mut defs: Vec<ReflectedDef> = Vec::new();
    let mut source_names = SourceNames::default();
    for name in RESERVED_LITERAL_BUILTINS {
        source_names.record(&Name::from_string(name))?;
    }
    native_rule_keys::check_keys_in_prelude(&Environment::with_prelude())?;
    for name in RESERVED_NATIVE_RULE_KEYS {
        source_names.record(&Name::from_string(name))?;
    }
    let mut skips: Vec<SkipEntry> = vec![
        SkipEntry {
            item: "(model gap) Quot".to_string(),
            reason: "quotient primitives (Quot.mk/lift/ind reduction) are a kernel-native rule \
                     family, not RecursorVal rules; outside the RecEnv image. Their names are \
                     reserved native rule keys, so the KernelAcceptsTcIn / TypingTcIn quotient \
                     rules key on the reflected Quot.lift / Quot.ind / Quot.mk"
                .to_string(),
        },
        SkipEntry {
            item: "(model gap) struct-eta".to_string(),
            reason: "structure eta / projection reduction is kernel-native, not a RecursorVal \
                     rule; outside the RecEnv model"
                .to_string(),
        },
        SkipEntry {
            item: "(model gap) native-reducers".to_string(),
            reason: "kernel native reducers (Nat/BitVec accelerated ops) bypass rule-based \
                     reduction; outside the RecEnv model. The reduce_nat / reduce_int / \
                     reduce_int_pred_fold folds of the specification world's canonical heads \
                     are DERIVED KernelAcceptsTcIn conversions over the head's definition \
                     (the E4d native Nat / Int lemmas, generated/accepts_tc_native_nat.json), \
                     not RecEnv rules"
                .to_string(),
        },
        SkipEntry {
            item: "literals (constructor normalization)".to_string(),
            reason: "no longer a model gap: a literal leaf IS reflected, through the tagged \
                     literal codec -- a Nat literal as literal_nat n, a String literal as \
                     literal_string (string_lit_code cs) with cs its Unicode scalar values in \
                     order (literal_string_codec: the payload is the character list, a \
                     bijection proved both ways). Constructor normalization is not a RecEnv \
                     rule: it is the KernelAcceptsTcIn / TypingTcIn lit_zero / lit_succ rules \
                     (Nat) and lit_string_expand (String, keyed on the reflected String.ofList / \
                     Char.ofNat / List.cons / List.nil / Char names and the admission fact \
                     StringLitAdmitIn)"
                .to_string(),
        },
    ];

    for ind in REFLECT_INDUCTIVES {
        let rec_name = format!("{ind}.rec");
        let Some(rv) = env.get_recursor(&Name::from_string(&rec_name)) else {
            skips.push(SkipEntry {
                item: rec_name,
                reason: "recursor not found in the kernel environment".to_string(),
            });
            continue;
        };
        match reflect_recursor(rv, env.get_const(&rv.name)) {
            Ok(rec) => {
                source_names.record(&rv.name)?;
                for param in &rv.level_params {
                    source_names.record(param)?;
                }
                source_names.expression(&rv.type_, true)?;
                for rule in &rv.rules {
                    source_names.record(&rule.constructor_name)?;
                    source_names.expression(&rule.rhs, true)?;
                }
                if rec.is_k {
                    skips.push(SkipEntry {
                        item: format!("{rec_name} (K-extension)"),
                        reason: "is_k recursor: syntactic rules ARE reflected and RecMeta \
                                 carries the kernel's is_k flag; the K-like conversion itself \
                                 is the KernelAcceptsTcIn / TypingTcIn k_like rule (admission \
                                 fact RecKAdmitIn), not a RecEnv rule"
                            .to_string(),
                    });
                }
                recs.push(rec);
            }
            Err(reason) => skips.push(SkipEntry {
                item: rec_name,
                reason,
            }),
        }
    }

    for def in REFLECT_DEFS {
        let Some(ci) = env.get_const(&Name::from_string(def)) else {
            skips.push(SkipEntry {
                item: (*def).to_string(),
                reason: "constant not found in the kernel environment".to_string(),
            });
            continue;
        };
        match reflect_definition(ci) {
            Ok(reflected) => {
                source_names.record(&ci.name)?;
                for param in &ci.level_params {
                    source_names.record(param)?;
                }
                source_names.expression(&ci.type_, true)?;
                if let Some(value) = &ci.value {
                    source_names.expression(value, true)?;
                }
                defs.push(reflected);
            }
            Err(reason) => skips.push(SkipEntry {
                item: (*def).to_string(),
                reason,
            }),
        }
    }

    // Capture a bounded typing-data slice from actual source records, not the
    // modeled Nat fixture. Preserve partial-reflection diagnostics, but make
    // successful artifact emission require all four records below.
    let nat_signatures = match reflect_nat_signatures(env) {
        Ok(signatures) => {
            for signature in &signatures {
                let ci = env.get_const(&signature.name).ok_or_else(|| {
                    ReflectError::InvalidReflection {
                        detail: format!("captured signature {} disappeared", signature.name),
                    }
                })?;
                register_signature_source_names(ci, &mut source_names)?;
            }
            signatures
        }
        Err(reason) => {
            skips.push(SkipEntry {
                item: "(required typing slice) Nat/Nat.zero/Nat.succ/Nat.rec".to_string(),
                reason,
            });
            Vec::new()
        }
    };

    // Projection metadata is a required finite source image, not a new runtime
    // guard in the kernel's projection operator. A diagnostic partial image
    // may be returned, but cannot be published without this complete table.
    let (inductives, constructors, projection_witness) = match reflect_projection_metadata(env) {
        Ok((inductives, constructors, witness)) => {
            for signature in inductives
                .iter()
                .map(|ind| &ind.signature)
                .chain(constructors.iter().map(|ctor| &ctor.signature))
            {
                let ci = env.get_const(&signature.name).ok_or_else(|| {
                    ReflectError::InvalidReflection {
                        detail: format!(
                            "captured projection signature {} disappeared",
                            signature.name
                        ),
                    }
                })?;
                register_signature_source_names(ci, &mut source_names)?;
            }
            for ind in &inductives {
                for name in ind.constructor_names.iter().chain(&ind.all_names) {
                    source_names.record(name)?;
                }
            }
            for ctor in &constructors {
                source_names.record(&ctor.inductive_name)?;
            }
            (inductives, constructors, Some(witness))
        }
        Err(reason) => {
            skips.push(SkipEntry {
                item: "(required projection metadata) foundation inductives/constructors"
                    .to_string(),
                reason,
            });
            (Vec::new(), Vec::new(), None)
        }
    };

    // DELTA-CLOSURE HONESTY: every value-ful kernel constant referenced by a
    // reflected rhs/type/value but NOT itself reflected into the DefEnv is
    // delta-STUCK in the reflected env — ledger it so allowlist drift is
    // visible (with the current allowlist this section is empty).
    let mut referenced: BTreeMap<String, u64> = BTreeMap::new();
    for rec in &recs {
        count_consts(&rec.type_, &mut referenced);
        for rule in &rec.rules {
            count_consts(&rule.rhs, &mut referenced);
        }
    }
    for def in &defs {
        count_consts(&def.type_, &mut referenced);
        count_consts(&def.value, &mut referenced);
    }
    for signature in &nat_signatures {
        count_consts(&signature.type_, &mut referenced);
    }
    for signature in inductives
        .iter()
        .map(|ind| &ind.signature)
        .chain(constructors.iter().map(|ctor| &ctor.signature))
    {
        count_consts(&signature.type_, &mut referenced);
    }
    for name in referenced.keys() {
        let is_reflected_def = defs.iter().any(|d| &d.name == name);
        let actual_name =
            source_names
                .by_display
                .get(name)
                .ok_or_else(|| ReflectError::InvalidReflection {
                    detail: format!(
                        "constant dependency {name:?} has no actual structural source name"
                    ),
                })?;
        let is_valueful_const = env
            .get_const(actual_name)
            .is_some_and(|ci| ci.value.is_some());
        if is_valueful_const && !is_reflected_def {
            skips.push(SkipEntry {
                item: name.clone(),
                reason: "value-ful definition referenced by a reflected rhs/type/value but not in \
                         the DefEnv allowlist: delta-stuck in the reflected env"
                    .to_string(),
            });
        }
    }

    let mut interning = build_interning(&recs, &defs);
    append_signature_names(&mut interning, &nat_signatures);
    let projection_signatures = inductives
        .iter()
        .map(|ind| ind.signature.clone())
        .chain(constructors.iter().map(|ctor| ctor.signature.clone()))
        .collect::<Vec<_>>();
    append_signature_names(&mut interning, &projection_signatures);
    append_inductive_block_names(&mut interning, &inductives);
    native_rule_keys::append_native_rule_keys(&mut interning);
    Ok(Reflection {
        recs,
        defs,
        nat_signatures,
        inductives,
        constructors,
        projection_witness,
        interning,
        skips,
    })
}

// This is a signature-capture check, not a generic source admission theorem.
// The expected metadata and the looked-up ConstantInfo must agree before any
// field is translated. Inductive/constructor/recursor CIs are Definition-kind
// and value-less in the current source; they must not enter REFLECT_DEFS.
fn reflect_source_signature(
    name: &Name,
    params: &[Name],
    type_: &Expr,
    constant: Option<&ConstantInfo>,
) -> Result<ReflectedConstSig, String> {
    let ci = constant.ok_or_else(|| format!("required signature {name} is absent"))?;
    if &ci.name != name {
        return Err(format!(
            "signature {name}: actual ConstantInfo name mismatch"
        ));
    }
    if ci.level_params != params {
        return Err(format!(
            "signature {name}: ordered universe parameters mismatch"
        ));
    }
    if &ci.type_ != type_ {
        return Err(format!("signature {name}: schematic type mismatch"));
    }
    if ci.kind != ConstantKind::Definition || ci.value.is_some() {
        return Err(format!(
            "signature {name}: expected this finite source family's value-less Definition entry"
        ));
    }
    Ok(ReflectedConstSig {
        name: ci.name.clone(),
        level_params: ci.level_params.clone(),
        type_: reflect_definition_expr(&ci.type_)
            .map_err(|reason| format!("signature {name} type unrepresentable: {reason}"))?,
    })
}

fn reflect_nat_signatures(env: &Environment) -> Result<Vec<ReflectedConstSig>, String> {
    let requested = Name::from_string("Nat.rec");
    let rec = env
        .get_recursor(&requested)
        .ok_or_else(|| "required Nat.rec metadata is absent".to_string())?;
    if rec.name != requested || rec.inductive_name != Name::from_string("Nat") {
        return Err("Nat.rec metadata has the wrong structural identity/family".to_string());
    }
    let ind = env
        .get_inductive(&rec.inductive_name)
        .ok_or_else(|| "required Nat family metadata is absent".to_string())?;
    if ind.name != rec.inductive_name
        || ind.constructor_names != [Name::from_string("Nat.zero"), Name::from_string("Nat.succ")]
    {
        return Err("Nat family identity or ordered constructor names disagree".to_string());
    }
    let mut signatures = vec![reflect_source_signature(
        &ind.name,
        &ind.level_params,
        &ind.type_,
        env.get_const(&ind.name),
    )?];
    for (index, name) in ind.constructor_names.iter().enumerate() {
        let ctor = env
            .get_constructor(name)
            .ok_or_else(|| format!("required constructor metadata {name} is absent"))?;
        if &ctor.name != name
            || ctor.inductive_name != ind.name
            || ctor.constructor_idx as usize != index
            || ctor.level_params != ind.level_params
        {
            return Err(format!(
                "constructor {name}: source family/order/parameters disagree"
            ));
        }
        signatures.push(reflect_source_signature(
            &ctor.name,
            &ctor.level_params,
            &ctor.type_,
            env.get_const(&ctor.name),
        )?);
    }
    signatures.push(reflect_source_signature(
        &rec.name,
        &rec.level_params,
        &rec.type_,
        env.get_const(&rec.name),
    )?);
    Ok(signatures)
}

// These are structural capture guards, not a reimplementation of strict
// positivity or admission. Preserve the ordered list exactly, including when
// it is the originals-only result of nested restoration.
fn validate_inductive_block_names(
    family: &Name,
    all_names: &[Name],
    constructor_names: &[Name],
) -> Result<(), String> {
    if all_names.is_empty() || !all_names.contains(family) {
        return Err(format!(
            "inductive {family}: final block is empty or omits its own family"
        ));
    }
    let mut seen = std::collections::HashSet::new();
    let mut names = SourceNames::default();
    for name in all_names {
        if !seen.insert(name) {
            return Err(format!("inductive {family}: repeated final block identity"));
        }
        names.record(name).map_err(|error| error.to_string())?;
    }
    for name in constructor_names {
        if all_names.contains(name) {
            return Err(format!(
                "inductive {family}: constructor identity collides with final block family"
            ));
        }
        names.record(name).map_err(|error| error.to_string())?;
    }
    Ok(())
}

// Read the actual final Environment, not a reconstructed declaration. Each
// named sibling must still be an inductive and report the same ordered block,
// parameter count and ordered universe parameters. Sibling types and index
// counts need NOT agree. These checks do not connect a nested-restored block to
// the auxiliary-inclusive block used by the source's earlier strict validator.
fn validate_source_inductive_block(env: &Environment, ind: &InductiveVal) -> Result<(), String> {
    validate_inductive_block_names(&ind.name, &ind.all_names, &ind.constructor_names)?;
    // Resolve every identity before comparing lists, so absent/wrong-kind
    // members are diagnosed as lookup failures rather than list disagreement.
    let members = ind
        .all_names
        .iter()
        .map(|name| {
            env.get_inductive(name).ok_or_else(|| {
                format!(
                    "inductive {}: final block member {name} has absent or wrong-kind metadata",
                    ind.name
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (name, member) in ind.all_names.iter().zip(members) {
        if &member.name != name
            || member.all_names != ind.all_names
            || member.num_params != ind.num_params
            || member.level_params != ind.level_params
        {
            return Err(format!(
                "inductive {}: final block member {name} identity/order/parameters disagree",
                ind.name
            ));
        }
        validate_inductive_block_names(&member.name, &member.all_names, &member.constructor_names)?;
    }
    Ok(())
}

fn reflect_inductive_metadata(
    expected: &Name,
    ind: &InductiveVal,
    constant: Option<&ConstantInfo>,
) -> Result<ReflectedInductive, String> {
    if &ind.name != expected {
        return Err(format!("inductive {expected}: source identity mismatch"));
    }
    validate_inductive_block_names(&ind.name, &ind.all_names, &ind.constructor_names)?;
    if ind.num_params.checked_add(ind.num_indices)
        != Some(clean_kernel::inductive::count_pi_args(&ind.type_))
    {
        return Err(format!(
            "inductive {expected}: parameter/index telescope count mismatch"
        ));
    }
    let mut seen = std::collections::HashSet::new();
    for name in &ind.constructor_names {
        if name == &ind.name || !seen.insert(name) {
            return Err(format!(
                "inductive {expected}: repeated/colliding constructor identity"
            ));
        }
    }
    Ok(ReflectedInductive {
        signature: reflect_source_signature(&ind.name, &ind.level_params, &ind.type_, constant)?,
        num_params: ind.num_params,
        num_indices: ind.num_indices,
        constructor_names: ind.constructor_names.clone(),
        all_names: ind.all_names.clone(),
    })
}

fn reflect_constructor_metadata(
    ind: &InductiveVal,
    index: usize,
    ctor: &ConstructorVal,
    constant: Option<&ConstantInfo>,
) -> Result<ReflectedConstructor, String> {
    if ind.constructor_names.get(index) != Some(&ctor.name)
        || ctor.inductive_name != ind.name
        || ctor.constructor_idx as usize != index
        || ctor.num_params != ind.num_params
        || ctor.level_params != ind.level_params
    {
        return Err(format!(
            "constructor {}: source parent/order/parameters disagree",
            ctor.name
        ));
    }
    // Reuse the actual builder's telescope counter, rather than inventing an
    // independently normalized arity. This is a bounded source-capture check.
    if ctor.num_params.checked_add(ctor.num_fields)
        != Some(clean_kernel::inductive::count_pi_args(&ctor.type_))
    {
        return Err(format!(
            "constructor {}: parameter/field telescope count mismatch",
            ctor.name
        ));
    }
    Ok(ReflectedConstructor {
        signature: reflect_source_signature(&ctor.name, &ctor.level_params, &ctor.type_, constant)?,
        inductive_name: ctor.inductive_name.clone(),
        num_params: ctor.num_params,
        num_fields: ctor.num_fields,
        constructor_idx: ctor.constructor_idx,
    })
}

fn reflect_projection_metadata(
    env: &Environment,
) -> Result<
    (
        Vec<ReflectedInductive>,
        Vec<ReflectedConstructor>,
        ReflectedProjectionWitness,
    ),
    String,
> {
    let mut inductives = Vec::new();
    let mut constructors = Vec::new();
    let mut names = std::collections::HashSet::new();
    for spelling in REFLECT_INDUCTIVES {
        let expected = Name::from_string(spelling);
        let ind = env
            .get_inductive(&expected)
            .ok_or_else(|| format!("required inductive metadata {expected} is absent"))?;
        validate_source_inductive_block(env, ind)?;
        let reflected = reflect_inductive_metadata(&expected, ind, env.get_const(&expected))?;
        if !names.insert(ind.name.clone()) {
            return Err(format!(
                "projection metadata name {} is duplicated",
                ind.name
            ));
        }
        for (index, name) in ind.constructor_names.iter().enumerate() {
            let ctor = env
                .get_constructor(name)
                .ok_or_else(|| format!("required constructor metadata {name} is absent"))?;
            let reflected_ctor =
                reflect_constructor_metadata(ind, index, ctor, env.get_const(name))?;
            if !names.insert(ctor.name.clone()) {
                return Err(format!(
                    "projection metadata name {} is duplicated",
                    ctor.name
                ));
            }
            constructors.push(reflected_ctor);
        }
        inductives.push(reflected);
    }
    let prod = env
        .get_inductive(&Name::from_string("ProdType"))
        .ok_or_else(|| "required ProdType witness metadata is absent".to_string())?;
    if prod.num_params != 2
        || prod.num_indices != 0
        || !prod.level_params.is_empty()
        || prod.constructor_names.len() != 1
    {
        return Err(
            "the finite ProdType witness requires its actual monomorphic two-parameter structure"
                .to_string(),
        );
    }
    let ctor = env
        .get_constructor(&prod.constructor_names[0])
        .ok_or_else(|| "required ProdType constructor is absent".to_string())?;
    if ctor.num_fields != 2 {
        return Err("the finite ProdType witness requires two actual fields".to_string());
    }
    let actual_name = |name: &str| {
        env.get_const(&Name::from_string(name))
            .map(|ci| Expr::const_(ci.name.clone(), vec![]))
            .ok_or_else(|| format!("required ProdType witness argument {name} is absent"))
    };
    let nat = actual_name("Nat")?;
    let zero = actual_name("Nat.zero")?;
    let one = Expr::app(actual_name("Nat.succ")?, zero.clone());
    let value = [nat.clone(), nat.clone(), zero, one]
        .into_iter()
        .fold(Expr::const_(ctor.name.clone(), vec![]), Expr::app);
    let type_ = TypeChecker::new(env)
        .infer_type_full(&value)
        .map_err(|error| format!("actual ProdType constructor caller is ill typed: {error}"))?;
    let expected = Expr::app(
        Expr::app(Expr::const_(prod.name.clone(), vec![]), nat.clone()),
        nat,
    );
    if type_ != expected {
        return Err("actual ProdType caller inferred a different type".to_string());
    }
    Ok((
        inductives,
        constructors,
        ReflectedProjectionWitness {
            value: reflect_definition_expr(&value)?,
            type_: reflect_definition_expr(&type_)?,
        },
    ))
}

fn register_signature_source_names(
    ci: &ConstantInfo,
    source_names: &mut SourceNames,
) -> Result<(), ReflectError> {
    source_names.record(&ci.name)?;
    for param in &ci.level_params {
        source_names.record(param)?;
    }
    source_names.expression(&ci.type_, true)
}

// The existing reduction image keeps its frequency-derived tags. Signature-only
// names are appended lexicographically; repeated names do not reweight old tags.
fn append_signature_names(interning: &mut Vec<(String, u64)>, signatures: &[ReflectedConstSig]) {
    let mut names = BTreeMap::new();
    for signature in signatures {
        bump(&signature.name.to_string(), &mut names);
        for param in &signature.level_params {
            bump(&param.to_string(), &mut names);
        }
        count_semantic_names(&signature.type_, &mut names);
    }
    for name in names.into_keys() {
        if !interning.iter().any(|(existing, _)| existing == &name) {
            interning.push((name, interning.len() as u64));
        }
    }
}

// Append only previously unseen semantic keys after ALL existing signature
// tags. Sorting these new keys never sorts or deduplicates the captured block.
fn append_inductive_block_names(
    interning: &mut Vec<(String, u64)>,
    inductives: &[ReflectedInductive],
) {
    let names = inductives
        .iter()
        .flat_map(|ind| &ind.all_names)
        .map(ToString::to_string)
        .collect::<std::collections::BTreeSet<_>>();
    for name in names {
        if !interning.iter().any(|(existing, _)| existing == &name) {
            interning.push((name, interning.len() as u64));
        }
    }
}

/// Reflect the complete definition record from one actual kernel constant.
/// An unrepresentable type OR value rejects the record whole; fields are never
/// borrowed from another declaration or replaced by an invented sort.
fn reflect_definition(ci: &ConstantInfo) -> Result<ReflectedDef, String> {
    // The current allowlist consists of ordinary computational definitions.
    // A stored value alone is not permission to unfold: opaque declarations
    // also retain values. Full kernel delta can unfold Theorem, but extending
    // this bounded reflection to that separate kind requires an explicit policy.
    if ci.kind != ConstantKind::Definition {
        return Err(format!(
            "unsupported declaration kind {:?}: this reflection accepts ordinary definitions only",
            ci.kind
        ));
    }
    let value = ci
        .value
        .as_ref()
        .ok_or_else(|| "constant has no value; nothing to unfold".to_string())?;
    let type_ = reflect_definition_expr(&ci.type_)
        .map_err(|reason| format!("schematic type unrepresentable: {reason}"))?;
    let value = reflect_definition_expr(value)
        .map_err(|reason| format!("value unrepresentable: {reason}"))?;
    Ok(ReflectedDef {
        name: ci.name.to_string(),
        is_reducible: ci.is_reducible,
        level_params: ci.level_params.iter().map(ToString::to_string).collect(),
        type_,
        value,
    })
}

/// Reflect one kernel [`RecursorVal`]; errors are skip reasons. The stored
/// signature must match the constant queried by the actual structural Name.
/// This consistency check is not validation of typed recursor admission,
/// alternate argument layouts, unsafe/partial policy, or rule RHS semantics.
fn reflect_recursor(
    rv: &RecursorVal,
    constant: Option<&ConstantInfo>,
) -> Result<ReflectedRec, String> {
    if rv.arg_order != RecursorArgOrder::MajorAfterMinors {
        return Err(format!(
            "arg order {:?}: iota_reduct models only the MajorAfterMinors layout",
            rv.arg_order
        ));
    }
    let constant =
        constant.ok_or_else(|| "recursor ConstantInfo signature not found".to_string())?;
    if constant.name != rv.name {
        return Err("recursor/ConstantInfo name mismatch".to_string());
    }
    if constant.level_params != rv.level_params {
        return Err("recursor/ConstantInfo ordered universe parameters mismatch".to_string());
    }
    if constant.type_ != rv.type_ {
        return Err("recursor/ConstantInfo schematic type mismatch".to_string());
    }
    let type_ = reflect_definition_expr(&rv.type_)
        .map_err(|reason| format!("recursor schematic type unrepresentable: {reason}"))?;
    let mut rules = Vec::with_capacity(rv.rules.len());
    for rule in &rv.rules {
        // Production selects this branch using the immediate AST tag. Both
        // adapters erase MData, so checking the reflected Lam is insufficient.
        if !rule.rhs.is_lam() {
            return Err(format!(
                "rule for {} is not an immediate source Lambda; legacy non-lambda/fallback RHS branch is outside the reflected image",
                rule.constructor_name
            ));
        }
        let rhs = reflect_definition_expr(&rule.rhs).map_err(|reason| {
            format!(
                "rule for {} has unrepresentable rhs: {reason}",
                rule.constructor_name
            )
        })?;
        rules.push(ReflectedRule {
            ctor: rule.constructor_name.to_string(),
            num_fields: rule.num_fields,
            rhs,
        });
    }
    Ok(ReflectedRec {
        name: rv.name.to_string(),
        level_params: rv.level_params.iter().map(ToString::to_string).collect(),
        type_,
        num_params: rv.num_params,
        num_motives: rv.num_motives,
        num_minors: rv.num_minors,
        num_indices: rv.num_indices,
        major_after_minors: true,
        is_k: rv.is_k,
        rules,
    })
}

/// Count every name occurrence (recursor keys, rule ctor keys, def keys,
/// consts and level parameters inside terms) and assign unary tags by (count desc, name asc) so
/// the hottest names get the shortest `Nat.succ` chains. Injective by
/// construction (one tag per distinct string). Missing literal builtin names
/// are appended in the declared reservation order, preserving encountered tags.
/// The separate signature-only slice subsequently appends new semantic names
/// without reweighting this existing reduction-image table.
fn build_interning(recs: &[ReflectedRec], defs: &[ReflectedDef]) -> Vec<(String, u64)> {
    let mut counts: BTreeMap<String, u64> = BTreeMap::new();
    for rec in recs {
        bump(&rec.name, &mut counts);
        for param in &rec.level_params {
            bump(param, &mut counts);
        }
        count_semantic_names(&rec.type_, &mut counts);
        for rule in &rec.rules {
            bump(&rule.ctor, &mut counts);
            count_semantic_names(&rule.rhs, &mut counts);
        }
    }
    for def in defs {
        bump(&def.name, &mut counts);
        for param in &def.level_params {
            bump(param, &mut counts);
        }
        count_semantic_names(&def.type_, &mut counts);
        count_semantic_names(&def.value, &mut counts);
    }
    let mut by_freq: Vec<(String, u64)> = counts.into_iter().collect();
    by_freq.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let mut interning: Vec<(String, u64)> = by_freq
        .into_iter()
        .enumerate()
        .map(|(tag, (name, _count))| (name, tag as u64))
        .collect();
    for &name in RESERVED_LITERAL_BUILTINS {
        if !interning.iter().any(|(existing, _)| existing == name) {
            interning.push((name.to_string(), interning.len() as u64));
        }
    }
    interning
}

fn bump(name: &str, counts: &mut BTreeMap<String, u64>) {
    *counts.entry(name.to_string()).or_insert(0) += 1;
}

fn count_level_names(level: &SpecLevel, counts: &mut BTreeMap<String, u64>) {
    match level {
        SpecLevel::Zero => {}
        SpecLevel::Param(name) => bump(name, counts),
        SpecLevel::Succ(inner) => count_level_names(inner, counts),
        SpecLevel::Max(left, right) | SpecLevel::IMax(left, right) => {
            count_level_names(left, counts);
            count_level_names(right, counts);
        }
    }
}

/// Interning includes universe parameter occurrences; they are not delta edges.
fn count_semantic_names(e: &SpecExpr, counts: &mut BTreeMap<String, u64>) {
    match e {
        SpecExpr::Sort(level) => count_level_names(level, counts),
        SpecExpr::BVar(_) => {}
        SpecExpr::Const(name, levels) => {
            bump(name, counts);
            for level in levels {
                count_level_names(level, counts);
            }
        }
        SpecExpr::App(left, right) | SpecExpr::Lam(left, right) | SpecExpr::Pi(left, right) => {
            count_semantic_names(left, counts);
            count_semantic_names(right, counts);
        }
        SpecExpr::Let_(type_, value, body) => {
            count_semantic_names(type_, counts);
            count_semantic_names(value, counts);
            count_semantic_names(body, counts);
        }
        // The codec's defs are spec definitions, not interned kernel names.
        SpecExpr::Lit(_) => {}
    }
}

/// Only actual constant expression nodes are definition-dependency edges.
fn count_consts(e: &SpecExpr, counts: &mut BTreeMap<String, u64>) {
    match e {
        SpecExpr::Sort(_) | SpecExpr::BVar(_) => {}
        SpecExpr::Const(n, _) => *counts.entry(n.clone()).or_insert(0) += 1,
        SpecExpr::App(a, b) | SpecExpr::Lam(a, b) | SpecExpr::Pi(a, b) => {
            count_consts(a, counts);
            count_consts(b, counts);
        }
        SpecExpr::Let_(a, b, c) => {
            count_consts(a, counts);
            count_consts(b, counts);
            count_consts(c, counts);
        }
        SpecExpr::Lit(_) => {}
    }
}

fn max_nat_in_expr(e: &SpecExpr) -> u64 {
    match e {
        SpecExpr::Sort(_) => 0,
        SpecExpr::BVar(i) => u64::from(*i),
        SpecExpr::Const(..) => 0,
        SpecExpr::App(a, b) | SpecExpr::Lam(a, b) | SpecExpr::Pi(a, b) => {
            max_nat_in_expr(a).max(max_nat_in_expr(b))
        }
        SpecExpr::Let_(a, b, c) => max_nat_in_expr(a)
            .max(max_nat_in_expr(b))
            .max(max_nat_in_expr(c)),
        // Literal numerals render inline as decimal, never as pool atoms.
        SpecExpr::Lit(_) => 0,
    }
}

fn reflected_pi_arity(mut expr: &SpecExpr) -> u32 {
    let mut arity = 0_u32;
    while let SpecExpr::Pi(_, body) = expr {
        arity = arity.saturating_add(1);
        expr = body;
    }
    arity
}

/// Maximum parenthesis nesting depth of a rendered line — the measured
/// quantity the parser's `MAX_EXPR_DEPTH = 128` guard constrains.
#[must_use]
pub fn max_paren_depth(s: &str) -> u32 {
    let mut d: u32 = 0;
    let mut mx: u32 = 0;
    for c in s.chars() {
        match c {
            '(' => {
                d += 1;
                if d > mx {
                    mx = d;
                }
            }
            ')' => d = d.saturating_sub(1),
            _ => {}
        }
    }
    mx
}

/// Unary spec-Nat literal for `n` (`Nat.zero` / `(Nat.succ ...)`). Used only
/// inside the depth-2 `kcre_nat_*` helper definitions — inlining unary
/// literals into the env term blows the parser's `MAX_EXPR_DEPTH = 128` guard
/// (measured: the naive single literal reaches paren depth 163; with
/// `kcre_nat_*`/`kcre_name_*` atom leaves it is 64).
#[must_use]
pub fn render_nat(n: u64) -> String {
    let mut s = String::from("Nat.zero");
    for _ in 0..n {
        s = format!("(Nat.succ {s})");
    }
    s
}

/// The depth-1 spec-Nat atom for `n` (`kcre_nat_<n>`), backed by the helper
/// definition pool emitted at the top of the generated def script.
#[must_use]
fn nat_atom(n: u64) -> String {
    format!("kcre_nat_{n}")
}

/// Nat-shaped spec-`Level` literal for a level-erased sort depth `n`
/// (`Level.zero` / `(Level.succ ...)`). Since the levels-promotion B2 flip
/// (`KExpr.sort : Level`), the reflected sort argument must be a `Level`, not a
/// `Nat`. This keeps the SAME level-collapse semantics as `erase_level_to_nat`
/// (param/imax already folded to a height) but re-encodes that height as the
/// unary spec `Level` `Level.succ^n Level.zero`. Sort depths are tiny (0/1 in
/// the foundation core), so inlining stays well under the parser depth guard.
/// Kept only as a legacy numeric-level rendering utility; definition images
/// use structural `Reflection::render_level` instead.
#[must_use]
pub fn render_level_of_nat(n: u64) -> String {
    let mut s = String::from("Level.zero");
    for _ in 0..n {
        s = format!("(Level.succ {s})");
    }
    s
}

impl Reflection {
    // Internal image consistency only: an unselected member can have no
    // signature in this finite image. A coherently truncated/forged image is
    // not authenticated by these guards; source capture and independent
    // field-for-field fidelity remain the authority for the complete list.
    fn validate_inductive_blocks(&self) -> Result<(), ReflectError> {
        let invalid = |detail: String| ReflectError::InvalidReflection { detail };
        let mut names = SourceNames::default();
        let mut membership = std::collections::HashMap::<&Name, &ReflectedInductive>::new();
        for ind in &self.inductives {
            validate_inductive_block_names(
                &ind.signature.name,
                &ind.all_names,
                &ind.constructor_names,
            )
            .map_err(invalid)?;
            for name in &ind.all_names {
                names.record(name)?;
                if self
                    .constructors
                    .iter()
                    .any(|ctor| &ctor.signature.name == name)
                    || self.recs.iter().any(|rec| rec.name == name.to_string())
                    || self.defs.iter().any(|def| def.name == name.to_string())
                {
                    return Err(invalid(format!(
                        "final block member {name} has a non-inductive image"
                    )));
                }
                if let Some(previous) = membership.insert(name, ind) {
                    if previous.all_names != ind.all_names
                        || previous.num_params != ind.num_params
                        || previous.signature.level_params != ind.signature.level_params
                    {
                        return Err(invalid(format!(
                            "final block member {name}: image order/parameters disagree"
                        )));
                    }
                }
                if let Some(member) = self
                    .inductives
                    .iter()
                    .find(|other| &other.signature.name == name)
                {
                    if member.all_names != ind.all_names
                        || member.num_params != ind.num_params
                        || member.signature.level_params != ind.signature.level_params
                    {
                        return Err(invalid(format!(
                            "final block member {name}: selected image order/parameters disagree"
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_projection_metadata(&self) -> Result<(), ReflectError> {
        let invalid = |detail: String| ReflectError::InvalidReflection { detail };
        if self.inductives.len() != REFLECT_INDUCTIVES.len() {
            return Err(invalid(
                "required projection metadata must contain every allowlisted inductive".to_string(),
            ));
        }
        self.validate_inductive_blocks()?;
        let mut constructors = self.constructors.iter();
        let mut names = SourceNames::default();
        let mut seen = std::collections::HashSet::new();
        for (ind, expected) in self.inductives.iter().zip(REFLECT_INDUCTIVES) {
            if ind.signature.name != Name::from_string(expected)
                || !seen.insert(&ind.signature.name)
            {
                return Err(invalid(format!(
                    "projection inductive order/identity mismatch at {expected}"
                )));
            }
            if ind.num_params.checked_add(ind.num_indices)
                != Some(reflected_pi_arity(&ind.signature.type_))
            {
                return Err(invalid(format!(
                    "projection inductive {expected}: telescope count mismatch"
                )));
            }
            names.record(&ind.signature.name)?;
            for name in &ind.all_names {
                names.record(name)?;
            }
            for parameter in &ind.signature.level_params {
                names.record(parameter)?;
            }
            for (index, name) in ind.constructor_names.iter().enumerate() {
                let ctor = constructors
                    .next()
                    .ok_or_else(|| invalid(format!("missing projection constructor {name}")))?;
                if &ctor.signature.name != name
                    || ctor.inductive_name != ind.signature.name
                    || ctor.constructor_idx as usize != index
                    || ctor.num_params != ind.num_params
                    || ctor.signature.level_params != ind.signature.level_params
                    || !seen.insert(&ctor.signature.name)
                {
                    return Err(invalid(format!(
                        "projection constructor {name}: parent/order/parameters disagree"
                    )));
                }
                if ctor.num_params.checked_add(ctor.num_fields)
                    != Some(reflected_pi_arity(&ctor.signature.type_))
                {
                    return Err(invalid(format!(
                        "projection constructor {name}: telescope count mismatch"
                    )));
                }
                names.record(name)?;
                names.record(&ctor.inductive_name)?;
                for parameter in &ctor.signature.level_params {
                    names.record(parameter)?;
                }
            }
        }
        if constructors.next().is_some() {
            return Err(invalid(
                "projection table has unassociated extra constructors".to_string(),
            ));
        }
        for signature in self.nat_signatures.iter().take(3) {
            let same = self
                .inductives
                .iter()
                .map(|ind| &ind.signature)
                .chain(self.constructors.iter().map(|ctor| &ctor.signature))
                .find(|candidate| candidate.name == signature.name);
            if same != Some(signature) {
                return Err(invalid(format!(
                    "Nat typing/projection signatures disagree at {}",
                    signature.name
                )));
            }
        }
        if self.projection_witness.is_none() {
            return Err(invalid(
                "required source-checked ProdType witness is absent".to_string(),
            ));
        }
        Ok(())
    }

    fn validate_for_emission(&self) -> Result<(), ReflectError> {
        if !self.interning_injective() {
            return Err(ReflectError::InvalidReflection {
                detail: "interning table is not injective".to_string(),
            });
        }
        let mut tags = self
            .interning
            .iter()
            .map(|(_, tag)| *tag)
            .collect::<Vec<_>>();
        tags.sort_unstable();
        for (expected, actual) in (0_u64..).zip(tags) {
            if expected != actual {
                return Err(ReflectError::InvalidReflection {
                    detail: format!(
                        "interning tags are not contiguous from zero: expected {expected}, found {actual}"
                    ),
                });
            }
        }

        let mut required_names: std::collections::BTreeSet<String> = RESERVED_LITERAL_BUILTINS
            .iter()
            .chain(RESERVED_NATIVE_RULE_KEYS)
            .map(|name| (*name).to_string())
            .collect();
        for rec in &self.recs {
            required_names.insert(rec.name.clone());
            required_names.extend(rec.level_params.iter().cloned());
            let mut signature_names = BTreeMap::new();
            count_semantic_names(&rec.type_, &mut signature_names);
            required_names.extend(signature_names.into_keys());
            for rule in &rec.rules {
                required_names.insert(rule.ctor.clone());
                let mut referenced = BTreeMap::new();
                count_semantic_names(&rule.rhs, &mut referenced);
                required_names.extend(referenced.into_keys());
            }
        }
        for def in &self.defs {
            required_names.insert(def.name.clone());
            required_names.extend(def.level_params.iter().cloned());
            let mut referenced = BTreeMap::new();
            count_semantic_names(&def.type_, &mut referenced);
            count_semantic_names(&def.value, &mut referenced);
            required_names.extend(referenced.into_keys());
        }
        if self.nat_signatures.len() != NAT_SIGNATURE_NAMES.len() {
            return Err(ReflectError::InvalidReflection {
                detail: "required Nat typing slice must contain all four source signatures"
                    .to_string(),
            });
        }
        for (signature, expected) in self.nat_signatures.iter().zip(NAT_SIGNATURE_NAMES) {
            if signature.name != Name::from_string(expected) {
                return Err(ReflectError::InvalidReflection {
                    detail: format!("required Nat signature order/identity mismatch at {expected}"),
                });
            }
            required_names.insert(signature.name.to_string());
            required_names.extend(signature.level_params.iter().map(ToString::to_string));
            let mut referenced = BTreeMap::new();
            count_semantic_names(&signature.type_, &mut referenced);
            required_names.extend(referenced.into_keys());
        }
        self.validate_projection_metadata()?;
        for ind in &self.inductives {
            required_names.extend(ind.all_names.iter().map(ToString::to_string));
        }
        for signature in self
            .inductives
            .iter()
            .map(|ind| &ind.signature)
            .chain(self.constructors.iter().map(|ctor| &ctor.signature))
        {
            required_names.insert(signature.name.to_string());
            required_names.extend(signature.level_params.iter().map(ToString::to_string));
            let mut referenced = BTreeMap::new();
            count_semantic_names(&signature.type_, &mut referenced);
            required_names.extend(referenced.into_keys());
        }
        if let Some(witness) = &self.projection_witness {
            let mut referenced = BTreeMap::new();
            count_semantic_names(&witness.value, &mut referenced);
            count_semantic_names(&witness.type_, &mut referenced);
            required_names.extend(referenced.into_keys());
        }
        for name in required_names {
            if self.tag_of(&name).is_none() {
                return Err(ReflectError::InvalidReflection {
                    detail: format!("semantic name {name:?} has no interning entry"),
                });
            }
        }

        let nat_rec = self
            .recs
            .iter()
            .find(|rec| rec.name == "Nat.rec")
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "required non-vacuity witness recursor Nat.rec was not reflected"
                    .to_string(),
            })?;
        let signature = &self.nat_signatures[3];
        if signature.name.to_string() != nat_rec.name
            || signature
                .level_params
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                != nat_rec.level_params
            || signature.type_ != nat_rec.type_
        {
            return Err(ReflectError::InvalidReflection {
                detail: "Nat typing slice and active recursor signature disagree".to_string(),
            });
        }
        if nat_rec.level_params.len() != 1 {
            return Err(ReflectError::InvalidReflection {
                detail: format!(
                    "the Nat.rec witness explicitly chooses [Level.zero], but the actual signature declares {} universe parameters",
                    nat_rec.level_params.len()
                ),
            });
        }
        if !nat_rec.rules.iter().any(|rule| rule.ctor == "Nat.zero") {
            return Err(ReflectError::InvalidReflection {
                detail: "required Nat.rec/Nat.zero non-vacuity rule was not reflected".to_string(),
            });
        }
        let Some(delta_witness) = self
            .defs
            .iter()
            .find(|def| def.name == "def_env_lift_closed_b")
        else {
            return Err(ReflectError::InvalidReflection {
                detail: "required delta witness definition def_env_lift_closed_b was not reflected"
                    .to_string(),
            });
        };
        if !delta_witness.level_params.is_empty() {
            return Err(ReflectError::InvalidReflection {
                detail: "the delta non-vacuity witness supplies zero universe arguments, but def_env_lift_closed_b declares parameters"
                    .to_string(),
            });
        }
        Ok(())
    }

    /// Interning-table lookup (real name -> tag). All names occurring in the
    /// reflection are present by construction.
    fn tag_of(&self, name: &str) -> Option<u64> {
        self.interning
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, t)| *t)
    }

    /// Spec `Name` atom for a real name (trust edge 1): `kcre_name_<tag>`,
    /// backed by the helper definition
    /// `def kcre_name_<tag> : Name := Name.str Name.anonymous kcre_nat_<tag>`.
    fn render_name(&self, name: &str) -> Result<String, ReflectError> {
        let tag = self
            .tag_of(name)
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: format!("semantic name {name:?} has no interning entry"),
            })?;
        Ok(format!("kcre_name_{tag}"))
    }

    /// Largest Nat needed by any leaf of the reflection (interning tags,
    /// RecMeta counts, rule field counts, bvar indices) — the
    /// size of the `kcre_nat_*` helper pool.
    #[must_use]
    pub fn max_nat_used(&self) -> u64 {
        let mut mx = self.interning.iter().map(|(_, t)| *t).max().unwrap_or(0);
        for rec in &self.recs {
            mx = mx.max(max_nat_in_expr(&rec.type_));
            for n in [
                u64::from(rec.num_params),
                u64::from(rec.num_motives),
                u64::from(rec.num_minors),
                u64::from(rec.num_indices),
            ] {
                mx = mx.max(n);
            }
            for rule in &rec.rules {
                mx = mx.max(u64::from(rule.num_fields));
                mx = mx.max(max_nat_in_expr(&rule.rhs));
            }
        }
        for def in &self.defs {
            mx = mx.max(max_nat_in_expr(&def.type_));
            mx = mx.max(max_nat_in_expr(&def.value));
        }
        for signature in &self.nat_signatures {
            mx = mx.max(max_nat_in_expr(&signature.type_));
        }
        for ind in &self.inductives {
            mx = mx
                .max(max_nat_in_expr(&ind.signature.type_))
                .max(u64::from(ind.num_params))
                .max(u64::from(ind.num_indices));
        }
        for ctor in &self.constructors {
            mx = mx
                .max(max_nat_in_expr(&ctor.signature.type_))
                .max(u64::from(ctor.num_params))
                .max(u64::from(ctor.num_fields))
                .max(u64::from(ctor.constructor_idx));
        }
        if let Some(witness) = &self.projection_witness {
            mx = mx
                .max(max_nat_in_expr(&witness.value))
                .max(max_nat_in_expr(&witness.type_));
        }
        mx
    }

    fn render_level(&self, l: &SpecLevel) -> Result<String, ReflectError> {
        Ok(match l {
            SpecLevel::Zero => "Level.zero".to_string(),
            SpecLevel::Param(name) => format!("(Level.param {})", self.render_name(name)?),
            SpecLevel::Succ(x) => format!("(Level.succ {})", self.render_level(x)?),
            SpecLevel::Max(a, b) => format!(
                "(Level.max {} {})",
                self.render_level(a)?,
                self.render_level(b)?
            ),
            SpecLevel::IMax(a, b) => format!(
                "(Level.imax {} {})",
                self.render_level(a)?,
                self.render_level(b)?
            ),
        })
    }

    fn render_levels(&self, ls: &[SpecLevel]) -> Result<String, ReflectError> {
        let mut out = String::from("(ListType.nil Level)");
        for l in ls.iter().rev() {
            out = format!("(ListType.cons Level {} {})", self.render_level(l)?, out);
        }
        Ok(out)
    }

    fn render_params(&self, params: &[String]) -> Result<String, ReflectError> {
        let mut out = String::from("(ListType.nil Name)");
        for param in params.iter().rev() {
            out = format!("(ListType.cons Name {} {})", self.render_name(param)?, out);
        }
        Ok(out)
    }

    fn render_definition(&self, def: &ReflectedDef) -> Result<String, ReflectError> {
        let mut type_ = String::new();
        self.render_expr(&def.type_, &mut type_)?;
        let mut value = String::new();
        self.render_expr(&def.value, &mut value)?;
        Ok(format!(
            "(KDefSig.mk (KConstSig.mk {} {}) {})",
            self.render_params(&def.level_params)?,
            type_,
            value,
        ))
    }

    fn render_const_signature(
        &self,
        signature: &ReflectedConstSig,
    ) -> Result<String, ReflectError> {
        let mut type_ = String::new();
        self.render_expr(&signature.type_, &mut type_)?;
        let params = signature
            .level_params
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        Ok(format!(
            "(KConstSig.mk {} {})",
            self.render_params(&params)?,
            type_
        ))
    }

    fn render_nat_typing_slice(&self, out: &mut String) -> Result<(), ReflectError> {
        // validate_for_emission checked the four identities and Nat.rec agreement.
        for (index, (signature, atom)) in self
            .nat_signatures
            .iter()
            .zip(NAT_SIGNATURE_ATOMS)
            .enumerate()
        {
            let value = if index == 3 {
                let rec = self
                    .recs
                    .iter()
                    .find(|rec| rec.name == "Nat.rec")
                    .ok_or_else(|| ReflectError::InvalidReflection {
                        detail: "validated Nat.rec signature disappeared".to_string(),
                    })?;
                self.recursor_atom(rec, "signature")?
            } else {
                self.render_const_signature(signature)?
            };
            let _ = writeln!(out, "def {atom} : KConstSig := {value}");
        }
        let mut lookup = "(OptionType.none KConstSig)".to_string();
        for (signature, atom) in self.nat_signatures.iter().zip(NAT_SIGNATURE_ATOMS).rev() {
            lookup = format!(
                "(opt_pick KConstSig (name_eqb nm {}) {atom} {lookup})",
                self.render_name(&signature.name.to_string())?,
            );
        }
        let _ = writeln!(
            out,
            "def kcre_nat_tenv : KDeclEnv := fun (nm : Name) => {lookup}"
        );
        Ok(())
    }

    fn metadata_atom(&self, name: &Name, kind: &str, field: &str) -> Result<String, ReflectError> {
        self.tag_of(&name.to_string())
            .map(|tag| format!("kcre_{kind}_{field}_{tag}"))
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: format!("projection metadata {name} has no interning entry"),
            })
    }

    fn render_projection_metadata(&self, out: &mut String) -> Result<(), ReflectError> {
        let mut table_index = 0_usize;
        let _ = writeln!(
            out,
            "def kcre_ind_ctor_env_0 : IndCtorEnv := IndCtorEnv.empty"
        );
        let mut lookup = "(OptionType.none KConstSig)".to_string();
        for ind in &self.inductives {
            let signature = self.metadata_atom(&ind.signature.name, "ind", "signature")?;
            let meta = self.metadata_atom(&ind.signature.name, "ind", "meta")?;
            let name = self.render_name(&ind.signature.name.to_string())?;
            let constructors = ind
                .constructor_names
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            let all_names = ind
                .all_names
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            let _ = writeln!(
                out,
                "def {signature} : KConstSig := {}",
                self.render_const_signature(&ind.signature)?
            );
            let _ = writeln!(
                out,
                "def {meta} : KIndMeta := KIndMeta.mk {signature} {} {} {} {}",
                nat_atom(u64::from(ind.num_params)),
                nat_atom(u64::from(ind.num_indices)),
                self.render_params(&constructors)?,
                self.render_params(&all_names)?
            );
            let _ = writeln!(out, "def kcre_ind_ctor_env_{} : IndCtorEnv := IndCtorEnv.addInd kcre_ind_ctor_env_{table_index} {name} {meta}", table_index + 1);
            table_index += 1;
            lookup = format!("(opt_pick KConstSig (name_eqb nm {name}) {signature} {lookup})");
            for ctor in self
                .constructors
                .iter()
                .filter(|ctor| ctor.inductive_name == ind.signature.name)
            {
                let signature = self.metadata_atom(&ctor.signature.name, "ctor", "signature")?;
                let meta = self.metadata_atom(&ctor.signature.name, "ctor", "meta")?;
                let ctor_name = self.render_name(&ctor.signature.name.to_string())?;
                let _ = writeln!(
                    out,
                    "def {signature} : KConstSig := {}",
                    self.render_const_signature(&ctor.signature)?
                );
                let _ = writeln!(
                    out,
                    "def {meta} : KCtorMeta := KCtorMeta.mk {signature} {name} {} {} {}",
                    nat_atom(u64::from(ctor.num_params)),
                    nat_atom(u64::from(ctor.num_fields)),
                    nat_atom(u64::from(ctor.constructor_idx))
                );
                let _ = writeln!(out, "def kcre_ind_ctor_env_{} : IndCtorEnv := IndCtorEnv.addCtor kcre_ind_ctor_env_{table_index} {ctor_name} {meta}", table_index + 1);
                table_index += 1;
                lookup =
                    format!("(opt_pick KConstSig (name_eqb nm {ctor_name}) {signature} {lookup})");
            }
        }
        let _ = writeln!(
            out,
            "def kcre_ind_ctor_env : IndCtorEnv := kcre_ind_ctor_env_{table_index}"
        );
        let _ = writeln!(
            out,
            "def kcre_ind_ctor_tenv : KDeclEnv := fun (nm : Name) => {lookup}"
        );
        let prod = self
            .inductives
            .iter()
            .find(|ind| ind.signature.name == Name::from_string("ProdType"))
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "required ProdType metadata disappeared".to_string(),
            })?;
        let ctor =
            prod.constructor_names
                .first()
                .ok_or_else(|| ReflectError::InvalidReflection {
                    detail: "required ProdType constructor disappeared".to_string(),
                })?;
        for (atom, type_, value) in [
            (
                "kcre_prod_type_name",
                "Name",
                self.render_name(&prod.signature.name.to_string())?,
            ),
            (
                "kcre_prod_mk_name",
                "Name",
                self.render_name(&ctor.to_string())?,
            ),
            (
                "kcre_prod_type_signature",
                "KConstSig",
                self.metadata_atom(&prod.signature.name, "ind", "signature")?,
            ),
            (
                "kcre_prod_mk_signature",
                "KConstSig",
                self.metadata_atom(ctor, "ctor", "signature")?,
            ),
            (
                "kcre_prod_ind_meta",
                "KIndMeta",
                self.metadata_atom(&prod.signature.name, "ind", "meta")?,
            ),
            (
                "kcre_prod_ctor_meta",
                "KCtorMeta",
                self.metadata_atom(ctor, "ctor", "meta")?,
            ),
        ] {
            let _ = writeln!(out, "def {atom} : {type_} := {value}");
        }
        let eq = self
            .inductives
            .iter()
            .find(|ind| ind.signature.name == Name::from_string("Eq"))
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "required Eq metadata disappeared".to_string(),
            })?;
        let refl = self
            .constructors
            .iter()
            .find(|ctor| {
                ctor.signature.name == Name::from_string("Eq.refl")
                    && ctor.inductive_name == eq.signature.name
            })
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "required Eq.refl metadata disappeared".to_string(),
            })?;
        for (atom, type_, value) in [
            (
                "kcre_eq_type_name",
                "Name",
                self.render_name(&eq.signature.name.to_string())?,
            ),
            (
                "kcre_eq_refl_name",
                "Name",
                self.render_name(&refl.signature.name.to_string())?,
            ),
            (
                "kcre_eq_type_signature",
                "KConstSig",
                self.metadata_atom(&eq.signature.name, "ind", "signature")?,
            ),
            (
                "kcre_eq_refl_signature",
                "KConstSig",
                self.metadata_atom(&refl.signature.name, "ctor", "signature")?,
            ),
            (
                "kcre_eq_ind_meta",
                "KIndMeta",
                self.metadata_atom(&eq.signature.name, "ind", "meta")?,
            ),
            (
                "kcre_eq_refl_meta",
                "KCtorMeta",
                self.metadata_atom(&refl.signature.name, "ctor", "meta")?,
            ),
        ] {
            let _ = writeln!(out, "def {atom} : {type_} := {value}");
        }
        let witness =
            self.projection_witness
                .as_ref()
                .ok_or_else(|| ReflectError::InvalidReflection {
                    detail: "required ProdType witness disappeared".to_string(),
                })?;
        for (name, expr) in [
            ("kcre_witness_prod_value", &witness.value),
            ("kcre_witness_prod_type", &witness.type_),
        ] {
            let mut rendered = String::new();
            self.render_expr(expr, &mut rendered)?;
            let _ = writeln!(out, "def {name} : KExpr := {rendered}");
        }
        Ok(())
    }

    fn render_recursor_signature(&self, rec: &ReflectedRec) -> Result<String, ReflectError> {
        let mut type_ = String::new();
        self.render_expr(&rec.type_, &mut type_)?;
        Ok(format!(
            "(KConstSig.mk {} {})",
            self.render_params(&rec.level_params)?,
            type_,
        ))
    }

    fn recursor_atom(&self, rec: &ReflectedRec, field: &str) -> Result<String, ReflectError> {
        let tag = self
            .tag_of(&rec.name)
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: format!("recursor {} has no interning entry", rec.name),
            })?;
        Ok(format!("kcre_rec_{field}_{tag}"))
    }

    fn render_recursor_meta(&self, rec: &ReflectedRec) -> Result<String, ReflectError> {
        Ok(format!(
            "(RecMeta.mk {} {} {} {} {} {} {})",
            nat_atom(u64::from(rec.num_params)),
            nat_atom(u64::from(rec.num_motives)),
            nat_atom(u64::from(rec.num_minors)),
            nat_atom(u64::from(rec.num_indices)),
            if rec.major_after_minors {
                "Bool.true"
            } else {
                "Bool.false"
            },
            self.recursor_atom(rec, "signature")?,
            nat_atom(u64::from(rec.is_k)),
        ))
    }

    fn render_expr(&self, e: &SpecExpr, out: &mut String) -> Result<(), ReflectError> {
        match e {
            SpecExpr::Sort(level) => {
                let _ = write!(out, "(KExpr.sort {})", self.render_level(level)?);
            }
            SpecExpr::BVar(i) => {
                let _ = write!(out, "(KExpr.bvar {})", nat_atom(u64::from(*i)));
            }
            SpecExpr::Const(n, ls) => {
                let _ = write!(
                    out,
                    "(KExpr.const {} {})",
                    self.render_name(n)?,
                    self.render_levels(ls)?
                );
            }
            SpecExpr::App(f, a) => {
                out.push_str("(KExpr.app ");
                self.render_expr(f, out)?;
                out.push(' ');
                self.render_expr(a, out)?;
                out.push(')');
            }
            SpecExpr::Lam(t, b) => {
                out.push_str("(KExpr.lam ");
                self.render_expr(t, out)?;
                out.push(' ');
                self.render_expr(b, out)?;
                out.push(')');
            }
            SpecExpr::Pi(t, b) => {
                out.push_str("(KExpr.pi ");
                self.render_expr(t, out)?;
                out.push(' ');
                self.render_expr(b, out)?;
                out.push(')');
            }
            SpecExpr::Let_(t, v, b) => {
                out.push_str("(KExpr.let_ ");
                self.render_expr(t, out)?;
                out.push(' ');
                self.render_expr(v, out)?;
                out.push(' ');
                self.render_expr(b, out)?;
                out.push(')');
            }
            SpecExpr::Lit(lit) => out.push_str(&render_literal(lit)),
        }
        Ok(())
    }

    fn apply_expr_spine(head: SpecExpr, args: impl IntoIterator<Item = SpecExpr>) -> SpecExpr {
        args.into_iter().fold(head, |function, argument| {
            SpecExpr::App(Box::new(function), Box::new(argument))
        })
    }

    /// Construct a complete, closed Nat.zero iota redex and its expected
    /// reduct from the reflected `Nat.rec` metadata and rule.
    ///
    /// The consumers use only the two generated constants, so changes to
    /// parameter/motive/minor/index counts or rule RHS shape cannot leave a
    /// hand-written witness spine behind.
    fn nat_zero_witness(&self) -> Result<NatZeroWitness, ReflectError> {
        let nat_rec = self
            .recs
            .iter()
            .find(|rec| rec.name == "Nat.rec")
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "validated Nat.rec witness disappeared".to_string(),
            })?;
        if !nat_rec.major_after_minors {
            return Err(ReflectError::InvalidReflection {
                detail: "Nat.rec is not in the modeled MajorAfterMinors layout".to_string(),
            });
        }
        // This witness deliberately supplies the one actual Nat.rec universe.
        // A changed source signature must be handled explicitly, not silently
        // filled with defaults or treated as a monomorphic head.
        if nat_rec.level_params.len() != 1 {
            return Err(ReflectError::InvalidReflection {
                detail: "Nat.rec witness requires exactly one source universe parameter for its explicit [Level.zero] choice".to_string(),
            });
        }
        let levels = vec![SpecLevel::Zero];
        let nat_zero_rule = nat_rec
            .rules
            .iter()
            .find(|rule| rule.ctor == "Nat.zero")
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "validated Nat.zero witness rule disappeared".to_string(),
            })?;
        if nat_zero_rule.num_fields != 0 {
            return Err(ReflectError::InvalidReflection {
                detail: format!(
                    "Nat.zero witness requires a nullary constructor, reflected num_fields={}",
                    nat_zero_rule.num_fields
                ),
            });
        }
        let prefix_count = nat_rec
            .num_params
            .checked_add(nat_rec.num_motives)
            .and_then(|n| n.checked_add(nat_rec.num_minors))
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "Nat.rec witness prefix count overflowed u32".to_string(),
            })?;

        // Closed Sort 0 placeholders are sufficient because iota_reduct only
        // performs name-keyed spine surgery; it does not inspect their types.
        let prefix = (0..prefix_count)
            .map(|_| SpecExpr::Sort(SpecLevel::Zero))
            .collect::<Vec<_>>();
        let indices = (0..nat_rec.num_indices)
            .map(|_| SpecExpr::Sort(SpecLevel::Zero))
            .collect::<Vec<_>>();
        let mut redex_args = prefix.clone();
        redex_args.extend(indices);
        redex_args.push(SpecExpr::Const("Nat.zero".to_string(), Vec::new()));
        let redex = Self::apply_expr_spine(
            SpecExpr::Const("Nat.rec".to_string(), levels.clone()),
            redex_args,
        );

        // Nat.zero has no fields and there is no over-application. Retain the
        // schematic RHS and prefix separately: the emitter applies this prefix
        // AFTER the existing checked recursor_rhs_instance computation.
        Ok(NatZeroWitness {
            redex,
            rhs: nat_zero_rule.rhs.clone(),
            prefix,
            levels,
        })
    }

    /// Render the `kernel_core_red_env` value TERM (a single-line Lean-syntax
    /// `RedEnv` term, `the_red_env.rs`-style, with `kcre_nat_*`/`kcre_name_*`
    /// atom leaves so its nesting stays under the parser's
    /// `MAX_EXPR_DEPTH = 128` guard).
    fn value_term(&self) -> Result<String, ReflectError> {
        let mut rec_env = String::from("RecEnv.empty");
        for rec in &self.recs {
            let mut rules = String::from("RecRules.nil");
            for rule in rec.rules.iter().rev() {
                let mut rhs = String::new();
                self.render_expr(&rule.rhs, &mut rhs)?;
                rules = format!(
                    "(RecRules.cons (RecRule.mk {} {} {}) {})",
                    self.render_name(&rule.ctor)?,
                    nat_atom(u64::from(rule.num_fields)),
                    rhs,
                    rules
                );
            }
            let meta = self.recursor_atom(rec, "meta")?;
            rec_env = format!(
                "(RecEnv.addRec {} {} {} {})",
                rec_env,
                self.render_name(&rec.name)?,
                meta,
                rules
            );
        }
        let mut def_env = String::from("DefEnv.empty");
        for def in &self.defs {
            def_env = format!(
                "(DefEnv.addDef {} {} {})",
                def_env,
                self.render_name(&def.name)?,
                self.render_definition(def)?,
            );
        }
        Ok(format!("RedEnv.mk {rec_env} {def_env} kcre_ind_ctor_env"))
    }

    /// Render only the Nat-zero witness fragment. This private component does
    /// not certify that a Reflection is complete: def_script validates the
    /// entire batch before calling it. Synthetic spine tests exercise this
    /// same renderer without pretending their partial data can be published.
    fn render_nat_zero_witness(
        &self,
        nat_zero: &NatZeroWitness,
        out: &mut String,
    ) -> Result<(), ReflectError> {
        let _ = writeln!(
            out,
            "def kcre_witness_rec_levels : ListType Level := {}",
            self.render_levels(&nat_zero.levels)?,
        );
        let mut redex = String::new();
        self.render_expr(&nat_zero.redex, &mut redex)?;
        let _ = writeln!(out, "def kcre_witness_nat_zero_redex : KExpr := {redex}");
        let mut rhs = String::new();
        self.render_expr(&nat_zero.rhs, &mut rhs)?;
        let _ = writeln!(out, "def kcre_witness_nat_zero_rhs : KExpr := {rhs}");
        let mut prefix = String::from("(ListType.nil KExpr)");
        for argument in nat_zero.prefix.iter().rev() {
            let mut rendered = String::new();
            self.render_expr(argument, &mut rendered)?;
            prefix = format!("(ListType.cons KExpr {rendered} {prefix})");
        }
        let _ = writeln!(out,
            "def kcre_witness_nat_zero_reduct : KExpr := apply_spine {prefix} (recursor_rhs_instance (recmeta_signature fixture_nat_rec_meta) kcre_witness_nat_zero_rhs kcre_witness_rec_levels)"
        );
        Ok(())
    }

    /// Render the full generated DEF SCRIPT: one Lean-syntax `def` per line —
    /// the `kcre_nat_*` unary pool (depth 2 each), the `kcre_name_*` interned
    /// name constants (depth 1 each, trust edge 1), per-recursor signature and
    /// metadata atoms, the required four actual Nat signatures and their
    /// concrete typing environment, generated semantic witness
    /// helpers for the live Nat-zero iota rule and one real delta entry, then
    /// the `kernel_core_red_env` term itself. Registration replays the lines in
    /// order; every line is a value-ful `def` (census-neutral).
    ///
    /// This script shape exists because of a MEASURED parser constraint: the
    /// naive fully-inlined literal nests to paren depth 163, past the
    /// parser's `MAX_EXPR_DEPTH = 128` DoS guard. Every current emitted line is
    /// measured and checked by the generator before publication.
    /// # Errors
    /// Returns [`ReflectError::InvalidReflection`] unless name interning is
    /// injective, contiguous, and complete and both generated non-vacuity
    /// witnesses are present.
    pub fn def_script(&self) -> Result<String, ReflectError> {
        self.validate_for_emission()?;
        let nat_zero = self.nat_zero_witness()?;
        let delta = self
            .defs
            .iter()
            .find(|def| def.name == "def_env_lift_closed_b")
            .ok_or_else(|| ReflectError::InvalidReflection {
                detail: "validated delta witness definition disappeared".to_string(),
            })?;

        let mut out = String::new();
        let max_nat = self.max_nat_used();
        let _ = writeln!(out, "def kcre_nat_0 : Nat := Nat.zero");
        for n in 1..=max_nat {
            let _ = writeln!(out, "def kcre_nat_{n} : Nat := Nat.succ kcre_nat_{}", n - 1);
        }
        let mut rows: Vec<(u64, &str)> = self
            .interning
            .iter()
            .map(|(n, t)| (*t, n.as_str()))
            .collect();
        rows.sort_unstable();
        for (tag, real) in rows {
            let _ = writeln!(
                out,
                "def kcre_name_{tag} : Name := Name.str Name.anonymous kcre_nat_{tag} -- {real}"
            );
        }
        for rec in &self.recs {
            let _ = writeln!(
                out,
                "def {} : KConstSig := {}",
                self.recursor_atom(rec, "signature")?,
                self.render_recursor_signature(rec)?,
            );
            let _ = writeln!(
                out,
                "def {} : RecMeta := {}",
                self.recursor_atom(rec, "meta")?,
                self.render_recursor_meta(rec)?,
            );
            if rec.name == "Nat.rec" {
                let _ = writeln!(
                    out,
                    "def fixture_nat_rec_meta : RecMeta := {}",
                    self.recursor_atom(rec, "meta")?,
                );
            }
        }
        self.render_nat_typing_slice(&mut out)?;
        self.render_projection_metadata(&mut out)?;
        self.render_nat_zero_witness(&nat_zero, &mut out)?;
        let mut value = String::new();
        self.render_expr(&delta.value, &mut value)?;
        let _ = writeln!(
            out,
            "def kcre_witness_delta_head : Name := {}",
            self.render_name("def_env_lift_closed_b")?
        );
        let _ = writeln!(out, "def kcre_witness_delta_value : KExpr := {value}");
        let _ = writeln!(
            out,
            "def kernel_core_red_env : RedEnv := {}",
            self.value_term()?
        );
        Ok(out)
    }

    /// Render the interning table (trust edge 1): one `tag<TAB>real-name`
    /// line per entry, tag-ascending.
    #[must_use]
    pub fn interning_tsv(&self) -> String {
        let mut rows: Vec<(u64, &str)> = self
            .interning
            .iter()
            .map(|(n, t)| (*t, n.as_str()))
            .collect();
        rows.sort_unstable();
        let mut out = String::new();
        for (tag, name) in rows {
            let _ = writeln!(out, "{tag}\t{name}");
        }
        out
    }

    /// Render the skip ledger + coverage summary (trust edge 3),
    /// lean_export-style: partial-but-honest, never silently weakened.
    /// # Errors
    /// Returns [`ReflectError::InvalidReflection`] if any rendered semantic
    /// name is absent from the interning table.
    pub fn skip_ledger_md(&self) -> Result<String, ReflectError> {
        self.validate_for_emission()?;
        let value_term = self.value_term()?;
        let n_rules: usize = self.recs.iter().map(|r| r.rules.len()).sum();
        let mut out = String::new();
        let _ = writeln!(out, "# kernel_core_red_env skip ledger (GENERATED)");
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "Generated by the canonical Trust `targo --unverified run --release -p clean-verify --bin red_env_reflect` lane."
        );
        let _ = writeln!(
            out,
            "Trust edges: (1) bounded structural source-name collision refusal plus injective Nat-tag interning; (2) structural five-constructor levels in definition and recursor signature/RHS images, with immediate source Lambda and MajorAfterMinors policy checks before metadata erasure; (3) this skip ledger. See `clean_verify::red_env_reflect` module docs."
        );
        let _ = writeln!(
            out,
            "Definition records bind ordered parameters/type/body to one ConstantInfo. Recursor metadata binds ordered parameters/type to one RecursorVal and requires exact agreement with its actual-name ConstantInfo signature. This is not a production smart-universe substitution theorem, typed declaration/recursor admission, a generic NameRep theorem, or Rust refinement. The immediate source Lambda/MajorAfterMinors branch is reflected with structural RHS universes, and the active guarded model computes its signature-indexed instance. This finite-seed adapter agreement is not generic Rust refinement; non-lambda fallback and the other layout remain outside the image."
        );
        let _ = writeln!(out);
        let _ = writeln!(out,
            "The required four-entry Nat typing slice copies actual ConstantInfo identities, ordered parameters and structural types, cross-checked against the same family's inductive/constructor/recursor metadata. Value-less Definition entries are captured as signatures, never delta definitions. The source builder validates metadata, rule payloads and the declaration before recording FullKernelCheck; this capture is not a formal soundness proof of that validator.");
        let _ = writeln!(
            out,
            "Nat typing signature records: {} (required: 4).",
            self.nat_signatures.len()
        );
        let _ = writeln!(out,
            "Projection metadata records: {} inductives, {} constructors. Signatures copy actual ConstantInfo records and agree with actual InductiveVal/ConstructorVal types and ordered universe parameters; constructor parent/order and source telescope counts are checked. The exact final stored ordered all_names block is retained, with actual sibling identity/block/parameter consistency checks. Nested restoration can remove auxiliaries from that stored block; correspondence with the earlier transformed strict-validation context remains a separate obligation. These are capture-time coherence refusals, not new runtime projection guards. The same signature records populate kcre_ind_ctor_tenv. The generated ProdType constructor application passed actual source full inference before its structural image was emitted. This finite source check is not generic model-to-Rust typing correspondence, projection preservation or a full inductive admission theorem; recursive/nested/elimination flags remain outside these metadata images.",
            self.inductives.len(), self.constructors.len());
        let _ = writeln!(
            out,
            "## Coverage: {} recursors ({} rules), {} definitions, {} interned names",
            self.recs.len(),
            n_rules,
            self.defs.len(),
            self.interning.len()
        );
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "Depth budget (measured): the env term nests to paren depth {} with \
             kcre_nat_*/kcre_name_*/kcre_rec_* atom leaves; the deepest script line is {} \
             ({} nat helpers, {} name helpers, {} recursor signature/metadata pairs); the \
             naive fully-inlined literal exceeds the parser MAX_EXPR_DEPTH=128 guard.",
            max_paren_depth(&value_term),
            max_paren_depth(&self.def_script()?),
            self.max_nat_used() + 1,
            self.interning.len(),
            self.recs.len(),
        );
        let _ = writeln!(out);
        for rec in &self.recs {
            let _ = writeln!(
                out,
                "- rec `{}`: params={} motives={} minors={} indices={} rules={} universe_params={:?}; schematic signature/RHS preserve structural levels; source=immediate-Lambda/MajorAfterMinors{}",
                rec.name,
                rec.num_params,
                rec.num_motives,
                rec.num_minors,
                rec.num_indices,
                rec.rules.len(),
                rec.level_params,
                if rec.is_k { " [is_k]" } else { "" }
            );
        }
        for def in &self.defs {
            let _ = writeln!(
                out,
                "- def `{}`: universe_params={:?}; schematic type/body preserve structural levels{}",
                def.name,
                def.level_params,
                if def.is_reducible {
                    ""
                } else {
                    " [not marked reducible]"
                }
            );
        }
        let _ = writeln!(out);
        let _ = writeln!(out, "## Skips ({} entries)", self.skips.len());
        let _ = writeln!(out);
        for skip in &self.skips {
            let _ = writeln!(out, "- `{}`: {}", skip.item, skip.reason);
        }
        Ok(out)
    }

    /// Build the kernel `Expr` of the spec `KExpr` TERM for `e` — the same
    /// term the def script renders (atom leaves `kcre_nat_*`/`kcre_name_*`),
    /// as a first-class kernel expression. Used by the one-rfl cost probes to
    /// whnf-force full per-element checker work (`nat_eqb (bvar_ceiling rhs)
    /// 0` traverses the whole rhs), which the Bool.and short-circuit of the
    /// env-level fold otherwise hides.
    ///
    /// # Errors
    /// Returns [`ReflectError::InvalidReflection`] if `e` references a semantic
    /// name absent from this reflection's interning table.
    pub fn kexpr_term(&self, e: &SpecExpr) -> Result<Expr, ReflectError> {
        Ok(match e {
            SpecExpr::Sort(level) => {
                Expr::app(Expr::const_str("KExpr.sort"), self.level_term(level)?)
            }
            SpecExpr::BVar(i) => Expr::app(
                Expr::const_str("KExpr.bvar"),
                Expr::const_str(&nat_atom(u64::from(*i))),
            ),
            SpecExpr::Const(n, ls) => Expr::apps(
                Expr::const_str("KExpr.const"),
                [
                    Expr::const_str(&self.render_name(n)?),
                    self.levels_term(ls)?,
                ],
            ),
            SpecExpr::App(f, a) => Expr::apps(
                Expr::const_str("KExpr.app"),
                [self.kexpr_term(f)?, self.kexpr_term(a)?],
            ),
            SpecExpr::Lam(t, b) => Expr::apps(
                Expr::const_str("KExpr.lam"),
                [self.kexpr_term(t)?, self.kexpr_term(b)?],
            ),
            SpecExpr::Pi(t, b) => Expr::apps(
                Expr::const_str("KExpr.pi"),
                [self.kexpr_term(t)?, self.kexpr_term(b)?],
            ),
            SpecExpr::Let_(t, v, b) => Expr::apps(
                Expr::const_str("KExpr.let_"),
                [
                    self.kexpr_term(t)?,
                    self.kexpr_term(v)?,
                    self.kexpr_term(b)?,
                ],
            ),
            SpecExpr::Lit(lit) => literal_term(lit),
        })
    }

    fn level_term(&self, l: &SpecLevel) -> Result<Expr, ReflectError> {
        Ok(match l {
            SpecLevel::Zero => Expr::const_str("Level.zero"),
            SpecLevel::Param(name) => Expr::app(
                Expr::const_str("Level.param"),
                Expr::const_str(&self.render_name(name)?),
            ),
            SpecLevel::Succ(x) => Expr::app(Expr::const_str("Level.succ"), self.level_term(x)?),
            SpecLevel::Max(a, b) => Expr::apps(
                Expr::const_str("Level.max"),
                [self.level_term(a)?, self.level_term(b)?],
            ),
            SpecLevel::IMax(a, b) => Expr::apps(
                Expr::const_str("Level.imax"),
                [self.level_term(a)?, self.level_term(b)?],
            ),
        })
    }

    fn levels_term(&self, ls: &[SpecLevel]) -> Result<Expr, ReflectError> {
        let mut out = Expr::app(Expr::const_str("ListType.nil"), Expr::const_str("Level"));
        for l in ls.iter().rev() {
            out = Expr::apps(
                Expr::const_str("ListType.cons"),
                [Expr::const_str("Level"), self.level_term(l)?, out],
            );
        }
        Ok(out)
    }

    /// Interning injectivity (trust edge 1): every real name has exactly one
    /// tag and every tag exactly one real name.
    #[must_use]
    pub fn interning_injective(&self) -> bool {
        let names: std::collections::BTreeSet<&str> =
            self.interning.iter().map(|(n, _)| n.as_str()).collect();
        let tags: std::collections::BTreeSet<u64> =
            self.interning.iter().map(|(_, t)| *t).collect();
        names.len() == self.interning.len() && tags.len() == self.interning.len()
    }
}

/// The FIDELITY GATE core: regenerate the reflection from the live kernel env
/// and compare the three artifacts 1:1 against the committed generated files.
///
/// # Errors
/// Returns [`ReflectError::InvalidReflection`] if the live reflection cannot
/// safely be emitted, or [`ReflectError::Drift`] naming the first drifted
/// artifact and divergent byte region.
pub fn fidelity_check(
    env: &Environment,
    committed_script: &str,
    committed_interning: &str,
    committed_skips: &str,
) -> Result<Reflection, ReflectError> {
    let fresh = reflect_foundation_core(env)?;
    let fresh_script = fresh.def_script()?;
    compare_artifact("def script", &fresh_script, committed_script)?;
    compare_artifact(
        "interning table",
        &fresh.interning_tsv(),
        committed_interning,
    )?;
    compare_artifact("skip ledger", &fresh.skip_ledger_md()?, committed_skips)?;
    Ok(fresh)
}

fn compare_artifact(
    artifact: &'static str,
    fresh: &str,
    committed: &str,
) -> Result<(), ReflectError> {
    if fresh == committed {
        return Ok(());
    }
    // Locate the first divergent byte for an actionable message.
    let pos = fresh
        .bytes()
        .zip(committed.bytes())
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| fresh.len().min(committed.len()));
    let lo = pos.saturating_sub(60);
    let f_end = (pos + 60).min(fresh.len());
    let c_end = (pos + 60).min(committed.len());
    Err(ReflectError::Drift {
        artifact,
        detail: format!(
            "first divergence at byte {pos}: regenerated ...{}... vs committed ...{}... \
             (lengths {} vs {}); re-run the red_env_reflect bin and review",
            fresh.get(lo..f_end).unwrap_or(""),
            committed.get(lo..c_end).unwrap_or(""),
            fresh.len(),
            committed.len()
        ),
    })
}

#[cfg(test)]
mod fidelity_tests;

mod native_rule_keys;
pub use native_rule_keys::RESERVED_NATIVE_RULE_KEYS;

#[cfg(test)]
mod tests {
    use super::*;

    /// A literal leaf reflects through the tagged codec and the string payload
    /// decoding: each Unicode scalar value in order, decimal numerals, and a
    /// `Nat` literal past `u64` in decimal (not `BigNat`'s hex `Display`).
    #[test]
    fn test_literal_leaves_reflect_through_the_codec() {
        let s = clean_kernel::Literal::String(std::sync::Arc::from("h\u{e9}\u{1f600}"));
        assert_eq!(
            render_literal(&s),
            "(literal_string (string_lit_code (ListType.cons Nat 104 (ListType.cons Nat 233 \
             (ListType.cons Nat 128512 (ListType.nil Nat))))))"
        );
        let empty = clean_kernel::Literal::String(std::sync::Arc::from(""));
        assert_eq!(
            render_literal(&empty),
            "(literal_string (string_lit_code (ListType.nil Nat)))"
        );
        let small = clean_kernel::Literal::Nat(clean_kernel::BigNat::from_u64(55296));
        assert_eq!(render_literal(&small), "(literal_nat 55296)");
        // 2^64 * 3 + 5 = 55340232221128654853.
        let big = clean_kernel::Literal::Nat(clean_kernel::BigNat::from_limbs(vec![5, 3]));
        assert_eq!(render_literal(&big), "(literal_nat 55340232221128654853)");
        // 2^128 = 340282366920938463463374607431768211456: a chunk boundary.
        let boundary = clean_kernel::Literal::Nat(clean_kernel::BigNat::from_limbs(vec![0, 0, 1]));
        assert_eq!(
            render_literal(&boundary),
            "(literal_nat 340282366920938463463374607431768211456)"
        );
        // The foundation-core image carries the literal whole.
        let e = Expr::str_lit("ab");
        assert_eq!(
            reflect_expr_with_policy(&e, true).expect("a literal reflects"),
            SpecExpr::Lit(clean_kernel::Literal::String(std::sync::Arc::from("ab")))
        );
    }

    #[test]
    fn test_live_recursor_seed_census_before_metadata_erasure() {
        crate::test_utils::run_with_stack(|| {
            // This is a census of the actual generator seed, not a proof of
            // production reduction or a claim about imported environments.
            let seed = crate::spec::Specification::new_red_env_reflection_seed()
                .expect("live artifact-independent reflection seed");
            let env = seed.env();
            let mut rules = 0;
            let mut immediate_lambdas = 0;
            let mut mdata_wrapped_lambdas = Vec::new();
            let mut other_rhs = Vec::new();
            let mut after_minors = 0;
            let mut after_motive = 0;
            let mut k_recursors = Vec::new();
            let mut constructor_associations = 0;
            let mut source_signatures = 0;

            for ind in REFLECT_INDUCTIVES {
                let name = Name::from_string(&format!("{ind}.rec"));
                let rv = env
                    .get_recursor(&name)
                    .expect("every allowlisted recursor exists");
                assert_eq!(rv.name, name);
                assert_eq!(rv.inductive_name, Name::from_string(ind));
                let ci = env
                    .get_const(&name)
                    .expect("actual recursor signature exists");
                assert_eq!(
                    ci.level_params, rv.level_params,
                    "{} ordered universes",
                    rv.name
                );
                assert_eq!(ci.type_, rv.type_, "{} schematic type", rv.name);
                source_signatures += 1;
                reflect_definition_expr(&rv.type_)
                    .expect("recursor type has a level-preserving image");
                rv.validate_metadata()
                    .expect("seed recursor telescope metadata");
                match rv.arg_order {
                    RecursorArgOrder::MajorAfterMinors => after_minors += 1,
                    RecursorArgOrder::MajorAfterMotive => after_motive += 1,
                }
                if rv.is_k {
                    k_recursors.push(rv.name.to_string());
                }
                let inductive = env
                    .get_inductive(&rv.inductive_name)
                    .expect("actual recursor family metadata exists");
                assert_eq!(
                    rv.rules.len(),
                    inductive.constructor_names.len(),
                    "{} rule count",
                    rv.name
                );
                let mut rule_rows = Vec::new();
                for (index, rule) in rv.rules.iter().enumerate() {
                    rules += 1;
                    // Inspect the immediate production AST tag FIRST. Neither
                    // strip_mdata nor either reflection adapter selects this branch.
                    if rule.rhs.is_lam() {
                        immediate_lambdas += 1;
                    } else if rule.rhs.strip_mdata().is_lam() {
                        mdata_wrapped_lambdas
                            .push(format!("{}:{}", rv.name, rule.constructor_name));
                    } else {
                        other_rhs.push(format!("{}:{}", rv.name, rule.constructor_name));
                    }
                    let ctor = env
                        .get_constructor(&rule.constructor_name)
                        .expect("every source rule has constructor metadata");
                    assert_eq!(ctor.name, rule.constructor_name);
                    assert_eq!(ctor.inductive_name, rv.inductive_name);
                    assert_eq!(
                        ctor.constructor_idx as usize, index,
                        "{} canonical rule order",
                        rv.name
                    );
                    assert_eq!(inductive.constructor_names[index], rule.constructor_name);
                    assert_eq!(ctor.num_fields, rule.num_fields);
                    assert_eq!(rule.recursive_fields.len(), rule.num_fields as usize);
                    constructor_associations += 1;
                    let ctor_ci = env
                        .get_const(&rule.constructor_name)
                        .expect("actual constructor signature exists");
                    assert_eq!(ctor_ci.level_params, ctor.level_params);
                    assert_eq!(ctor_ci.type_, ctor.type_);
                    source_signatures += 1;
                    rule_rows.push(format!(
                        "{}:index={}/fields={}/recursive={:?}",
                        rule.constructor_name,
                        ctor.constructor_idx,
                        rule.num_fields,
                        rule.recursive_fields
                    ));
                }
                eprintln!("recursor_seed_row name={} params={:?} layout={:?} is_k={} p={} m={} minors={} i={} rules={:?}",
                    rv.name, rv.level_params, rv.arg_order, rv.is_k, rv.num_params,
                    rv.num_motives, rv.num_minors, rv.num_indices, rule_rows);
            }
            eprintln!("recursor_seed_census recursors={} rules={rules} immediate_lambdas={immediate_lambdas} mdata_wrapped_lambdas={mdata_wrapped_lambdas:?} other_rhs={other_rhs:?} major_after_minors={after_minors} major_after_motive={after_motive} is_k={k_recursors:?} constructor_associations={constructor_associations} source_signatures={source_signatures}", REFLECT_INDUCTIVES.len());

            // Pin this finite migration frontier. Failure must name the new
            // source branch rather than silently dropping selected records.
            assert_eq!(REFLECT_INDUCTIVES.len(), 21);
            assert_eq!(rules, 42);
            assert_eq!(immediate_lambdas, rules,
                "lambda-only migration misses metadata-wrapped {mdata_wrapped_lambdas:?} or other {other_rhs:?} RHSs");
            assert_eq!((after_minors, after_motive), (21, 0));
            assert_eq!(
                k_recursors,
                vec!["Eq.rec".to_string()],
                "K remains an explicit additional source reduction branch"
            );
            assert_eq!((constructor_associations, source_signatures), (42, 63));

            let nat = env
                .get_recursor(&Name::from_string("Nat.rec"))
                .expect("actual Nat.rec");
            assert_eq!(nat.level_params, vec![Name::from_string("u")]);
            assert_eq!(
                (
                    nat.num_params,
                    nat.num_motives,
                    nat.num_minors,
                    nat.num_indices
                ),
                (0, 1, 2, 0)
            );
            assert_eq!(nat.rules[0].constructor_name, Name::from_string("Nat.zero"));
            assert_eq!(nat.rules[1].constructor_name, Name::from_string("Nat.succ"));
            assert!(nat.rules[0].recursive_fields.is_empty());
            assert_eq!(nat.rules[1].recursive_fields, vec![true]);
            assert!(env
                .get_inductive(&Name::from_string("Nat"))
                .expect("Nat")
                .level_params
                .is_empty());

            let reflected =
                reflect_foundation_core(env).expect("complete current reflection batch");
            assert_eq!(reflected.recs.len(), REFLECT_INDUCTIVES.len());
            assert_eq!(
                reflected
                    .recs
                    .iter()
                    .map(|rec| rec.rules.len())
                    .sum::<usize>(),
                rules
            );
            for (rec, ind) in reflected.recs.iter().zip(REFLECT_INDUCTIVES) {
                assert_eq!(rec.name, format!("{ind}.rec"));
                let rv = env
                    .get_recursor(&Name::from_string(&rec.name))
                    .expect("censused actual recursor");
                assert_eq!(
                    rec.level_params,
                    rv.level_params
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                );
                assert_eq!(
                    rec.type_,
                    reflect_definition_expr(&rv.type_).expect("signature")
                );
                for param in &rec.level_params {
                    assert!(
                        reflected.tag_of(param).is_some(),
                        "signature parameter is interned"
                    );
                }
            }
            let nat_rec = reflected
                .recs
                .iter()
                .find(|rec| rec.name == "Nat.rec")
                .expect("actual reflected Nat.rec");
            let nat_meta = reflected
                .recursor_atom(nat_rec, "meta")
                .expect("Nat metadata atom");
            let script = reflected.def_script().expect("fresh guarded-iota script");
            assert!(script.contains(&format!(
                "def fixture_nat_rec_meta : RecMeta := {nat_meta}\n"
            )));
            assert!(reflected
                .value_term()
                .expect("actual RecEnv term")
                .contains(&nat_meta));
            for rec in &reflected.recs {
                assert!(script.contains(&format!(
                    "def {} : KConstSig := {}\n",
                    reflected
                        .recursor_atom(rec, "signature")
                        .expect("signature atom"),
                    reflected
                        .render_recursor_signature(rec)
                        .expect("signature rendering"),
                )));
                assert!(script.contains(&format!(
                    "def {} : RecMeta := {}\n",
                    reflected.recursor_atom(rec, "meta").expect("metadata atom"),
                    reflected
                        .render_recursor_meta(rec)
                        .expect("metadata rendering"),
                )));
            }
        });
    }

    fn signature_fixture() -> (RecursorVal, ConstantInfo) {
        use std::sync::Arc;
        let z = Name::from_string("z");
        let a = Name::from_string("a");
        // Raw constructors deliberately preserve an unsimplified IMax/Max.
        // This synthetic representation fixture is not a typed admission.
        let level = Level::IMax(
            Arc::new(Level::Max(
                Arc::new(Level::Param(z.clone())).into(),
                Arc::new(Level::Zero).into(),
            ))
            .into(),
            Arc::new(Level::Succ(Arc::new(Level::Param(a.clone())).into())).into(),
        );
        let type_ = Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::sort(level.clone()),
            Expr::const_str_levels("OnlyInSignature", vec![level.clone()]),
        );
        let rv = RecursorVal {
            name: Name::from_string("Fixture.rec"),
            level_params: vec![z, a],
            type_,
            arg_order: RecursorArgOrder::MajorAfterMinors,
            inductive_name: Name::from_string("Fixture"),
            num_params: 0,
            num_motives: 1,
            num_minors: 1,
            num_indices: 0,
            is_k: false,
            rules: vec![clean_kernel::RecursorRule {
                constructor_name: Name::from_string("Fixture.mk"),
                num_fields: 0,
                recursive_fields: vec![],
                rhs: Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    Expr::sort(level.clone()),
                    Expr::const_str_levels("OnlyInRule", vec![level]),
                ),
            }],
        };
        let ci = ConstantInfo::new(
            rv.name.clone(),
            rv.level_params.clone(),
            rv.type_.clone(),
            None,
            false,
        );
        (rv, ci)
    }

    #[test]
    fn test_recursor_signature_and_rhs_preserve_order_and_structural_levels() {
        let (rv, ci) = signature_fixture();
        let rec = reflect_recursor(&rv, Some(&ci)).expect("matching source signatures");
        assert_eq!(rec.level_params, ["z", "a"]);
        let level = SpecLevel::IMax(
            Box::new(SpecLevel::Max(
                Box::new(SpecLevel::Param("z".to_string())),
                Box::new(SpecLevel::Zero),
            )),
            Box::new(SpecLevel::Succ(Box::new(SpecLevel::Param("a".to_string())))),
        );
        assert_eq!(
            rec.type_,
            SpecExpr::Pi(
                Box::new(SpecExpr::Sort(level.clone())),
                Box::new(SpecExpr::Const(
                    "OnlyInSignature".to_string(),
                    vec![level.clone()]
                )),
            )
        );
        assert_eq!(
            rec.rules[0].rhs,
            SpecExpr::Lam(
                Box::new(SpecExpr::Sort(level.clone())),
                Box::new(SpecExpr::Const("OnlyInRule".to_string(), vec![level])),
            ),
            "active rule reflection preserves the same structural levels as its signature"
        );
        let reflection = Reflection {
            interning: build_interning(std::slice::from_ref(&rec), &[]),
            recs: vec![rec],
            ..Reflection::default()
        };
        let rec = &reflection.recs[0];
        let z = reflection
            .render_name("z")
            .expect("signature-only parameter z");
        let a = reflection
            .render_name("a")
            .expect("signature-only parameter a");
        let signature = reflection
            .render_recursor_signature(rec)
            .expect("faithful signature");
        assert!(signature.starts_with(&format!(
            "(KConstSig.mk (ListType.cons Name {z} (ListType.cons Name {a} (ListType.nil Name))) "
        )));
        assert!(signature.contains("Level.imax"));
        assert!(signature.contains("Level.max"));
        assert!(reflection.tag_of("OnlyInSignature").is_some());
        let mut referenced = BTreeMap::new();
        count_consts(&rec.type_, &mut referenced);
        assert_eq!(
            referenced.keys().map(String::as_str).collect::<Vec<_>>(),
            ["OnlyInSignature"]
        );
        let mut names = SourceNames::default();
        names
            .expression(&rv.type_, true)
            .expect("faithful signature registry");
        assert_eq!(names.by_display.get("z"), Some(&Name::from_string("z")));
        assert_eq!(names.by_display.get("a"), Some(&Name::from_string("a")));
        for missing in ["z", "a", "OnlyInSignature"] {
            let mut broken = reflection.clone();
            broken.interning.retain(|(name, _)| name != missing);
            assert!(
                broken.render_recursor_signature(&broken.recs[0]).is_err(),
                "missing signature-only semantic name {missing} must fail closed"
            );
        }
        let mut large_bvar = reflection;
        large_bvar.recs[0].type_ = SpecExpr::BVar(1000);
        assert_eq!(
            large_bvar.max_nat_used(),
            1000,
            "signature bvars need Nat atoms too"
        );
    }

    #[test]
    fn test_recursor_signature_rejects_missing_or_disagreeing_constant_info() {
        let (rv, ci) = signature_fixture();
        assert_eq!(
            reflect_recursor(&rv, None).expect_err("missing constant"),
            "recursor ConstantInfo signature not found"
        );
        let mut changed = ci.clone();
        changed.name = Name::from_string("Other.rec");
        assert_eq!(
            reflect_recursor(&rv, Some(&changed)).expect_err("wrong actual name"),
            "recursor/ConstantInfo name mismatch"
        );
        changed = ci.clone();
        changed.level_params.reverse();
        assert_eq!(
            reflect_recursor(&rv, Some(&changed)).expect_err("reordered parameters"),
            "recursor/ConstantInfo ordered universe parameters mismatch"
        );
        changed = ci.clone();
        changed.level_params.pop();
        assert_eq!(
            reflect_recursor(&rv, Some(&changed)).expect_err("missing parameter"),
            "recursor/ConstantInfo ordered universe parameters mismatch"
        );
        changed = ci;
        changed.type_ = Expr::sort(Level::Zero);
        assert_eq!(
            reflect_recursor(&rv, Some(&changed)).expect_err("changed schematic type"),
            "recursor/ConstantInfo schematic type mismatch"
        );
    }

    #[test]
    fn test_recursor_signature_unrepresentable_type_refuses_whole_record() {
        let (mut rv, mut ci) = signature_fixture();
        rv.type_ = Expr::proj(Name::from_string("Unsupported"), 0, Expr::bvar(0));
        ci.type_ = rv.type_.clone();
        let refusal = reflect_recursor(&rv, Some(&ci)).expect_err("signature has no image");
        assert!(refusal.starts_with("recursor schematic type unrepresentable:"));
        assert!(
            reflect_legacy_erased_iota_expr(&rv.rules[0].rhs).is_ok(),
            "a representable RHS must not hide a refused signature"
        );
    }

    #[test]
    fn test_recursor_source_lambda_branch_changes_under_metadata_wrapper() {
        let (mut rv, ci) = signature_fixture();
        let bare = rv.rules[0].rhs.clone();
        let wrapped = Expr::mdata(
            vec![(
                Name::from_string("census"),
                clean_kernel::MDataValue::Bool(true),
            )],
            bare.clone(),
        );
        assert!(bare.is_lam());
        assert!(
            !wrapped.is_lam(),
            "production branch inspects the immediate source tag"
        );
        assert!(wrapped.strip_mdata().is_lam());
        assert_eq!(
            reflect_definition_expr(&bare).expect("bare faithful image"),
            reflect_definition_expr(&wrapped).expect("wrapped faithful image")
        );
        assert_eq!(
            reflect_legacy_erased_iota_expr(&bare).expect("bare legacy image"),
            reflect_legacy_erased_iota_expr(&wrapped).expect("wrapped legacy image")
        );
        // Both adapters erase MData, so reflected Lam alone is not evidence
        // that the production RecursorRule RHS selected its lambda branch.
        let accepted = reflect_recursor(&rv, Some(&ci)).expect("actual immediate source Lambda");
        assert_eq!(
            accepted.rules[0].rhs,
            reflect_definition_expr(&wrapped).expect("same image")
        );
        rv.rules[0].rhs = wrapped;
        let refused = reflect_recursor(&rv, Some(&ci))
            .expect_err("metadata wrapper selects another source branch");
        assert!(refused.contains("not an immediate source Lambda"));
        assert_eq!(rv.type_, ci.type_, "only the RHS policy tag changed");
        assert_eq!(
            rv.level_params, ci.level_params,
            "signature data stayed fixed"
        );
        rv.rules[0].rhs = Expr::bvar(0);
        assert!(reflect_recursor(&rv, Some(&ci))
            .expect_err("non-lambda fallback")
            .contains("not an immediate source Lambda"));
    }

    fn checked_sort_definition(env: &mut Environment, name: Name, params: Vec<Name>, level: Level) {
        env.add_decl(clean_kernel::Declaration::Definition {
            name,
            level_params: params,
            type_: Expr::sort(Level::succ(level.clone())),
            value: Expr::sort(level),
            is_reducible: false,
        })
        .expect("checked schematic sort definition");
    }

    #[test]
    fn test_definition_levels_preserve_raw_five_constructor_trees_in_both_routes() {
        use std::sync::Arc;
        let z = Level::Param(Name::from_string("z"));
        let a = Level::Param(Name::from_string("a"));
        // Raw variants are essential: smart IMax(_, zero) would collapse before reflection.
        let level = Level::IMax(
            Arc::new(Level::Max(
                Arc::new(Level::Succ(Arc::new(z).into())).into(),
                Arc::new(a.clone()).into(),
            ))
            .into(),
            Arc::new(Level::IMax(
                Arc::new(a).into(),
                Arc::new(Level::Zero).into(),
            ))
            .into(),
        );
        let expected = SpecLevel::IMax(
            Box::new(SpecLevel::Max(
                Box::new(SpecLevel::Succ(Box::new(SpecLevel::Param("z".to_string())))),
                Box::new(SpecLevel::Param("a".to_string())),
            )),
            Box::new(SpecLevel::IMax(
                Box::new(SpecLevel::Param("a".to_string())),
                Box::new(SpecLevel::Zero),
            )),
        );
        assert_eq!(reflect_level(&level), expected);
        let reflection = Reflection {
            interning: vec![
                ("z".to_string(), 0),
                ("a".to_string(), 1),
                ("Head".to_string(), 2),
            ],
            ..Reflection::default()
        };
        let expected_level = "(Level.imax (Level.max (Level.succ (Level.param kcre_name_0)) (Level.param kcre_name_1)) (Level.imax (Level.param kcre_name_1) Level.zero))";
        let param_z = Expr::app(
            Expr::const_str("Level.param"),
            Expr::const_str("kcre_name_0"),
        );
        let param_a = Expr::app(
            Expr::const_str("Level.param"),
            Expr::const_str("kcre_name_1"),
        );
        let expected_term = Expr::apps(
            Expr::const_str("Level.imax"),
            [
                Expr::apps(
                    Expr::const_str("Level.max"),
                    [
                        Expr::app(Expr::const_str("Level.succ"), param_z),
                        param_a.clone(),
                    ],
                ),
                Expr::apps(
                    Expr::const_str("Level.imax"),
                    [param_a, Expr::const_str("Level.zero")],
                ),
            ],
        );
        assert_eq!(
            reflection
                .render_level(&expected)
                .expect("all parameter names present"),
            expected_level
        );
        assert_eq!(
            reflection
                .level_term(&expected)
                .expect("all parameter names present"),
            expected_term
        );
        for (source, image, rendered, term) in [
            (Expr::sort(level.clone()), SpecExpr::Sort(expected.clone()),
                format!("(KExpr.sort {expected_level})"),
                Expr::app(Expr::const_str("KExpr.sort"), expected_term.clone())),
            (Expr::const_str_levels("Head", vec![level]), SpecExpr::Const("Head".to_string(), vec![expected]),
                format!("(KExpr.const kcre_name_2 (ListType.cons Level {expected_level} (ListType.nil Level)))"),
                Expr::apps(Expr::const_str("KExpr.const"), [
                    Expr::const_str("kcre_name_2"),
                    Expr::apps(Expr::const_str("ListType.cons"), [
                        Expr::const_str("Level"), expected_term,
                        Expr::app(Expr::const_str("ListType.nil"), Expr::const_str("Level")),
                    ]),
                ])),
        ] {
            assert_eq!(reflect_definition_expr(&source).expect("represented expression"), image);
            let mut text = String::new();
            reflection.render_expr(&image, &mut text).expect("text emission");
            assert_eq!(text, rendered);
            assert_eq!(reflection.kexpr_term(&image).expect("Expr emission"), term);
            let mut missing = reflection.clone();
            missing.interning.retain(|(name, _)| name != "a");
            assert!(missing.render_expr(&image, &mut String::new()).is_err());
            assert!(missing.kexpr_term(&image).is_err());
        }
    }

    #[test]
    fn test_legacy_iota_adapter_is_deliberately_not_the_faithful_definition_adapter() {
        use std::sync::Arc;
        let parameter = Level::Param(Name::from_string("u"));
        let raw = Level::IMax(
            Arc::new(Level::succ(parameter.clone())).into(),
            Arc::new(parameter).into(),
        );
        let source = Expr::app(
            Expr::sort(raw.clone()),
            Expr::const_str_levels("Head", vec![raw]),
        );
        let erased = reflect_legacy_erased_iota_expr(&source).expect("represented rule");
        assert_eq!(
            erased,
            SpecExpr::App(
                Box::new(SpecExpr::Sort(SpecLevel::Succ(Box::new(SpecLevel::Zero)))),
                Box::new(SpecExpr::Const(
                    "Head".to_string(),
                    vec![SpecLevel::IMax(
                        Box::new(SpecLevel::Succ(Box::new(SpecLevel::Zero))),
                        Box::new(SpecLevel::Zero),
                    )]
                )),
            )
        );
        assert_ne!(
            erased,
            reflect_definition_expr(&source).expect("faithful definition image")
        );
    }

    #[test]
    fn test_structural_name_collisions_reject_complete_reflection_batch() {
        let collisions = [
            (Name::anon().str("7"), Name::anon().num(7)),
            (
                Name::anon().str("nested.u"),
                Name::anon().str("nested").str("u"),
            ),
            (Name::anon(), Name::anon().str("[anonymous]")),
        ];
        for (left, right) in collisions {
            assert_ne!(left, right, "actual structural names differ");
            assert_eq!(
                left.to_string(),
                right.to_string(),
                "the display key collides"
            );
            let mut one_record = Environment::new();
            checked_sort_definition(
                &mut one_record,
                Name::from_string("Nat.add"),
                vec![left.clone(), right.clone()],
                Level::Param(left.clone()),
            );
            assert!(matches!(reflect_foundation_core(&one_record),
                Err(ReflectError::InvalidReflection { detail }) if detail.contains("distinct structural")));
            let mut two_records = Environment::new();
            checked_sort_definition(
                &mut two_records,
                Name::from_string("Nat.add"),
                vec![left.clone()],
                Level::Param(left),
            );
            checked_sort_definition(
                &mut two_records,
                Name::from_string("Nat.sub"),
                vec![right.clone()],
                Level::Param(right),
            );
            assert!(matches!(reflect_foundation_core(&two_records),
                Err(ReflectError::InvalidReflection { detail }) if detail.contains("distinct structural")));
        }
    }

    #[test]
    fn test_semantic_parameter_names_are_not_constant_dependency_edges() {
        let u = Name::from_string("OnlyInLevels");
        let mut env = Environment::new();
        checked_sort_definition(&mut env, u.clone(), vec![], Level::Zero);
        checked_sort_definition(
            &mut env,
            Name::from_string("Nat.add"),
            vec![u.clone()],
            Level::Param(u),
        );
        let reflection = reflect_foundation_core(&env).expect("unambiguous actual names");
        assert!(
            reflection.tag_of("OnlyInLevels").is_some(),
            "parameter occurrence is interned"
        );
        assert!(
            !reflection.skips.iter().any(|s| s.item == "OnlyInLevels"),
            "a level parameter must not invent a valueful constant dependency"
        );
        let mut dependencies = BTreeMap::new();
        for def in &reflection.defs {
            count_consts(&def.type_, &mut dependencies);
            count_consts(&def.value, &mut dependencies);
        }
        assert!(dependencies.is_empty());
    }

    #[test]
    fn test_dependency_ledger_uses_actual_structural_name_not_display_reparse() {
        let actual = Name::anon().str("7");
        assert_ne!(actual, Name::from_string(&actual.to_string()));
        let mut env = Environment::new();
        checked_sort_definition(&mut env, actual.clone(), vec![], Level::Zero);
        env.add_decl(clean_kernel::Declaration::Definition {
            name: Name::from_string("Nat.add"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::Zero)),
            value: Expr::const_(actual, vec![]),
            is_reducible: false,
        })
        .expect("checked reference to the actual noncanonical source name");
        let reflection = reflect_foundation_core(&env).expect("collision-free noncanonical name");
        assert!(
            reflection
                .skips
                .iter()
                .any(|s| s.item == "7" && s.reason.contains("value-ful")),
            "the actual valueful constant must be recorded even though from_string would miss it"
        );
    }

    #[test]
    fn test_batch_name_registry_rejects_tsv_ambiguity_and_keeps_reserved_identity() {
        for name in [
            Name::anon().str(""),
            Name::anon().str("tab\tkey"),
            Name::anon().str("line\nkey"),
        ] {
            let mut registry = SourceNames::default();
            assert!(registry.record(&name).is_err());
        }
        let mut registry = SourceNames::default();
        for name in RESERVED_LITERAL_BUILTINS {
            registry
                .record(&Name::from_string(name))
                .expect("canonical reserved name");
            registry
                .record(&Name::anon().str(name))
                .expect("same actual structural name");
        }
        assert_eq!(registry.by_display.len(), RESERVED_LITERAL_BUILTINS.len());
    }

    #[test]
    fn test_definition_reflection_rejects_kind_drift_with_unchanged_payload() {
        let valid = ConstantInfo::new(
            Name::from_string("Payload"),
            vec![],
            Expr::sort(Level::succ(Level::Zero)),
            Some(Expr::sort(Level::Zero)),
            false,
        );
        assert_eq!(valid.kind, ConstantKind::Definition);
        let reflected = reflect_definition(&valid).expect("ordinary non-abbreviation definition");
        assert!(!reflected.is_reducible);
        for kind in [
            ConstantKind::Opaque,
            ConstantKind::Theorem,
            ConstantKind::Axiom,
        ] {
            // Change ONLY kind, so neither an unchanged reducibility hint nor
            // the exact same parameter/type/value payload can mask kind drift.
            let mut changed = valid.clone();
            changed.kind = kind;
            assert_eq!(changed.level_params, valid.level_params);
            assert_eq!(changed.type_, valid.type_);
            assert_eq!(changed.value, valid.value);
            assert_eq!(changed.is_reducible, valid.is_reducible);
            assert_eq!(changed.reducibility, valid.reducibility);
            assert_eq!(
                reflect_definition(&changed).expect_err("unsupported kind must be refused"),
                format!(
                    "unsupported declaration kind {kind:?}: this reflection accepts ordinary definitions only"
                ),
            );
        }
        let mut abbreviation = valid;
        abbreviation.is_reducible = true;
        abbreviation.reducibility = clean_kernel::Reducibility::Reducible;
        assert!(
            reflect_definition(&abbreviation)
                .expect("ordinary abbreviation definition is also supported")
                .is_reducible
        );
    }

    #[test]
    fn test_definition_kind_refusals_are_recorded_for_checked_valueful_entries() {
        use clean_kernel::{BinderInfo, Declaration};

        // forall (P : Prop), P -> P has a value accepted as a Definition,
        // Theorem, or Opaque declaration. Each environment goes through real
        // checked admission, unlike the deliberate field-mutation control above.
        let type_ = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::Zero),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        let value = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::Zero),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        );
        let name = Name::from_string("Nat.add"); // An actual allowlisted key.
        for kind in [
            ConstantKind::Definition,
            ConstantKind::Opaque,
            ConstantKind::Theorem,
        ] {
            let decl = match kind {
                ConstantKind::Definition => Declaration::Definition {
                    name: name.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                    value: value.clone(),
                    is_reducible: false,
                },
                ConstantKind::Opaque => Declaration::Opaque {
                    name: name.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                    value: value.clone(),
                },
                ConstantKind::Theorem => Declaration::Theorem {
                    name: name.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                    value: value.clone(),
                },
                ConstantKind::Axiom => unreachable!("fixture kinds all carry values"),
            };
            let mut env = Environment::new();
            env.add_decl(decl).expect("checked identity declaration");
            let ci = env.get_const(&name).expect("admitted fixture");
            assert_eq!(ci.kind, kind);
            assert_eq!(ci.type_, type_);
            assert_eq!(ci.value.as_ref(), Some(&value));
            let reflection = reflect_foundation_core(&env).expect("unambiguous checked fixture");
            let reflected = reflection.defs.iter().any(|def| def.name == "Nat.add");
            let refusal = reflection.skips.iter().find(|skip| skip.item == "Nat.add");
            if kind == ConstantKind::Definition {
                assert!(
                    reflected,
                    "the current ordinary-definition domain is accepted"
                );
                assert!(refusal.is_none());
            } else {
                assert!(
                    !reflected,
                    "unsupported valueful kind must not produce a delta entry"
                );
                assert_eq!(
                    refusal.expect("kind refusal must be visible in the ledger").reason,
                    format!(
                        "unsupported declaration kind {kind:?}: this reflection accepts ordinary definitions only"
                    ),
                );
            }
        }
    }

    #[test]
    fn test_definition_reflection_keeps_one_source_record_and_parameter_order() {
        let ci = ConstantInfo::new(
            Name::from_string("Payload"),
            vec![Name::from_string("z"), Name::from_string("a")],
            Expr::const_str_levels("OnlyInType", vec![Level::Param(Name::from_string("z"))]),
            Some(Expr::const_str_levels(
                "OnlyInValue",
                vec![Level::Param(Name::from_string("a"))],
            )),
            false,
        );
        let reflected = reflect_definition(&ci).expect("both fields are representable");
        assert_eq!(reflected.name, "Payload");
        assert_eq!(reflected.level_params, ["z", "a"]);
        assert!(!reflected.is_reducible);
        assert_eq!(
            reflected.type_,
            SpecExpr::Const(
                "OnlyInType".to_string(),
                vec![SpecLevel::Param("z".to_string())]
            ),
            "the actual schematic type retains its parameter occurrence"
        );
        assert_eq!(
            reflected.value,
            SpecExpr::Const(
                "OnlyInValue".to_string(),
                vec![SpecLevel::Param("a".to_string())]
            ),
            "the body is distinct from the type and retains its own parameter"
        );
        let reflection = Reflection {
            interning: build_interning(&[], std::slice::from_ref(&reflected)),
            defs: vec![reflected],
            ..Reflection::default()
        };
        let z = reflection.render_name("z").expect("first parameter");
        let a = reflection.render_name("a").expect("second parameter");
        let type_name = reflection
            .render_name("OnlyInType")
            .expect("type-only name");
        let value_name = reflection
            .render_name("OnlyInValue")
            .expect("value-only name");
        assert_eq!(
            reflection.render_definition(&reflection.defs[0]).expect("record rendering"),
            format!(
                "(KDefSig.mk (KConstSig.mk (ListType.cons Name {z} (ListType.cons Name {a} (ListType.nil Name))) (KExpr.const {type_name} (ListType.cons Level (Level.param {z}) (ListType.nil Level)))) (KExpr.const {value_name} (ListType.cons Level (Level.param {a}) (ListType.nil Level))))"
            ),
            "one signature owns the original ordered params and type; value is separate"
        );
        let mut missing_type = reflection.clone();
        missing_type
            .interning
            .retain(|(name, _)| name != "OnlyInType");
        assert!(missing_type
            .render_definition(&missing_type.defs[0])
            .is_err());
        let mut missing_param = reflection.clone();
        missing_param.interning.retain(|(name, _)| name != "z");
        assert!(missing_param
            .render_definition(&missing_param.defs[0])
            .is_err());
    }

    #[test]
    fn test_definition_reflection_rejects_unrepresentable_type_or_value_whole() {
        let valid = ConstantInfo::new(
            Name::from_string("Payload"),
            vec![],
            Expr::sort(Level::succ(Level::Zero)),
            Some(Expr::sort(Level::Zero)),
            true,
        );
        let reflected = reflect_definition(&valid).expect("representable record");
        assert_eq!(
            reflected.type_,
            SpecExpr::Sort(SpecLevel::Succ(Box::new(SpecLevel::Zero)))
        );
        assert_eq!(reflected.value, SpecExpr::Sort(SpecLevel::Zero));
        let mut literal = valid.clone();
        literal.type_ = Expr::nat_lit(7);
        literal.value = Some(Expr::nat_lit(11));
        let reflected_literal =
            reflect_definition(&literal).expect("literal nodes now have images");
        assert_eq!(
            reflected_literal.type_,
            SpecExpr::Lit(clean_kernel::Literal::Nat(clean_kernel::BigNat::from_u64(
                7
            )))
        );
        assert_eq!(
            reflected_literal.value,
            SpecExpr::Lit(clean_kernel::Literal::Nat(clean_kernel::BigNat::from_u64(
                11
            )))
        );
        let mut invalid_type = valid.clone();
        invalid_type.type_ = Expr::proj(Name::from_string("Unsupported"), 0, Expr::bvar(0));
        assert!(reflect_definition(&invalid_type)
            .expect_err("unsupported type rejects the complete record")
            .starts_with("schematic type unrepresentable:"));
        let mut invalid_value = valid.clone();
        invalid_value.value = Some(Expr::proj(
            Name::from_string("Unsupported"),
            0,
            Expr::bvar(0),
        ));
        assert!(reflect_definition(&invalid_value)
            .expect_err("unsupported body rejects the complete record")
            .starts_with("value unrepresentable:"));
        let mut no_value = valid;
        no_value.value = None;
        assert!(reflect_definition(&no_value)
            .expect_err("no body cannot produce a definition record")
            .starts_with("constant has no value"));
    }

    #[test]
    fn test_legacy_erased_iota_sort_height_remains_explicitly_erased() {
        let p = Level::Param(Name::from_string("u"));
        assert_eq!(erase_level_to_nat(&p), 0, "param erases to 0");
        let s = Level::succ(Level::Zero);
        assert_eq!(erase_level_to_nat(&s), 1, "succ adds 1");
        // `Level::imax` is a SMART constructor with Lean 4 parity, not a raw
        // variant: `imax(_, 0)` normalises to `Zero` before `erase_level_to_nat`
        // ever sees it (level/mod.rs:482-485). So this pair is not a test of the
        // IMax arm at all — it is a test that the normalisation happened.
        let collapsed = Level::imax(s.clone(), Level::Zero);
        assert_eq!(collapsed, Level::Zero, "imax(_, 0) normalises to zero");
        assert_eq!(erase_level_to_nat(&collapsed), 0, "and so erases to 0");

        // To reach the IMax arm the right operand must be neither definitely
        // zero nor definitely nonzero — i.e. a bare param. Then the erasure is
        // the max of the erased sides: succ(u) -> 1, v -> 0.
        let m = Level::imax(Level::succ(p.clone()), Level::Param(Name::from_string("v")));
        assert!(matches!(m, Level::IMax(_, _)), "this imax must survive");
        assert_eq!(erase_level_to_nat(&m), 1, "imax erases to max");
    }

    #[test]
    fn test_signature_only_capture_accepts_bodyless_source_and_rejects_mismatches() {
        let (rv, ci) = signature_fixture();
        let good = reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, Some(&ci))
            .expect("body-less Definition signature is represented");
        assert_eq!(good.name, ci.name);
        assert_eq!(good.level_params, ci.level_params);
        assert_eq!(
            good.type_,
            reflect_definition_expr(&ci.type_).expect("structural type")
        );
        assert!(ci.value.is_none());
        assert!(
            reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, None)
                .expect_err("absent signature")
                .contains("absent")
        );
        let mut bad = ci.clone();
        bad.name = Name::from_string("Wrong.rec");
        assert!(
            reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, Some(&bad))
                .expect_err("wrong actual name")
                .contains("name mismatch")
        );
        bad = ci.clone();
        bad.level_params.reverse();
        assert!(
            reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, Some(&bad))
                .expect_err("reordered parameters")
                .contains("parameters mismatch")
        );
        bad = ci.clone();
        bad.type_ = Expr::sort(Level::Zero);
        assert!(
            reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, Some(&bad))
                .expect_err("wrong actual type")
                .contains("type mismatch")
        );
        for kind in [
            ConstantKind::Axiom,
            ConstantKind::Theorem,
            ConstantKind::Opaque,
        ] {
            bad = ci.clone();
            bad.kind = kind;
            assert!(
                reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, Some(&bad))
                    .expect_err("different source kind")
                    .contains("value-less Definition")
            );
        }
        bad = ci.clone();
        bad.value = Some(Expr::bvar(0));
        assert!(
            reflect_source_signature(&rv.name, &rv.level_params, &rv.type_, Some(&bad)).is_err()
        );
        bad = ci.clone();
        bad.type_ = Expr::proj(Name::from_string("Unsupported"), 0, Expr::bvar(0));
        assert!(
            reflect_source_signature(&rv.name, &rv.level_params, &bad.type_, Some(&bad))
                .expect_err("unrepresented signature node")
                .contains("unrepresentable")
        );
    }

    #[test]
    fn test_signature_names_preserve_structural_identity_and_old_tags() {
        let left = Name::anon().str("nested.u");
        let right = Name::anon().str("nested").str("u");
        assert_ne!(left, right);
        assert_eq!(left.to_string(), right.to_string());
        let ci = ConstantInfo::new(
            Name::from_string("Signature"),
            vec![left.clone()],
            Expr::sort(Level::Param(right)),
            None,
            false,
        );
        assert!(
            matches!(register_signature_source_names(&ci, &mut SourceNames::default()),
            Err(ReflectError::InvalidReflection { detail }) if detail.contains("distinct structural"))
        );
        let ci = ConstantInfo::new(
            Name::anon().str("7"),
            vec![Name::from_string("OnlyParameter")],
            Expr::sort(Level::Param(Name::from_string("OnlyType"))),
            None,
            false,
        );
        let mut registry = SourceNames::default();
        register_signature_source_names(&ci, &mut registry).expect("unambiguous actual names");
        assert_eq!(registry.by_display.get("7"), Some(&ci.name));
        assert_ne!(
            Name::from_string("7"),
            ci.name,
            "display parsing loses source identity"
        );
        let signature = reflect_source_signature(&ci.name, &ci.level_params, &ci.type_, Some(&ci))
            .expect("signature image");
        let mut tags = vec![("Nat".to_string(), 0), ("String".to_string(), 1)];
        let before = tags.clone();
        append_signature_names(&mut tags, std::slice::from_ref(&signature));
        assert_eq!(
            &tags[..before.len()],
            before.as_slice(),
            "old tags must stay fixed"
        );
        assert_eq!(
            &tags[before.len()..],
            [
                ("7".to_string(), 2),
                ("OnlyParameter".to_string(), 3),
                ("OnlyType".to_string(), 4),
            ]
        );
        let once = tags.clone();
        append_signature_names(&mut tags, &[signature]);
        assert_eq!(
            tags, once,
            "repeated signature names do not renumber or duplicate"
        );
    }

    #[test]
    fn test_live_nat_signature_slice_uses_actual_records_and_preserves_tags() {
        crate::test_utils::run_with_stack(|| {
            let seed = crate::spec::Specification::new_red_env_reflection_seed().expect("seed");
            let reflection = reflect_foundation_core(seed.env()).expect("source reflection");
            assert_eq!(reflection.nat_signatures.len(), 4);
            let old_tags = build_interning(&reflection.recs, &reflection.defs);
            assert_eq!(
                &reflection.interning[..old_tags.len()],
                old_tags,
                "signature-only metadata must not reweight existing reduction names"
            );
            for (signature, expected) in reflection.nat_signatures.iter().zip(NAT_SIGNATURE_NAMES) {
                let ci = seed
                    .env()
                    .get_const(&signature.name)
                    .expect("actual-name source CI");
                assert_eq!(signature.name, Name::from_string(expected));
                assert_eq!(signature.level_params, ci.level_params);
                assert_eq!(
                    signature.type_,
                    reflect_definition_expr(&ci.type_).expect("source type")
                );
                assert_eq!(ci.kind, ConstantKind::Definition);
                assert!(ci.value.is_none());
                assert!(
                    !reflection
                        .defs
                        .iter()
                        .any(|def| def.name == signature.name.to_string()),
                    "signature capture must not invent a delta body"
                );
            }
            let script = reflection.def_script().expect("complete source data emits");
            for atom in NAT_SIGNATURE_ATOMS {
                assert!(script.contains(&format!("def {atom} : KConstSig :=")));
            }
            assert!(script.contains("def kcre_nat_tenv : KDeclEnv := fun (nm : Name) =>"));
            let nat_lookup = script
                .lines()
                .find(|line| line.starts_with("def kcre_nat_tenv"))
                .expect("actual generated lookup");
            assert!(
                !nat_lookup.contains("fixture_nat_"),
                "late fixture aliases are unavailable"
            );
            for signature in &reflection.nat_signatures {
                assert!(nat_lookup.contains(
                    &reflection
                        .render_name(&signature.name.to_string())
                        .expect("same validated name table")
                ));
            }
            let mut absent = reflection.clone();
            absent.nat_signatures.remove(1);
            assert!(
                absent.def_script().is_err(),
                "missing required CI must not publish"
            );
            let mut wrong_rec = reflection.clone();
            wrong_rec.nat_signatures[3].level_params.clear();
            assert!(
                wrong_rec.def_script().is_err(),
                "recursor signature disagreement refuses"
            );
            let mut missing_key = reflection.clone();
            missing_key.interning.retain(|(name, _)| name != "Nat.zero");
            assert!(
                missing_key.def_script().is_err(),
                "missing interned source key refuses"
            );
        });
    }

    #[test]
    fn test_absent_nat_signature_slice_is_ledgered_and_cannot_emit() {
        let reflection = reflect_foundation_core(&Environment::new()).expect("partial diagnostic");
        assert!(reflection.nat_signatures.is_empty());
        assert!(reflection
            .skips
            .iter()
            .any(|skip| skip.item.starts_with("(required typing slice)")
                && skip.reason.contains("absent")));
        assert!(
            reflection.def_script().is_err(),
            "an absent typing slice cannot become an artifact"
        );
    }

    #[test]
    fn test_live_projection_metadata_and_source_checked_prod_caller() {
        crate::test_utils::run_with_stack(|| {
            let seed = crate::spec::Specification::new_red_env_reflection_seed().expect("seed");
            let env = seed.env();
            let reflection = reflect_foundation_core(env).expect("complete source image");
            assert_eq!(reflection.inductives.len(), REFLECT_INDUCTIVES.len());
            let mut ctor_count = 0;
            for (image, expected) in reflection.inductives.iter().zip(REFLECT_INDUCTIVES) {
                let actual = env
                    .get_inductive(&Name::from_string(expected))
                    .expect("actual family");
                assert_eq!(image.signature.name, actual.name);
                assert_eq!(image.signature.level_params, actual.level_params);
                assert_eq!(
                    image.signature.type_,
                    reflect_definition_expr(&actual.type_).unwrap()
                );
                assert_eq!(image.num_params, actual.num_params);
                assert_eq!(image.num_indices, actual.num_indices);
                assert_eq!(image.constructor_names, actual.constructor_names);
                assert_eq!(image.all_names, actual.all_names);
                for (index, name) in actual.constructor_names.iter().enumerate() {
                    let source = env
                        .get_constructor(name)
                        .expect("actual associated constructor");
                    let captured = &reflection.constructors[ctor_count];
                    assert_eq!(captured.signature.name, source.name);
                    assert_eq!(captured.signature.level_params, source.level_params);
                    assert_eq!(
                        captured.signature.type_,
                        reflect_definition_expr(&source.type_).unwrap()
                    );
                    assert_eq!(captured.inductive_name, actual.name);
                    assert_eq!(captured.num_params, source.num_params);
                    assert_eq!(captured.num_fields, source.num_fields);
                    assert_eq!(captured.constructor_idx as usize, index);
                    ctor_count += 1;
                }
            }
            assert_eq!(reflection.constructors.len(), ctor_count);
            let witness = reflection
                .projection_witness
                .as_ref()
                .expect("source-checked caller");
            let nat = SpecExpr::Const("Nat".to_string(), vec![]);
            let zero = SpecExpr::Const("Nat.zero".to_string(), vec![]);
            assert_eq!(
                witness.value,
                Reflection::apply_expr_spine(
                    SpecExpr::Const("ProdType.mk".to_string(), vec![]),
                    [
                        nat.clone(),
                        nat.clone(),
                        zero.clone(),
                        SpecExpr::App(
                            Box::new(SpecExpr::Const("Nat.succ".to_string(), vec![])),
                            Box::new(zero)
                        )
                    ]
                )
            );
            assert_eq!(
                witness.type_,
                Reflection::apply_expr_spine(
                    SpecExpr::Const("ProdType".to_string(), vec![]),
                    [nat.clone(), nat]
                )
            );
            let script = reflection.def_script().expect("complete metadata emits");
            assert!(
                max_paren_depth(&script) < 128,
                "metadata atoms must respect the real parser depth"
            );
            for line in script.lines() {
                clean_parser::parse_decl(line)
                    .unwrap_or_else(|error| panic!("generated line must parse: {line}\n{error:?}"));
            }
            for name in [
                "kcre_ind_ctor_env",
                "kcre_ind_ctor_tenv",
                "kcre_prod_ind_meta",
                "kcre_prod_ctor_meta",
                "kcre_prod_type_signature",
                "kcre_prod_mk_signature",
                "kcre_witness_prod_value",
                "kcre_witness_prod_type",
            ] {
                assert!(script
                    .lines()
                    .any(|line| line.starts_with(&format!("def {name} :"))));
            }
            assert!(script
                .lines()
                .find(|line| line.starts_with("def kernel_core_red_env :"))
                .unwrap()
                .ends_with("kcre_ind_ctor_env"));
            let original = build_interning(&reflection.recs, &reflection.defs);
            assert_eq!(
                &reflection.interning[..original.len()],
                original,
                "metadata-only names append without changing the reduction name ranks"
            );
        });
    }

    #[test]
    fn test_projection_metadata_refuses_corrupted_source_associations_and_signatures() {
        crate::test_utils::run_with_stack(|| {
            let mut env = Environment::new();
            let z = Name::from_string("z");
            let a = Name::from_string("a");
            let family = Name::from_string("ProjectionMetaPair");
            let ctor_name = Name::from_string("ProjectionMetaPair.mk");
            let levels = vec![Level::param(z.clone()), Level::param(a.clone())];
            let result = Expr::app(
                Expr::app(Expr::const_(family.clone(), levels.clone()), Expr::bvar(3)),
                Expr::bvar(2),
            );
            env.add_inductive(clean_kernel::InductiveDecl {
                level_params: vec![z, a],
                num_params: 2,
                types: vec![clean_kernel::InductiveType {
                    name: family.clone(),
                    type_: Expr::pi(
                        clean_kernel::BinderInfo::Default,
                        Expr::sort(levels[0].clone()),
                        Expr::pi(
                            clean_kernel::BinderInfo::Default,
                            Expr::sort(levels[1].clone()),
                            Expr::sort(Level::max(levels[0].clone(), levels[1].clone())),
                        ),
                    ),
                    constructors: vec![clean_kernel::Constructor {
                        name: ctor_name.clone(),
                        type_: Expr::pi(
                            clean_kernel::BinderInfo::Default,
                            Expr::sort(levels[0].clone()),
                            Expr::pi(
                                clean_kernel::BinderInfo::Default,
                                Expr::sort(levels[1].clone()),
                                Expr::pi(
                                    clean_kernel::BinderInfo::Default,
                                    Expr::bvar(1),
                                    Expr::pi(
                                        clean_kernel::BinderInfo::Default,
                                        Expr::bvar(1),
                                        result,
                                    ),
                                ),
                            ),
                        ),
                    }],
                }],
            })
            .expect("genuinely admit a two-universe source family");
            let ind = env.get_inductive(&family).unwrap();
            let ctor = env.get_constructor(&ctor_name).unwrap();
            let ind_ci = env.get_const(&family).unwrap();
            let ctor_ci = env.get_const(&ctor_name).unwrap();
            reflect_inductive_metadata(&family, ind, Some(ind_ci)).unwrap();
            reflect_constructor_metadata(ind, 0, ctor, Some(ctor_ci)).unwrap();

            let mut bad = ctor.clone();
            bad.inductive_name = Name::from_string("WrongParent");
            assert!(reflect_constructor_metadata(ind, 0, &bad, Some(ctor_ci))
                .unwrap_err()
                .contains("parent/order"));
            bad = ctor.clone();
            bad.constructor_idx = 1;
            assert!(reflect_constructor_metadata(ind, 0, &bad, Some(ctor_ci)).is_err());
            bad = ctor.clone();
            bad.level_params.reverse();
            assert!(reflect_constructor_metadata(ind, 0, &bad, Some(ctor_ci)).is_err());
            bad = ctor.clone();
            bad.num_params += 1;
            assert!(reflect_constructor_metadata(ind, 0, &bad, Some(ctor_ci)).is_err());
            bad = ctor.clone();
            bad.num_fields += 1;
            assert!(reflect_constructor_metadata(ind, 0, &bad, Some(ctor_ci))
                .unwrap_err()
                .contains("telescope count"));
            let mut wrong_ci = ctor_ci.clone();
            wrong_ci.level_params.reverse();
            assert!(reflect_constructor_metadata(ind, 0, ctor, Some(&wrong_ci))
                .unwrap_err()
                .contains("parameters mismatch"));
            wrong_ci = ctor_ci.clone();
            wrong_ci.type_ = Expr::prop();
            assert!(reflect_constructor_metadata(ind, 0, ctor, Some(&wrong_ci))
                .unwrap_err()
                .contains("type mismatch"));
            assert!(reflect_constructor_metadata(ind, 0, ctor, None)
                .unwrap_err()
                .contains("absent"));
            let mut bad_ind = ind.clone();
            bad_ind.constructor_names.push(ctor_name);
            assert!(reflect_inductive_metadata(&family, &bad_ind, Some(ind_ci))
                .unwrap_err()
                .contains("colliding"));
            bad_ind = ind.clone();
            bad_ind.num_indices += 1;
            assert!(reflect_inductive_metadata(&family, &bad_ind, Some(ind_ci))
                .unwrap_err()
                .contains("telescope count"));
            let mut wrong_ind_ci = ind_ci.clone();
            wrong_ind_ci.level_params.reverse();
            assert!(
                reflect_inductive_metadata(&family, ind, Some(&wrong_ind_ci))
                    .unwrap_err()
                    .contains("parameters mismatch")
            );
        });
    }

    #[test]
    fn test_projection_metadata_missing_or_incoherent_image_cannot_publish() {
        crate::test_utils::run_with_stack(|| {
            let seed = crate::spec::Specification::new_red_env_reflection_seed().expect("seed");
            let good = reflect_foundation_core(seed.env()).expect("source image");
            good.def_script().expect("positive publication control");
            let mut bad = good.clone();
            bad.inductives.pop();
            assert!(bad.def_script().is_err());
            bad = good.clone();
            bad.constructors.pop();
            assert!(bad.def_script().is_err());
            bad = good.clone();
            bad.constructors[0].inductive_name = Name::from_string("WrongParent");
            assert!(bad.def_script().is_err());
            bad = good.clone();
            bad.constructors[0].num_fields += 1;
            assert!(bad.def_script().is_err());
            bad = good.clone();
            bad.inductives[0].constructor_names.reverse();
            assert!(bad.def_script().is_err());
            bad = good.clone();
            bad.projection_witness = None;
            assert!(bad.def_script().is_err());
            let absent = reflect_foundation_core(&Environment::new()).expect("partial diagnostics");
            assert!(absent.inductives.is_empty());
            assert!(absent.skips.iter().any(|skip| skip
                .item
                .starts_with("(required projection metadata)")
                && skip.reason.contains("absent")));
            assert!(absent.def_script().is_err());
        });
    }

    #[test]
    fn test_render_nat_unary() {
        assert_eq!(render_nat(0), "Nat.zero");
        assert_eq!(render_nat(2), "(Nat.succ (Nat.succ Nat.zero))");
    }

    #[test]
    fn test_interning_orders_by_frequency_then_name() {
        let recs = vec![ReflectedRec {
            name: "B.rec".to_string(),
            level_params: vec![],
            type_: SpecExpr::Sort(SpecLevel::Zero),
            num_params: 0,
            num_motives: 1,
            num_minors: 1,
            num_indices: 0,
            major_after_minors: true,
            is_k: false,
            rules: vec![ReflectedRule {
                ctor: "B.mk".to_string(),
                num_fields: 0,
                rhs: SpecExpr::App(
                    Box::new(SpecExpr::Const("Hot".to_string(), vec![])),
                    Box::new(SpecExpr::Const("Hot".to_string(), vec![])),
                ),
            }],
        }];
        let interning = build_interning(&recs, &[]);
        assert_eq!(
            interning.first().map(|(n, t)| (n.as_str(), *t)),
            Some(("Hot", 0)),
            "most frequent name gets tag 0"
        );
        assert_eq!(
            interning
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            ["Hot", "B.mk", "B.rec", "Nat", "String"],
            "reserved builtins must not renumber encountered names"
        );
        let r = Reflection {
            recs,
            defs: vec![],
            nat_signatures: vec![],
            inductives: vec![],
            constructors: vec![],
            projection_witness: None,
            interning,
            skips: vec![],
        };
        assert!(r.interning_injective(), "interning must be injective");
        assert!(
            matches!(r.def_script(), Err(ReflectError::InvalidReflection { .. })),
            "artifact emission must fail closed when required live witnesses are absent"
        );
    }

    #[test]
    fn test_nat_zero_witness_spine_is_derived_from_reflected_metadata() {
        let recs = vec![ReflectedRec {
            name: "Nat.rec".to_string(),
            level_params: vec!["u".to_string()],
            type_: SpecExpr::Sort(SpecLevel::Zero),
            num_params: 1,
            num_motives: 1,
            num_minors: 0,
            num_indices: 1,
            major_after_minors: true,
            is_k: false,
            rules: vec![ReflectedRule {
                ctor: "Nat.zero".to_string(),
                num_fields: 0,
                rhs: SpecExpr::Const("Witness.rhs".to_string(), vec![]),
            }],
        }];
        let defs = vec![ReflectedDef {
            name: "def_env_lift_closed_b".to_string(),
            is_reducible: true,
            level_params: vec![],
            type_: SpecExpr::Sort(SpecLevel::Zero),
            value: SpecExpr::Const("Witness.delta".to_string(), vec![]),
        }];
        // This test intentionally exercises a synthetic, non-Nat metadata
        // shape. Its signature data is only a renderer fixture, not source evidence.
        let nat_name = Name::from_string("Nat");
        let nat_type = SpecExpr::Const("Nat".to_string(), vec![]);
        let nat_signatures = vec![
            ReflectedConstSig {
                name: nat_name,
                level_params: vec![],
                type_: SpecExpr::Sort(SpecLevel::Succ(Box::new(SpecLevel::Zero))),
            },
            ReflectedConstSig {
                name: Name::from_string("Nat.zero"),
                level_params: vec![],
                type_: nat_type.clone(),
            },
            ReflectedConstSig {
                name: Name::from_string("Nat.succ"),
                level_params: vec![],
                type_: SpecExpr::Pi(Box::new(nat_type.clone()), Box::new(nat_type)),
            },
            ReflectedConstSig {
                name: Name::from_string("Nat.rec"),
                level_params: vec![Name::from_string("u")],
                type_: recs[0].type_.clone(),
            },
        ];
        let mut interning = build_interning(&recs, &defs);
        append_signature_names(&mut interning, &nat_signatures);
        let reflection = Reflection {
            interning,
            recs,
            defs,
            nat_signatures,
            skips: vec![],
            ..Reflection::default()
        };
        let witness = reflection
            .nat_zero_witness()
            .expect("synthetic metadata should produce a witness");

        fn spine(mut expression: &SpecExpr) -> (&SpecExpr, Vec<&SpecExpr>) {
            let mut reversed = Vec::new();
            while let SpecExpr::App(function, argument) = expression {
                reversed.push(argument.as_ref());
                expression = function.as_ref();
            }
            reversed.reverse();
            (expression, reversed)
        }

        let (redex_head, redex_args) = spine(&witness.redex);
        assert_eq!(
            redex_head,
            &SpecExpr::Const("Nat.rec".to_string(), vec![SpecLevel::Zero])
        );
        assert_eq!(witness.levels, vec![SpecLevel::Zero]);
        assert_eq!(
            redex_args.len(),
            4,
            "params + motives + minors + indices + major"
        );
        assert_eq!(
            redex_args.last().copied(),
            Some(&SpecExpr::Const("Nat.zero".to_string(), vec![]))
        );

        assert_eq!(
            witness.rhs,
            SpecExpr::Const("Witness.rhs".to_string(), vec![])
        );
        assert_eq!(witness.prefix.len(), 2, "params + motives + minors only");
        let mut script = String::new();
        reflection
            .render_nat_zero_witness(&witness, &mut script)
            .expect("synthetic witness fragment renders through the production component");
        assert_eq!(script.lines().count(), 4);
        for line in script.lines() {
            clean_parser::parse_decl(line).expect("each rendered witness definition parses");
        }
        assert!(script.contains("def kcre_witness_rec_levels : ListType Level := (ListType.cons Level Level.zero (ListType.nil Level))"));
        assert!(script.contains("recursor_rhs_instance (recmeta_signature fixture_nat_rec_meta) kcre_witness_nat_zero_rhs kcre_witness_rec_levels"));
        let error = reflection
            .def_script()
            .expect_err("synthetic witness data is not a complete publishable source reflection");
        assert!(
            matches!(error, ReflectError::InvalidReflection { detail } if detail.contains("required projection metadata")),
            "full emission must retain its required metadata validation"
        );
        let mut wrong_arity = reflection.clone();
        wrong_arity.recs[0].level_params.clear();
        assert!(wrong_arity.nat_zero_witness().is_err());
        assert!(wrong_arity.def_script().is_err());
    }

    #[test]
    fn test_parse_interning_tsv_accepts_canonical_contiguous_table() {
        let parsed = parse_interning_tsv("0\tNat\n1\tNat.zero\n2\tNat.succ\n")
            .expect("canonical table should parse");
        assert_eq!(parsed.get("Nat.zero"), Some(&1));
    }

    #[test]
    fn test_parse_interning_tsv_rejects_every_ambiguous_shape() {
        for (label, table) in [
            ("duplicate tag", "0\tNat\n0\tNat.zero\n"),
            ("duplicate name", "0\tNat\n1\tNat\n"),
            ("tag gap", "0\tNat\n2\tNat.zero\n"),
            ("extra column", "0\tNat\textra\n"),
            ("noncanonical tag", "00\tNat\n"),
        ] {
            assert!(
                parse_interning_tsv(table).is_err(),
                "{label} must fail whole-table validation"
            );
        }
    }

    #[test]
    fn test_committed_name_atom_rejects_missing_semantic_name() {
        let error = committed_name_atom("__definitely_not_a_kernel_name__")
            .expect_err("missing semantic name must fail");
        assert!(matches!(error, InterningTableError::MissingName(_)));
    }

    #[test]
    fn test_builtin_reservation_does_not_duplicate_encountered_names() {
        let defs = vec![ReflectedDef {
            name: "String".to_string(),
            is_reducible: true,
            level_params: vec![],
            type_: SpecExpr::Sort(SpecLevel::Zero),
            value: SpecExpr::Const("Nat".to_string(), vec![]),
        }];
        assert_eq!(
            build_interning(&[], &defs),
            vec![("Nat".to_string(), 0), ("String".to_string(), 1)]
        );
    }

    #[test]
    fn test_name_tag_lookup_uses_validated_table_not_builtin_numbers() {
        assert_eq!(name_tag_in_table("0\tString\n1\tNat\n", "Nat"), Ok(1));
        assert_eq!(name_tag_in_table("0\tNat\n1\tString\n", "Nat"), Ok(0));
        assert!(name_tag_in_table("0\tNat\n2\tString\n", "Nat").is_err());
        assert!(name_tag_in_table("0\tNat\n", "String").is_err());
    }

    #[test]
    fn test_fresh_artifact_constructor_rejects_bad_table_before_full_build() {
        let result = crate::Specification::new_with_red_env_reflection_artifacts(
            "deliberately not a script: this must never be reached",
            "0\tNat\n2\tString\n",
        );
        assert!(matches!(result, Err(crate::spec::SpecError::EnvError(_))));
    }
}
