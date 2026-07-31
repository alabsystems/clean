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
//! compares it 1:1 (rule-for-rule, field-for-field on the erased image)
//! against the committed generated artifacts; any drift fails.
//!
//! ## The three encoding TRUST EDGES (each named, each mechanical)
//!
//! 1. **Name interning** (`build_interning`). The spec models
//!    `Name = anonymous | str Name Nat` with a NAT tag (rec_env.rs); real
//!    kernel names are string-based hierarchical names. The generator builds
//!    an INJECTIVE interning table `real name string -> Name.str Name.anonymous
//!    <unary Nat tag>` (tags assigned by descending occurrence count, then
//!    lexicographic — deterministic). Injectivity is what makes every
//!    `name_eqb` verdict over the reflected env agree with real-name equality:
//!    equal strings map to the same tag, distinct strings to distinct tags.
//!    Guarded by `interning_injective` + the emitted-table fidelity test.
//! 2. **Level erasure**. Spec `KExpr.sort` carries a `Level`, including
//!    `param`, but the current reflection deliberately collapses levels:
//!    - `Sort l` is collapsed to a numeric height by [`erase_level_to_nat`]
//!      (`zero`→0, `succ`→+1, `max`/`imax`→max of the erasures — `imax`'s
//!      "0 if right is 0" collapse is dropped, `param`→0), then rendered as
//!      `KExpr.sort (Level.succ^height Level.zero)`;
//!    - `const` universe arguments erase structurally to spec `Level` terms
//!      via [`erase_level_to_spec`] (`param`→`Level.zero`).
//!    This is REDUCTION-FAITHFUL for the modeled fragment: `iota_reduct` /
//!    `delta_reduct` (iota_step.rs / delta_step.rs) are name-keyed spine
//!    surgeries that never inspect sorts or const level lists.
//! 3. **Coverage-with-skips** (the ledger). Everything outside the RecEnv/
//!    DefEnv model is SKIPPED WITH A REASON, lean_export-style, never
//!    silently weakened: Quot rules, K-like reduction (`is_k` recursors are
//!    reflected for their SYNTACTIC rules, with the unmodeled K-extension
//!    recorded), structural eta, native reducers, literals, and any
//!    `Expr` node with no reflected `KExpr` image (projections, literals,
//!    fvars, mode extensions). `Let` is represented directly and `MData` is
//!    transparently erased. A recursor/definition containing an
//!    unrepresentable node is skipped whole.
//!
//! ## What is reflected
//!
//! - Every allowlisted inductive's `<T>.rec` [`clean_kernel::RecursorVal`]
//!   becomes `RecEnv.addRec <interned name> (RecMeta.mk params motives minors
//!   indices major_after_minors) <rules>`, each [`clean_kernel::RecursorRule`]
//!   becoming `RecRule.mk <interned ctor> <num_fields> <level-erased rhs>` —
//!   the REAL rule rhs, translated node-for-node into the `KExpr` vocabulary.
//! - Every allowlisted definition's kernel value becomes
//!   `DefEnv.addDef <interned name> <level-erased value>`.
//!
//! ## Generated artifact shape (the measured parser constraint)
//!
//! The reflection is emitted as a DEF SCRIPT (one `def` per line): a
//! `kcre_nat_<k>` unary pool (depth 2 each), one
//! `def kcre_name_<tag> : Name := Name.str Name.anonymous kcre_nat_<tag>` per
//! interned name (depth 1), then the single `kernel_core_red_env : RedEnv`
//! term whose leaves are those atoms. This shape is forced by a MEASURED
//! constraint: the parser rejects expressions past `MAX_EXPR_DEPTH = 128`,
//! and the naive fully-inlined literal (unary tags in place) nests to paren
//! depth 163; with atom leaves the deepest line is ~64. The helper defs are
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

use clean_kernel::{Environment, Expr, ExprKind, Level, Name, RecursorArgOrder, RecursorVal};

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
    let mut expected = 0_u64;
    for tag in tags {
        if tag != expected {
            return Err(InterningTableError::Invalid(format!(
                "tags are not contiguous from zero: expected {expected}, found {tag}"
            )));
        }
        expected += 1;
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
    let by_name = parse_interning_tsv(COMMITTED_INTERNING_TSV)?;
    by_name
        .get(real_name)
        .map(|tag| format!("kcre_name_{tag}"))
        .ok_or_else(|| InterningTableError::MissingName(real_name.to_string()))
}

/// Foundation-core INDUCTIVE allowlist: the `<T>.rec` recursors reflected into
/// the `RecEnv` leg. These are exactly the types the modeled fragment itself
/// is written in (foundation_types / expr_model / rec_env / delta_step /
/// par_reduces_cd), so the reflected reduction environment contains the
/// metatheory's own object language.
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
    "DefEnv",
    "RedEnv",
];

/// Foundation-core DEFINITION allowlist: the reducible defs reflected into the
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
    // delta_step_core
    "defval_for",
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
    /// Collapsed numeric height later rendered as
    /// `KExpr.sort (Level.succ^height Level.zero)`.
    Sort(u64),
    /// `KExpr.bvar <nat>`.
    BVar(u32),
    /// `KExpr.app f a`.
    App(Box<SpecExpr>, Box<SpecExpr>),
    /// `KExpr.lam ty body` (binder name/info dropped; spec lam is anonymous).
    Lam(Box<SpecExpr>, Box<SpecExpr>),
    /// `KExpr.pi ty body`.
    Pi(Box<SpecExpr>, Box<SpecExpr>),
    /// `KExpr.const <interned name> <level-erased universe args>`.
    Const(String, Vec<SpecLevel>),
    /// `KExpr.let_ ty val body` (binder name/info and the non-dependent flag
    /// dropped; the seventh constructor in the live nine-constructor model).
    Let_(Box<SpecExpr>, Box<SpecExpr>, Box<SpecExpr>),
}

/// Level-erased image of a kernel [`Level`] for `const` universe arguments
/// (`param` collapses to `Zero`; see trust edge 2).
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
}

/// One reflected recursor rule (the erased image of a kernel
/// [`clean_kernel::RecursorRule`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedRule {
    /// Real constructor name (interned at render time).
    pub ctor: String,
    /// Kernel `num_fields`.
    pub num_fields: u32,
    /// The REAL rule rhs, level-erased into the `KExpr` vocabulary.
    pub rhs: SpecExpr,
}

/// One reflected recursor (the erased image of a kernel [`RecursorVal`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedRec {
    /// Real recursor name (e.g. `Nat.rec`; interned at render time).
    pub name: String,
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

/// One reflected definition (the erased image of a kernel value-ful constant).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedDef {
    /// Real definition name (interned at render time).
    pub name: String,
    /// Whether the kernel marks the constant reducible (recorded in the
    /// ledger; delta over the reflected env models value-ful unfolding).
    pub is_reducible: bool,
    /// The REAL kernel value, level-erased into the `KExpr` vocabulary.
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

/// The complete foundation-core reflection of a kernel environment.
#[derive(Debug, Clone, Default)]
pub struct Reflection {
    /// Reflected recursors, in `REFLECT_INDUCTIVES` order.
    pub recs: Vec<ReflectedRec>,
    /// Reflected definitions, in `REFLECT_DEFS` order.
    pub defs: Vec<ReflectedDef>,
    /// Interning table: real name -> unary Nat tag (trust edge 1).
    pub interning: Vec<(String, u64)>,
    /// Skip ledger (trust edge 3).
    pub skips: Vec<SkipEntry>,
}

/// Collapse a kernel [`Level`] to a numeric height for the reflected
/// `KExpr.sort` payload (trust edge 2): `zero`→0, `succ`→+1,
/// `max`/`imax`→max, `param`→0. Rendering re-encodes the height as a spec
/// `Level.succ^n Level.zero`.
#[must_use]
pub fn erase_level_to_nat(l: &Level) -> u64 {
    match l {
        Level::Zero | Level::Param(_) => 0,
        Level::Succ(x) => erase_level_to_nat(x).saturating_add(1),
        Level::Max(a, b) | Level::IMax(a, b) => erase_level_to_nat(a).max(erase_level_to_nat(b)),
    }
}

/// Erase a kernel [`Level`] to a spec `Level` term for `const` universe
/// arguments (trust edge 2): structural on `zero`/`succ`/`max`/`imax`,
/// `param`→`Level.zero`.
#[must_use]
pub fn erase_level_to_spec(l: &Level) -> SpecLevel {
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

/// Translate a kernel [`Expr`] into the spec `KExpr` vocabulary, or report the
/// first unrepresentable node (trust edge 3). `MData` is unwrapped
/// transparently (the kernel type checker treats it as transparent).
///
/// # Errors
/// Returns the human-readable node description that has no `KExpr` image.
pub fn reflect_expr(e: &Expr) -> Result<SpecExpr, String> {
    match e.kind() {
        ExprKind::BVar(i) => Ok(SpecExpr::BVar(*i)),
        ExprKind::Sort(l) => Ok(SpecExpr::Sort(erase_level_to_nat(l))),
        ExprKind::Const(n, ls) => Ok(SpecExpr::Const(
            n.to_string(),
            ls.iter().map(erase_level_to_spec).collect(),
        )),
        ExprKind::App(f, a) => Ok(SpecExpr::App(
            Box::new(reflect_expr(f)?),
            Box::new(reflect_expr(a)?),
        )),
        ExprKind::Lam(_, ty, b) => Ok(SpecExpr::Lam(
            Box::new(reflect_expr(ty)?),
            Box::new(reflect_expr(b)?),
        )),
        ExprKind::Pi(_, ty, b) => Ok(SpecExpr::Pi(
            Box::new(reflect_expr(ty)?),
            Box::new(reflect_expr(b)?),
        )),
        ExprKind::MData(_, inner) => reflect_expr(inner),
        ExprKind::Let(_, ty, val, body, _) => Ok(SpecExpr::Let_(
            Box::new(reflect_expr(ty)?),
            Box::new(reflect_expr(val)?),
            Box::new(reflect_expr(body)?),
        )),
        ExprKind::Lit(_) => Err("literal node (literals outside the RecEnv model)".to_string()),
        ExprKind::Proj(..) => {
            Err("proj node (struct projection/eta outside the RecEnv model)".to_string())
        }
        ExprKind::FVar(_) => Err("free variable (open term; no KExpr image)".to_string()),
        other => Err(format!("{other:?}-headed node (no KExpr image)")),
    }
}

/// Reflect the foundation core of `env` (see module docs). Deterministic:
/// allowlist order for items, frequency-then-lexicographic interning order.
#[must_use]
pub fn reflect_foundation_core(env: &Environment) -> Reflection {
    let mut recs: Vec<ReflectedRec> = Vec::new();
    let mut defs: Vec<ReflectedDef> = Vec::new();
    let mut skips: Vec<SkipEntry> = vec![
        SkipEntry {
            item: "(model gap) Quot".to_string(),
            reason: "quotient primitives (Quot.mk/lift/ind reduction) are a kernel-native rule \
                     family, not RecursorVal rules; outside the RecEnv model"
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
                     reduction; outside the RecEnv model"
                .to_string(),
        },
        SkipEntry {
            item: "(model gap) literals".to_string(),
            reason: "KExpr has a literal node, but Nat/String literal constructor-normalization \
                     is kernel-native and is not represented by this RecEnv snapshot"
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
        match reflect_recursor(rv) {
            Ok(rec) => {
                if rec.is_k {
                    skips.push(SkipEntry {
                        item: format!("{rec_name} (K-extension)"),
                        reason: "is_k recursor: syntactic rules ARE reflected, but the K-like \
                                 (proof-irrelevant) reduction extension is kernel-native and \
                                 outside the RecEnv model"
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
        let Some(value) = ci.value.as_ref() else {
            skips.push(SkipEntry {
                item: (*def).to_string(),
                reason: "constant has no value (axiom/opaque); nothing to unfold".to_string(),
            });
            continue;
        };
        match reflect_expr(value) {
            Ok(v) => defs.push(ReflectedDef {
                name: (*def).to_string(),
                is_reducible: ci.is_reducible,
                value: v,
            }),
            Err(reason) => skips.push(SkipEntry {
                item: (*def).to_string(),
                reason: format!("value unrepresentable: {reason}"),
            }),
        }
    }

    // DELTA-CLOSURE HONESTY: every value-ful kernel constant referenced by a
    // reflected rhs/value but NOT itself reflected into the DefEnv is
    // delta-STUCK in the reflected env — ledger it so allowlist drift is
    // visible (with the current allowlist this section is empty).
    let mut referenced: BTreeMap<String, u64> = BTreeMap::new();
    for rec in &recs {
        for rule in &rec.rules {
            count_consts(&rule.rhs, &mut referenced);
        }
    }
    for def in &defs {
        count_consts(&def.value, &mut referenced);
    }
    for name in referenced.keys() {
        let is_reflected_def = defs.iter().any(|d| &d.name == name);
        let is_valueful_const = env
            .get_const(&Name::from_string(name))
            .is_some_and(|ci| ci.value.is_some());
        if is_valueful_const && !is_reflected_def {
            skips.push(SkipEntry {
                item: name.clone(),
                reason: "value-ful definition referenced by a reflected rhs/value but not in \
                         the DefEnv allowlist: delta-stuck in the reflected env"
                    .to_string(),
            });
        }
    }

    let interning = build_interning(&recs, &defs);
    Reflection {
        recs,
        defs,
        interning,
        skips,
    }
}

/// Reflect one kernel [`RecursorVal`]; errors are skip reasons.
fn reflect_recursor(rv: &RecursorVal) -> Result<ReflectedRec, String> {
    if rv.arg_order != RecursorArgOrder::MajorAfterMinors {
        return Err(format!(
            "arg order {:?}: iota_reduct models only the MajorAfterMinors layout",
            rv.arg_order
        ));
    }
    let mut rules = Vec::with_capacity(rv.rules.len());
    for rule in &rv.rules {
        let rhs = reflect_expr(&rule.rhs).map_err(|reason| {
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
/// consts inside terms) and assign unary tags by (count desc, name asc) so
/// the hottest names get the shortest `Nat.succ` chains. Injective by
/// construction (one tag per distinct string).
fn build_interning(recs: &[ReflectedRec], defs: &[ReflectedDef]) -> Vec<(String, u64)> {
    let mut counts: BTreeMap<String, u64> = BTreeMap::new();
    for rec in recs {
        bump(&rec.name, &mut counts);
        for rule in &rec.rules {
            bump(&rule.ctor, &mut counts);
            count_consts(&rule.rhs, &mut counts);
        }
    }
    for def in defs {
        bump(&def.name, &mut counts);
        count_consts(&def.value, &mut counts);
    }
    let mut by_freq: Vec<(String, u64)> = counts.into_iter().collect();
    by_freq.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    by_freq
        .into_iter()
        .enumerate()
        .map(|(tag, (name, _count))| (name, tag as u64))
        .collect()
}

fn bump(name: &str, counts: &mut BTreeMap<String, u64>) {
    *counts.entry(name.to_string()).or_insert(0) += 1;
}

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
    }
}

fn max_nat_in_expr(e: &SpecExpr) -> u64 {
    match e {
        SpecExpr::Sort(n) => *n,
        SpecExpr::BVar(i) => u64::from(*i),
        SpecExpr::Const(..) => 0,
        SpecExpr::App(a, b) | SpecExpr::Lam(a, b) | SpecExpr::Pi(a, b) => {
            max_nat_in_expr(a).max(max_nat_in_expr(b))
        }
        SpecExpr::Let_(a, b, c) => max_nat_in_expr(a)
            .max(max_nat_in_expr(b))
            .max(max_nat_in_expr(c)),
    }
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
pub fn nat_atom(n: u64) -> String {
    format!("kcre_nat_{n}")
}

/// Nat-shaped spec-`Level` literal for a level-erased sort depth `n`
/// (`Level.zero` / `(Level.succ ...)`). Since the levels-promotion B2 flip
/// (`KExpr.sort : Level`), the reflected sort argument must be a `Level`, not a
/// `Nat`. This keeps the SAME level-collapse semantics as [`erase_level_to_nat`]
/// (param/imax already folded to a height) but re-encodes that height as the
/// unary spec `Level` `Level.succ^n Level.zero`. Sort depths are tiny (0/1 in
/// the foundation core), so inlining stays well under the parser depth guard.
/// The faithful `param`/`imax`-preserving reflection remains B5.
#[must_use]
pub fn render_level_of_nat(n: u64) -> String {
    let mut s = String::from("Level.zero");
    for _ in 0..n {
        s = format!("(Level.succ {s})");
    }
    s
}

impl Reflection {
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

        let mut required_names = std::collections::BTreeSet::new();
        for rec in &self.recs {
            required_names.insert(rec.name.clone());
            for rule in &rec.rules {
                required_names.insert(rule.ctor.clone());
                let mut referenced = BTreeMap::new();
                count_consts(&rule.rhs, &mut referenced);
                required_names.extend(referenced.into_keys());
            }
        }
        for def in &self.defs {
            required_names.insert(def.name.clone());
            let mut referenced = BTreeMap::new();
            count_consts(&def.value, &mut referenced);
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
        if !nat_rec.rules.iter().any(|rule| rule.ctor == "Nat.zero") {
            return Err(ReflectError::InvalidReflection {
                detail: "required Nat.rec/Nat.zero non-vacuity rule was not reflected".to_string(),
            });
        }
        if !self
            .defs
            .iter()
            .any(|def| def.name == "def_env_lift_closed_b")
        {
            return Err(ReflectError::InvalidReflection {
                detail: "required delta witness definition def_env_lift_closed_b was not reflected"
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
    /// RecMeta counts, rule field counts, bvar indices, sort depths) — the
    /// size of the `kcre_nat_*` helper pool.
    #[must_use]
    pub fn max_nat_used(&self) -> u64 {
        let mut mx = self.interning.iter().map(|(_, t)| *t).max().unwrap_or(0);
        for rec in &self.recs {
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
            mx = mx.max(max_nat_in_expr(&def.value));
        }
        mx
    }

    fn render_level(l: &SpecLevel) -> String {
        match l {
            SpecLevel::Zero => "Level.zero".to_string(),
            SpecLevel::Succ(x) => format!("(Level.succ {})", Self::render_level(x)),
            SpecLevel::Max(a, b) => format!(
                "(Level.max {} {})",
                Self::render_level(a),
                Self::render_level(b)
            ),
            SpecLevel::IMax(a, b) => format!(
                "(Level.imax {} {})",
                Self::render_level(a),
                Self::render_level(b)
            ),
        }
    }

    fn render_levels(&self, ls: &[SpecLevel]) -> String {
        let mut out = String::from("(ListType.nil Level)");
        for l in ls.iter().rev() {
            out = format!("(ListType.cons Level {} {})", Self::render_level(l), out);
        }
        out
    }

    fn render_expr(&self, e: &SpecExpr, out: &mut String) -> Result<(), ReflectError> {
        match e {
            SpecExpr::Sort(n) => {
                let _ = write!(out, "(KExpr.sort {})", render_level_of_nat(*n));
            }
            SpecExpr::BVar(i) => {
                let _ = write!(out, "(KExpr.bvar {})", nat_atom(u64::from(*i)));
            }
            SpecExpr::Const(n, ls) => {
                let _ = write!(
                    out,
                    "(KExpr.const {} {})",
                    self.render_name(n)?,
                    self.render_levels(ls)
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
    fn nat_zero_witness(&self) -> Result<(SpecExpr, SpecExpr), ReflectError> {
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
            .map(|_| SpecExpr::Sort(0))
            .collect::<Vec<_>>();
        let indices = (0..nat_rec.num_indices)
            .map(|_| SpecExpr::Sort(0))
            .collect::<Vec<_>>();
        let mut redex_args = prefix.clone();
        redex_args.extend(indices);
        redex_args.push(SpecExpr::Const("Nat.zero".to_string(), Vec::new()));
        let redex = Self::apply_expr_spine(
            SpecExpr::Const("Nat.rec".to_string(), Vec::new()),
            redex_args,
        );

        // Nat.zero contributes no constructor fields and this canonical
        // witness has no over-application, so the modeled reduct is precisely
        // the reflected rule RHS applied to the metadata-derived prefix.
        let reduct = Self::apply_expr_spine(nat_zero_rule.rhs.clone(), prefix);
        Ok((redex, reduct))
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
            let meta = format!(
                "(RecMeta.mk {} {} {} {} {})",
                nat_atom(u64::from(rec.num_params)),
                nat_atom(u64::from(rec.num_motives)),
                nat_atom(u64::from(rec.num_minors)),
                nat_atom(u64::from(rec.num_indices)),
                if rec.major_after_minors {
                    "Bool.true"
                } else {
                    "Bool.false"
                }
            );
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
            let mut value = String::new();
            self.render_expr(&def.value, &mut value)?;
            def_env = format!(
                "(DefEnv.addDef {} {} {})",
                def_env,
                self.render_name(&def.name)?,
                value
            );
        }
        Ok(format!("RedEnv.mk {rec_env} {def_env}"))
    }

    /// Render the full generated DEF SCRIPT: one Lean-syntax `def` per line —
    /// the `kcre_nat_*` unary pool (depth 2 each), the `kcre_name_*` interned
    /// name constants (depth 1 each, trust edge 1), generated semantic witness
    /// helpers for the live Nat-zero iota rule and one real delta entry, then
    /// the `kernel_core_red_env` term itself. Registration replays the lines in
    /// order; every line is a value-ful `def` (census-neutral).
    ///
    /// This script shape exists because of a MEASURED parser constraint: the
    /// naive fully-inlined literal nests to paren depth 163, past the
    /// parser's `MAX_EXPR_DEPTH = 128` DoS guard; with the helper atoms the
    /// deepest line is paren depth ~64.
    /// # Errors
    /// Returns [`ReflectError::InvalidReflection`] unless name interning is
    /// injective, contiguous, and complete and both generated non-vacuity
    /// witnesses are present.
    pub fn def_script(&self) -> Result<String, ReflectError> {
        self.validate_for_emission()?;
        let (nat_zero_redex, nat_zero_reduct) = self.nat_zero_witness()?;
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
        let mut redex = String::new();
        self.render_expr(&nat_zero_redex, &mut redex)?;
        let _ = writeln!(out, "def kcre_witness_nat_zero_redex : KExpr := {redex}");
        let mut reduct = String::new();
        self.render_expr(&nat_zero_reduct, &mut reduct)?;
        let _ = writeln!(out, "def kcre_witness_nat_zero_reduct : KExpr := {reduct}");
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
            "Generated by `cargo run --release -p clean-verify --bin red_env_reflect`."
        );
        let _ = writeln!(
            out,
            "Trust edges: (1) injective Nat-tag name interning; (2) level erasure \
             (sort levels -> collapsed Level.succ^n Level.zero height, const levels -> \
             param-free spec Level); (3) this \
             skip ledger. See `clean_verify::red_env_reflect` module docs."
        );
        let _ = writeln!(out);
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
             kcre_nat_*/kcre_name_* atom leaves ({} nat helpers, {} name helpers); the \
             naive fully-inlined literal exceeds the parser MAX_EXPR_DEPTH=128 guard.",
            max_paren_depth(&value_term),
            self.max_nat_used() + 1,
            self.interning.len()
        );
        let _ = writeln!(out);
        for rec in &self.recs {
            let _ = writeln!(
                out,
                "- rec `{}`: params={} motives={} minors={} indices={} rules={}{}",
                rec.name,
                rec.num_params,
                rec.num_motives,
                rec.num_minors,
                rec.num_indices,
                rec.rules.len(),
                if rec.is_k { " [is_k]" } else { "" }
            );
        }
        for def in &self.defs {
            let _ = writeln!(
                out,
                "- def `{}`{}",
                def.name,
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
            SpecExpr::Sort(n) => {
                // Nat-shaped spec-`Level` literal `Level.succ^n Level.zero`
                // (levels-promotion B2: `KExpr.sort : Level`).
                let mut lvl = Expr::const_str("Level.zero");
                for _ in 0..*n {
                    lvl = Expr::app(Expr::const_str("Level.succ"), lvl);
                }
                Expr::app(Expr::const_str("KExpr.sort"), lvl)
            }
            SpecExpr::BVar(i) => Expr::app(
                Expr::const_str("KExpr.bvar"),
                Expr::const_str(&nat_atom(u64::from(*i))),
            ),
            SpecExpr::Const(n, ls) => Expr::apps(
                Expr::const_str("KExpr.const"),
                [
                    Expr::const_str(&self.render_name(n)?),
                    Self::levels_term(ls),
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
        })
    }

    fn level_term(l: &SpecLevel) -> Expr {
        match l {
            SpecLevel::Zero => Expr::const_str("Level.zero"),
            SpecLevel::Succ(x) => Expr::app(Expr::const_str("Level.succ"), Self::level_term(x)),
            SpecLevel::Max(a, b) => Expr::apps(
                Expr::const_str("Level.max"),
                [Self::level_term(a), Self::level_term(b)],
            ),
            SpecLevel::IMax(a, b) => Expr::apps(
                Expr::const_str("Level.imax"),
                [Self::level_term(a), Self::level_term(b)],
            ),
        }
    }

    fn levels_term(ls: &[SpecLevel]) -> Expr {
        let mut out = Expr::app(Expr::const_str("ListType.nil"), Expr::const_str("Level"));
        for l in ls.iter().rev() {
            out = Expr::apps(
                Expr::const_str("ListType.cons"),
                [Expr::const_str("Level"), Self::level_term(l), out],
            );
        }
        out
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
    let fresh = reflect_foundation_core(env);
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
mod tests {
    use super::*;

    #[test]
    fn test_erase_level_to_nat_collapses_param_and_imax() {
        let p = Level::Param(Name::from_string("u"));
        assert_eq!(erase_level_to_nat(&p), 0, "param erases to 0");
        let s = Level::succ(Level::Zero);
        assert_eq!(erase_level_to_nat(&s), 1, "succ adds 1");
        let m = Level::imax(s.clone(), Level::Zero);
        assert_eq!(erase_level_to_nat(&m), 1, "imax erases to max");
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
        let r = Reflection {
            recs,
            defs: vec![],
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
            value: SpecExpr::Const("Witness.delta".to_string(), vec![]),
        }];
        let reflection = Reflection {
            interning: build_interning(&recs, &defs),
            recs,
            defs,
            skips: vec![],
        };
        let (redex, reduct) = reflection
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

        let (redex_head, redex_args) = spine(&redex);
        assert_eq!(redex_head, &SpecExpr::Const("Nat.rec".to_string(), vec![]));
        assert_eq!(
            redex_args.len(),
            4,
            "params + motives + minors + indices + major"
        );
        assert_eq!(
            redex_args.last().copied(),
            Some(&SpecExpr::Const("Nat.zero".to_string(), vec![]))
        );

        let (reduct_head, reduct_args) = spine(&reduct);
        assert_eq!(
            reduct_head,
            &SpecExpr::Const("Witness.rhs".to_string(), vec![])
        );
        assert_eq!(
            reduct_args.len(),
            2,
            "rule RHS receives params + motives + minors only"
        );
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
}
