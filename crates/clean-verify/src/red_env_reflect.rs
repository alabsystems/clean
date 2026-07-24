// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 2 (the_red_env discharge program): the REFLECTION GENERATOR.
//!
//! Mechanically reflects the FOUNDATION CORE of the real kernel environment —
//! the environment `Specification::new()` actually builds — into a `RedEnv`
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
//! 2. **Level erasure**. Spec `KExpr.sort` carries a `Nat` and spec `Level`
//!    has no `param` constructor, so the reflection is LEVEL-ERASED:
//!    - `Sort l` erases to `KExpr.sort <nat>` via [`erase_level_to_nat`]
//!      (`zero`→0, `succ`→+1, `max`/`imax`→max of the erasures — `imax`'s
//!      "0 if right is 0" collapse is dropped, `param`→0);
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
//!    `Expr` node with no `KExpr` image (`let`/`proj`/`lit`/`mdata`-opaque
//!    payloads, fvars, mode extensions). A recursor/definition containing an
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
//! Consumed by the `red_env_reflect` bin (emits the generated artifacts under
//! `spec/core_spec/generated/`) and by the fidelity-gate tests
//! (`tests/kernel_core_red_env_fidelity.rs`).

use std::collections::BTreeMap;
use std::fmt::Write as _;

use clean_kernel::{Environment, Expr, ExprKind, Level, Name, RecursorArgOrder, RecursorVal};

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
    /// `KExpr.sort <nat>` (level-erased image of `Sort l`).
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
    /// dropped; the genuine let constructor of the promoted 7-ctor fragment).
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

/// Erase a kernel [`Level`] to the `Nat` payload of `KExpr.sort`
/// (trust edge 2): `zero`→0, `succ`→+1, `max`/`imax`→max, `param`→0.
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
    #[must_use]
    pub fn render_name(&self, name: &str) -> String {
        let tag = self.tag_of(name).unwrap_or(u64::MAX);
        format!("kcre_name_{tag}")
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

    fn render_expr(&self, e: &SpecExpr, out: &mut String) {
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
                    self.render_name(n),
                    self.render_levels(ls)
                );
            }
            SpecExpr::App(f, a) => {
                out.push_str("(KExpr.app ");
                self.render_expr(f, out);
                out.push(' ');
                self.render_expr(a, out);
                out.push(')');
            }
            SpecExpr::Lam(t, b) => {
                out.push_str("(KExpr.lam ");
                self.render_expr(t, out);
                out.push(' ');
                self.render_expr(b, out);
                out.push(')');
            }
            SpecExpr::Pi(t, b) => {
                out.push_str("(KExpr.pi ");
                self.render_expr(t, out);
                out.push(' ');
                self.render_expr(b, out);
                out.push(')');
            }
            SpecExpr::Let_(t, v, b) => {
                out.push_str("(KExpr.let_ ");
                self.render_expr(t, out);
                out.push(' ');
                self.render_expr(v, out);
                out.push(' ');
                self.render_expr(b, out);
                out.push(')');
            }
        }
    }

    /// Render the `kernel_core_red_env` value TERM (a single-line Lean-syntax
    /// `RedEnv` term, `the_red_env.rs`-style, with `kcre_nat_*`/`kcre_name_*`
    /// atom leaves so its nesting stays under the parser's
    /// `MAX_EXPR_DEPTH = 128` guard).
    #[must_use]
    pub fn value_term(&self) -> String {
        let mut rec_env = String::from("RecEnv.empty");
        for rec in &self.recs {
            let mut rules = String::from("RecRules.nil");
            for rule in rec.rules.iter().rev() {
                let mut rhs = String::new();
                self.render_expr(&rule.rhs, &mut rhs);
                rules = format!(
                    "(RecRules.cons (RecRule.mk {} {} {}) {})",
                    self.render_name(&rule.ctor),
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
                self.render_name(&rec.name),
                meta,
                rules
            );
        }
        let mut def_env = String::from("DefEnv.empty");
        for def in &self.defs {
            let mut value = String::new();
            self.render_expr(&def.value, &mut value);
            def_env = format!(
                "(DefEnv.addDef {} {} {})",
                def_env,
                self.render_name(&def.name),
                value
            );
        }
        format!("RedEnv.mk {rec_env} {def_env}")
    }

    /// Render the full generated DEF SCRIPT: one Lean-syntax `def` per line —
    /// the `kcre_nat_*` unary pool (depth 2 each), the `kcre_name_*` interned
    /// name constants (depth 1 each, trust edge 1), then the
    /// `kernel_core_red_env` term itself. Registration replays the lines in
    /// order; every line is a value-ful `def` (census-neutral).
    ///
    /// This script shape exists because of a MEASURED parser constraint: the
    /// naive fully-inlined literal nests to paren depth 163, past the
    /// parser's `MAX_EXPR_DEPTH = 128` DoS guard; with the helper atoms the
    /// deepest line is paren depth ~64.
    #[must_use]
    pub fn def_script(&self) -> String {
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
        let _ = writeln!(
            out,
            "def kernel_core_red_env : RedEnv := {}",
            self.value_term()
        );
        out
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
    #[must_use]
    pub fn skip_ledger_md(&self) -> String {
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
             (sorts -> Nat depth, const levels -> param-free spec Level); (3) this \
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
            max_paren_depth(&self.value_term()),
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
        out
    }

    /// Build the kernel `Expr` of the spec `KExpr` TERM for `e` — the same
    /// term the def script renders (atom leaves `kcre_nat_*`/`kcre_name_*`),
    /// as a first-class kernel expression. Used by the one-rfl cost probes to
    /// whnf-force full per-element checker work (`nat_eqb (bvar_ceiling rhs)
    /// 0` traverses the whole rhs), which the Bool.and short-circuit of the
    /// env-level fold otherwise hides.
    pub fn kexpr_term(&self, e: &SpecExpr) -> Expr {
        match e {
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
                [Expr::const_str(&self.render_name(n)), Self::levels_term(ls)],
            ),
            SpecExpr::App(f, a) => Expr::apps(
                Expr::const_str("KExpr.app"),
                [self.kexpr_term(f), self.kexpr_term(a)],
            ),
            SpecExpr::Lam(t, b) => Expr::apps(
                Expr::const_str("KExpr.lam"),
                [self.kexpr_term(t), self.kexpr_term(b)],
            ),
            SpecExpr::Pi(t, b) => Expr::apps(
                Expr::const_str("KExpr.pi"),
                [self.kexpr_term(t), self.kexpr_term(b)],
            ),
            SpecExpr::Let_(t, v, b) => Expr::apps(
                Expr::const_str("KExpr.let_"),
                [self.kexpr_term(t), self.kexpr_term(v), self.kexpr_term(b)],
            ),
        }
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
/// Returns [`ReflectError::Drift`] naming the first drifted artifact and the
/// first divergent line/region.
pub fn fidelity_check(
    env: &Environment,
    committed_script: &str,
    committed_interning: &str,
    committed_skips: &str,
) -> Result<Reflection, ReflectError> {
    let fresh = reflect_foundation_core(env);
    compare_artifact("def script", &fresh.def_script(), committed_script)?;
    compare_artifact(
        "interning table",
        &fresh.interning_tsv(),
        committed_interning,
    )?;
    compare_artifact("skip ledger", &fresh.skip_ledger_md(), committed_skips)?;
    Ok(fresh)
}

fn compare_artifact(
    artifact: &'static str,
    fresh: &str,
    committed: &str,
) -> Result<(), ReflectError> {
    let fresh_t = fresh.trim();
    let committed_t = committed.trim();
    if fresh_t == committed_t {
        return Ok(());
    }
    // Locate the first divergent byte for an actionable message.
    let pos = fresh_t
        .bytes()
        .zip(committed_t.bytes())
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| fresh_t.len().min(committed_t.len()));
    let lo = pos.saturating_sub(60);
    let f_end = (pos + 60).min(fresh_t.len());
    let c_end = (pos + 60).min(committed_t.len());
    Err(ReflectError::Drift {
        artifact,
        detail: format!(
            "first divergence at byte {pos}: regenerated ...{}... vs committed ...{}... \
             (lengths {} vs {}); re-run the red_env_reflect bin and review",
            fresh_t.get(lo..f_end).unwrap_or(""),
            committed_t.get(lo..c_end).unwrap_or(""),
            fresh_t.len(),
            committed_t.len()
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_erase_level_to_nat_collapses_param_and_imax() {
        use std::sync::Arc;
        let p = Level::Param(Name::from_string("u"));
        assert_eq!(erase_level_to_nat(&p), 0, "param erases to 0");
        let s = Level::Succ(Arc::new(Level::Zero));
        assert_eq!(erase_level_to_nat(&s), 1, "succ adds 1");
        let m = Level::IMax(Arc::new(s.clone()), Arc::new(Level::Zero));
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
    }
}
