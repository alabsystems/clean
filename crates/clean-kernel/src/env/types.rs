// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core environment types.
//!
//! This module contains the fundamental types used by the Environment:
//! - `TransparencyMode` - controls definition unfolding behavior
//! - `Reducibility` - reducibility level for definitions
//! - `KernelClassInfo` - type class metadata
//! - `KernelInstanceInfo` - instance metadata
//! - `ConstantInfo` - constant declaration info
//! - `Declaration` - declaration variants
//! - `EnvError` - environment error types
//!
//! Extracted from `env/mod.rs` for organization and compile time improvements.
//! See issue #1161.

use crate::expr::Expr;
use crate::inductive::InductiveError;
use crate::name::Name;
use serde::{Deserialize, Serialize};

/// Transparency mode for definition unfolding during type checking
///
/// Controls how aggressively definitions are unfolded during type checking,
/// unification, and rule matching.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum TransparencyMode {
    /// Only unfold `@[reducible]` definitions (most conservative)
    Reducible,
    /// Reducible + typeclass instances (for instance resolution)
    Instances,
    /// Most definitions except `@[irreducible]` (default)
    #[default]
    Default,
    /// Everything including `@[irreducible]` (maximum unfolding)
    All,
}

/// Reducibility hints for a definition, matching Lean 4's `ReducibilityHints`.
///
/// Determines unfold ordering during delta reduction in definitional equality.
/// The `height` field on `Regular` encodes definition depth: definitions that
/// reference other definitions get higher heights, ensuring the "outer"
/// definition is unfolded first.
///
/// Reference: Lean 4 `src/kernel/declaration.h:35-47`, `declaration.cpp:24-49`
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum Reducibility {
    /// Always unfoldable — abbreviations/`@[reducible]` (Lean 4: `Abbreviation`)
    #[default]
    Reducible,
    /// Normal definitions with a computed height (Lean 4: `Regular(height)`)
    ///
    /// Height = 1 + max(height of all constants referenced in definition value).
    /// Higher height means the definition is unfolded first in delta reduction.
    Regular(u32),
    /// Only unfoldable in All mode (`@[irreducible]`)
    Irreducible,
    /// Never unfoldable (theorems/opaque declarations) (Lean 4: `Opaque`)
    Opaque,
}

impl Reducibility {
    /// Backwards-compatible alias: `Semireducible` is `Regular(0)`.
    pub const SEMIREDUCIBLE: Reducibility = Reducibility::Regular(0);

    /// Get the definition height (0 for non-Regular variants).
    pub fn height(&self) -> u32 {
        match self {
            Reducibility::Regular(h) => *h,
            _ => 0,
        }
    }

    /// Check if this is a `Regular` hint (not abbreviation/irreducible/opaque).
    /// Used in same-head optimization: Lean 4 only tries argument-wise comparison
    /// when both hints are Regular (type_checker.cpp:922).
    pub fn is_regular(&self) -> bool {
        matches!(self, Reducibility::Regular(_))
    }

    /// Compare two reducibility hints for delta reduction ordering.
    ///
    /// Returns:
    /// - `Ordering::Less` (-1): unfold self first (self is "more reducible")
    /// - `Ordering::Greater` (+1): unfold other first
    /// - `Ordering::Equal` (0): unfold both
    ///
    /// Ordering: Reducible (abbrev) > Regular (by height, taller first) > Opaque
    ///
    /// Reference: Lean 4 `declaration.cpp:24-49`
    pub fn compare(&self, other: &Reducibility) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self.kind_rank(), other.kind_rank()) {
            (a, b) if a == b => {
                // Same kind
                match (self, other) {
                    (Reducibility::Regular(h1), Reducibility::Regular(h2)) => {
                        // Higher height = unfold first = Less
                        h2.cmp(h1) // reversed: h1 > h2 => Less (unfold h1)
                    }
                    _ => Ordering::Equal, // both Reducible, both Irreducible, or both Opaque
                }
            }
            (a, b) => a.cmp(&b), // Lower rank = more reducible = Less (unfold first)
        }
    }

    /// Rank for ordering: lower = more reducible = unfold first.
    /// Reducible(0) > Regular(1) > Irreducible(2) > Opaque(3)
    fn kind_rank(&self) -> u8 {
        match self {
            Reducibility::Reducible => 0,
            Reducibility::Regular(_) => 1,
            Reducibility::Irreducible => 2,
            Reducibility::Opaque => 3,
        }
    }

    /// Check if this definition should be unfolded at the given transparency
    pub fn should_unfold(&self, mode: TransparencyMode) -> bool {
        match (self, mode) {
            (Reducibility::Reducible, _) => true,
            (Reducibility::Regular(_), TransparencyMode::Reducible) => false,
            (Reducibility::Regular(_), _) => true,
            (Reducibility::Irreducible, TransparencyMode::All) => true,
            (Reducibility::Irreducible, _) => false,
            (Reducibility::Opaque, _) => false,
        }
    }
}

/// Kernel-side type class information (minimal, no elaborator dependencies)
///
/// This stores information about type classes defined via `add_inductive()`.
/// The elaborator's InstanceTable can be populated from this data.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KernelClassInfo {
    /// Name of the type class (e.g., `HAdd`)
    pub name: Name,
    /// Number of parameters the class takes
    pub num_params: usize,
    /// Indices of "output parameters" that can be inferred from other params
    pub out_params: Vec<usize>,
    /// Indices of "semi-output parameters"
    pub semi_out_params: Vec<usize>,
}

/// Kernel-side instance information
///
/// Stores information about instances registered via kernel init functions.
/// The elaborator's InstanceTable can be populated from this data.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KernelInstanceInfo {
    /// Name of the instance definition (e.g., `instHAddNat`)
    pub name: Name,
    /// Name of the class this instance implements (e.g., `HAdd`)
    pub class_name: Name,
    /// Priority (higher = tried first)
    pub priority: u32,
    /// Instance type with correct binder info (Fix #443).
    /// For toParent instances like CommRing.toRing, the projection constant has
    /// `Default` binders, but the instance needs `Implicit`/`InstImplicit` binders
    /// for proper instance resolution. This field stores the canonical instance type.
    #[serde(default)]
    pub type_: Option<Expr>,
    /// Instance value with correct binder info (Fix #443).
    /// See `type_` for explanation.
    #[serde(default)]
    pub value: Option<Expr>,
}

/// Clean's fabricated priority for an instance whose real priority is UNKNOWN.
///
/// **This is not Lean's default.** Lean's default for an unannotated `instance`
/// is [`LEAN_DEFAULT_INSTANCE_PRIORITY`] (1000); 100 is Lean's `low`. The value
/// here is deliberately low so that a guess ranks BELOW anything whose real
/// priority is known — in particular below every `InstanceEntry` the `.olean`
/// import decodes (`clean-olean`'s shape heuristic backfills at this value on
/// purpose, so a real registration always outranks a fabricated one).
///
/// A hand-registered prelude instance that MIRRORS A REAL LEAN INSTANCE must
/// therefore NOT use this constant: its priority is known, and it is whatever
/// the shipped `.olean` serializes. Using 100 there is the defect
/// `data/prelude_instance_priority_census.json` measures and
/// `scripts/check_prelude_instance_priority_ratchet.py` ratchets shut.
pub const DEFAULT_INSTANCE_PRIORITY: u32 = 100;

/// Lean 4's priority for an `instance` declared with no `(priority := …)`.
///
/// Ground truth is the `u64` Lean serializes into `Lean.Meta.instanceExtension`
/// in every shipped `.olean`, **not** any attribute in Lean's source. Reading
/// the number off a source attribute is what produced three separate defects:
/// `@[default_instance 100] instance instOfNatNat …` was read as priority 100
/// (`8d80c9d98`), but `@[default_instance]` is a DIFFERENT TABLE — it orders
/// literal-type DEFAULTING, not `synthInstance` candidate selection — and the
/// `instance` itself is unannotated, so its real priority is this 1000.
pub const LEAN_DEFAULT_INSTANCE_PRIORITY: u32 = 1000;

// ============================================================================
// Attribute Registry Types (#1133)
// ============================================================================

/// Simp lemma priority level
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
pub enum SimpPriority {
    /// Default priority (1000)
    #[default]
    Default,
    /// Custom priority value
    Custom(u32),
}

impl SimpPriority {
    /// Get the numeric priority value
    pub fn value(&self) -> u32 {
        match self {
            SimpPriority::Default => 1000,
            SimpPriority::Custom(p) => *p,
        }
    }
}

/// Information about a registered simp lemma
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SimpLemmaInfo {
    /// Name of the lemma
    pub name: Name,
    /// Priority (higher = tried first)
    pub priority: SimpPriority,
}

/// The kind of constant declaration, preserving the Lean 4 distinction between
/// Definition, Theorem, Opaque, and Axiom.
///
/// This is needed because both Theorem and Opaque map to `Reducibility::Opaque`,
/// so reducibility alone cannot distinguish them during round-trips through
/// `ConstantInfo` (e.g., serialization + `loadEnvironment` merge).
///
/// Reference: Lean 4 `src/kernel/declaration.h` — `DefinitionVal`, `TheoremVal`,
/// `OpaqueVal`, `AxiomVal` are distinct types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum ConstantKind {
    /// Normal definition with a computable value
    #[default]
    Definition,
    /// Theorem — proof-irrelevant, never compared by value
    Theorem,
    /// Opaque constant — has a hidden value not exposed during reduction
    Opaque,
    /// Axiom — no value, taken on faith
    Axiom,
}

/// Information about a constant
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConstantInfo {
    /// Name of the constant
    pub name: Name,
    /// Universe parameters
    pub level_params: Vec<Name>,
    /// Type of the constant
    pub type_: Expr,
    /// Value (None for axioms/opaque)
    pub value: Option<Expr>,
    /// Whether this can be unfolded during type checking.
    /// Primary serde input; drives `reducibility` in constructors. Prefer
    /// constructors over direct field mutation so the two stay in sync.
    pub is_reducible: bool,
    /// Full reducibility level. Derived from `is_reducible` in `new()`;
    /// use `new_with_reducibility()` for explicit control.
    #[serde(default)]
    pub reducibility: Reducibility,
    /// The kind of declaration (Definition, Theorem, Opaque, Axiom).
    /// Preserves the Lean 4 distinction that `reducibility` alone cannot encode.
    #[serde(default)]
    pub kind: ConstantKind,
}

impl ConstantInfo {
    /// Create a new constant with automatic reducibility derivation from is_reducible.
    /// Defaults to `ConstantKind::Definition`.
    /// REQUIRES: none (pure constructor)
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    #[must_use]
    pub fn new(
        name: Name,
        level_params: Vec<Name>,
        type_: Expr,
        value: Option<Expr>,
        is_reducible: bool,
    ) -> Self {
        Self {
            name,
            level_params,
            type_,
            value,
            reducibility: if is_reducible {
                Reducibility::Reducible
            } else {
                Reducibility::Regular(0)
            },
            is_reducible,
            kind: ConstantKind::Definition,
        }
    }

    /// Create a constant with explicit `Reducibility` and `ConstantKind`.
    /// Derives `is_reducible` from `reducibility` to keep fields consistent.
    #[must_use]
    pub fn new_with_reducibility(
        name: Name,
        level_params: Vec<Name>,
        type_: Expr,
        value: Option<Expr>,
        reducibility: Reducibility,
        kind: ConstantKind,
    ) -> Self {
        Self {
            name,
            level_params,
            type_,
            value,
            is_reducible: matches!(reducibility, Reducibility::Reducible),
            reducibility,
            kind,
        }
    }
}

/// Opaque data stored inside a persistent environment extension entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum EnvExtensionEntryData {
    /// Tagged scalar or null pointer value.
    Scalar(u64),
    /// Raw object bytes (includes header). Pointer relocation is not applied.
    Object(Vec<u8>),
}

/// A single persistent environment extension entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EnvExtensionEntry {
    /// Entry key name
    pub name: Name,
    /// Opaque entry payload
    pub data: EnvExtensionEntryData,
}

/// Persistent env extension state (Lean 4-style).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PersistentEnvExtensionState {
    /// Entries imported per module index.
    pub imported_entries: Vec<Vec<EnvExtensionEntry>>,
    /// Opaque extension state blob (unused for now).
    pub state: Vec<u8>,
}

/// A declaration to add to the environment
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Declaration {
    /// Definition with a value
    Definition {
        /// Fully qualified name
        name: Name,
        /// Universe level parameters
        level_params: Vec<Name>,
        /// Type of the definition
        type_: Expr,
        /// Defining value
        value: Expr,
        /// Whether the definition should be eagerly unfolded
        is_reducible: bool,
    },
    /// Axiom (type without value)
    Axiom {
        /// Fully qualified name
        name: Name,
        /// Universe level parameters
        level_params: Vec<Name>,
        /// Type of the axiom
        type_: Expr,
    },
    /// Theorem (like definition but proof-irrelevant)
    Theorem {
        /// Fully qualified name
        name: Name,
        /// Universe level parameters
        level_params: Vec<Name>,
        /// Type (proposition) of the theorem
        type_: Expr,
        /// Proof term
        value: Expr,
    },
    /// Opaque constant (has value but not unfolded)
    Opaque {
        /// Fully qualified name
        name: Name,
        /// Universe level parameters
        level_params: Vec<Name>,
        /// Type of the opaque constant
        type_: Expr,
        /// Hidden value (not exposed during reduction)
        value: Expr,
    },
}

/// Errors that can occur when manipulating the environment
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum EnvError {
    /// A declaration with this name already exists
    #[error("Duplicate declaration: {0}")]
    DuplicateName(Name),
    /// Error during inductive type processing
    #[error("Inductive type error: {0}")]
    Inductive(#[from] InductiveError),
    /// Referenced inductive type not found
    #[error("Unknown inductive: {0}")]
    UnknownInductive(Name),
    /// Type is not a structure (structures have exactly one constructor)
    #[error("Not a structure (expected exactly one constructor): {0}")]
    NotStructure(Name),
    /// Field count mismatch when registering structure fields
    #[error("Invalid number of fields for {struct_name}: expected {expected}, got {actual}")]
    InvalidFieldCount {
        /// Name of the structure type
        struct_name: Name,
        /// Expected number of fields
        expected: u32,
        /// Actual number of fields provided
        actual: u32,
    },
    /// Duplicate field name in structure definition
    #[error("Duplicate field name {field} in structure {struct_name}")]
    DuplicateFieldName {
        /// Name of the structure type
        struct_name: Name,
        /// Name of the duplicate field
        field: Name,
    },
    /// Declaration failed type checking
    #[error("Type check error in declaration {name}: {source}")]
    TypeCheckFailed {
        /// Name of the declaration that failed
        name: Name,
        /// The underlying type error
        source: crate::tc::TypeError,
    },
    /// Declaration type has duplicate universe level parameters
    #[error("Duplicate universe level parameter '{param}' in declaration {name}")]
    DuplicateLevelParam {
        /// Name of the declaration
        name: Name,
        /// The duplicate parameter name
        param: Name,
    },
    /// Theorem type does not live in Prop (Sort 0)
    #[error("Theorem {name}: type must be a Prop, but inferred sort is {sort:?}")]
    TheoremTypeNotProp {
        /// Name of the theorem
        name: Name,
        /// The sort that was inferred for the type
        sort: crate::level::Level,
    },
    /// Declaration contains free variables (FVar), which must not appear in the environment
    #[error("Declaration {name} contains free variables (fvar ids {fvars:?})")]
    ContainsFreeVar {
        /// Name of the declaration
        name: Name,
        /// The distinct FVar ids found (bounded sample, diagnostic only). The
        /// id range classifies the leak at a glance: elaborator-scope locals
        /// are minted low, tactic-created FVars sit at or above the tactic
        /// `fvar_base`.
        fvars: Vec<u64>,
    },
    /// Declaration contains metavariables (expression or universe level), which must not
    /// appear in the environment. Matches Lean 4's check_no_metavar.
    #[error("Declaration {name} contains metavariables")]
    ContainsMetavar {
        /// Name of the declaration
        name: Name,
    },
    /// Declaration references undefined universe level parameter
    #[error("Undefined universe level parameter '{param}' in declaration {name}")]
    UndefinedLevelParam {
        /// Name of the declaration
        name: Name,
        /// The undefined parameter name
        param: Name,
    },
    /// An initializer requires a declaration that has not been registered yet.
    #[error("{init} requires declaration {decl}")]
    MissingRequiredDeclaration {
        /// Initializer name enforcing the dependency.
        init: &'static str,
        /// Missing declaration name.
        decl: Name,
    },
    /// An idempotent initializer found an existing declaration under its
    /// owned name whose exact kind/type/value did not match the initializer's
    /// canonical declaration.
    #[error("initializer declaration conflict at {name}: {detail}")]
    InitializationConflict {
        /// Conflicting declaration name.
        name: Name,
        /// Exact mismatch summary.
        detail: String,
    },
    /// A required declaration exists but does not have the expected binder shape.
    #[error("{init} expected {decl} to have shape: {detail}")]
    InvalidDeclarationShape {
        /// Initializer validating the declaration shape.
        init: &'static str,
        /// Declaration whose structure was unexpected.
        decl: Name,
        /// Short description of the required shape.
        detail: &'static str,
    },
    /// Mode compatibility error (e.g., classical axioms in Cubical mode)
    #[error("Mode error: {0}")]
    Mode(#[from] crate::mode::ModeError),
    /// No generated overlay payload is available for this namespace.
    #[error("Unsupported generated namespace overlay: {namespace}")]
    UnsupportedGeneratedNamespace {
        /// Namespace prefix requested for generated overlay loading.
        namespace: String,
    },
    /// Inductive type's codomain is not a Sort expression.
    /// The fully-applied inductive type must return Sort(l) for some level l.
    #[error("Inductive type {name}: codomain is not a Sort after stripping {num_params} params")]
    InductiveCodomainNotSort {
        /// Name of the inductive type
        name: Name,
        /// Number of parameters stripped
        num_params: u32,
    },
    /// MASQUERADE proof-quality lint rejected a theorem at registration time.
    /// Fired only when `CLEAN_STRICT_PROOF_QUALITY=1` is set, per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Phase 4.
    #[error("MASQUERADE proof for {name}: {detail}")]
    MasqueradeProof {
        /// Name of the theorem whose proof term failed the lint.
        name: Name,
        /// Rendered findings summary from `ProofQualityError`.
        detail: String,
    },
    /// The `mm_axiom_only` proof-dropping fast path was reached WITHOUT the
    /// sanctioned two-pass sentinel established (see `MmAxiomOnlyGuard`). This
    /// fail-closes the "axiom-only" escape hatch: the flag alone is no longer
    /// sufficient to drop a theorem's proof value unchecked — the caller must be
    /// provably inside the Metamath two-pass PASS-1 that re-verifies every proof
    /// in PASS-2. See Pillar-1 gap G1.
    #[error(
        "Declaration {name}: mm_axiom_only proof-drop reached without the two-pass \
         sentinel (misuse of the axiom-only fast path outside the sanctioned \
         Metamath two-pass); refusing to register an unchecked theorem type"
    )]
    AxiomOnlyMisuse {
        /// Name of the theorem whose proof would have been dropped unchecked.
        name: Name,
    },
    /// `upgrade_axiom_to_checked_decl`: no constant with the incoming
    /// declaration's name exists in the environment, so there is no value-free
    /// stub to upgrade.
    #[error("Upgrade target {name} does not exist in the environment")]
    UpgradeTargetMissing {
        /// Name of the declaration the upgrade targeted.
        name: Name,
    },
    /// `upgrade_axiom_to_checked_decl`: the existing constant already carries a
    /// value. The checked upgrade only ever replaces a VALUE-FREE (axiom-stub)
    /// entry; a value-bearing constant is never overwritten.
    #[error(
        "Upgrade target {name} already has a value; only value-free constants can be upgraded"
    )]
    UpgradeTargetHasValue {
        /// Name of the declaration the upgrade targeted.
        name: Name,
    },
    /// `upgrade_axiom_to_checked_decl`: the incoming declaration carries no
    /// value (it is an `Axiom`), so there is nothing checked to upgrade to.
    #[error("Upgrade for {name} carries no value; only value-bearing declarations can upgrade a value-free constant")]
    UpgradeValueMissing {
        /// Name of the declaration the upgrade targeted.
        name: Name,
    },
    /// `upgrade_axiom_to_checked_decl`: the incoming declaration's type is not
    /// the existing value-free constant's type (compared alpha-insensitively on
    /// positional level params: structural equality first, then the kernel's
    /// `is_def_eq`). Replacing the entry would change the constant's stated
    /// type, so the upgrade fails closed.
    #[error("Upgrade for {name} declares a different type than the existing value-free constant: {detail}")]
    UpgradeTypeMismatch {
        /// Name of the declaration the upgrade targeted.
        name: Name,
        /// What differed (level-param arity or the type itself).
        detail: String,
    },
}

/// Collect a bounded, deduplicated sample of the FVar ids occurring in the
/// given expressions — the diagnostic payload for
/// [`EnvError::ContainsFreeVar`]. The id VALUES classify a leak at a glance
/// (elaborator-scope locals are minted low; tactic-created FVars sit at or
/// above the tactic `fvar_base`), which is what makes a "contains free
/// variables" rejection actionable without a debugger. Runs only on the
/// error path; capped at 8 ids.
pub fn collect_fvar_ids_for_diagnostics(exprs: &[&Expr]) -> Vec<u64> {
    use crate::expr::visitor::ExprVisitor;
    struct Collector(Vec<u64>);
    impl ExprVisitor for Collector {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: crate::expr::FVarId) {
            if self.0.len() < 8 && !self.0.contains(&id.0) {
                self.0.push(id.0);
            }
        }
    }
    let mut collector = Collector(Vec::new());
    for expr in exprs {
        if expr.has_fvar_quick() {
            collector.visit_expr(expr);
        }
    }
    collector.0.sort_unstable();
    collector.0
}
