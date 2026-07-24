// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute types for surface syntax declarations.

/// A parsed attribute like `@[instance 50]` or `@[defaultInstance]`
///
/// Covers core Lean 4 builtin attributes. Based on Lean 4 reference documentation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribute {
    // === Type class instance attributes ===
    /// `@[instance N]` - set instance priority to N
    InstancePriority(u32),
    /// `@[default_instance]` / `@[default_instance N]` — register the
    /// declaration in the default-instance table consulted when a type-class
    /// goal's carrier is still an open metavariable (Lean
    /// `Lean/Elab/DefaultInstance`). It does NOT change the instance's
    /// ordinary resolution priority: a `@[default_instance] instance` still
    /// registers as a normal instance at the default priority (1000).
    DefaultInstance {
        /// Explicit default-instance priority (`@[default_instance 200]`);
        /// `None` means Lean's `default` priority (1000).
        priority: Option<u32>,
    },

    // === Simplifier/tactic attributes ===
    /// `@[simp]` - register as simp lemma with optional priority
    Simp { priority: Option<SimpPriority> },
    /// `@[congr]` - register congruence lemma for simp
    Congr,
    /// `@[ext]` - register extensionality lemma
    Ext,
    /// `@[refl]` - register reflexivity lemma
    Refl,
    /// `@[symm]` - register symmetry lemma
    Symm,

    // === Reducibility attributes ===
    /// `@[reducible]` - unfold during elaboration and definitional equality
    Reducible,
    /// `@[semireducible]` - default, unfold during type class resolution
    Semireducible,
    /// `@[irreducible]` - never unfold automatically
    Irreducible,

    // === Compiler/inlining attributes ===
    /// `@[inline]` - inline function when possible
    Inline,
    /// `@[always_inline]` - always inline, even at -O0
    AlwaysInline,
    /// `@[noinline]` - never inline this function
    Noinline,
    /// `@[macro_inline]` - inline before macro expansion
    MacroInline,
    /// `@[inline_if_reduce]` - inline only if it reduces term size
    InlineIfReduce,
    /// `@[specialize]` - generate specialized versions for concrete args
    Specialize,
    /// `@[nospecialize]` - don't generate specialized versions
    Nospecialize,

    // === FFI/extern attributes ===
    /// `@[extern "name"]` - external C function binding
    Extern(String),
    /// `@[export name]` - export function to C with given name
    Export(String),
    /// `@[implemented_by name]` - replace with external implementation
    ImplementedBy(String),

    // === Documentation/deprecation ===
    /// `@[deprecated]` or `@[deprecated "message"]` - mark as deprecated
    Deprecated(Option<String>),

    // === Other common attributes ===
    /// `@[csimp]` - computational simp lemma (for runtime evaluation)
    Csimp,
    /// `@[match_pattern]` - can be used in match patterns
    MatchPattern,
    /// `@[class]` - declare as type class
    Class,
    /// `@[coe]` - register as coercion
    Coe,
    /// `@[init]` - run at initialization time
    Init,

    // === Aesop ===
    /// `@[aesop ...]` - aesop rule registration
    Aesop(AesopAttr),

    // === Fallback ===
    /// Unknown attribute (stored for error reporting)
    Unknown(String),
}

/// Simp lemma priority
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SimpPriority {
    /// Low priority - tried after normal lemmas
    Low,
    /// Normal priority (default)
    #[default]
    Normal,
    /// High priority - tried before normal lemmas
    High,
}

/// Aesop attribute configuration for rule registration
///
/// Examples:
/// - `@[aesop safe apply]` - safe apply rule at 100%
/// - `@[aesop unsafe 30%]` - unsafe rule at 30%
/// - `@[aesop norm simp]` - normalization simp rule
/// - `@[aesop safe cases Or]` - cases rule for hypotheses of type `Or`
/// - `@[aesop safe apply, Measurable]` - safe apply rule in Measurable rule set
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AesopAttr {
    /// Rule phase (safe, unsafe, norm)
    pub phase: AesopPhase,
    /// Rule builder (apply, cases, constructors, etc.)
    pub builder: AesopBuilder,
    /// Builder arguments (e.g., `@[aesop safe cases Or]` stores `["Or"]`)
    pub builder_args: Vec<String>,
    /// Priority for unsafe rules (0-100, percentage). None means 100 for safe/norm.
    pub priority: Option<u32>,
    /// Rule sets this rule belongs to. Empty means default rule set.
    /// Used for domain-specific tactics like `measurability`, `continuity`.
    pub rule_sets: Vec<String>,
    /// Index mode for fast lookup during proof search.
    /// Defaults to Target (indexed by goal conclusion head).
    pub index_mode: AesopIndexMode,
}

/// How an aesop rule is indexed for fast lookup during proof search
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AesopIndexMode {
    /// Index by goal conclusion head constant (default)
    #[default]
    Target,
    /// Index by hypothesis type head constant
    Hyps,
    /// No indexing - check for all goals (universal rules)
    Unindexed,
}

/// Aesop rule phase - determines when/how rules are applied
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AesopPhase {
    /// Safe rules - won't cause divergence, always tried
    Safe,
    /// Unsafe rules - potentially non-terminating, require probability
    Unsafe,
    /// Normalization rules - always apply, expected to be idempotent
    Norm,
}

/// Aesop rule builder - how the rule is applied to goals
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AesopBuilder {
    /// Apply theorem as forward step
    Apply,
    /// Case split on hypothesis
    Cases,
    /// Try all constructors of inductive type
    Constructors,
    /// Destruct hypothesis
    Destruct,
    /// Add hypothesis from theorem (forward reasoning)
    Forward,
    /// Use as simp lemma
    Simp,
    /// Run arbitrary tactic
    Tactic,
    /// Unfold definition
    Unfold,
}

impl Attribute {
    /// Get the instance priority from this attribute, if any
    #[must_use]
    pub fn instance_priority(&self) -> Option<u32> {
        match self {
            Attribute::InstancePriority(p) => Some(*p),
            // `@[default_instance]` does NOT override the instance's ordinary
            // resolution priority (it feeds the separate default-instance
            // table). Mapping it to `Some(0)` here used to silently demote a
            // `@[default_instance] instance` below every plain instance, so
            // ground goals stopped resolving it (B99).
            Attribute::DefaultInstance { .. } => None,
            // All other attributes have no instance priority
            _ => None,
        }
    }
}
