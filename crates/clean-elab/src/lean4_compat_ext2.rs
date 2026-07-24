// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Lean 4 compatibility: syntax desugaring, attribute compat, option
//! handling, auto-bound implicits, universe inference, notation compat, tactic
//! mapping, instance priority, version tracking, and statistics.
//!
//! Builds on [`lean4_compat`] and [`lean4_compat_ext`].

use crate::lean4_compat_ext::Lean4Version;
use hashbrown::HashMap;
use std::cell::Cell;
use std::fmt;
use thiserror::Error;

// ── Errors ──────────────────────────────────────────────────────────────────

/// Errors specific to the extended compatibility layer.
#[derive(Debug, Error)]
pub(crate) enum CompatExt2Error {
    #[error("unknown Lean 4 attribute `{name}`")]
    UnknownAttribute { name: String },
    #[error("invalid option value for `{name}`: expected {expected}, got `{actual}`")]
    InvalidOptionValue {
        name: String,
        expected: &'static str,
        actual: String,
    },
    #[error("unsupported do-notation form: {detail}")]
    UnsupportedDoNotation { detail: String },
    #[error("notation precedence out of range [0, 1024]: {value}")]
    PrecedenceOutOfRange { value: u32 },
}

// ── Syntax desugaring ───────────────────────────────────────────────────────

/// Classification of a Lean 4 do-notation form for desugaring.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum DoForm {
    Bind { var: String, monadic: String },
    LetAssign { var: String, value: String },
    Return { value: String },
    IfThenElse,
    ForIn,
    TryCatch,
    Unless,
}

/// Describes a where-clause desugaring step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WhereDesugar {
    pub(crate) name: String,
    pub(crate) is_rec: bool,
}

/// Describes an anonymous constructor desugaring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AnonCtorDesugar {
    pub(crate) target_type: String,
    pub(crate) arg_count: usize,
}

/// Classify a do-notation keyword into its desugaring form.
#[must_use]
pub(crate) fn classify_do_form(keyword: &str) -> Option<DoForm> {
    match keyword {
        "let" => Some(DoForm::LetAssign {
            var: String::new(),
            value: String::new(),
        }),
        "return" => Some(DoForm::Return {
            value: String::new(),
        }),
        "if" => Some(DoForm::IfThenElse),
        "for" => Some(DoForm::ForIn),
        "try" => Some(DoForm::TryCatch),
        "unless" => Some(DoForm::Unless),
        _ => None,
    }
}

// ── Attribute compatibility ─────────────────────────────────────────────────

/// Lean 4 attribute kinds supported by the compatibility layer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum Lean4Attribute {
    Simp,
    Inline,
    AlwaysInline,
    Noinline,
    Reducible,
    Irreducible,
    Semireducible,
    Instance { priority: Option<u32> },
    DefaultInstance { priority: Option<u32> },
    Class,
    Extern { name: Option<String> },
    Export { name: String },
    Deprecated { msg: Option<String> },
    Csimp,
    Congr,
    Ext,
    Refl,
    Symm,
    MacroInline,
    InlineIfReduce,
    Specialize,
    Nospecialize,
    ImplementedBy { impl_name: String },
    Coe,
    MatchPattern,
    Init,
}

/// Parse a Lean 4 attribute name (without the `@[...]` brackets) into a typed
/// [`Lean4Attribute`] value.
pub(crate) fn parse_attribute(input: &str) -> Result<Lean4Attribute, CompatExt2Error> {
    let trimmed = input.trim();
    // Handle parameterized attributes
    if let Some(rest) = trimmed.strip_prefix("instance") {
        let priority = parse_optional_priority(rest);
        return Ok(Lean4Attribute::Instance { priority });
    }
    if let Some(rest) = trimmed.strip_prefix("default_instance") {
        let priority = parse_optional_priority(rest);
        return Ok(Lean4Attribute::DefaultInstance { priority });
    }
    if let Some(rest) = trimmed.strip_prefix("implemented_by ") {
        return Ok(Lean4Attribute::ImplementedBy {
            impl_name: rest.trim().to_owned(),
        });
    }
    if let Some(rest) = trimmed.strip_prefix("export ") {
        return Ok(Lean4Attribute::Export {
            name: rest.trim().to_owned(),
        });
    }
    if let Some(rest) = trimmed.strip_prefix("extern") {
        let name = rest.trim();
        return Ok(Lean4Attribute::Extern {
            name: if name.is_empty() {
                None
            } else {
                Some(name.trim_matches('"').to_owned())
            },
        });
    }
    if let Some(rest) = trimmed.strip_prefix("deprecated") {
        let msg = rest.trim().trim_matches('"');
        return Ok(Lean4Attribute::Deprecated {
            msg: if msg.is_empty() {
                None
            } else {
                Some(msg.to_owned())
            },
        });
    }
    match trimmed {
        "simp" => Ok(Lean4Attribute::Simp),
        "inline" => Ok(Lean4Attribute::Inline),
        "always_inline" => Ok(Lean4Attribute::AlwaysInline),
        "noinline" => Ok(Lean4Attribute::Noinline),
        "reducible" => Ok(Lean4Attribute::Reducible),
        "irreducible" => Ok(Lean4Attribute::Irreducible),
        "semireducible" => Ok(Lean4Attribute::Semireducible),
        "class" => Ok(Lean4Attribute::Class),
        "csimp" => Ok(Lean4Attribute::Csimp),
        "congr" => Ok(Lean4Attribute::Congr),
        "ext" => Ok(Lean4Attribute::Ext),
        "refl" => Ok(Lean4Attribute::Refl),
        "symm" => Ok(Lean4Attribute::Symm),
        "macro_inline" => Ok(Lean4Attribute::MacroInline),
        "inline_if_reduce" => Ok(Lean4Attribute::InlineIfReduce),
        "specialize" => Ok(Lean4Attribute::Specialize),
        "nospecialize" => Ok(Lean4Attribute::Nospecialize),
        "coe" => Ok(Lean4Attribute::Coe),
        "match_pattern" => Ok(Lean4Attribute::MatchPattern),
        "init" => Ok(Lean4Attribute::Init),
        _ => Err(CompatExt2Error::UnknownAttribute {
            name: trimmed.to_owned(),
        }),
    }
}

fn parse_optional_priority(rest: &str) -> Option<u32> {
    rest.trim().parse::<u32>().ok()
}

// ── Option handling ─────────────────────────────────────────────────────────

/// A parsed Lean 4 `set_option` value.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum OptionValue {
    Bool(bool),
    Nat(u64),
    String(String),
}

impl fmt::Display for OptionValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Nat(n) => write!(f, "{n}"),
            Self::String(s) => write!(f, "\"{s}\""),
        }
    }
}

/// Well-known Lean 4 options with their expected types.
#[must_use]
pub(crate) fn known_option_type(name: &str) -> Option<&'static str> {
    match name {
        "pp.all"
        | "pp.notation"
        | "pp.universes"
        | "pp.fullNames"
        | "pp.explicit"
        | "autoImplicit"
        | "relaxedAutoImplicit"
        | "autoBoundImplicitLocal" => Some("Bool"),
        "maxRecDepth" | "maxHeartbeats" | "synthInstance.maxHeartbeats" => Some("Nat"),
        _ => None,
    }
}

/// Parse a `set_option` value string given the option name.
pub(crate) fn parse_option_value(name: &str, raw: &str) -> Result<OptionValue, CompatExt2Error> {
    let expected_type = known_option_type(name);
    let trimmed = raw.trim();
    match expected_type {
        Some("Bool") => match trimmed {
            "true" => Ok(OptionValue::Bool(true)),
            "false" => Ok(OptionValue::Bool(false)),
            _ => Err(CompatExt2Error::InvalidOptionValue {
                name: name.to_owned(),
                expected: "Bool",
                actual: trimmed.to_owned(),
            }),
        },
        Some("Nat") => trimmed.parse::<u64>().map(OptionValue::Nat).map_err(|_| {
            CompatExt2Error::InvalidOptionValue {
                name: name.to_owned(),
                expected: "Nat",
                actual: trimmed.to_owned(),
            }
        }),
        _ => Ok(OptionValue::String(trimmed.to_owned())),
    }
}

// ── Auto-bound implicit compatibility ───────────────────────────────────────

/// Lean 4 `variable` binding mode for auto-bound implicits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum AutoBoundMode {
    /// `variable (α : Type)` — explicit binder.
    Explicit,
    /// `variable {α : Type}` — implicit binder.
    Implicit,
    /// `variable [Inhabited α]` — instance binder.
    Instance,
    /// `variable {{α : Type}}` — strict implicit.
    StrictImplicit,
}

/// Determine auto-bound mode from bracket characters.
#[must_use]
pub(crate) fn auto_bound_mode_from_brackets(open: char, close: char) -> Option<AutoBoundMode> {
    match (open, close) {
        ('(', ')') => Some(AutoBoundMode::Explicit),
        ('{', '}') => Some(AutoBoundMode::Implicit),
        ('[', ']') => Some(AutoBoundMode::Instance),
        _ => None,
    }
}

// ── Universe polymorphism compatibility ─────────────────────────────────────

/// Auto-inferred universe level placeholder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UniversePlaceholder {
    pub(crate) name: String,
    pub(crate) is_auto: bool,
}

/// Generate fresh universe variable names that do not collide with existing
/// names in the declaration.
#[must_use]
pub(crate) fn fresh_universe_name(existing: &[String]) -> String {
    for suffix in 0u32.. {
        let candidate = if suffix == 0 {
            "u".to_owned()
        } else {
            format!("u_{suffix}")
        };
        if !existing.iter().any(|n| n == &candidate) {
            return candidate;
        }
    }
    "u_fresh".to_owned()
}

// ── Notation compatibility ──────────────────────────────────────────────────

/// A Lean 4 precedence value (0..1024).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Precedence(u32);

impl Precedence {
    pub(crate) const MIN: Self = Self(0);
    pub(crate) const MAX: Self = Self(1024);
    pub(crate) const DEFAULT: Self = Self(0);

    /// Create a precedence, validating the range.
    pub(crate) fn new(value: u32) -> Result<Self, CompatExt2Error> {
        if value > 1024 {
            return Err(CompatExt2Error::PrecedenceOutOfRange { value });
        }
        Ok(Self(value))
    }

    #[must_use]
    pub(crate) fn value(self) -> u32 {
        self.0
    }
}

/// Map well-known Lean 4 notation names to clean precedence defaults.
#[must_use]
pub(crate) fn default_precedence_for_notation(kind: &str) -> Precedence {
    match kind {
        "infixl" | "infixr" | "infix" => Precedence(65),
        "prefix" => Precedence(100),
        "postfix" => Precedence(100),
        "notation" => Precedence::DEFAULT,
        _ => Precedence::DEFAULT,
    }
}

// ── Tactic syntax mapping ───────────────────────────────────────────────────

/// Extended tactic name mapping: Lean 4 names that differ in clean.
/// Identity mappings (same name in both) are omitted.
#[must_use]
pub(crate) fn extended_tactic_map() -> HashMap<&'static str, &'static str> {
    HashMap::from([
        ("rw", "rewrite"),
        ("let", "let_tac"),
        ("exact?", "exact_search"),
        ("simp?", "simp_search"),
    ])
}

/// Resolve a Lean 4 tactic name to its clean equivalent.
#[must_use]
pub(crate) fn resolve_tactic_ext(name: &str) -> Option<&'static str> {
    extended_tactic_map().get(name).copied()
}

// ── Instance priority handling ──────────────────────────────────────────────

/// Resolve Lean 4 instance priority from attribute arguments.
///
/// Lean 4 convention: higher numeric priority = tried first.
/// Default is 100 if unspecified.
#[must_use]
pub(crate) fn resolve_instance_priority(explicit: Option<u32>) -> u32 {
    explicit.unwrap_or(100)
}

/// Check whether a priority value is within the standard Lean 4 range.
#[must_use]
pub(crate) fn is_valid_instance_priority(priority: u32) -> bool {
    priority <= 10_000
}

// ── Compatibility version tracking ──────────────────────────────────────────

/// Compat feature flags gated on target Lean 4 version.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompatFeatureFlags {
    pub(crate) do_notation_v2: bool,
    pub(crate) structure_eta: bool,
    pub(crate) match_discriminant_refinement: bool,
    pub(crate) mathverse_tactic: bool,
    pub(crate) grind_tactic: bool,
    pub(crate) auto_implicit: bool,
    pub(crate) relaxed_auto_implicit: bool,
}

impl CompatFeatureFlags {
    /// Compute feature flags for a given target Lean 4 version.
    #[must_use]
    pub(crate) fn for_version(v: &Lean4Version) -> Self {
        Self {
            do_notation_v2: *v >= Lean4Version::new(4, 1, 0),
            structure_eta: *v >= Lean4Version::new(4, 2, 0),
            match_discriminant_refinement: *v >= Lean4Version::new(4, 3, 0),
            mathverse_tactic: *v >= Lean4Version::new(4, 2, 0),
            grind_tactic: *v >= Lean4Version::new(4, 8, 0),
            auto_implicit: *v >= Lean4Version::new(4, 0, 0),
            relaxed_auto_implicit: *v >= Lean4Version::new(4, 7, 0),
        }
    }

    /// Number of enabled features.
    #[must_use]
    pub(crate) fn enabled_count(&self) -> usize {
        [
            self.do_notation_v2,
            self.structure_eta,
            self.match_discriminant_refinement,
            self.mathverse_tactic,
            self.grind_tactic,
            self.auto_implicit,
            self.relaxed_auto_implicit,
        ]
        .iter()
        .filter(|&&f| f)
        .count()
    }
}

// ── Statistics ──────────────────────────────────────────────────────────────

/// Tracks compat features triggered during elaboration.
#[derive(Debug, Clone, Default)]
pub(crate) struct CompatStats {
    pub(crate) do_desugar_count: Cell<u64>,
    pub(crate) where_desugar_count: Cell<u64>,
    pub(crate) anon_ctor_count: Cell<u64>,
    pub(crate) attr_compat_count: Cell<u64>,
    pub(crate) option_count: Cell<u64>,
    pub(crate) tactic_translate_count: Cell<u64>,
    pub(crate) auto_bound_count: Cell<u64>,
    pub(crate) universe_infer_count: Cell<u64>,
    pub(crate) notation_lookup_count: Cell<u64>,
    pub(crate) fallback_count: Cell<u64>,
}

impl CompatStats {
    /// Create a fresh stats tracker.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Increment a counter by name. Returns the new value.
    pub(crate) fn increment(&self, counter: CompatCounter) -> u64 {
        let cell = match counter {
            CompatCounter::DoDesugar => &self.do_desugar_count,
            CompatCounter::WhereDesugar => &self.where_desugar_count,
            CompatCounter::AnonCtor => &self.anon_ctor_count,
            CompatCounter::AttrCompat => &self.attr_compat_count,
            CompatCounter::Option => &self.option_count,
            CompatCounter::TacticTranslate => &self.tactic_translate_count,
            CompatCounter::AutoBound => &self.auto_bound_count,
            CompatCounter::UniverseInfer => &self.universe_infer_count,
            CompatCounter::NotationLookup => &self.notation_lookup_count,
            CompatCounter::Fallback => &self.fallback_count,
        };
        let new_val = cell.get() + 1;
        cell.set(new_val);
        new_val
    }

    /// Total operations tracked.
    #[must_use]
    pub(crate) fn total(&self) -> u64 {
        self.do_desugar_count.get()
            + self.where_desugar_count.get()
            + self.anon_ctor_count.get()
            + self.attr_compat_count.get()
            + self.option_count.get()
            + self.tactic_translate_count.get()
            + self.auto_bound_count.get()
            + self.universe_infer_count.get()
            + self.notation_lookup_count.get()
            + self.fallback_count.get()
    }
}

/// Named counters for [`CompatStats::increment`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum CompatCounter {
    DoDesugar,
    WhereDesugar,
    AnonCtor,
    AttrCompat,
    Option,
    TacticTranslate,
    AutoBound,
    UniverseInfer,
    NotationLookup,
    Fallback,
}
