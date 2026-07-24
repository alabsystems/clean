// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Aesop tactic types
//!
//! Types for registering and indexing rules used by the `aesop` proof automation tactic.

use crate::name::Name;
use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

use super::TransparencyMode;

/// Set of Aesop rules organized by phase
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct AesopRuleSet {
    /// Safe rules - always tried, won't cause divergence
    pub safe_rules: Vec<AesopRule>,
    /// Unsafe rules - potentially non-terminating, ordered by priority
    pub unsafe_rules: Vec<AesopRule>,
    /// Normalization rules - always apply, expected to be idempotent
    pub norm_rules: Vec<AesopRule>,
    /// Priority overrides for specific rules when used from this set
    /// Maps rule name -> priority override (0-100)
    #[serde(default)]
    pub priority_overrides: HashMap<Name, u32>,
}

/// A registered aesop rule
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AesopRule {
    /// Declaration name this rule refers to
    pub name: Name,
    /// Rule phase (safe, unsafe, norm)
    pub phase: AesopRulePhase,
    /// Rule builder (apply, cases, constructors, etc.)
    pub builder: AesopRuleBuilder,
    /// Builder arguments (e.g., target type for `cases`)
    #[serde(default)]
    pub builder_args: Vec<Name>,
    /// Priority (0-100, percentage) - only meaningful for unsafe rules
    pub priority: u32,
    /// Index mode - how the rule is indexed for fast lookup
    #[serde(default)]
    pub index_mode: AesopIndexMode,
    /// Transparency mode for this rule's type checking
    #[serde(default)]
    pub transparency: TransparencyMode,
}

/// Aesop rule phase - determines when/how rules are applied
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AesopRulePhase {
    /// Safe rules - won't cause divergence, always tried
    Safe,
    /// Unsafe rules - potentially non-terminating, require probability
    Unsafe,
    /// Normalization rules - always apply, expected to be idempotent
    Norm,
}

/// Aesop rule builder - how the rule is applied to goals
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AesopRuleBuilder {
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

/// How an aesop rule is indexed for fast lookup
///
/// Index modes control which goals a rule is considered for:
/// - Target: indexed by goal conclusion head (default)
/// - Hyps: indexed by hypothesis type heads
/// - Unindexed: considered for all goals
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum AesopIndexMode {
    /// Index by goal conclusion head constant (default)
    #[default]
    Target,
    /// Index by hypothesis type head constant
    Hyps,
    /// No indexing - check for all goals (universal rules)
    Unindexed,
}

impl AesopRuleSet {
    /// Get the effective priority for a rule, considering overrides.
    ///
    /// If this set has a priority override for the rule's name, returns that.
    /// Otherwise returns the rule's inherent priority.
    ///
    /// This enables rule sets to adjust priorities contextually:
    /// ```text
    /// -- Base set with default priority
    /// @[aesop safe apply] my_lemma
    ///
    /// -- Override in specific context
    /// @[aesop unsafe 50 apply (rule_sets := [MySpecialSet])] my_lemma
    /// ```
    /// REQUIRES: none (pure function)
    /// ENSURES: Returns the override priority if present; otherwise returns `rule.priority`.
    pub fn effective_priority(&self, rule: &AesopRule) -> u32 {
        self.priority_overrides
            .get(&rule.name)
            .copied()
            .unwrap_or(rule.priority)
    }

    /// Set a priority override for a specific rule in this set.
    ///
    /// Returns the previous override if one existed.
    /// REQUIRES: none (mutates self)
    /// ENSURES: Returns the previous override for `rule_name` (if any) and stores `priority`.
    pub fn set_priority_override(&mut self, rule_name: Name, priority: u32) -> Option<u32> {
        self.priority_overrides.insert(rule_name, priority)
    }

    /// Remove a priority override for a specific rule.
    ///
    /// Returns the removed override if one existed.
    /// REQUIRES: none (mutates self)
    /// ENSURES: Returns the removed override for `rule_name` (if any) and deletes the entry.
    pub fn remove_priority_override(&mut self, rule_name: &Name) -> Option<u32> {
        self.priority_overrides.remove(rule_name)
    }

    /// Check if this set has a priority override for a rule.
    /// REQUIRES: none (pure function)
    /// ENSURES: Returns true iff an override exists for `rule_name` in this set.
    pub fn has_priority_override(&self, rule_name: &Name) -> bool {
        self.priority_overrides.contains_key(rule_name)
    }
}
