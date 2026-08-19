// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type class, aesop rule, and attribute registry methods.
//!
//! Extracted from env/mod.rs for maintainability (see #1161).
//! Contains registration and lookup methods for type classes,
//! instances, aesop rules, simp lemmas, and other attributes.

use crate::expr::{Expr, ExprKind};
use crate::name::Name;

use super::aesop::{AesopIndexMode, AesopRule, AesopRuleBuilder, AesopRulePhase, AesopRuleSet};
use super::types::{
    EnvError, KernelClassInfo, KernelInstanceInfo, Reducibility, SimpLemmaInfo, SimpPriority,
};
use super::Environment;

impl Environment {
    // ========================================================================
    // Type class and instance registration
    // ========================================================================

    /// Register a type class
    ///
    /// This is called by kernel init functions after defining a type class via `add_inductive()`.
    /// The elaborator's InstanceTable is initialized from this data.
    ///
    /// # Arguments
    /// * `info` - The class information to register
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn register_class(&mut self, info: KernelClassInfo) {
        self.classes.insert(info.name.clone(), info);
        self.generation += 1;
    }

    /// Register an instance for a type class
    ///
    /// This is called by kernel init functions after defining an instance via `add_decl()`.
    /// Instances are stored in resolution order: highest priority first, and —
    /// within one priority tier — **most-recently-registered first**.
    ///
    /// The most-recent-first tiebreak within a tier is the observable Lean 4
    /// semantics: for two equal-priority instances the later-declared one is
    /// resolved first, so a later `instance` overrides an earlier one (Lean
    /// `src/Lean/Meta/Instances.lean`, `addInstance`/`addInstanceEntry`
    /// prepends the new entry; `SynthInstance` then reaches it before older
    /// same-priority entries). The elaborator's `InstanceTable` is rebuilt from
    /// this Vec verbatim (`infer/elab_init.rs::init_instances_from_env` iterates
    /// `get_class_instances` in order and appends within a tier), and
    /// `candidate_order`'s registration-order tiebreak (ascending index) then
    /// picks the front — i.e. the most recent — so this ordering flows straight
    /// through to resolution. Sweep B12 (`classes_instances/p06`): a value-pin
    /// bug where the first-declared instance used to win.
    ///
    /// # Arguments
    /// * `info` - The instance information to register
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn register_instance(&mut self, info: KernelInstanceInfo) {
        // Add to reverse lookup for O(1) instance check
        self.instance_names.insert(info.name.clone());

        let instances = self.instances.entry(info.class_name.clone()).or_default();
        // Insert before the first entry of equal-or-lower priority, so a new
        // instance sits ahead of existing same-priority ones (most-recent-first)
        // while still ordered strictly below any higher-priority instance.
        let pos = instances
            .iter()
            .position(|i| i.priority <= info.priority)
            .unwrap_or(instances.len());
        instances.insert(pos, info);
        self.generation += 1;
    }

    /// Idempotently install an initializer-owned instance-registry entry.
    /// Existing state is accepted only when exactly one complete entry matches;
    /// duplicates or same-name metadata drift fail closed.
    pub(crate) fn ensure_exact_instance(
        &mut self,
        info: KernelInstanceInfo,
    ) -> Result<(), EnvError> {
        let existing: Vec<&KernelInstanceInfo> = self
            .instances
            .values()
            .flat_map(|entries| entries.iter())
            .filter(|entry| entry.name == info.name)
            .collect();
        if existing.is_empty() {
            self.register_instance(info);
            return Ok(());
        }
        let exact = existing.len() == 1
            && existing[0].class_name == info.class_name
            && existing[0].priority == info.priority
            && existing[0].type_ == info.type_
            && existing[0].value == info.value;
        if !exact {
            return Err(EnvError::InitializationConflict {
                name: info.name,
                detail: "existing instance registry has duplicate or noncanonical metadata"
                    .to_string(),
            });
        }
        // Repair a missing reverse index without duplicating the canonical
        // entry (useful after interrupted/custom environment construction).
        if self.instance_names.insert(info.name) {
            self.generation += 1;
        }
        Ok(())
    }

    /// Adopt an authoritative priority for an ALREADY-registered instance,
    /// re-seating it in its class bucket so the priority-descending invariant
    /// of [`Self::get_class_instances`] still holds.
    ///
    /// This exists for one job: Clean seeds a hand-rolled prelude whose
    /// instance priorities are GUESSED, then imports a real Lean environment
    /// that serializes the true priority in every `.olean`. Import is
    /// first-registered-wins, so without this the guess would win permanently —
    /// and instance priority decides which candidate `synthInstance` reaches
    /// first, i.e. the shape of every elaborated term. Three separate defects
    /// (`instOfNatNat` 100-vs-1000, `instLTNat` 100-vs-1000, and the B101
    /// hetero bridges) were fixed one row at a time before this path existed.
    ///
    /// Only the priority moves: `class_name`, `type_` and `value` are the
    /// hand-registered entry's own (the prelude sets `type_`/`value` for
    /// binder-info fidelity that the persisted Lean entry does not carry, so
    /// replacing the whole entry would lose it). The entry is re-inserted with
    /// [`Self::register_instance`]'s placement rule — front of its new tier —
    /// which is exactly where a fresh registration at this moment would land.
    ///
    /// Returns the previous priority, or `None` when `name` is not a
    /// registered instance (nothing is created: never fabricate metadata).
    ///
    /// SOUNDNESS: instance metadata is elaboration-only. It steers which
    /// candidate `resolve_instance` tries first; every synthesized term is
    /// still kernel re-checked by its caller. A wrong priority can only cost
    /// completeness/parity, never admit a false proof.
    ///
    /// ENSURES: on `Some`, `get_class_instances(class)` contains exactly one
    /// entry named `name`, with the requested priority, still ordered
    /// priority-descending.
    /// REQUIRES: none
    pub fn adopt_instance_priority(&mut self, name: &Name, priority: u32) -> Option<u32> {
        if !self.instance_names.contains(name) {
            return None;
        }
        let class_name = self
            .instances
            .iter()
            .find(|(_, entries)| entries.iter().any(|e| &e.name == name))
            .map(|(class, _)| class.clone())?;
        let entries = self.instances.get_mut(&class_name)?;
        let pos = entries.iter().position(|e| &e.name == name)?;
        let previous = entries[pos].priority;
        if previous == priority {
            return Some(previous);
        }
        let mut info = entries.remove(pos);
        info.priority = priority;
        let insert_at = entries
            .iter()
            .position(|e| e.priority <= priority)
            .unwrap_or(entries.len());
        entries.insert(insert_at, info);
        self.generation += 1;
        Some(previous)
    }

    /// Check if a name is a registered type class
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn is_class(&self, name: &Name) -> bool {
        self.classes.contains_key(name)
    }

    /// Check if a name is a registered instance
    ///
    /// Used by `unfold_with_transparency` for `TransparencyMode::Instances`.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn is_instance(&self, name: &Name) -> bool {
        self.instance_names.contains(name)
    }

    /// Record the synthesization order for an instance (Lean's
    /// `InstanceEntry.synthOrder`: binder indices into the instance type's
    /// Pi telescope, in the order the resolver must synthesize them so that
    /// each sub-goal's solution determines the metavariables consumed by
    /// later ones — `Lean/Meta/Instances.lean:46-60`).
    ///
    /// Populated by the `.olean` import bridge from decoded
    /// `Lean.Meta.instanceExtension` entries. Elaboration metadata only:
    /// steers sub-goal scheduling in `resolve_instance`; every synthesized
    /// term is still kernel re-checked by its caller.
    /// ENSURES: `get_instance_synth_order(&name)` returns the stored order.
    /// REQUIRES: none
    pub fn set_instance_synth_order(&mut self, name: Name, order: Vec<usize>) {
        self.instance_synth_orders.insert(name, order);
        self.generation += 1;
    }

    /// Look up the recorded synthesization order for an instance.
    ///
    /// Returns `None` for instances without a persisted order (the
    /// hand-registered prelude lane); the elaborator then computes a
    /// Lean-style default (out-param-driven, mirroring `computeSynthOrder`,
    /// `Lean/Meta/Instances.lean:145-229`).
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_instance_synth_order(&self, name: &Name) -> Option<&[usize]> {
        self.instance_synth_orders.get(name).map(Vec::as_slice)
    }

    /// Look up a type class by name.
    ///
    /// Returns class metadata including the class name and associated info.
    ///
    /// # Returns
    /// - `Some(&KernelClassInfo)` if `name` is a registered type class
    /// - `None` if no class with this name has been registered
    ///
    /// Type classes are registered via [`Self::register_class`].
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_class_info(&self, name: &Name) -> Option<&KernelClassInfo> {
        self.classes.get(name)
    }

    /// Get all instances for a type class, sorted by priority (highest first).
    ///
    /// Returns instances registered for the given class name. Instance priority
    /// determines the order: higher priority instances appear first.
    ///
    /// # Returns
    /// - Non-empty slice if the class has registered instances
    /// - Empty slice if no instances or class not found
    ///
    /// Instances are registered via [`Self::register_instance`].
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_class_instances(&self, class_name: &Name) -> &[KernelInstanceInfo] {
        self.instances.get(class_name).map_or(&[], Vec::as_slice)
    }

    /// Iterate all registered classes.
    ///
    /// Note: Iteration order is arbitrary (HashMap-based storage).
    ///
    /// ENSURES: Returns exactly `num_classes()` items
    /// ENSURES: Each class is returned exactly once
    /// REQUIRES: none
    pub fn classes(&self) -> impl Iterator<Item = &KernelClassInfo> {
        self.classes.values()
    }

    /// Get number of registered classes
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_classes(&self) -> usize {
        self.classes.len()
    }

    /// Get total number of instances
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_instances(&self) -> usize {
        self.instances.values().map(Vec::len).sum()
    }

    /// Iterate over all registered instances across all classes.
    ///
    /// Note: Iteration order between classes is arbitrary (HashMap-based storage).
    /// Instances within each class are sorted by priority (highest first).
    ///
    /// ENSURES: Returns exactly `num_instances()` items
    /// ENSURES: Each instance is returned exactly once
    /// ENSURES: Instances from the same class appear consecutively
    /// REQUIRES: none
    pub fn instances(&self) -> impl Iterator<Item = &KernelInstanceInfo> {
        self.instances.values().flat_map(|v| v.iter())
    }

    // ========================================================================
    // Aesop rule management
    // ========================================================================

    /// Register an aesop rule for tactic search
    ///
    /// Rules are stored by phase (safe, unsafe, norm) and can be looked up
    /// during aesop tactic execution. Rules are also indexed by their index_mode
    /// for fast lookup during proof search.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn register_aesop_rule(&mut self, rule: AesopRule) {
        // Index the rule based on its index_mode
        self.index_aesop_rule(&rule);

        // Store in phase-based lists (backward compatibility)
        match rule.phase {
            AesopRulePhase::Safe => self.aesop_rules.safe_rules.push(rule),
            AesopRulePhase::Unsafe => {
                // Insert sorted by priority (higher priority first)
                let pos = self
                    .aesop_rules
                    .unsafe_rules
                    .partition_point(|r| r.priority > rule.priority);
                self.aesop_rules.unsafe_rules.insert(pos, rule);
            }
            AesopRulePhase::Norm => self.aesop_rules.norm_rules.push(rule),
        }
    }

    /// Index an aesop rule based on its index_mode
    fn index_aesop_rule(&mut self, rule: &AesopRule) {
        match rule.index_mode {
            AesopIndexMode::Target => {
                // For Unfold rules, index by the definition name itself
                // (since the goal head will be the definition being unfolded).
                // For other rules, use the conclusion type head.
                let head = if rule.builder == AesopRuleBuilder::Unfold {
                    Some(rule.name.clone())
                } else {
                    self.get_rule_target_head(&rule.name)
                };

                if let Some(head) = head {
                    self.aesop_target_index
                        .entry(head)
                        .or_default()
                        .push(rule.clone());
                } else {
                    // If we can't determine the head, treat as unindexed
                    self.aesop_unindexed_rules.push(rule.clone());
                }
            }
            AesopIndexMode::Hyps => {
                // For hyps-indexed rules, we need the first hypothesis type head
                if let Some(head) = self.get_rule_hyps_head(&rule.name) {
                    self.aesop_hyps_index
                        .entry(head)
                        .or_default()
                        .push(rule.clone());
                } else {
                    // If we can't determine the head, treat as unindexed
                    self.aesop_unindexed_rules.push(rule.clone());
                }
            }
            AesopIndexMode::Unindexed => {
                self.aesop_unindexed_rules.push(rule.clone());
            }
        }
    }

    /// Extract the head constant from a rule's conclusion type
    ///
    /// For a theorem `∀ x y, P x y → Q x`, this returns `Some(Q)`.
    /// Returns None if the conclusion doesn't have a constant head.
    fn get_rule_target_head(&self, name: &Name) -> Option<Name> {
        let const_info = self.get_const(name)?;
        let ty = &const_info.type_;
        // Skip leading ∀/Pi binders to get to the conclusion
        let conclusion = self.get_conclusion_type(ty);
        // Extract head constant from the conclusion
        self.get_head_const(&conclusion)
    }

    /// Extract the head constant from a rule's first hypothesis type
    ///
    /// For a theorem `∀ x, P x → Q x`, this returns `Some(P)`.
    /// Returns None if there's no hypothesis or it doesn't have a constant head.
    fn get_rule_hyps_head(&self, name: &Name) -> Option<Name> {
        let const_info = self.get_const(name)?;
        let ty = &const_info.type_;
        // Find the first non-implicit hypothesis (arrow/forall with default binder info)
        self.get_first_hyp_head(ty)
    }

    /// Get the conclusion type (skip leading Pi/forall)
    fn get_conclusion_type(&self, ty: &Expr) -> Expr {
        let mut current = ty.clone();
        loop {
            match &current.kind {
                ExprKind::Pi(_, _, body) => {
                    current = (**body).clone();
                }
                _ => return current,
            }
        }
    }

    /// Get head constant from an expression
    fn get_head_const(&self, expr: &Expr) -> Option<Name> {
        let head = expr.get_app_fn();
        match &head.kind {
            ExprKind::Const(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    /// Get the head constant of the first explicit hypothesis type
    ///
    /// This returns the head of the first Pi domain. For hyps-indexed rules,
    /// this is the type that must appear as a hypothesis for the rule to match.
    fn get_first_hyp_head(&self, ty: &Expr) -> Option<Name> {
        match &ty.kind {
            ExprKind::Pi(_, domain, _) => {
                // Get the head constant from the domain (hypothesis type)
                self.get_head_const(domain)
            }
            _ => None,
        }
    }

    /// Get rules indexed by target head constant
    ///
    /// Returns rules that match the given goal conclusion head,
    /// plus all unindexed rules.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_rules_for_target(&self, target_head: &Name) -> Vec<&AesopRule> {
        let mut rules = Vec::new();

        // Target-indexed rules matching this head
        if let Some(indexed) = self.aesop_target_index.get(target_head) {
            rules.extend(indexed.iter());
        }

        // Unindexed rules always match
        rules.extend(self.aesop_unindexed_rules.iter());

        rules
    }

    /// Get rules indexed by hypothesis type heads
    ///
    /// Returns rules that match any of the given hypothesis type heads,
    /// plus all unindexed rules.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_rules_for_hyps(&self, hyp_heads: &[Name]) -> Vec<&AesopRule> {
        let mut rules = Vec::new();

        for head in hyp_heads {
            if let Some(indexed) = self.aesop_hyps_index.get(head) {
                rules.extend(indexed.iter());
            }
        }

        // Unindexed rules always match
        rules.extend(self.aesop_unindexed_rules.iter());

        rules
    }

    /// Get all registered safe rules.
    ///
    /// Convenience method equivalent to `get_aesop_rules(AesopRulePhase::Safe)`.
    /// Use when you specifically need safe rules; use [`Self::get_aesop_rules`] for
    /// parameterized access when the phase is determined at runtime.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_aesop_safe_rules(&self) -> &[AesopRule] {
        &self.aesop_rules.safe_rules
    }

    /// Get all registered unsafe rules (ordered by priority, highest first).
    ///
    /// Convenience method equivalent to `get_aesop_rules(AesopRulePhase::Unsafe)`.
    /// Use when you specifically need unsafe rules; use [`Self::get_aesop_rules`] for
    /// parameterized access when the phase is determined at runtime.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_aesop_unsafe_rules(&self) -> &[AesopRule] {
        &self.aesop_rules.unsafe_rules
    }

    /// Get all registered normalization rules.
    ///
    /// Convenience method equivalent to `get_aesop_rules(AesopRulePhase::Norm)`.
    /// Use when you specifically need norm rules; use [`Self::get_aesop_rules`] for
    /// parameterized access when the phase is determined at runtime.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_aesop_norm_rules(&self) -> &[AesopRule] {
        &self.aesop_rules.norm_rules
    }

    /// Get all registered aesop rules by phase.
    ///
    /// This is the parameterized version of the phase-specific getters.
    /// Use this when the phase is determined at runtime; use the convenience
    /// methods ([`Self::get_aesop_safe_rules`], [`Self::get_aesop_unsafe_rules`],
    /// [`Self::get_aesop_norm_rules`]) for cleaner code when the phase is known
    /// statically.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_aesop_rules(&self, phase: AesopRulePhase) -> &[AesopRule] {
        match phase {
            AesopRulePhase::Safe => &self.aesop_rules.safe_rules,
            AesopRulePhase::Unsafe => &self.aesop_rules.unsafe_rules,
            AesopRulePhase::Norm => &self.aesop_rules.norm_rules,
        }
    }

    /// Get the entire aesop rule set
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_aesop_rule_set(&self) -> &AesopRuleSet {
        &self.aesop_rules
    }

    // ========================================================================
    // Named rule set management
    // ========================================================================

    /// Declare a new aesop rule set
    ///
    /// This must be called before rules can be registered to the rule set.
    /// Corresponds to `declare_aesop_rule_sets [Name]` in Lean.
    ///
    /// # Example
    /// ```text
    /// env.declare_aesop_rule_set(Name::from_string("Measurable"));
    /// ```
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn declare_aesop_rule_set(&mut self, name: Name) {
        if !self.declared_aesop_rule_sets.contains(&name) {
            self.declared_aesop_rule_sets.insert(name.clone());
            self.aesop_rule_sets.insert(name, AesopRuleSet::default());
        }
    }

    /// Check if a rule set has been declared
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn is_aesop_rule_set_declared(&self, name: &Name) -> bool {
        self.declared_aesop_rule_sets.contains(name)
    }

    /// Register an aesop rule to a named rule set
    ///
    /// The rule set must be declared first with `declare_aesop_rule_set`.
    /// Returns false if the rule set doesn't exist.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn register_aesop_rule_to_set(&mut self, rule_set: &Name, rule: AesopRule) -> bool {
        if let Some(set) = self.aesop_rule_sets.get_mut(rule_set) {
            match rule.phase {
                AesopRulePhase::Safe => set.safe_rules.push(rule),
                AesopRulePhase::Unsafe => {
                    let pos = set
                        .unsafe_rules
                        .partition_point(|r| r.priority > rule.priority);
                    set.unsafe_rules.insert(pos, rule);
                }
                AesopRulePhase::Norm => set.norm_rules.push(rule),
            }
            true
        } else {
            false
        }
    }

    /// Get a named rule set
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_named_rule_set(&self, name: &Name) -> Option<&AesopRuleSet> {
        self.aesop_rule_sets.get(name)
    }

    /// Get all declared rule set names
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_declared_rule_sets(&self) -> impl Iterator<Item = &Name> {
        self.declared_aesop_rule_sets.iter()
    }

    /// Get rules from multiple rule sets combined
    ///
    /// Returns a combined AesopRuleSet with rules from all specified sets.
    /// If no sets are specified, returns the default rule set.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_combined_rule_sets(&self, rule_set_names: &[Name]) -> AesopRuleSet {
        if rule_set_names.is_empty() {
            return self.aesop_rules.clone();
        }

        let mut combined = AesopRuleSet::default();

        for name in rule_set_names {
            if let Some(set) = self.aesop_rule_sets.get(name) {
                combined.safe_rules.extend(set.safe_rules.iter().cloned());
                combined.norm_rules.extend(set.norm_rules.iter().cloned());

                // Merge unsafe rules maintaining sorted order
                for rule in &set.unsafe_rules {
                    let pos = combined
                        .unsafe_rules
                        .partition_point(|r| r.priority > rule.priority);
                    combined.unsafe_rules.insert(pos, rule.clone());
                }
            }
        }

        combined
    }

    // ========================================================================
    // Attribute Registry Methods (#1133)
    // ========================================================================

    /// Register a simp lemma.
    ///
    /// Bumps the environment generation counter: downstream caches (type
    /// checker caches, the elaborator's per-environment simp lemma-set cache)
    /// key on `generation()`, and a bare `attribute [simp] foo` mutates the
    /// observable simp set without any `add_decl`, so it must invalidate them.
    pub fn register_simp_lemma(&mut self, name: Name, priority: SimpPriority) {
        self.simp_lemmas
            .insert(name.clone(), SimpLemmaInfo { name, priority });
        self.generation += 1;
        self.simp_registry_revision += 1;
    }

    /// Revision counter of the simp-lemma registry: bumped only by
    /// [`Self::register_simp_lemma`] / [`Self::unregister_simp_lemma`],
    /// never by `add_decl`. See the field doc for the caching contract.
    pub fn simp_registry_revision(&self) -> u64 {
        self.simp_registry_revision
    }

    /// Check if a declaration is a registered simp lemma.
    pub fn is_simp_lemma(&self, name: &Name) -> bool {
        self.simp_lemmas.contains_key(name)
    }

    /// Get simp lemma info if registered.
    pub fn get_simp_lemma(&self, name: &Name) -> Option<&SimpLemmaInfo> {
        self.simp_lemmas.get(name)
    }

    /// Get all registered simp lemmas.
    pub fn get_simp_lemmas(&self) -> impl Iterator<Item = &SimpLemmaInfo> {
        self.simp_lemmas.values()
    }

    /// O(1) count of registered simp lemmas (cache-key component; avoids the
    /// O(L) iterator walk on every simp-set cache lookup).
    pub fn simp_lemma_count(&self) -> usize {
        self.simp_lemmas.len()
    }

    /// Remove a simp lemma registration.
    ///
    /// Returns `true` if a registration existed and was removed.
    pub fn unregister_simp_lemma(&mut self, name: &Name) -> bool {
        let removed = self.simp_lemmas.remove(name).is_some();
        if removed {
            self.generation += 1;
            self.simp_registry_revision += 1;
        }
        removed
    }

    /// Register an extern binding.
    pub fn register_extern(&mut self, decl_name: Name, extern_name: String) {
        self.extern_bindings.insert(decl_name, extern_name);
    }

    /// Get extern binding for a declaration.
    pub fn get_extern(&self, name: &Name) -> Option<&String> {
        self.extern_bindings.get(name)
    }

    /// Check if a declaration has an extern binding.
    pub fn is_extern(&self, name: &Name) -> bool {
        self.extern_bindings.contains_key(name)
    }

    /// Register an export binding.
    pub fn register_export(&mut self, decl_name: Name, export_name: String) {
        self.export_bindings.insert(decl_name, export_name);
    }

    /// Get export binding for a declaration.
    pub fn get_export(&self, name: &Name) -> Option<&String> {
        self.export_bindings.get(name)
    }

    /// Check if a declaration has an export binding.
    pub fn is_export(&self, name: &Name) -> bool {
        self.export_bindings.contains_key(name)
    }

    /// Register a deprecation.
    pub fn register_deprecated(&mut self, name: Name, message: Option<String>) {
        self.deprecated.insert(name, message);
    }

    /// Check if a declaration is deprecated.
    pub fn is_deprecated(&self, name: &Name) -> bool {
        self.deprecated.contains_key(name)
    }

    /// Get deprecation message for a declaration (if any).
    ///
    /// Returns `Some(Some(msg))` if deprecated with a message,
    /// `Some(None)` if deprecated without a message,
    /// `None` if not deprecated.
    pub fn get_deprecation_message(&self, name: &Name) -> Option<&Option<String>> {
        self.deprecated.get(name)
    }

    /// Register an inline hint.
    pub fn register_inline(&mut self, name: Name) {
        self.inline_hints.insert(name);
    }

    /// Check if a declaration has @[inline] attribute.
    pub fn is_inline(&self, name: &Name) -> bool {
        self.inline_hints.contains(name)
    }

    /// Register a noinline hint.
    pub fn register_noinline(&mut self, name: Name) {
        self.noinline_hints.insert(name);
    }

    /// Check if a declaration has @[noinline] attribute.
    pub fn is_noinline(&self, name: &Name) -> bool {
        self.noinline_hints.contains(name)
    }

    /// Register an always_inline hint.
    pub fn register_always_inline(&mut self, name: Name) {
        self.always_inline_hints.insert(name);
    }

    /// Check if a declaration has @[always_inline] attribute.
    pub fn is_always_inline(&self, name: &Name) -> bool {
        self.always_inline_hints.contains(name)
    }

    /// Register a specialize hint.
    pub fn register_specialize(&mut self, name: Name) {
        self.specialize_hints.insert(name);
    }

    /// Check if a declaration has @[specialize] attribute.
    pub fn is_specialize(&self, name: &Name) -> bool {
        self.specialize_hints.contains(name)
    }

    /// Register a macro_inline hint.
    pub fn register_macro_inline(&mut self, name: Name) {
        self.macro_inline_hints.insert(name);
    }

    /// Check if a declaration has @[macro_inline] attribute.
    pub fn is_macro_inline(&self, name: &Name) -> bool {
        self.macro_inline_hints.contains(name)
    }

    /// Register an inline_if_reduce hint.
    pub fn register_inline_if_reduce(&mut self, name: Name) {
        self.inline_if_reduce_hints.insert(name);
    }

    /// Check if a declaration has @[inline_if_reduce] attribute.
    pub fn is_inline_if_reduce(&self, name: &Name) -> bool {
        self.inline_if_reduce_hints.contains(name)
    }

    /// Register a nospecialize hint.
    pub fn register_nospecialize(&mut self, name: Name) {
        self.nospecialize_hints.insert(name);
    }

    /// Check if a declaration has @[nospecialize] attribute.
    pub fn is_nospecialize(&self, name: &Name) -> bool {
        self.nospecialize_hints.contains(name)
    }

    /// Register a csimp lemma.
    pub fn register_csimp(&mut self, name: Name) {
        self.csimp_lemmas.insert(name);
    }

    /// Check if a declaration is a csimp lemma.
    pub fn is_csimp(&self, name: &Name) -> bool {
        self.csimp_lemmas.contains(name)
    }

    /// Register a congr lemma.
    pub fn register_congr(&mut self, name: Name) {
        self.congr_lemmas.insert(name);
    }

    /// Check if a declaration is a congr lemma.
    pub fn is_congr(&self, name: &Name) -> bool {
        self.congr_lemmas.contains(name)
    }

    /// Register an ext lemma.
    pub fn register_ext(&mut self, name: Name) {
        self.ext_lemmas.insert(name);
    }

    /// Check if a declaration is an ext lemma.
    pub fn is_ext(&self, name: &Name) -> bool {
        self.ext_lemmas.contains(name)
    }

    /// Register a refl lemma.
    pub fn register_refl(&mut self, name: Name) {
        self.refl_lemmas.insert(name);
    }

    /// Check if a declaration is a refl lemma.
    pub fn is_refl(&self, name: &Name) -> bool {
        self.refl_lemmas.contains(name)
    }

    /// Register a symm lemma.
    pub fn register_symm(&mut self, name: Name) {
        self.symm_lemmas.insert(name);
    }

    /// Check if a declaration is a symm lemma.
    pub fn is_symm(&self, name: &Name) -> bool {
        self.symm_lemmas.contains(name)
    }

    // ========================================================================
    // Coercion registration (@[coe])
    // ========================================================================

    /// Register a declaration as a coercion.
    pub fn register_coercion(&mut self, name: Name) {
        self.coercion_decls.insert(name);
    }

    /// Check if a declaration is registered as a coercion.
    pub fn is_coercion(&self, name: &Name) -> bool {
        self.coercion_decls.contains(name)
    }

    // ========================================================================
    // Match pattern registration (@[match_pattern])
    // ========================================================================

    /// Register a declaration as usable in match patterns.
    pub fn register_match_pattern(&mut self, name: Name) {
        self.match_pattern_decls.insert(name);
    }

    /// Check if a declaration is registered as a match pattern.
    pub fn is_match_pattern(&self, name: &Name) -> bool {
        self.match_pattern_decls.contains(name)
    }

    // ========================================================================
    // Init function registration (@[init])
    // ========================================================================

    /// Register a declaration as an initialization function.
    pub fn register_init_fn(&mut self, name: Name) {
        self.init_fn_decls.insert(name);
    }

    /// Check if a declaration is registered as an init function.
    pub fn is_init_fn(&self, name: &Name) -> bool {
        self.init_fn_decls.contains(name)
    }

    // ========================================================================
    // Default instance registration (@[default_instance])
    // ========================================================================

    /// Register a declaration as a default instance (priority 0).
    pub fn register_default_instance(&mut self, name: Name) {
        self.default_instance_decls.insert(name);
    }

    /// Check if a declaration is registered as a default instance.
    pub fn is_default_instance(&self, name: &Name) -> bool {
        self.default_instance_decls.contains(name)
    }

    // ========================================================================
    // Derive handler registration (@[derive_handler])
    // ========================================================================

    /// Register a declaration as a derive handler for `class_name`.
    ///
    /// Re-registering the same `(class_name, handler_name)` pair is a no-op.
    pub fn register_derive_handler(&mut self, class_name: Name, handler_name: Name) {
        let handlers = self.derive_handlers.entry(class_name).or_default();
        if !handlers.iter().any(|name| name == &handler_name) {
            handlers.push(handler_name);
        }
    }

    /// Return all derive handlers registered for `class_name`, in registration order.
    pub fn get_derive_handlers(&self, class_name: &Name) -> Option<&[Name]> {
        self.derive_handlers.get(class_name).map(Vec::as_slice)
    }

    // ========================================================================
    // Declaration modifiers (private, protected, noncomputable)
    // ========================================================================

    /// Mark a declaration as `private` (not exported outside its module).
    pub fn mark_private(&mut self, name: Name) {
        self.private_decls.insert(name);
    }

    /// Check if a declaration is marked `private`.
    pub fn is_private(&self, name: &Name) -> bool {
        self.private_decls.contains(name)
    }

    /// Mark a declaration as `protected` (accessible only via fully qualified name).
    pub fn mark_protected(&mut self, name: Name) {
        self.protected_decls.insert(name);
    }

    /// Check if a declaration is marked `protected`.
    pub fn is_protected(&self, name: &Name) -> bool {
        self.protected_decls.contains(name)
    }

    /// Mark a declaration as `noncomputable` (no code generation).
    pub fn mark_noncomputable(&mut self, name: Name) {
        self.noncomputable_decls.insert(name);
    }

    /// Check if a declaration is marked `noncomputable`.
    pub fn is_noncomputable(&self, name: &Name) -> bool {
        self.noncomputable_decls.contains(name)
    }

    /// Mark a declaration as `partial` (non-terminating allowed).
    pub fn mark_partial(&mut self, name: Name) {
        self.partial_decls.insert(name);
    }

    /// Check if a declaration is marked `partial`.
    pub fn is_partial(&self, name: &Name) -> bool {
        self.partial_decls.contains(name)
    }

    /// Mark a declaration as `unsafe`.
    pub fn mark_unsafe(&mut self, name: Name) {
        self.unsafe_decls.insert(name);
    }

    /// Check if a declaration is marked `unsafe`.
    pub fn is_unsafe(&self, name: &Name) -> bool {
        self.unsafe_decls.contains(name)
    }

    /// Set the reducibility level for a constant.
    ///
    /// This allows post-declaration reducibility modification via attributes
    /// like `@[reducible]`, `@[semireducible]`, or `@[irreducible]`.
    ///
    /// Returns `true` if the constant was found and updated, `false` otherwise.
    pub(crate) fn set_reducibility(&mut self, name: &Name, reducibility: Reducibility) -> bool {
        if let Some(constant) = self.constants.get_mut(name) {
            constant.reducibility = reducibility;
            // Also update legacy is_reducible flag for compatibility
            constant.is_reducible = matches!(reducibility, Reducibility::Reducible);
            self.generation += 1;
            true
        } else {
            false
        }
    }

    /// Get the reducibility level for a constant.
    ///
    /// Returns `None` if the constant doesn't exist.
    pub fn get_reducibility(&self, name: &Name) -> Option<Reducibility> {
        self.constants.get(name).map(|c| c.reducibility)
    }
}
