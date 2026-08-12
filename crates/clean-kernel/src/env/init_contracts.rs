// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Contract metadata fields (init_name, required_symbols, expected_new_symbols)
// and the ClosureAuditResult.contract_id field are structural parts of the
// contract model used by W1/W3 in Steps 2-3. Suppress until fully wired.
//! Machine-checked dependency closure contracts for `init_*` functions.
//!
//! Each `InitContract` declares:
//! - the initializer it covers,
//! - its prerequisite contracts (dependency edges),
//! - the symbols that must be present before the initializer runs,
//! - (optionally) the new symbols the initializer is expected to add.
//!
//! A closure verifier in tests builds a fresh `Environment`, executes
//! contracts in topological order, and checks that every constant
//! referenced by newly-added declarations was either already present
//! or added by the same initializer.
//!
//! See `designs/2026-02-11-init-dependency-closure-contract.md` and #1461.

use crate::env::{EnvError, Environment};
use crate::name::Name;
use std::collections::{HashMap, HashSet, VecDeque};

/// Stable identifier for one init contract.
///
/// Uses a string tag so contracts are self-documenting in test output.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InitContractId(pub &'static str);

impl std::fmt::Display for InitContractId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

/// A machine-readable dependency contract for one `init_*` function.
pub struct InitContract {
    /// Stable identifier for this contract.
    pub id: InitContractId,
    /// Human-readable name of the init function (e.g. `"init_topology_subspace"`).
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub init_name: &'static str,
    /// Prerequisite contract ids that must be executed before this one.
    pub dependencies: Vec<InitContractId>,
    /// Constant names that must be present in the environment before running
    /// this initializer (beyond what dependencies provide).
    pub required_symbols: Vec<&'static str>,
    /// If set, the exact new constant names the initializer is expected to add.
    /// Empty means "don't check exact additions, only check closure".
    pub expected_new_symbols: Vec<&'static str>,
    /// The init function to call on `Environment`.
    pub init_fn: fn(&mut Environment) -> Result<(), EnvError>,
}

/// A registry of init contracts with graph validation and closure checking.
pub struct InitContractRegistry {
    contracts: Vec<InitContract>,
    id_index: HashMap<InitContractId, usize>,
}

/// Result of a dependency closure audit for one contract.
#[derive(Debug)]
pub struct ClosureAuditResult {
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub contract_id: InitContractId,
    /// Constants that were referenced by newly-added declarations but were
    /// not present in the environment (missing dependencies).
    pub missing_symbols: Vec<String>,
    /// Constants that were newly added by the initializer.
    pub added_symbols: Vec<String>,
    /// Whether the closure check passed (no missing symbols).
    pub passed: bool,
}

impl InitContractRegistry {
    /// Build a registry from a list of contracts.
    ///
    /// Does not validate the graph — call `validate_graph` for that.
    pub(crate) fn new(contracts: Vec<InitContract>) -> Self {
        let id_index: HashMap<InitContractId, usize> = contracts
            .iter()
            .enumerate()
            .map(|(i, c)| (c.id.clone(), i))
            .collect();
        Self {
            contracts,
            id_index,
        }
    }

    /// Check that all dependency references resolve to known contract ids.
    ///
    /// Returns a list of `(contract_id, unknown_dep_id)` pairs for any
    /// unresolved references.
    pub(crate) fn find_unknown_deps(&self) -> Vec<(InitContractId, InitContractId)> {
        let mut unknown = Vec::new();
        for contract in &self.contracts {
            for dep in &contract.dependencies {
                if !self.id_index.contains_key(dep) {
                    unknown.push((contract.id.clone(), dep.clone()));
                }
            }
        }
        unknown
    }

    /// Find duplicate contract identifiers.
    ///
    /// Duplicate IDs are invalid because they make dependency resolution and
    /// target lookup ambiguous.
    pub(crate) fn find_duplicate_ids(&self) -> Vec<InitContractId> {
        let mut counts: HashMap<InitContractId, usize> = HashMap::new();
        for contract in &self.contracts {
            *counts.entry(contract.id.clone()).or_insert(0) += 1;
        }

        let mut duplicates: Vec<InitContractId> = counts
            .into_iter()
            .filter_map(|(id, count)| if count > 1 { Some(id) } else { None })
            .collect();
        duplicates.sort_by_key(|id| id.0);
        duplicates
    }

    /// Check that the contract dependency graph is acyclic.
    ///
    /// Uses Kahn's algorithm. Returns `Ok(topological_order)` on success,
    /// or `Err(cycle_members)` listing contract ids involved in cycles.
    pub(crate) fn topological_order(&self) -> Result<Vec<InitContractId>, Vec<InitContractId>> {
        let n = self.contracts.len();
        let mut in_degree: Vec<usize> = vec![0; n];
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

        for (i, contract) in self.contracts.iter().enumerate() {
            for dep in &contract.dependencies {
                if let Some(&dep_idx) = self.id_index.get(dep) {
                    adj[dep_idx].push(i);
                    in_degree[i] += 1;
                }
            }
        }

        let mut queue: VecDeque<usize> = VecDeque::new();
        for (i, &deg) in in_degree.iter().enumerate() {
            if deg == 0 {
                queue.push_back(i);
            }
        }

        let mut order = Vec::with_capacity(n);
        while let Some(idx) = queue.pop_front() {
            order.push(self.contracts[idx].id.clone());
            for &next in &adj[idx] {
                in_degree[next] -= 1;
                if in_degree[next] == 0 {
                    queue.push_back(next);
                }
            }
        }

        if order.len() == n {
            Ok(order)
        } else {
            // Remaining nodes with in_degree > 0 are in cycles.
            let cycle_members: Vec<InitContractId> = in_degree
                .iter()
                .enumerate()
                .filter(|(_, &deg)| deg > 0)
                .map(|(i, _)| self.contracts[i].id.clone())
                .collect();
            Err(cycle_members)
        }
    }

    /// Run a full dependency-closure audit for a single contract.
    ///
    /// 1. Build a fresh `Environment::new()`.
    /// 2. Execute prerequisite contracts in topological order.
    /// 3. Snapshot constant set before target init.
    /// 4. Run target init function.
    /// 5. Diff newly-added constants.
    /// 6. For each new constant, collect referenced symbols from `type_` and `value`.
    /// 7. Enforce `required_symbols` are present before running the target init.
    /// 8. Report any referenced symbol not in (pre-snapshot ∪ newly-added ∪ allowlist).
    /// 9. If `expected_new_symbols` is set, enforce exact added-symbol match.
    pub(crate) fn audit_closure(
        &self,
        target_id: &InitContractId,
        primitive_allowlist: &HashSet<String>,
    ) -> Result<ClosureAuditResult, String> {
        let duplicate_ids = self.find_duplicate_ids();
        if !duplicate_ids.is_empty() {
            return Err(format!("duplicate contract ids: {:?}", duplicate_ids));
        }

        let unknown_deps = self.find_unknown_deps();
        if !unknown_deps.is_empty() {
            return Err(format!("unknown dependency ids: {:?}", unknown_deps));
        }

        let target_idx = self
            .id_index
            .get(target_id)
            .ok_or_else(|| format!("unknown contract id: {target_id}"))?;

        // Compute transitive dependency set via BFS.
        let dep_order = self.transitive_dep_order(*target_idx)?;

        // Build fresh environment and execute dependencies.
        let mut env = Environment::new();

        for dep_idx in &dep_order {
            let contract = &self.contracts[*dep_idx];
            (contract.init_fn)(&mut env)
                .map_err(|e| format!("dependency {} failed: {e:?}", contract.id))?;
        }

        // Snapshot constants before target init.
        let pre_constants: HashSet<String> = env.constants().map(|c| c.name.to_string()).collect();

        let target = &self.contracts[*target_idx];

        // Enforce contract-level preconditions before running the target init.
        let missing_required: Vec<String> = target
            .required_symbols
            .iter()
            .filter(|sym| !pre_constants.contains(**sym) && !primitive_allowlist.contains(**sym))
            .map(|sym| (*sym).to_string())
            .collect();
        if !missing_required.is_empty() {
            return Err(format!(
                "target {} missing required symbols before init: {:?}",
                target.id, missing_required
            ));
        }

        // Run target init.
        (target.init_fn)(&mut env).map_err(|e| format!("target {} failed: {e:?}", target.id))?;

        // Diff: find newly added constants.
        let post_constants: HashSet<String> = env.constants().map(|c| c.name.to_string()).collect();

        let added: HashSet<String> = post_constants.difference(&pre_constants).cloned().collect();

        if !target.expected_new_symbols.is_empty() {
            let expected: HashSet<String> = target
                .expected_new_symbols
                .iter()
                .map(|s| s.to_string())
                .collect();

            let mut missing_expected: Vec<String> = expected.difference(&added).cloned().collect();
            missing_expected.sort();
            let mut unexpected_added: Vec<String> = added.difference(&expected).cloned().collect();
            unexpected_added.sort();

            if !missing_expected.is_empty() || !unexpected_added.is_empty() {
                return Err(format!(
                    "target {} expected_new_symbols mismatch: missing {:?}, unexpected {:?}",
                    target.id, missing_expected, unexpected_added
                ));
            }
        }

        // For each new constant, collect all referenced symbols.
        let mut missing = Vec::new();
        for const_name_str in &added {
            let const_name = Name::from_string(const_name_str);
            if let Some(info) = env.get_const(&const_name) {
                let mut refs = info.type_.collect_constants();
                if let Some(val) = &info.value {
                    let val_refs = val.collect_constants();
                    for r in val_refs {
                        refs.insert(r);
                    }
                }

                for ref_name in &refs {
                    let ref_str = ref_name.to_string();
                    if !pre_constants.contains(&ref_str)
                        && !added.contains(&ref_str)
                        && !primitive_allowlist.contains(&ref_str)
                    {
                        let msg =
                            format!("{const_name_str} references {ref_str} which is not in scope");
                        if !missing.contains(&msg) {
                            missing.push(msg);
                        }
                    }
                }
            }
        }

        missing.sort();
        let mut added_sorted: Vec<String> = added.into_iter().collect();
        added_sorted.sort();

        Ok(ClosureAuditResult {
            contract_id: target_id.clone(),
            missing_symbols: missing.clone(),
            added_symbols: added_sorted,
            passed: missing.is_empty(),
        })
    }

    /// Compute transitive dependency indices in topological order for a target.
    fn transitive_dep_order(&self, target_idx: usize) -> Result<Vec<usize>, String> {
        // BFS to find all transitive deps as a set.
        let mut visited: HashSet<usize> = HashSet::new();
        let mut queue: VecDeque<usize> = VecDeque::new();

        for dep_id in &self.contracts[target_idx].dependencies {
            if let Some(&dep_idx) = self.id_index.get(dep_id) {
                if visited.insert(dep_idx) {
                    queue.push_back(dep_idx);
                }
            }
        }

        while let Some(idx) = queue.pop_front() {
            for dep_id in &self.contracts[idx].dependencies {
                if let Some(&dep_idx) = self.id_index.get(dep_id) {
                    if visited.insert(dep_idx) {
                        queue.push_back(dep_idx);
                    }
                }
            }
        }

        if visited.is_empty() {
            return Ok(Vec::new());
        }

        // Use whole-graph topological order and filter to dependency set.
        // This preserves deterministic execution order.
        let global_order = self.topological_order().map_err(|cycle| {
            let cycle_ids: Vec<&str> = cycle.iter().map(|id| id.0).collect();
            format!(
                "cycle in transitive deps of {}: {:?}",
                self.contracts[target_idx].id, cycle_ids
            )
        })?;

        let order: Vec<usize> = global_order
            .into_iter()
            .filter_map(|id| self.id_index.get(&id).copied())
            .filter(|idx| visited.contains(idx))
            .collect();

        if order.len() != visited.len() {
            return Err(format!(
                "failed to order all transitive deps of {}",
                self.contracts[target_idx].id
            ));
        }

        Ok(order)
    }

    /// Get a contract by id.
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn get(&self, id: &InitContractId) -> Option<&InitContract> {
        self.id_index.get(id).map(|&idx| &self.contracts[idx])
    }

    /// Number of contracts in the registry.
    pub(crate) fn len(&self) -> usize {
        self.contracts.len()
    }

    /// Whether the registry is empty.
    pub(crate) fn is_empty(&self) -> bool {
        self.contracts.is_empty()
    }
}

/// Build the default primitive allowlist.
///
/// These are constants guaranteed to exist in `Environment::new()` (post-sorry)
/// or are fundamental type-theory primitives that don't require explicit init.
pub(crate) fn default_primitive_allowlist() -> HashSet<String> {
    [
        // Sort/Prop/Type are built-in, not constants, but some references
        // resolve to these. Keep them in the allowlist defensively.
        "Prop",
        "Type",
        "Sort", // sorry is initialized by Environment::new()
        "sorry",
        "sorryAx",
        // Heterogeneous equality is foundational and initialized right after
        // `init_eq` (`init_prelude_core`), so it is universally available like
        // `Eq`'s built-ins. Lean v4.30's `noConfusion` convention references
        // `HEq`/`HEq.refl`/`eq_of_heq` in the generated `noConfusion` of every
        // parameterized inductive (per the dependent-field/major HEq premises),
        // so every contract that builds such an inductive transitively pulls
        // them in. They are provably in scope at build time
        // (`Environment::with_prelude()` succeeds), so allowlist them here
        // rather than threading an `init_heq` edge through ~13 contracts.
        "HEq",
        "HEq.refl",
        "eq_of_heq",
        // True/False are initialized by init_true_false, not Environment::new().
        // Keep them out of the primitive allowlist so dependency edges are enforced.
    ]
    .iter()
    .map(|s| s.to_string())
    .collect()
}

// --- Wave 1 contract definitions ---

/// Build Wave 1 contracts for #1461.
///
/// Covers the active failing symbols: Nat.le, Nat.lt, Subtype, Iff, Or.
/// These contracts are the initial set; W1/W3 will add closure tests on top.
///
/// Key notes on which init provides which constants:
/// - `init_le()` provides LE, LE.le, LE.mk, Nat.le, Nat.le.refl, Nat.le.step, instLENat
/// - `init_lt()` provides LT, LT.lt, LT.mk, Nat.lt, instLTNat (depends on init_le)
/// - `init_classical()` provides Nonempty, Classical.choice, Classical.em, Classical.byContradiction (depends on true_false, or)
/// - `init_or()` is standalone, provides Or, Or.inl, Or.inr, Or.rec
/// - `init_iff()` is standalone (no deps), provides Iff, Iff.intro
/// - `init_and()` is standalone, provides And, And.intro
pub(crate) fn wave1_contracts() -> Vec<InitContract> {
    vec![
        // --- Core prerequisites (many inits depend on these) ---
        InitContract {
            id: InitContractId("eq"),
            init_name: "init_eq",
            dependencies: vec![],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_eq(),
        },
        InitContract {
            id: InitContractId("true_false"),
            init_name: "init_true_false",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec!["Eq"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_true_false(),
        },
        InitContract {
            id: InitContractId("and"),
            init_name: "init_and",
            dependencies: vec![],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_and(),
        },
        InitContract {
            id: InitContractId("or"),
            init_name: "init_or",
            dependencies: vec![],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_or(),
        },
        InitContract {
            id: InitContractId("classical"),
            init_name: "init_classical",
            dependencies: vec![InitContractId("true_false"), InitContractId("or")],
            required_symbols: vec!["True", "False", "Or"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_classical(),
        },
        InitContract {
            id: InitContractId("iff"),
            init_name: "init_iff",
            dependencies: vec![],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_iff(),
        },
        InitContract {
            id: InitContractId("nat"),
            init_name: "init_nat",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat(),
        },
        InitContract {
            id: InitContractId("exists"),
            init_name: "init_exists",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_exists(),
        },
        InitContract {
            id: InitContractId("subtype"),
            init_name: "init_subtype",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_subtype(),
        },
        // --- Order prerequisites ---
        // init_le provides: LE, LE.le, LE.mk, Nat.le, Nat.le.refl, Nat.le.step, instLENat
        InitContract {
            id: InitContractId("le"),
            init_name: "init_le",
            dependencies: vec![InitContractId("nat")],
            required_symbols: vec!["Nat"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_le(),
        },
        // init_lt provides: LT, LT.lt, LT.mk, Nat.lt, instLTNat (depends on init_le)
        InitContract {
            id: InitContractId("lt"),
            init_name: "init_lt",
            dependencies: vec![InitContractId("le")],
            required_symbols: vec!["Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_lt(),
        },
        InitContract {
            id: InitContractId("preorder"),
            init_name: "init_preorder",
            dependencies: vec![InitContractId("le"), InitContractId("lt")],
            required_symbols: vec!["LE", "LT", "LE.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_preorder(),
        },
        InitContract {
            id: InitContractId("partial_order"),
            init_name: "init_partial_order",
            dependencies: vec![
                InitContractId("preorder"),
                InitContractId("lt"),
                InitContractId("eq"),
            ],
            required_symbols: vec!["Preorder", "Eq"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_partial_order(),
        },
        InitContract {
            id: InitContractId("linear_order"),
            init_name: "init_linear_order",
            dependencies: vec![InitContractId("partial_order"), InitContractId("classical")],
            required_symbols: vec!["PartialOrder", "Or"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_linear_order(),
        },
        InitContract {
            id: InitContractId("decidable"),
            init_name: "init_decidable",
            dependencies: vec![InitContractId("true_false")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_decidable(),
        },
        InitContract {
            id: InitContractId("reflexive"),
            init_name: "init_reflexive",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_reflexive(),
        },
        InitContract {
            id: InitContractId("irrefl"),
            init_name: "init_irrefl",
            dependencies: vec![InitContractId("true_false")],
            required_symbols: vec!["False"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_irrefl(),
        },
        InitContract {
            id: InitContractId("trans"),
            init_name: "init_trans",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_trans(),
        },
        InitContract {
            id: InitContractId("antisymm"),
            init_name: "init_antisymm",
            dependencies: vec![InitContractId("eq")],
            required_symbols: vec!["Eq"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_antisymm(),
        },
        InitContract {
            id: InitContractId("asymm"),
            init_name: "init_asymm",
            dependencies: vec![InitContractId("true_false")],
            required_symbols: vec!["False"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_asymm(),
        },
        // --- Nat-order intermediate contracts ---
        InitContract {
            id: InitContractId("nat_preorder"),
            init_name: "init_nat_preorder",
            dependencies: vec![
                InitContractId("preorder"),
                InitContractId("le"),
                InitContractId("lt"),
            ],
            required_symbols: vec!["Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_preorder(),
        },
        InitContract {
            id: InitContractId("nat_partial_order"),
            init_name: "init_nat_partial_order",
            dependencies: vec![
                InitContractId("nat_preorder"),
                InitContractId("partial_order"),
            ],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_partial_order(),
        },
        // --- Nat-order target contracts (Wave 1 / Step 3) ---
        // These contracts verify closure for functions that reference Nat.le/Nat.lt.
        // Nat.le is provided by init_le, Nat.lt by init_lt.
        InitContract {
            id: InitContractId("nat_le_reflexive"),
            init_name: "init_nat_le_reflexive",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("reflexive"),
            ],
            required_symbols: vec!["Nat", "Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_le_reflexive(),
        },
        InitContract {
            id: InitContractId("nat_lt_irrefl"),
            init_name: "init_nat_lt_irrefl",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("lt"),
                InitContractId("irrefl"),
            ],
            required_symbols: vec!["Nat", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_irrefl(),
        },
        InitContract {
            id: InitContractId("nat_lt_asymm"),
            init_name: "init_nat_lt_asymm",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("lt"),
                InitContractId("asymm"),
            ],
            required_symbols: vec!["Nat", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_asymm(),
        },
        InitContract {
            id: InitContractId("nat_lt_trans"),
            init_name: "init_nat_lt_trans",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("lt"),
                InitContractId("trans"),
            ],
            required_symbols: vec!["Nat", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_trans(),
        },
        InitContract {
            id: InitContractId("nat_linear_order"),
            init_name: "init_nat_linear_order",
            dependencies: vec![
                InitContractId("nat_partial_order"),
                InitContractId("linear_order"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_linear_order(),
        },
        InitContract {
            id: InitContractId("nat_decidable_ord"),
            init_name: "init_nat_decidable_ord",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("decidable"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_decidable_ord(),
        },
        // --- Topology target contracts (Wave 1 / Step 2) ---
        // Note: topology contracts require additional init functions.
        // W3 will add full topology entries in Step 2.
        InitContract {
            id: InitContractId("topological_space"),
            init_name: "init_topological_space",
            dependencies: vec![
                InitContractId("and"),
                InitContractId("exists"),
                InitContractId("true_false"),
                InitContractId("iff"),
            ],
            required_symbols: vec!["True", "False", "And", "Exists", "Iff"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_topological_space(),
        },
        InitContract {
            id: InitContractId("topology_continuous"),
            init_name: "init_topology_continuous",
            dependencies: vec![InitContractId("topological_space"), InitContractId("iff")],
            required_symbols: vec!["TopologicalSpace", "IsOpen", "Iff"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_topology_continuous(),
        },
        InitContract {
            id: InitContractId("topology_subspace"),
            init_name: "init_topology_subspace",
            dependencies: vec![
                InitContractId("topology_continuous"),
                InitContractId("topological_space"),
                InitContractId("subtype"),
                InitContractId("eq"),
                InitContractId("exists"),
            ],
            required_symbols: vec!["Subtype", "TopologicalSpace"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_topology_subspace(),
        },
        InitContract {
            id: InitContractId("topology_higher_homotopy"),
            init_name: "init_topology_higher_homotopy",
            dependencies: vec![
                InitContractId("topological_space"),
                InitContractId("eq"),
                InitContractId("nat"),
                InitContractId("lt"),
            ],
            required_symbols: vec!["TopologicalSpace", "Nat", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_topology_higher_homotopy(),
        },
        // --- Wave 2: Nat-order extended contracts ---
        // These cover init functions that directly reference Nat.le/Nat.lt
        // plus Iff/Or, extending the #1461 closure coverage beyond Wave 1.
        InitContract {
            id: InitContractId("nat_le_antisymm"),
            init_name: "init_nat_le_antisymm",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("eq"),
                InitContractId("antisymm"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Eq"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_le_antisymm(),
        },
        InitContract {
            id: InitContractId("nat_le_trans"),
            init_name: "init_nat_le_trans",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("trans"),
            ],
            required_symbols: vec!["Nat", "Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_le_trans(),
        },
        InitContract {
            id: InitContractId("strict_order"),
            init_name: "init_strict_order",
            dependencies: vec![InitContractId("irrefl"), InitContractId("trans")],
            required_symbols: vec!["Irrefl", "Trans"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_strict_order(),
        },
        InitContract {
            id: InitContractId("nat_lt_strict_order"),
            init_name: "init_nat_lt_strict_order",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("lt"),
                InitContractId("strict_order"),
                InitContractId("nat_lt_irrefl"),
                InitContractId("nat_lt_trans"),
            ],
            required_symbols: vec!["Nat", "Nat.lt", "StrictOrder"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_strict_order(),
        },
        InitContract {
            id: InitContractId("nat_trans_lt_le_lt"),
            init_name: "init_nat_trans_lt_le_lt",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("trans"),
                InitContractId("le"),
                InitContractId("lt"),
            ],
            required_symbols: vec!["Nat", "Nat.lt", "Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_trans_lt_le_lt(),
        },
        InitContract {
            id: InitContractId("nat_trans_le_lt_lt"),
            init_name: "init_nat_trans_le_lt_lt",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("trans"),
                InitContractId("le"),
                InitContractId("lt"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_trans_le_lt_lt(),
        },
        InitContract {
            id: InitContractId("nat_trans_lt_lt_le"),
            init_name: "init_nat_trans_lt_lt_le",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("trans"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("nat_lt_trans"),
            ],
            required_symbols: vec!["Nat", "Nat.lt", "Nat.le", "Nat.lt_trans"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_trans_lt_lt_le(),
        },
        // Iff/Or contracts — these reference active failure symbols Iff and Or.
        InitContract {
            id: InitContractId("nat_not_lt_le"),
            init_name: "init_nat_not_lt_le",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("iff"),
                InitContractId("true_false"),
            ],
            required_symbols: vec!["Nat", "Nat.lt", "Nat.le", "Iff", "False"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_not_lt_le(),
        },
        InitContract {
            id: InitContractId("nat_succ_lt"),
            init_name: "init_nat_succ_lt",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("iff"),
            ],
            required_symbols: vec!["Nat", "Nat.lt", "Nat.le", "Iff"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_succ_lt(),
        },
        InitContract {
            id: InitContractId("nat_lt_or_eq_of_le"),
            init_name: "init_nat_lt_or_eq_of_le",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("eq"),
                InitContractId("classical"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt", "Or"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_or_eq_of_le(),
        },
        InitContract {
            id: InitContractId("nat_lt_of_le_of_ne"),
            init_name: "init_nat_lt_of_le_of_ne",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("eq"),
                InitContractId("true_false"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt", "False"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_of_le_of_ne(),
        },
        InitContract {
            id: InitContractId("nat_lt_trichotomy"),
            init_name: "init_nat_lt_trichotomy",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("lt"),
                InitContractId("eq"),
                InitContractId("classical"),
            ],
            required_symbols: vec!["Nat", "Nat.lt", "Or"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_lt_trichotomy(),
        },
        InitContract {
            id: InitContractId("nat_succ_base"),
            init_name: "init_nat_succ_base",
            dependencies: vec![InitContractId("nat"), InitContractId("le")],
            required_symbols: vec!["Nat", "Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_succ_base(),
        },
        // Arithmetic order contracts — depend on nat_linear_order (transitively blocked).
        InitContract {
            id: InitContractId("nat_add_ord"),
            init_name: "init_nat_add_ord",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("nat_linear_order"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_add_ord(),
        },
        InitContract {
            id: InitContractId("nat_mul_ord"),
            init_name: "init_nat_mul_ord",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("nat_linear_order"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_mul_ord(),
        },
        InitContract {
            id: InitContractId("nat_sub_ord"),
            init_name: "init_nat_sub_ord",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("nat_linear_order"),
            ],
            required_symbols: vec!["Nat", "Nat.le"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_sub_ord(),
        },
        InitContract {
            id: InitContractId("nat_pow_ord"),
            init_name: "init_nat_pow_ord",
            dependencies: vec![
                InitContractId("nat"),
                InitContractId("le"),
                InitContractId("lt"),
                InitContractId("nat_linear_order"),
            ],
            required_symbols: vec!["Nat", "Nat.le", "Nat.lt"],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_nat_pow_ord(),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contract_id_display() {
        let id = InitContractId("nat_le");
        assert_eq!(id.to_string(), "nat_le");
    }

    #[test]
    fn test_empty_registry() {
        let reg = InitContractRegistry::new(vec![]);
        assert!(reg.is_empty());
        assert_eq!(reg.len(), 0);
        assert!(reg.find_unknown_deps().is_empty());
        assert!(reg.topological_order().unwrap().is_empty());
    }

    #[test]
    fn test_single_contract_no_deps() {
        let reg = InitContractRegistry::new(vec![InitContract {
            id: InitContractId("test"),
            init_name: "test",
            dependencies: vec![],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_eq(),
        }]);

        assert_eq!(reg.len(), 1);
        assert!(reg.find_unknown_deps().is_empty());
        let order = reg.topological_order().unwrap();
        assert_eq!(order, vec![InitContractId("test")]);
    }

    #[test]
    fn test_unknown_dep_detection() {
        let reg = InitContractRegistry::new(vec![InitContract {
            id: InitContractId("child"),
            init_name: "child",
            dependencies: vec![InitContractId("nonexistent_parent")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_eq(),
        }]);

        let unknown = reg.find_unknown_deps();
        assert_eq!(unknown.len(), 1);
        assert_eq!(unknown[0].0, InitContractId("child"));
        assert_eq!(unknown[0].1, InitContractId("nonexistent_parent"));
    }

    #[test]
    fn test_audit_closure_rejects_unknown_dependency_ids() {
        let reg = InitContractRegistry::new(vec![InitContract {
            id: InitContractId("child"),
            init_name: "child",
            dependencies: vec![InitContractId("nonexistent_parent")],
            required_symbols: vec![],
            expected_new_symbols: vec![],
            init_fn: |env| env.init_eq(),
        }]);

        let allowlist = default_primitive_allowlist();
        let err = reg
            .audit_closure(&InitContractId("child"), &allowlist)
            .expect_err("audit should fail when contract dependencies are unknown");
        assert!(err.contains("unknown dependency ids"), "{err}");
        assert!(err.contains("nonexistent_parent"), "{err}");
    }

    #[test]
    fn test_default_primitive_allowlist_excludes_true_false() {
        let allowlist = default_primitive_allowlist();
        assert!(
            !allowlist.contains("True"),
            "True must come from init_true_false"
        );
        assert!(
            !allowlist.contains("False"),
            "False must come from init_true_false"
        );
    }

    #[test]
    fn test_duplicate_id_detection() {
        let reg = InitContractRegistry::new(vec![
            InitContract {
                id: InitContractId("dup"),
                init_name: "dup_a",
                dependencies: vec![],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
            InitContract {
                id: InitContractId("dup"),
                init_name: "dup_b",
                dependencies: vec![],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
        ]);

        let duplicates = reg.find_duplicate_ids();
        assert_eq!(duplicates, vec![InitContractId("dup")]);
    }

    #[test]
    fn test_cycle_detection() {
        let reg = InitContractRegistry::new(vec![
            InitContract {
                id: InitContractId("a"),
                init_name: "a",
                dependencies: vec![InitContractId("b")],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
            InitContract {
                id: InitContractId("b"),
                init_name: "b",
                dependencies: vec![InitContractId("a")],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
        ]);

        assert!(reg.find_unknown_deps().is_empty());
        let cycle = reg
            .topological_order()
            .expect_err("mutual dependency should produce a cycle error");
        assert_eq!(cycle.len(), 2);
    }

    #[test]
    fn test_linear_chain_topo_order() {
        let reg = InitContractRegistry::new(vec![
            InitContract {
                id: InitContractId("c"),
                init_name: "c",
                dependencies: vec![InitContractId("b")],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
            InitContract {
                id: InitContractId("a"),
                init_name: "a",
                dependencies: vec![],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
            InitContract {
                id: InitContractId("b"),
                init_name: "b",
                dependencies: vec![InitContractId("a")],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
        ]);

        let order = reg.topological_order().unwrap();
        // a must come before b, b before c
        let pos_a = order.iter().position(|x| x.0 == "a").unwrap();
        let pos_b = order.iter().position(|x| x.0 == "b").unwrap();
        let pos_c = order.iter().position(|x| x.0 == "c").unwrap();
        assert!(pos_a < pos_b);
        assert!(pos_b < pos_c);
    }

    #[test]
    fn test_audit_closure_enforces_required_symbols() {
        let reg = InitContractRegistry::new(vec![InitContract {
            id: InitContractId("required_guard"),
            init_name: "required_guard",
            dependencies: vec![],
            required_symbols: vec!["Definitely.Missing.Symbol"],
            expected_new_symbols: vec![],
            init_fn: |_env| Ok(()),
        }]);

        let allowlist = default_primitive_allowlist();
        let err = reg
            .audit_closure(&InitContractId("required_guard"), &allowlist)
            .expect_err("audit should fail when required symbols are missing");
        assert!(err.contains("missing required symbols"), "{err}");
        assert!(err.contains("Definitely.Missing.Symbol"), "{err}");
    }

    #[test]
    fn test_audit_closure_allows_required_symbol_from_allowlist() {
        let reg = InitContractRegistry::new(vec![InitContract {
            id: InitContractId("required_allowlisted"),
            init_name: "required_allowlisted",
            dependencies: vec![],
            required_symbols: vec!["Prop"],
            expected_new_symbols: vec![],
            init_fn: |_env| Ok(()),
        }]);

        let allowlist = default_primitive_allowlist();
        let result = reg
            .audit_closure(&InitContractId("required_allowlisted"), &allowlist)
            .expect("allowlisted required symbol should pass");
        assert!(result.passed);
    }

    #[test]
    fn test_audit_closure_enforces_expected_new_symbols() {
        let reg = InitContractRegistry::new(vec![InitContract {
            id: InitContractId("expected_guard"),
            init_name: "expected_guard",
            dependencies: vec![],
            required_symbols: vec![],
            expected_new_symbols: vec!["Eq"],
            init_fn: |_env| Ok(()),
        }]);

        let allowlist = default_primitive_allowlist();
        let err = reg
            .audit_closure(&InitContractId("expected_guard"), &allowlist)
            .expect_err("audit should fail when expected additions do not match");
        assert!(err.contains("expected_new_symbols mismatch"), "{err}");
        assert!(err.contains("Eq"), "{err}");
    }

    #[test]
    fn test_audit_closure_rejects_duplicate_ids() {
        let reg = InitContractRegistry::new(vec![
            InitContract {
                id: InitContractId("dup"),
                init_name: "dup_a",
                dependencies: vec![],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
            InitContract {
                id: InitContractId("dup"),
                init_name: "dup_b",
                dependencies: vec![],
                required_symbols: vec![],
                expected_new_symbols: vec![],
                init_fn: |env| env.init_eq(),
            },
        ]);

        let allowlist = default_primitive_allowlist();
        let err = reg
            .audit_closure(&InitContractId("dup"), &allowlist)
            .expect_err("audit should fail when contract ids are duplicated");
        assert!(err.contains("duplicate contract ids"), "{err}");
    }
}
