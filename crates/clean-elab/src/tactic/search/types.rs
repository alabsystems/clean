// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! AND-OR tree types and search tree for proof search.

use std::cmp::Ordering;
use std::collections::HashMap;

use crate::tactic::Goal;

// =============================================================================
// AND-OR Tree Types for Aesop Search
// =============================================================================

/// Unique identifier for goals in the search tree
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GoalId(pub(super) u64);

/// Unique identifier for rule applications
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RappId(pub(super) u64);

/// Success probability (0.0 to 1.0)
///
/// Aesop uses this for best-first ordering: higher probability goals are
/// explored first. This enables finding proofs faster by prioritizing
/// more promising branches.
#[derive(Debug, Clone, Copy)]
pub struct Percent(f64);

impl Percent {
    /// 100% success probability
    /// ENSURES: Returns a probability value equal to `1.0`.
    pub fn hundred() -> Self {
        Percent(1.0)
    }

    /// Create from a value (clamped to 0.0-1.0)
    /// ENSURES: Returned value is in the closed interval `[0.0, 1.0]`.
    /// ENSURES: Values below `0.0` clamp to `0.0`; values above `1.0` clamp to `1.0`.
    pub fn from_f64(v: f64) -> Self {
        Percent(v.clamp(0.0, 1.0))
    }
}

impl std::ops::Mul for Percent {
    type Output = Self;

    /// Combine probabilities (product for independent events)
    fn mul(self, other: Self) -> Self {
        Percent(self.0 * other.0)
    }
}

impl PartialEq for Percent {
    fn eq(&self, other: &Self) -> bool {
        (self.0 - other.0).abs() < f64::EPSILON
    }
}

impl Eq for Percent {}

impl PartialOrd for Percent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Percent {
    fn cmp(&self, other: &Self) -> Ordering {
        // Safe ordering for f64 in [0,1] range (no NaN/inf)
        self.0.partial_cmp(&other.0).unwrap_or(Ordering::Equal)
    }
}

/// State of a goal in the search tree
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GoalState {
    /// Goal hasn't been proven or shown unprovable yet
    Unknown,
    /// Goal was proven during normalization phase
    ProvenByNormalization,
    /// Goal was proven by a child rule application
    ProvenByRuleApplication(RappId),
    /// Goal is unprovable (all rules exhausted, all rapps failed)
    Unprovable,
}

impl GoalState {
    /// Check if the goal has been proven
    /// ENSURES: Returns `true` for normalization- or rapp-proven goals, and `false` otherwise.
    pub fn is_proven(&self) -> bool {
        matches!(
            self,
            Self::ProvenByNormalization | Self::ProvenByRuleApplication(_)
        )
    }

    /// Check if the goal is still active (not yet proven or shown unprovable)
    /// ENSURES: Returns `true` exactly when the state is `Unknown`.
    pub fn is_active(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

/// State of a rule application node
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeState {
    /// Rapp hasn't been fully evaluated yet
    Unknown,
    /// All subgoals were proven
    Proven,
    /// At least one subgoal is unprovable
    Unprovable,
}

// =============================================================================
// AND-OR Tree Node Structures
// =============================================================================

/// A goal node in the AND-OR tree (OR node)
///
/// OR semantics: the goal is proven if ANY child rapp is proven.
/// When one rapp succeeds, siblings become irrelevant.
#[derive(Debug, Clone)]
pub struct GoalData {
    /// Parent rule application (None for root goal)
    pub parent: Option<RappId>,
    /// Child rule applications (attempts to prove this goal)
    pub children: Vec<RappId>,
    /// Current state
    pub state: GoalState,
    /// The proof goal (target type + local context)
    pub goal: Goal,
    /// Depth in tree
    pub depth: usize,
    /// When this goal was last expanded
    pub last_expanded_in_iteration: usize,
}

/// A rule application node in the AND-OR tree (AND node)
///
/// AND semantics: the rapp is proven if ALL subgoals are proven.
/// If any subgoal becomes unprovable, the entire rapp fails.
#[derive(Debug, Clone)]
pub struct RappData {
    /// Parent goal this rapp is trying to prove
    pub parent: GoalId,
    /// Subgoals produced by applying this rule
    pub children: Vec<GoalId>,
    /// Current state
    pub state: NodeState,
}

// =============================================================================
// Search Tree
// =============================================================================

/// The complete AND-OR search tree
///
/// This tree represents the search space explored by aesop.
/// Goals are OR nodes (any child proving succeeds), and
/// rule applications are AND nodes (all subgoals must be proven).
#[derive(Debug, Clone)]
pub struct SearchTree {
    /// All goals indexed by id
    goals: HashMap<GoalId, GoalData>,
    /// All rule applications indexed by id
    rapps: HashMap<RappId, RappData>,
    /// Root goal id
    root: GoalId,
    /// Next goal id
    next_goal_id: u64,
    /// Next rapp id
    next_rapp_id: u64,
    /// Current iteration counter
    iteration: usize,
}

impl SearchTree {
    /// Create a new search tree with a root goal
    /// ENSURES: Returned tree contains exactly one root goal in `GoalState::Unknown`.
    /// ENSURES: Goal ids start at `0` for the root and future child goals start at `1`.
    pub fn new(root_goal: Goal) -> Self {
        let root_id = GoalId(0);
        let root_data = GoalData {
            parent: None,
            children: Vec::new(),
            state: GoalState::Unknown,
            goal: root_goal,
            depth: 0,
            last_expanded_in_iteration: 0,
        };

        let mut goals = HashMap::new();
        goals.insert(root_id, root_data);

        SearchTree {
            goals,
            rapps: HashMap::new(),
            root: root_id,
            next_goal_id: 1,
            next_rapp_id: 0,
            iteration: 0,
        }
    }

    /// Get the root goal id
    /// ENSURES: Returns the identifier of the tree's root goal.
    pub fn root(&self) -> GoalId {
        self.root
    }

    /// Get current iteration count
    /// ENSURES: Returns the number of times `next_iteration` has been called since construction.
    pub fn iteration(&self) -> usize {
        self.iteration
    }

    /// Increment iteration
    /// ENSURES: Increments `iteration()` by exactly one.
    pub fn next_iteration(&mut self) {
        self.iteration += 1;
    }

    /// Get a goal by id
    /// ENSURES: Returns `Some` iff a goal with id `id` is currently stored in the tree.
    pub fn get_goal(&self, id: GoalId) -> Option<&GoalData> {
        self.goals.get(&id)
    }

    /// Get a mutable goal by id
    /// ENSURES: Returns `Some` iff a goal with id `id` is currently stored in the tree.
    pub fn get_goal_mut(&mut self, id: GoalId) -> Option<&mut GoalData> {
        self.goals.get_mut(&id)
    }

    /// Get a rapp by id
    /// ENSURES: Returns `Some` iff a rapp with id `id` is currently stored in the tree.
    pub fn get_rapp(&self, id: RappId) -> Option<&RappData> {
        self.rapps.get(&id)
    }

    /// Get a mutable rapp by id
    /// ENSURES: Returns `Some` iff a rapp with id `id` is currently stored in the tree.
    pub fn get_rapp_mut(&mut self, id: RappId) -> Option<&mut RappData> {
        self.rapps.get_mut(&id)
    }

    /// Add a new goal as a child of a rapp
    /// REQUIRES: `parent_rapp` refers to a rapp in this tree when callers expect parent/child linkage.
    /// ENSURES: Inserts a new goal node whose `parent` field is `Some(parent_rapp)`.
    /// ENSURES: If `parent_rapp` exists, its `children` list gains the returned goal id.
    pub fn add_goal(&mut self, parent_rapp: RappId, goal: Goal) -> GoalId {
        let id = GoalId(self.next_goal_id);
        self.next_goal_id += 1;

        // Get parent depth
        let parent_depth = if let Some(rapp) = self.rapps.get(&parent_rapp) {
            if let Some(grandparent) = self.goals.get(&rapp.parent) {
                grandparent.depth + 1
            } else {
                1
            }
        } else {
            1
        };

        let goal_data = GoalData {
            parent: Some(parent_rapp),
            children: Vec::new(),
            state: GoalState::Unknown,
            goal,
            depth: parent_depth,
            last_expanded_in_iteration: 0,
        };

        self.goals.insert(id, goal_data);

        // Add to parent's children
        if let Some(rapp) = self.rapps.get_mut(&parent_rapp) {
            rapp.children.push(id);
        }

        id
    }

    /// Add a new rapp as a child of a goal
    /// REQUIRES: `parent_goal` refers to a goal in this tree when callers expect parent/child linkage.
    /// ENSURES: Inserts a new rapp node whose `parent` field is `parent_goal`.
    /// ENSURES: If `parent_goal` exists, its `children` list gains the returned rapp id.
    pub fn add_rapp(&mut self, parent_goal: GoalId) -> RappId {
        let id = RappId(self.next_rapp_id);
        self.next_rapp_id += 1;

        let rapp_data = RappData {
            parent: parent_goal,
            children: Vec::new(),
            state: NodeState::Unknown,
        };

        self.rapps.insert(id, rapp_data);

        // Add to parent's children
        if let Some(goal) = self.goals.get_mut(&parent_goal) {
            goal.children.push(id);
        }

        id
    }

    /// Check if the root is proven
    /// ENSURES: Returns `true` iff the root goal currently exists and `GoalState::is_proven()` is true.
    pub fn is_root_proven(&self) -> bool {
        self.goals
            .get(&self.root)
            .map(|g| g.state.is_proven())
            .unwrap_or(false)
    }

    /// Check if the root is unprovable
    /// ENSURES: Returns `true` iff the root goal currently exists and is marked `GoalState::Unprovable`.
    pub fn is_root_unprovable(&self) -> bool {
        self.goals
            .get(&self.root)
            .map(|g| g.state == GoalState::Unprovable)
            .unwrap_or(false)
    }
}

// =============================================================================
// Rule Attempt Tracking
// =============================================================================

/// Diagnostic record of a single rule application attempt during aesop search.
///
/// Tracks which rule was tried on which goal, whether it succeeded,
/// and how many subgoals it produced. Used for search diagnostics
/// and debugging proof search failures.
#[derive(Debug, Clone)]
pub struct RuleAttempt {
    /// Name of the rule that was tried
    pub rule_name: String,
    /// Whether the rule application succeeded
    pub success: bool,
    /// Number of subgoals produced (0 if the rule closed the goal)
    pub subgoals_produced: usize,
}

/// Aggregated search state wrapping the AND-OR tree with diagnostic tracking.
///
/// Provides iteration counting and per-goal rule attempt history
/// for post-search analysis of proof search behavior.
#[derive(Debug, Clone)]
pub struct AesopSearchState {
    /// The underlying AND-OR search tree
    pub(super) tree: SearchTree,
    /// Total iterations consumed so far
    pub(super) iteration_count: usize,
    /// Rule attempts indexed by the goal they were tried on
    pub(super) rule_attempts: HashMap<GoalId, Vec<RuleAttempt>>,
}

impl AesopSearchState {
    /// Create a new search state from a root goal.
    /// ENSURES: Returned state has `iteration_count == 0` and an empty rule attempt log.
    pub fn new(root_goal: Goal) -> Self {
        AesopSearchState {
            tree: SearchTree::new(root_goal),
            iteration_count: 0,
            rule_attempts: HashMap::new(),
        }
    }

    /// Access the underlying search tree.
    pub fn tree(&self) -> &SearchTree {
        &self.tree
    }

    /// Mutably access the underlying search tree.
    pub fn tree_mut(&mut self) -> &mut SearchTree {
        &mut self.tree
    }

    /// Get the total number of search iterations performed.
    pub fn iteration_count(&self) -> usize {
        self.iteration_count
    }

    /// Record a rule attempt on a specific goal.
    pub fn record_attempt(&mut self, goal_id: GoalId, attempt: RuleAttempt) {
        self.rule_attempts.entry(goal_id).or_default().push(attempt);
    }

    /// Get all rule attempts for a specific goal.
    pub fn attempts_for_goal(&self, goal_id: GoalId) -> &[RuleAttempt] {
        self.rule_attempts
            .get(&goal_id)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Get the total number of rule attempts across all goals.
    pub fn total_attempts(&self) -> usize {
        self.rule_attempts.values().map(|v| v.len()).sum()
    }

    /// Get the number of successful rule attempts across all goals.
    pub fn successful_attempts(&self) -> usize {
        self.rule_attempts
            .values()
            .flat_map(|v| v.iter())
            .filter(|a| a.success)
            .count()
    }
}

// =============================================================================
// Search Strategy
// =============================================================================

/// Search strategy for aesop goal selection
///
/// Controls the order in which goals are explored during proof search.
/// Different strategies have different trade-offs:
/// - BestFirst: Explores most promising goals first (default, good for finding short proofs)
/// - DepthFirst: LIFO order, explores deeply before backtracking (good for some Mathlib proofs)
/// - BreadthFirst: FIFO order, explores level by level (good for shortest proof guarantee)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AesopStrategy {
    /// Best-first search using priority queue (default)
    /// Explores goals with highest success probability first
    #[default]
    BestFirst,
    /// Depth-first search using stack (LIFO)
    /// Explores most recently added goals first
    DepthFirst,
    /// Breadth-first search using queue (FIFO)
    /// Explores goals in order they were added
    BreadthFirst,
}
