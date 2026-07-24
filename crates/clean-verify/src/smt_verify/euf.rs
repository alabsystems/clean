// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EUF (Equality + Uninterpreted Functions) theory checker.
//!
//! Validates equality reasoning rules:
//! - `eq_transitive`: BFS path search through equality edges
//! - `eq_congruent`: same function, argument equalities match positions
//! - `eq_congruent_pred`: like congruent but for predicate (Bool-sorted) apps
//! - `refl`: (= t t)
//! - `symm`: (= a b) -> (= b a)
//! - `trans`: chain of equalities
//! - `cong`: congruence with premise equalities
//!
//! Reference: ay's `~/ay/crates/ay-proof/src/checker/euf.rs`

use std::collections::{HashMap, HashSet, VecDeque};

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "euf";

/// Check a `refl` rule: `(cl (= t t))`.
///
/// The clause must contain exactly one literal, a positive equality
/// where LHS == RHS.
pub(crate) fn check_refl(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.len() != 1 {
        return fail(step_id, "refl clause must have exactly 1 literal");
    }

    match dag.as_equality(clause[0]) {
        Some((lhs, rhs)) if lhs == rhs => ok(step_id),
        Some(_) => fail(step_id, "refl: LHS != RHS"),
        None => fail(step_id, "refl: clause literal is not an equality"),
    }
}

/// Check a `symm` rule: premise `(= a b)` -> conclusion `(= b a)`.
///
/// Single premise, single conclusion literal, sides swapped.
pub(crate) fn check_symm(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    premises: &[SmtStepId],
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> StepVerdict {
    if clause.len() != 1 {
        return fail(step_id, "symm conclusion must have exactly 1 literal");
    }
    if premises.len() != 1 {
        return fail(step_id, "symm must have exactly 1 premise");
    }

    let premise_clause = match get_premise_clause(premises[0], derived_clauses) {
        Some(c) => c,
        None => return fail(step_id, "symm: premise has no clause"),
    };

    if premise_clause.len() != 1 {
        return fail(step_id, "symm: premise must have exactly 1 literal");
    }

    let prem_eq = match dag.as_equality(premise_clause[0]) {
        Some(eq) => eq,
        None => return fail(step_id, "symm: premise is not an equality"),
    };

    let conc_eq = match dag.as_equality(clause[0]) {
        Some(eq) => eq,
        None => return fail(step_id, "symm: conclusion is not an equality"),
    };

    if prem_eq.0 == conc_eq.1 && prem_eq.1 == conc_eq.0 {
        ok(step_id)
    } else {
        fail(step_id, "symm: sides not properly swapped")
    }
}

/// Check a `trans` rule: premises `(= a b), (= b c)` -> `(= a c)`.
///
/// Uses BFS chain through premise equalities.
pub(crate) fn check_trans(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    premises: &[SmtStepId],
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> StepVerdict {
    if clause.len() != 1 {
        return fail(step_id, "trans conclusion must have exactly 1 literal");
    }
    if premises.is_empty() {
        return fail(step_id, "trans must have at least 1 premise");
    }

    let conc_eq = match dag.as_equality(clause[0]) {
        Some(eq) => eq,
        None => return fail(step_id, "trans: conclusion is not an equality"),
    };

    // Collect equality edges from premises.
    let mut edges: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &pid in premises {
        let premise_clause = match get_premise_clause(pid, derived_clauses) {
            Some(c) => c,
            None => return fail(step_id, "trans: premise has no clause"),
        };
        if premise_clause.len() != 1 {
            return fail(step_id, "trans: premise must have exactly 1 literal");
        }
        match dag.as_equality(premise_clause[0]) {
            Some((a, b)) => edges.push((a, b)),
            None => return fail(step_id, "trans: premise is not an equality"),
        }
    }

    // BFS from conc_eq.0 to conc_eq.1 through undirected equality edges.
    if bfs_path_exists(conc_eq.0, conc_eq.1, &edges) {
        ok(step_id)
    } else {
        fail(
            step_id,
            "trans: no path from LHS to RHS through premise equalities",
        )
    }
}

/// Check `eq_transitive` theory lemma.
///
/// Clause: `(not (= a b)) (not (= b c)) ... (= a z)`.
/// All but the last literal are negated equalities forming a chain;
/// the last literal is a positive equality from first to last in the chain.
pub(crate) fn check_eq_transitive(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.len() < 2 {
        return fail(step_id, "eq_transitive clause needs at least 2 literals");
    }

    // Last literal should be a positive equality (the conclusion).
    let conclusion_eq = match dag.as_equality(*clause.last().expect("checked len >= 2")) {
        Some(eq) => eq,
        None => {
            return fail(
                step_id,
                "eq_transitive: last literal is not a positive equality",
            )
        }
    };

    // All other literals should be negated equalities.
    let mut edges: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &lit in &clause[..clause.len() - 1] {
        match dag.as_negated_equality(lit) {
            Some((a, b)) => edges.push((a, b)),
            None => {
                return fail(
                    step_id,
                    "eq_transitive: non-final literal is not a negated equality",
                )
            }
        }
    }

    // BFS: path from conclusion.lhs to conclusion.rhs through premise edges.
    if bfs_path_exists(conclusion_eq.0, conclusion_eq.1, &edges) {
        ok(step_id)
    } else {
        fail(
            step_id,
            "eq_transitive: no path from LHS to RHS through equality chain",
        )
    }
}

/// Check `eq_congruent` theory lemma.
///
/// Clause: `(not (= a1 b1)) ... (not (= an bn)) (= (f a1..an) (f b1..bn))`.
/// The last literal is a positive equality between two function applications
/// with the same symbol and arity. Each negated equality premise matches an
/// argument position.
pub(crate) fn check_eq_congruent(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.len() < 2 {
        return fail(step_id, "eq_congruent clause needs at least 2 literals");
    }

    // Last literal: (= (f a...) (f b...)).
    let conclusion_eq = match dag.as_equality(*clause.last().expect("checked len >= 2")) {
        Some(eq) => eq,
        None => return fail(step_id, "eq_congruent: last literal is not an equality"),
    };

    let (f_sym, f_args) = match dag.term(conclusion_eq.0) {
        Some(SmtTerm::App(sym, args)) => (sym, args),
        _ => return fail(step_id, "eq_congruent: LHS is not a function application"),
    };
    let (g_sym, g_args) = match dag.term(conclusion_eq.1) {
        Some(SmtTerm::App(sym, args)) => (sym, args),
        _ => return fail(step_id, "eq_congruent: RHS is not a function application"),
    };

    if f_sym != g_sym {
        return fail(step_id, "eq_congruent: different function symbols");
    }
    if f_args.len() != g_args.len() {
        return fail(step_id, "eq_congruent: different arities");
    }

    // Collect negated equalities from premises.
    let mut premise_eqs: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &lit in &clause[..clause.len() - 1] {
        match dag.as_negated_equality(lit) {
            Some((a, b)) => premise_eqs.push((a, b)),
            None => {
                return fail(
                    step_id,
                    "eq_congruent: non-final literal is not a negated equality",
                )
            }
        }
    }

    // Each argument position where f_args[i] != g_args[i] must have a
    // matching premise equality (in either direction).
    for i in 0..f_args.len() {
        if f_args[i] == g_args[i] {
            continue; // Same argument, no premise needed.
        }
        let has_match = premise_eqs.iter().any(|&(a, b)| {
            (a == f_args[i] && b == g_args[i]) || (a == g_args[i] && b == f_args[i])
        });
        if !has_match {
            return fail(
                step_id,
                &format!("eq_congruent: no premise equality for argument position {i}"),
            );
        }
    }

    ok(step_id)
}

/// Check `eq_congruent_pred` theory lemma.
///
/// Like `eq_congruent` but the conclusion is a predicate application (Bool-sorted):
/// `(not (= a1 b1)) ... (not (p a1..an)) (p b1..bn)`.
/// The last two literals are the negated/positive predicate application.
pub(crate) fn check_eq_congruent_pred(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.len() < 3 {
        return fail(
            step_id,
            "eq_congruent_pred clause needs at least 3 literals",
        );
    }

    // Last two literals: negated predicate and positive predicate.
    let neg_pred_lit = clause[clause.len() - 2];
    let pos_pred_lit = clause[clause.len() - 1];

    // The negated predicate literal could be Not(App(p, args1)) or
    // App(p, args1) where it appears negated.
    let (p_sym_neg, p_args_neg) = match extract_pred_from_negated(dag, neg_pred_lit) {
        Some(x) => x,
        None => {
            // Try swapping: maybe the positive is first.
            return check_eq_congruent_pred_swapped(dag, step_id, clause);
        }
    };

    let (p_sym_pos, p_args_pos) = match dag.term(pos_pred_lit) {
        Some(SmtTerm::App(sym, args)) => (sym.clone(), args.clone()),
        _ => {
            return fail(
                step_id,
                "eq_congruent_pred: positive literal is not an application",
            )
        }
    };

    if p_sym_neg != p_sym_pos {
        return fail(step_id, "eq_congruent_pred: different predicate symbols");
    }
    if p_args_neg.len() != p_args_pos.len() {
        return fail(step_id, "eq_congruent_pred: different predicate arities");
    }

    // Collect negated equalities from the first N-2 literals.
    let mut premise_eqs: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &lit in &clause[..clause.len() - 2] {
        match dag.as_negated_equality(lit) {
            Some((a, b)) => premise_eqs.push((a, b)),
            None => {
                return fail(
                    step_id,
                    "eq_congruent_pred: premise literal is not a negated equality",
                )
            }
        }
    }

    // Verify argument positions match.
    for i in 0..p_args_neg.len() {
        if p_args_neg[i] == p_args_pos[i] {
            continue;
        }
        let has_match = premise_eqs.iter().any(|&(a, b)| {
            (a == p_args_neg[i] && b == p_args_pos[i]) || (a == p_args_pos[i] && b == p_args_neg[i])
        });
        if !has_match {
            return fail(
                step_id,
                &format!("eq_congruent_pred: no premise equality for argument position {i}"),
            );
        }
    }

    ok(step_id)
}

/// Check `cong` step rule: premises are equalities, conclusion is equality
/// of function applications.
pub(crate) fn check_cong(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    premises: &[SmtStepId],
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> StepVerdict {
    if clause.len() != 1 {
        return fail(step_id, "cong conclusion must have exactly 1 literal");
    }

    let conc_eq = match dag.as_equality(clause[0]) {
        Some(eq) => eq,
        None => return fail(step_id, "cong: conclusion is not an equality"),
    };

    let (f_sym, f_args) = match dag.term(conc_eq.0) {
        Some(SmtTerm::App(sym, args)) => (sym, args),
        _ => return fail(step_id, "cong: LHS is not a function application"),
    };
    let (g_sym, g_args) = match dag.term(conc_eq.1) {
        Some(SmtTerm::App(sym, args)) => (sym, args),
        _ => return fail(step_id, "cong: RHS is not a function application"),
    };

    if f_sym != g_sym {
        return fail(step_id, "cong: different function symbols");
    }
    if f_args.len() != g_args.len() {
        return fail(step_id, "cong: different arities");
    }

    // Collect equalities from premises.
    let mut premise_eqs: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &pid in premises {
        let premise_clause = match get_premise_clause(pid, derived_clauses) {
            Some(c) => c,
            None => return fail(step_id, "cong: premise has no clause"),
        };
        if premise_clause.len() != 1 {
            return fail(step_id, "cong: premise must have exactly 1 literal");
        }
        match dag.as_equality(premise_clause[0]) {
            Some((a, b)) => premise_eqs.push((a, b)),
            None => return fail(step_id, "cong: premise is not an equality"),
        }
    }

    // Each differing argument must have a matching premise.
    for i in 0..f_args.len() {
        if f_args[i] == g_args[i] {
            continue;
        }
        let has_match = premise_eqs.iter().any(|&(a, b)| {
            (a == f_args[i] && b == g_args[i]) || (a == g_args[i] && b == f_args[i])
        });
        if !has_match {
            return fail(
                step_id,
                &format!("cong: no premise equality for argument position {i}"),
            );
        }
    }

    ok(step_id)
}

// ── Congruence Closure Checker ──────────────────────────────────────────────

/// Union-find with path compression and union-by-rank.
///
/// Each element is an `SmtTermId`. The internal storage maps `SmtTermId` to
/// its parent; roots are self-referencing with rank tracking.
struct UnionFind {
    parent: HashMap<SmtTermId, SmtTermId>,
    rank: HashMap<SmtTermId, u32>,
}

impl UnionFind {
    fn new() -> Self {
        Self {
            parent: HashMap::new(),
            rank: HashMap::new(),
        }
    }

    /// Ensure a term exists in the union-find.
    fn make_set(&mut self, t: SmtTermId) {
        self.parent.entry(t).or_insert(t);
        self.rank.entry(t).or_insert(0);
    }

    /// Find the representative of `t` with path compression.
    fn find(&mut self, t: SmtTermId) -> SmtTermId {
        self.make_set(t);
        let p = self.parent[&t];
        if p == t {
            return t;
        }
        let root = self.find(p);
        self.parent.insert(t, root);
        root
    }

    /// Union the equivalence classes of `a` and `b`.
    ///
    /// Returns `true` if the classes were disjoint and were merged;
    /// `false` if they were already in the same class.
    fn union(&mut self, a: SmtTermId, b: SmtTermId) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        let rank_a = self.rank[&ra];
        let rank_b = self.rank[&rb];
        if rank_a < rank_b {
            self.parent.insert(ra, rb);
        } else if rank_a > rank_b {
            self.parent.insert(rb, ra);
        } else {
            self.parent.insert(rb, ra);
            self.rank.insert(ra, rank_a + 1);
        }
        true
    }

    /// Check if `a` and `b` are in the same equivalence class.
    fn congruent(&mut self, a: SmtTermId, b: SmtTermId) -> bool {
        self.find(a) == self.find(b)
    }
}

/// Congruence closure state.
///
/// Collects all function application terms from the DAG, then processes
/// equality atoms to merge equivalence classes and propagate congruence.
struct CongruenceClosure<'a> {
    dag: &'a SmtProofDag,
    uf: UnionFind,
    /// All function application terms discovered during term collection.
    /// Maps term ID to (symbol, argument term IDs).
    apps: Vec<(SmtTermId, SmtSymbol, Vec<SmtTermId>)>,
}

impl<'a> CongruenceClosure<'a> {
    fn new(dag: &'a SmtProofDag) -> Self {
        Self {
            dag,
            uf: UnionFind::new(),
            apps: Vec::new(),
        }
    }

    /// Recursively collect all sub-terms reachable from `term_id`,
    /// registering them in the union-find and recording function apps.
    fn collect_terms(&mut self, term_id: SmtTermId) {
        // Avoid processing the same term twice.
        if self.uf.parent.contains_key(&term_id) {
            return;
        }
        self.uf.make_set(term_id);

        let term = match self.dag.term(term_id) {
            Some(t) => t.clone(),
            None => return,
        };

        match &term {
            SmtTerm::App(sym, args)
                if sym != &SmtSymbol::Named("=".to_string())
                    && sym != &SmtSymbol::Named("distinct".to_string()) =>
            {
                for &arg in args {
                    self.collect_terms(arg);
                }
                self.apps.push((term_id, sym.clone(), args.clone()));
            }
            SmtTerm::App(_, args) => {
                // Equality/distinct: collect sub-terms but don't register as congruence app.
                for &arg in args {
                    self.collect_terms(arg);
                }
            }
            SmtTerm::Not(inner) => {
                self.collect_terms(*inner);
            }
            SmtTerm::Ite(c, t, e) => {
                self.collect_terms(*c);
                self.collect_terms(*t);
                self.collect_terms(*e);
            }
            // Leaf terms: Var, Bool, Int, Rational, etc. -- just make_set is enough.
            _ => {}
        }
    }

    /// Merge the equivalence classes of `a` and `b`, then propagate congruence.
    ///
    /// After merging, scan all pairs of function applications to find new
    /// congruences. This is the naive O(n^2) congruence propagation; sufficient
    /// for typical proof clause sizes.
    fn merge(&mut self, a: SmtTermId, b: SmtTermId) {
        if !self.uf.union(a, b) {
            return; // Already congruent, nothing to propagate.
        }
        self.propagate_congruence();
    }

    /// Scan all function application pairs; merge those whose symbols match
    /// and all arguments are congruent. Repeat until fixpoint.
    fn propagate_congruence(&mut self) {
        loop {
            let mut merged_any = false;
            let n = self.apps.len();
            for i in 0..n {
                for j in (i + 1)..n {
                    let (id_i, sym_i, args_i) = &self.apps[i];
                    let (id_j, sym_j, args_j) = &self.apps[j];

                    if sym_i != sym_j || args_i.len() != args_j.len() {
                        continue;
                    }
                    if self.uf.congruent(*id_i, *id_j) {
                        continue; // Already merged.
                    }

                    let all_args_congruent = args_i
                        .iter()
                        .zip(args_j.iter())
                        .all(|(&ai, &aj)| self.uf.congruent(ai, aj));

                    if all_args_congruent {
                        let a = *id_i;
                        let b = *id_j;
                        self.uf.union(a, b);
                        merged_any = true;
                    }
                }
            }
            if !merged_any {
                break;
            }
        }
    }

    /// Check if `a` and `b` are in the same equivalence class.
    fn are_congruent(&mut self, a: SmtTermId, b: SmtTermId) -> bool {
        self.uf.congruent(a, b)
    }
}

/// Check a general EUF theory lemma via congruence closure.
///
/// The clause is a blocking clause (disjunction of negated conflict literals).
/// The conflict is the conjunction of the negations. For the lemma to be valid,
/// this conjunction must be unsatisfiable in the theory of EUF.
///
/// Algorithm:
/// 1. Parse clause literals: positive equalities become disequalities in the
///    conflict; negated equalities become equalities in the conflict.
///    Non-equality atoms become predicate disequalities/equalities.
/// 2. Process all equality atoms from the conflict via congruence closure.
/// 3. After closure, check all disequality atoms: if any `a != b` has `a ~ b`,
///    the conflict is unsatisfiable and the lemma is valid.
///
/// If no disequality is violated, the lemma is not provably valid via
/// congruence closure, and we fall back to structural acceptance.
pub(crate) fn check_euf_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "euf_generic: empty clause");
    }

    // Parse the blocking clause into conflict equalities and disequalities.
    //
    // Blocking clause literal -> conflict literal:
    //   positive (= a b)        -> conflict: a != b  (disequality)
    //   not (= a b)             -> conflict: a = b   (equality)
    //   positive non-eq atom P  -> conflict: P = false
    //   not(P)                  -> conflict: P = true
    //
    // For a simple EUF checker we focus on equality/disequality atoms.
    let mut equalities: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    let mut disequalities: Vec<(SmtTermId, SmtTermId)> = Vec::new();

    for &lit in clause {
        let term = match dag.term(lit) {
            Some(t) => t,
            None => return fail(step_id, "euf_generic: invalid term reference"),
        };

        match term {
            // Positive equality in blocking clause -> disequality in conflict.
            SmtTerm::App(SmtSymbol::Named(name), args) if name == "=" && args.len() == 2 => {
                disequalities.push((args[0], args[1]));
            }
            // Negated equality -> equality in conflict.
            SmtTerm::Not(inner) => {
                if let Some((a, b)) = dag.as_equality(*inner) {
                    equalities.push((a, b));
                } else {
                    // Negated non-equality atom: treat as predicate constraint.
                    // For simplicity, we cannot handle these in pure EUF.
                    // Structurally accept.
                    return structural_accept(step_id);
                }
            }
            // Non-equality positive atom: cannot handle in pure EUF equality checker.
            _ => {
                return structural_accept(step_id);
            }
        }
    }

    // Must have at least one disequality to derive a contradiction.
    if disequalities.is_empty() {
        return fail(step_id, "euf_generic: no disequality in clause");
    }

    // Build congruence closure over all involved terms.
    let mut cc = CongruenceClosure::new(dag);

    // Collect terms from all equalities and disequalities.
    for &(a, b) in &equalities {
        cc.collect_terms(a);
        cc.collect_terms(b);
    }
    for &(a, b) in &disequalities {
        cc.collect_terms(a);
        cc.collect_terms(b);
    }

    // Process all conflict equalities.
    for &(a, b) in &equalities {
        cc.merge(a, b);
    }

    // Check if any conflict disequality is violated (a != b but a ~ b).
    let any_violated = disequalities.iter().any(|&(a, b)| cc.are_congruent(a, b));

    if any_violated {
        ok(step_id)
    } else {
        fail(
            step_id,
            "euf_generic: congruence closure does not violate any disequality",
        )
    }
}

/// Structurally accept an EUF step that we cannot fully check.
fn structural_accept(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker: CHECKER_NAME,
        detail: Some("euf_generic: non-equality atoms, structurally accepted".to_string()),
    }
}

// -- Helper functions --

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

fn get_premise_clause(
    pid: SmtStepId,
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> Option<&Vec<SmtTermId>> {
    derived_clauses.get(pid.0 as usize)?.as_ref()
}

/// BFS path search through undirected equality edges.
fn bfs_path_exists(start: SmtTermId, goal: SmtTermId, edges: &[(SmtTermId, SmtTermId)]) -> bool {
    if start == goal {
        return true;
    }

    // Build adjacency list.
    let mut adj: HashMap<SmtTermId, Vec<SmtTermId>> = HashMap::new();
    for &(a, b) in edges {
        adj.entry(a).or_default().push(b);
        adj.entry(b).or_default().push(a);
    }

    let mut visited: HashSet<SmtTermId> = HashSet::new();
    let mut queue: VecDeque<SmtTermId> = VecDeque::new();
    visited.insert(start);
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        if let Some(neighbors) = adj.get(&current) {
            for &next in neighbors {
                if next == goal {
                    return true;
                }
                if visited.insert(next) {
                    queue.push_back(next);
                }
            }
        }
    }

    false
}

/// Extract predicate symbol and args from a negated literal.
///
/// Handles both `Not(App(p, args))` and searching for it.
fn extract_pred_from_negated(
    dag: &SmtProofDag,
    lit: SmtTermId,
) -> Option<(SmtSymbol, Vec<SmtTermId>)> {
    match dag.term(lit)? {
        SmtTerm::Not(inner) => match dag.term(*inner)? {
            SmtTerm::App(sym, args) => Some((sym.clone(), args.clone())),
            _ => None,
        },
        _ => None,
    }
}

/// Fallback for eq_congruent_pred when the last two literals are swapped.
fn check_eq_congruent_pred_swapped(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    // Try: second-to-last is positive, last is negated.
    let pos_pred_lit = clause[clause.len() - 2];
    let neg_pred_lit = clause[clause.len() - 1];

    let (p_sym_pos, p_args_pos) = match dag.term(pos_pred_lit) {
        Some(SmtTerm::App(sym, args)) => (sym.clone(), args.clone()),
        _ => {
            return fail(
                step_id,
                "eq_congruent_pred: cannot identify predicate literals",
            )
        }
    };

    let (p_sym_neg, p_args_neg) = match extract_pred_from_negated(dag, neg_pred_lit) {
        Some(x) => x,
        None => {
            return fail(
                step_id,
                "eq_congruent_pred: cannot identify negated predicate",
            )
        }
    };

    if p_sym_neg != p_sym_pos || p_args_neg.len() != p_args_pos.len() {
        return fail(step_id, "eq_congruent_pred: predicate mismatch (swapped)");
    }

    // Collect negated equalities.
    let mut premise_eqs: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &lit in &clause[..clause.len() - 2] {
        match dag.as_negated_equality(lit) {
            Some((a, b)) => premise_eqs.push((a, b)),
            None => {
                return fail(
                    step_id,
                    "eq_congruent_pred: premise is not a negated equality (swapped)",
                )
            }
        }
    }

    for i in 0..p_args_neg.len() {
        if p_args_neg[i] == p_args_pos[i] {
            continue;
        }
        let has_match = premise_eqs.iter().any(|&(a, b)| {
            (a == p_args_neg[i] && b == p_args_pos[i]) || (a == p_args_pos[i] && b == p_args_neg[i])
        });
        if !has_match {
            return fail(
                step_id,
                &format!("eq_congruent_pred: no premise for arg {i} (swapped)"),
            );
        }
    }

    ok(step_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtProofStep, SmtSort, SmtTerm};

    #[test]
    fn test_euf_refl_valid() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let eq_aa = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, a]));
        let step_id = SmtStepId(0);
        let verdict = check_refl(&dag, step_id, &[eq_aa]);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_euf_refl_invalid_different_sides() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let verdict = check_refl(&dag, SmtStepId(0), &[eq_ab]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_euf_refl_invalid_not_equality() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let verdict = check_refl(&dag, SmtStepId(0), &[a]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_euf_symm_valid() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let eq_ba = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![b, a]));

        let derived = vec![Some(vec![eq_ab])];
        let verdict = check_symm(&dag, SmtStepId(1), &[eq_ba], &[SmtStepId(0)], &derived);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_euf_trans_valid() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let eq_bc = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![b, c]));
        let eq_ac = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, c]));

        let derived = vec![Some(vec![eq_ab]), Some(vec![eq_bc])];
        let verdict = check_trans(
            &dag,
            SmtStepId(2),
            &[eq_ac],
            &[SmtStepId(0), SmtStepId(1)],
            &derived,
        );
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_euf_trans_invalid_no_path() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Int));
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        // Trying to prove a = d with only a = b.
        let eq_ad = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, d]));

        let derived = vec![Some(vec![eq_ab])];
        let verdict = check_trans(&dag, SmtStepId(1), &[eq_ad], &[SmtStepId(0)], &derived);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_euf_eq_transitive_valid() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));

        // (not (= a b))
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));

        // (not (= b c))
        let eq_bc = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![b, c]));
        let neq_bc = dag.add_term(SmtTerm::Not(eq_bc));

        // (= a c)
        let eq_ac = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, c]));

        let clause = vec![neq_ab, neq_bc, eq_ac];
        let verdict = check_eq_transitive(&dag, SmtStepId(0), &clause);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_euf_eq_congruent_valid() {
        let mut dag = SmtProofDag::new();
        let a1 = dag.add_term(SmtTerm::Var("a1".to_string(), SmtSort::Int));
        let b1 = dag.add_term(SmtTerm::Var("b1".to_string(), SmtSort::Int));

        // (not (= a1 b1))
        let eq_a1b1 = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("=".to_string()),
            vec![a1, b1],
        ));
        let neq = dag.add_term(SmtTerm::Not(eq_a1b1));

        // f(a1) and f(b1)
        let fa1 = dag.add_term(SmtTerm::App(SmtSymbol::Named("f".to_string()), vec![a1]));
        let fb1 = dag.add_term(SmtTerm::App(SmtSymbol::Named("f".to_string()), vec![b1]));

        // (= f(a1) f(b1))
        let eq_conc = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("=".to_string()),
            vec![fa1, fb1],
        ));

        let clause = vec![neq, eq_conc];
        let verdict = check_eq_congruent(&dag, SmtStepId(0), &clause);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_euf_eq_congruent_pred_valid() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));

        // (not (= a b))
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let neq = dag.add_term(SmtTerm::Not(eq_ab));

        // p(a) and p(b) -- predicate applications
        let pa = dag.add_term(SmtTerm::App(SmtSymbol::Named("p".to_string()), vec![a]));
        let pb = dag.add_term(SmtTerm::App(SmtSymbol::Named("p".to_string()), vec![b]));
        let neg_pa = dag.add_term(SmtTerm::Not(pa));

        // Clause: (not (= a b)) (not (p a)) (p b)
        let clause = vec![neq, neg_pa, pb];
        let verdict = check_eq_congruent_pred(&dag, SmtStepId(0), &clause);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_euf_cong_valid() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));

        let fa = dag.add_term(SmtTerm::App(SmtSymbol::Named("f".to_string()), vec![a]));
        let fb = dag.add_term(SmtTerm::App(SmtSymbol::Named("f".to_string()), vec![b]));
        let eq_fafb = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("=".to_string()),
            vec![fa, fb],
        ));

        let derived = vec![Some(vec![eq_ab])];
        let verdict = check_cong(&dag, SmtStepId(1), &[eq_fafb], &[SmtStepId(0)], &derived);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_bfs_path_simple() {
        let a = SmtTermId(0);
        let b = SmtTermId(1);
        let c = SmtTermId(2);
        let edges = vec![(a, b), (b, c)];
        assert!(bfs_path_exists(a, c, &edges));
        assert!(!bfs_path_exists(a, SmtTermId(99), &edges));
    }

    #[test]
    fn test_bfs_path_self() {
        let a = SmtTermId(0);
        assert!(bfs_path_exists(a, a, &[]));
    }

    // ── Union-Find tests ───────────────────────────────────────────────

    #[test]
    fn test_union_find_basic() {
        let mut uf = UnionFind::new();
        let a = SmtTermId(0);
        let b = SmtTermId(1);
        let c = SmtTermId(2);

        uf.make_set(a);
        uf.make_set(b);
        uf.make_set(c);

        assert!(!uf.congruent(a, b));
        assert!(uf.union(a, b));
        assert!(uf.congruent(a, b));
        assert!(!uf.congruent(a, c));
        assert!(uf.union(b, c));
        assert!(uf.congruent(a, c));
    }

    #[test]
    fn test_union_find_self_congruent() {
        let mut uf = UnionFind::new();
        let a = SmtTermId(0);
        uf.make_set(a);
        assert!(uf.congruent(a, a));
        assert!(!uf.union(a, a)); // Already same class.
    }

    #[test]
    fn test_union_find_double_union() {
        let mut uf = UnionFind::new();
        let a = SmtTermId(0);
        let b = SmtTermId(1);
        uf.make_set(a);
        uf.make_set(b);
        assert!(uf.union(a, b));
        assert!(!uf.union(a, b)); // Already merged.
    }

    // ── Congruence Closure check_euf_lemma tests ───────────────────────

    /// Helper: make equality term `(= a b)`.
    fn make_eq(dag: &mut SmtProofDag, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]))
    }

    /// Helper: make unary function application `f(a)`.
    fn make_app1(dag: &mut SmtProofDag, f: &str, a: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(f.to_string()), vec![a]))
    }

    /// Helper: make binary function application `f(a, b)`.
    fn make_app2(dag: &mut SmtProofDag, f: &str, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(f.to_string()), vec![a, b]))
    }

    #[test]
    fn test_euf_lemma_transitivity_valid() {
        // Conflict: a = b, b = c, a != c
        // Blocking clause: (= a b) is positive -> diseq in conflict? No.
        // Wait: blocking clause literals are the clause of the theory lemma.
        // For a theory lemma, the clause IS the valid disjunction.
        // The conflict is the conjunction of the NEGATIONS of the clause lits.
        //
        // Clause: not(= a b), not(= b c), (= a c)
        // Conflict (negations): (= a b), (= b c), not(= a c)  i.e., a=b, b=c, a!=c
        // This should be UNSAT by transitivity.

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_bc = make_eq(&mut dag, b, c);
        let eq_ac = make_eq(&mut dag, a, c);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));
        let neq_bc = dag.add_term(SmtTerm::Not(eq_bc));

        // Clause: not(= a b), not(= b c), (= a c)
        let clause = vec![neq_ab, neq_bc, eq_ac];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "transitivity should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_congruence_valid() {
        // Conflict: a = b, f(a) != f(b)
        // Blocking clause: not(= a b), (= f(a) f(b))
        // Conflict: a = b, f(a) != f(b)
        // CC: merge a ~ b -> congruence f(a) ~ f(b) -> violates f(a) != f(b).

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let fa = make_app1(&mut dag, "f", a);
        let fb = make_app1(&mut dag, "f", b);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_fa_fb = make_eq(&mut dag, fa, fb);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));

        // Clause: not(= a b), (= f(a) f(b))
        let clause = vec![neq_ab, eq_fa_fb];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "congruence should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_deep_congruence_valid() {
        // Conflict: a = b, b = c, f(a) = g(c), f(c) != g(a)
        // Blocking clause: not(= a b), not(= b c), not(= f(a) g(c)), (= f(c) g(a))
        // Conflict: a = b, b = c, f(a) = g(c), f(c) != g(a)
        //
        // CC: a ~ b ~ c
        // f(a) ~ f(b) ~ f(c) (congruence on f, since a ~ b ~ c)
        // g(a) ~ g(b) ~ g(c) (congruence on g, since a ~ b ~ c)
        // f(a) = g(c) merges f-class with g-class: f(a) ~ g(c) ~ g(a) (since c ~ a)
        // So f(c) ~ f(a) ~ g(c) ~ g(a) -> violates f(c) != g(a).

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
        let fa = make_app1(&mut dag, "f", a);
        let fc = make_app1(&mut dag, "f", c);
        let ga = make_app1(&mut dag, "g", a);
        let gc = make_app1(&mut dag, "g", c);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_bc = make_eq(&mut dag, b, c);
        let eq_fa_gc = make_eq(&mut dag, fa, gc);
        let eq_fc_ga = make_eq(&mut dag, fc, ga);

        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));
        let neq_bc = dag.add_term(SmtTerm::Not(eq_bc));
        let neq_fa_gc = dag.add_term(SmtTerm::Not(eq_fa_gc));

        // Clause: not(= a b), not(= b c), not(= f(a) g(c)), (= f(c) g(a))
        let clause = vec![neq_ab, neq_bc, neq_fa_gc, eq_fc_ga];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "deep congruence should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_invalid_no_connection() {
        // Conflict: a = b, c != d (no connection between the two pairs).
        // Blocking clause: not(= a b), (= c d)
        // CC: merge a ~ b, check c != d -> c and d are NOT congruent -> not violated.

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Int));

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_cd = make_eq(&mut dag, c, d);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));

        // Clause: not(= a b), (= c d)
        let clause = vec![neq_ab, eq_cd];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "should be invalid (no connection): {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_reflexivity_valid() {
        // Conflict: a != a
        // Blocking clause: (= a a)
        // Conflict: a != a -- trivially UNSAT because a ~ a always.

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let eq_aa = make_eq(&mut dag, a, a);

        // Clause: (= a a)
        let clause = vec![eq_aa];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "reflexivity should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_multiple_functions_valid() {
        // Conflict: f(a) = f(b), g(a) != g(b), a = b
        // Blocking clause: not(= a b), (= f(a) f(b)), (= g(a) g(b))
        // Wait -- that has three disequalities and only one equality.
        // Let me re-think.
        //
        // We want: a = b, f(a) = f(b), g(a) != g(b). UNSAT because
        // a ~ b -> g(a) ~ g(b) via congruence -> violates g(a) != g(b).
        //
        // Blocking clause: not(= a b), not(= f(a) f(b)), (= g(a) g(b))
        // Conflict: a = b, f(a) = f(b), g(a) != g(b)

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let fa = make_app1(&mut dag, "f", a);
        let fb = make_app1(&mut dag, "f", b);
        let ga = make_app1(&mut dag, "g", a);
        let gb = make_app1(&mut dag, "g", b);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_fa_fb = make_eq(&mut dag, fa, fb);
        let eq_ga_gb = make_eq(&mut dag, ga, gb);

        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));
        let neq_fa_fb = dag.add_term(SmtTerm::Not(eq_fa_fb));

        // Clause: not(= a b), not(= f(a) f(b)), (= g(a) g(b))
        let clause = vec![neq_ab, neq_fa_fb, eq_ga_gb];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "multiple functions should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_nested_functions_valid() {
        // Conflict: a = b, f(f(a)) != f(f(b))
        // CC: a ~ b -> f(a) ~ f(b) -> f(f(a)) ~ f(f(b)) -> violates disequality.
        //
        // Blocking clause: not(= a b), (= f(f(a)) f(f(b)))

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let fa = make_app1(&mut dag, "f", a);
        let fb = make_app1(&mut dag, "f", b);
        let ffa = make_app1(&mut dag, "f", fa);
        let ffb = make_app1(&mut dag, "f", fb);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_ffa_ffb = make_eq(&mut dag, ffa, ffb);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));

        let clause = vec![neq_ab, eq_ffa_ffb];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "nested functions should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_binary_function_valid() {
        // Conflict: a1 = b1, a2 = b2, h(a1, a2) != h(b1, b2)
        // CC: a1 ~ b1, a2 ~ b2 -> h(a1,a2) ~ h(b1,b2) -> violates diseq.
        //
        // Blocking clause: not(= a1 b1), not(= a2 b2), (= h(a1,a2) h(b1,b2))

        let mut dag = SmtProofDag::new();
        let a1 = dag.add_term(SmtTerm::Var("a1".to_string(), SmtSort::Int));
        let b1 = dag.add_term(SmtTerm::Var("b1".to_string(), SmtSort::Int));
        let a2 = dag.add_term(SmtTerm::Var("a2".to_string(), SmtSort::Int));
        let b2 = dag.add_term(SmtTerm::Var("b2".to_string(), SmtSort::Int));
        let ha = make_app2(&mut dag, "h", a1, a2);
        let hb = make_app2(&mut dag, "h", b1, b2);

        let eq_a1b1 = make_eq(&mut dag, a1, b1);
        let eq_a2b2 = make_eq(&mut dag, a2, b2);
        let eq_ha_hb = make_eq(&mut dag, ha, hb);
        let neq_a1b1 = dag.add_term(SmtTerm::Not(eq_a1b1));
        let neq_a2b2 = dag.add_term(SmtTerm::Not(eq_a2b2));

        let clause = vec![neq_a1b1, neq_a2b2, eq_ha_hb];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "binary function congruence should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_empty_clause_fails() {
        let dag = SmtProofDag::new();
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_euf_lemma_only_equalities_no_diseq() {
        // Clause: not(= a b)  -- conflict: a = b but no disequality to violate.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let eq_ab = make_eq(&mut dag, a, b);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));

        let clause = vec![neq_ab];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "no disequality means no contradiction: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_symmetry_implicit() {
        // Conflict: b = a, a != b -- should still work (symmetry).
        // Blocking clause: not(= b a), (= a b)
        // Conflict: b = a, a != b
        // CC: merge b ~ a, check a != b -> a ~ b -> violated.

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));

        let eq_ba = make_eq(&mut dag, b, a);
        let eq_ab = make_eq(&mut dag, a, b);
        let neq_ba = dag.add_term(SmtTerm::Not(eq_ba));

        let clause = vec![neq_ba, eq_ab];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "symmetry should work: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_long_chain_valid() {
        // Conflict: a = b, b = c, c = d, d = e, a != e
        // CC: a ~ b ~ c ~ d ~ e -> violates a != e.
        //
        // Blocking clause: not(= a b), not(= b c), not(= c d), not(= d e), (= a e)

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Int));
        let e = dag.add_term(SmtTerm::Var("e".to_string(), SmtSort::Int));

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_bc = make_eq(&mut dag, b, c);
        let eq_cd = make_eq(&mut dag, c, d);
        let eq_de = make_eq(&mut dag, d, e);
        let eq_ae = make_eq(&mut dag, a, e);

        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));
        let neq_bc = dag.add_term(SmtTerm::Not(eq_bc));
        let neq_cd = dag.add_term(SmtTerm::Not(eq_cd));
        let neq_de = dag.add_term(SmtTerm::Not(eq_de));

        let clause = vec![neq_ab, neq_bc, neq_cd, neq_de, eq_ae];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "long chain should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_multiple_disequalities_one_violated() {
        // Conflict: a = b, a != b, c != d
        // Only a != b is violated, but that's enough.
        //
        // Blocking clause: not(= a b), (= a b), (= c d)

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Int));

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_ab2 = make_eq(&mut dag, a, b); // Disequality target.
        let eq_cd = make_eq(&mut dag, c, d);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));

        let clause = vec![neq_ab, eq_ab2, eq_cd];
        let verdict = check_euf_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "one violated disequality suffices: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_euf_lemma_in_full_proof_pipeline() {
        // Integration test: build a full proof using EufGeneric and verify
        // through the main verify_smt_proof entry point.
        use crate::smt_verify::dag::{SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_bc = make_eq(&mut dag, b, c);
        let eq_ac = make_eq(&mut dag, a, c);
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));
        let neq_bc = dag.add_term(SmtTerm::Not(eq_bc));
        let neq_ac = dag.add_term(SmtTerm::Not(eq_ac));

        // assume (= a b)
        let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
        // assume (= b c)
        let s1 = dag.add_step(SmtProofStep::Assume(eq_bc));
        // assume not(= a c)
        let s2 = dag.add_step(SmtProofStep::Assume(neq_ac));
        // EUF generic lemma: not(= a b), not(= b c), (= a c)
        let s3 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Euf,
            kind: TheoryLemmaDetail::EufGeneric,
            clause: vec![neq_ab, neq_bc, eq_ac],
        });
        // Resolve s0 + s3 on eq_ab -> {neq_bc, eq_ac}
        let s4 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![neq_bc, eq_ac],
            premises: vec![s0, s3],
            pivot: Some(eq_ab),
        });
        // Resolve s1 + s4 on eq_bc -> {eq_ac}
        let s5 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![eq_ac],
            premises: vec![s1, s4],
            pivot: Some(eq_bc),
        });
        // Resolve s2 + s5 on eq_ac -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s2, s5],
            pivot: Some(eq_ac),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "EUF generic proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
            Some(&1)
        );
    }
}
