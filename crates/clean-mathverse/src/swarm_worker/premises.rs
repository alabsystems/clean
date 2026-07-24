// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise-guided ATP support for the swarm worker.
//!
//! The bare hammer ([`clean_auto::AutomationEngine::auto_prove`]) sees only the
//! goal, so it can only discharge goals that close from nothing — reflexivity,
//! `True`, a propositional tautology. Real corpus lemmas FOLLOW FROM other
//! lemmas. This module lifts the worker to the stronger entry,
//! [`clean_auto::AutomationEngine::auto_prove_with_premises`], by seeding a
//! [`PremiseDatabase`] from the lemmas already living in the search
//! [`Environment`] and letting MePo select a relevant subset per goal.
//!
//! # The premise pool
//!
//! A premise is an environment constant whose declaration is a
//! [`ConstantKind::Theorem`] or [`ConstantKind::Axiom`] — a proof-carrying fact
//! whose `type_` is a proposition usable as a superposition clause. To keep the
//! closed-over proof term well typed WITHOUT level inference, only
//! universe-monomorphic premises (`level_params.is_empty()`) are pooled; the
//! tier-1/tier-2 goals are themselves monomorphic by construction (the
//! classifiers reject universe-polymorphism), so this is the natural match.
//!
//! # Soundness
//!
//! Premises guide the SEARCH only. The engine hands superposition the premise
//! statements as hypothesis CLAUSES (free-variable binders) and biases
//! E-matching by MePo relevance, but the proof term it returns references those
//! premises as synthetic free variables recorded in
//! [`clean_auto::ProofResult::proof_context`]. [`closeover_premise_fvars`]
//! substitutes each such free variable with the actual environment CONSTANT it
//! stands for (`FVar(id) ↦ @PremiseName`), producing a closed term that
//! references real declarations. That closed term is then replayed through the
//! UNCHANGED C1 gate ([`crate::graduate::recheck::recheck_and_classify`]): the
//! kernel re-checks it against the original goal type and computes its
//! transitive axiom closure. A premise-misled wrong proof is `KernelRejected`;
//! a proof that leans on a domain-axiom premise surfaces as `AxiomDependent`.
//! The kernel, not the premise layer, is the sole arbiter.

use super::timeout::{run_with_hard_timeout, ProofJob};
use clean_auto::prelude::{MePoSelector, PremiseDatabase, ProofResult, QuantifierOrigin};
use clean_kernel::{ConstantKind, Environment, Expr, FVarId, Level, LocalContext, Name};
use std::sync::Arc;
use std::time::Duration;

/// MePo relevance threshold for premise selection. Set high (above the engine
/// default of 0.1) so only premises sharing a substantial, distinctive symbol
/// fraction with the goal are admitted. A low threshold floods the prover with
/// weakly-related clauses, and the superposition saturation loop is quadratic in
/// the clause set: every extra premise multiplies the per-iteration inference
/// cost. Focus beats recall here.
const MEPO_THRESHOLD: f64 = 0.3;

/// Hard cap on the premises handed to a single goal. Each premise becomes a
/// superposition clause and the prover's `generate_clauses` step is quadratic in
/// the processed set, so an unbounded (or large) premise set makes a hard or
/// FALSE goal grind through the full iteration budget — minutes per goal. A
/// tight cap keeps the clause set in the goal's immediate neighbourhood and the
/// search bounded; MePo's ranking puts the load-bearing premises first.
const MAX_PREMISES_PER_GOAL: usize = 8;

/// A pooled premise: the environment constant name it refers to, its declared
/// universe parameters, and its statement (the proposition it proves). The name
/// is what the closed-over proof term references; the statement is both the
/// superposition clause and the key used to map a proof-context free variable
/// back to this premise.
///
/// A premise may be universe-POLYMORPHIC (`level_params` non-empty) — the
/// algebra-hierarchy lemmas (`mul_one`, `one_mul`, …) are exactly this shape. A
/// polymorphic premise is INSTANTIATED at the goal's universe params before it
/// is offered as a hypothesis or closed over (see [`EnvPremise::instantiated`]):
/// the per-goal database, the emitted clause, and the closed-over `@Name.{ls}`
/// const all carry the goal's concrete levels, so the kernel re-checks a
/// fully-applied term. A premise whose arity does not match the goal's params is
/// simply not instantiable for that goal and is skipped (fail-closed).
#[derive(Clone, Debug)]
pub(crate) struct EnvPremise {
    /// The environment constant this premise refers to (a `Theorem`/`Axiom`).
    pub(crate) name: Name,
    /// The constant's declared universe parameters (empty for a monomorphic
    /// premise). Instantiated at the goal's params at use time.
    pub(crate) level_params: Vec<Name>,
    /// The proposition the constant proves (its `type_`), as DECLARED — still
    /// universe-polymorphic if `level_params` is non-empty.
    pub(crate) statement: Expr,
}

impl EnvPremise {
    /// The premise's statement instantiated at the goal's universe params, and
    /// the level list to apply to the constant when closing over. For a
    /// monomorphic premise (`level_params` empty) this is the statement verbatim
    /// with an empty level list. For a polymorphic premise it substitutes the
    /// declared params by `goal_levels` positionally — sound only when the
    /// arities match, so `None` is returned otherwise (the premise is not usable
    /// for this goal; fail-closed).
    fn instantiated(&self, goal_levels: &[Level]) -> Option<(Expr, Vec<Level>)> {
        if self.level_params.is_empty() {
            return Some((self.statement.clone(), Vec::new()));
        }
        if self.level_params.len() != goal_levels.len() {
            return None;
        }
        let stmt = self
            .statement
            .instantiate_level_params_direct(&self.level_params, goal_levels);
        Some((stmt, goal_levels.to_vec()))
    }
}

/// The premise pool seeded from an [`Environment`]: a [`PremiseDatabase`] for
/// MePo scoring plus the parallel [`EnvPremise`] records (name + statement) the
/// worker needs to close proof-context free variables back over real constants.
pub(crate) struct PremisePool {
    /// The MePo database, behind an `Arc` so it can be SHARED into the prover's
    /// timeout worker thread by refcount bump rather than cloned (`PremiseDatabase`
    /// is not `Clone`, and the corpus database is large).
    db: Arc<PremiseDatabase>,
    /// Parallel to the database: the constant each `PremiseId` refers to.
    /// Indexed by insertion order, which matches the `PremiseId` assignment in
    /// [`PremiseDatabase::add`].
    premises: Vec<EnvPremise>,
}

impl PremisePool {
    /// Seed a premise pool from every theorem/axiom constant in `env` —
    /// universe-MONOMORPHIC and universe-POLYMORPHIC alike. These are the
    /// proof-carrying facts a goal can follow from; definitions are skipped (they
    /// are not propositions).
    ///
    /// Universe-polymorphic premises are exactly the algebra-hierarchy lemmas
    /// (`mul_one`, `one_mul`, `mul_assoc`, …) a universe-polymorphic goal needs.
    /// Their DECLARED (still-polymorphic) statement is what MePo scores by symbol
    /// overlap — the head symbols are level-invariant — and the per-goal
    /// instantiation at use time (see [`PremisePool::select_hypotheses`]) makes
    /// the emitted clause and the closed-over const concrete; the kernel
    /// re-checks the fully-applied term, so pooling them stays sound.
    pub(crate) fn from_env(env: &Environment) -> Self {
        let mut db = PremiseDatabase::new();
        let mut premises = Vec::new();
        for c in env.constants() {
            if !matches!(c.kind, ConstantKind::Theorem | ConstantKind::Axiom) {
                continue;
            }
            db.add(c.name.clone(), c.type_.clone());
            premises.push(EnvPremise {
                name: c.name.clone(),
                level_params: c.level_params.clone(),
                statement: c.type_.clone(),
            });
        }
        Self {
            db: Arc::new(db),
            premises,
        }
    }

    /// Number of pooled premises.
    pub(crate) fn len(&self) -> usize {
        self.premises.len()
    }

    /// Select the premises MePo scores most relevant to `goal`, as the
    /// `(statement, origin)` hypothesis pairs [`clean_auto::AutomationEngine`]
    /// expects. Each origin is [`QuantifierOrigin::Named`] carrying both the
    /// constant name and the `PremiseId`, so MePo's relevance bonus reaches the
    /// E-matching scorer.
    ///
    /// `goal_levels` are the goal's universe params (empty for a monomorphic
    /// goal). A universe-polymorphic premise's statement is INSTANTIATED at these
    /// levels before it is emitted as a clause — so the prover sees a concrete
    /// proposition over the goal's universes. A polymorphic premise whose arity
    /// does not match `goal_levels` is dropped (it is not instantiable for this
    /// goal; fail-closed).
    pub(crate) fn select_hypotheses(
        &self,
        goal: &Expr,
        goal_levels: &[Level],
    ) -> Vec<(Expr, Option<QuantifierOrigin>)> {
        let selector = MePoSelector::new(self.db.as_ref())
            .with_threshold(MEPO_THRESHOLD)
            .with_max_premises(MAX_PREMISES_PER_GOAL);
        selector
            .select(goal)
            .into_iter()
            .filter_map(|p| {
                // Map the MePo hit back to the pooled record to learn its
                // declared level params, then instantiate at the goal's levels.
                let env_premise = self.premises.iter().find(|e| e.name == p.name)?;
                let (statement, _levels) = env_premise.instantiated(goal_levels)?;
                let origin = QuantifierOrigin::new(p.name.clone(), p.id);
                Some((statement, Some(origin)))
            })
            .collect()
    }

    /// A shared handle to the MePo database, for moving into the prover's
    /// timeout worker thread without a (non-`Clone`, large) deep copy.
    pub(crate) fn db_arc(&self) -> Arc<PremiseDatabase> {
        Arc::clone(&self.db)
    }

    /// Find a pooled premise whose statement — INSTANTIATED at `goal_levels` —
    /// is exactly `statement`, returning the const expression `@Name.{ls}` that
    /// proves it (the level list `ls` is empty for a monomorphic premise, the
    /// goal's levels for a polymorphic one). Returns the FIRST match in pool
    /// order: when several constants share the same instantiated statement they
    /// are interchangeable as proofs of it, so substituting any one is
    /// type-correct. Returns `None` only when NO premise instantiates to that
    /// statement — a free variable we cannot close, which the caller treats as a
    /// fail-closed miss (the kernel would reject the open term anyway).
    fn premise_const_for_statement(&self, statement: &Expr, goal_levels: &[Level]) -> Option<Expr> {
        self.premises.iter().find_map(|p| {
            let (inst_stmt, levels) = p.instantiated(goal_levels)?;
            (&inst_stmt == statement).then(|| Expr::const_(p.name.clone(), levels))
        })
    }
}

/// Close every premise-introduced free variable in `proof` back over the
/// environment constant it stands for.
///
/// `auto_prove_with_premises` returns a proof term that references each premise
/// it used as a synthetic free variable, recorded in `proof_ctx` as a
/// [`clean_kernel::LocalContext`] decl whose `type_` is the premise statement.
/// For each such decl this substitutes `FVar(id) ↦ @ConstantName` using the
/// pool's statement→name map.
///
/// `extra_fvars` lists free variables that are NOT premises (e.g. tier-2's
/// peeled `∀` binders) and must be left untouched for a later re-abstraction
/// pass — a decl with one of these ids is skipped here.
///
/// `goal_levels` are the goal's universe params; a universe-polymorphic premise
/// was offered to the prover instantiated at these levels, so it is matched and
/// closed over at the SAME levels (the emitted const is `@Name.{goal_levels}`).
/// Empty for a monomorphic goal.
///
/// Returns `None` if any premise decl's statement maps to NO pooled constant:
/// the term could still carry that free variable, so closing it is impossible
/// and the caller must fail closed (the kernel would reject the open term
/// anyway). When several constants share a statement, any one is a valid proof
/// of it, so the first is chosen. Returns `Some(term)` with every premise free
/// variable replaced otherwise; whether the result is fully closed is still the
/// kernel's call at the C1 gate.
pub(crate) fn closeover_premise_fvars(
    pool: &PremisePool,
    proof: &Expr,
    proof_ctx: &LocalContext,
    extra_fvars: &[FVarId],
    goal_levels: &[Level],
) -> Option<Expr> {
    let mut term = proof.clone();
    for decl in proof_ctx.iter() {
        if extra_fvars.contains(&decl.id) {
            // A caller-owned binder (tier-2 peeled ∀); leave it for the
            // re-abstraction pass.
            continue;
        }
        // The premise the prover used was offered INSTANTIATED at the goal's
        // levels, so match the proof-context statement against the pool at those
        // levels and recover the concrete `@Name.{ls}` const that proves it.
        let const_expr = pool.premise_const_for_statement(&decl.type_, goal_levels)?;
        term = term.subst_fvar(decl.id, &const_expr);
    }
    Some(term)
}

/// Run the premise-guided hammer on `goal` under a HARD per-goal wall-clock
/// `timeout`, returning the proof result.
///
/// Selects the MePo-relevant premises from `pool` on the calling thread, then
/// runs [`clean_auto::AutomationEngine::auto_prove_with_premises`] on a
/// dedicated worker thread via [`run_with_hard_timeout`]. The prover's own
/// `timeout` only fires BETWEEN saturation iterations, so a single hard goal can
/// otherwise grind past the wall and hang the batch; the worker-thread
/// `recv_timeout` is the hard backstop that guarantees the caller regains
/// control after at most `timeout` and the loop makes progress. On timeout the
/// prover thread is detached (a bounded, transient leak), and the goal is a MISS.
///
/// The shared, immutable corpus data (`env`, the pool's database) crosses into
/// the thread behind `Arc`, so a spawn is a refcount bump, not a deep clone of
/// the (large) environment. The returned proof term still references the used
/// premises as free variables; the caller closes them with
/// [`closeover_premise_fvars`] and the C1 kernel gate certifies — soundness is
/// untouched, a timeout can only ever turn a would-be proof into a miss.
///
/// When `with_premises` is `false` (the BASELINE control mode) NO premises are
/// offered: the hypotheses are empty and the database is empty, so the engine's
/// reachability collapses to the bare hammer. The two modes share every other
/// input (env, timeout, `local_ctx`, the C1 gate downstream), so a count
/// difference between a premise-guided run and a bare run isolates the premise
/// lift.
pub(crate) fn prove_with_premises(
    env: &Arc<Environment>,
    pool: &PremisePool,
    goal: &Expr,
    timeout: Duration,
    local_ctx: Option<&LocalContext>,
    with_premises: bool,
    goal_levels: &[Level],
) -> Option<ProofResult> {
    let (hypotheses, premise_db) = if with_premises {
        (pool.select_hypotheses(goal, goal_levels), pool.db_arc())
    } else {
        // Bare control: empty hypotheses + an empty premise database. MePo is
        // skipped entirely, matching `auto_prove`'s premise-free reachability.
        (Vec::new(), Arc::new(PremiseDatabase::new()))
    };

    let job = ProofJob {
        env: Arc::clone(env),
        goal: goal.clone(),
        hypotheses,
        premise_db,
        local_ctx: local_ctx.cloned(),
    };
    run_with_hard_timeout(job, timeout)
}
