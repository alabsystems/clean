// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `TacticM` — a fluent, composable tactic-building surface over `ProofState`.
//!
//! Keystone B of the Lean-4-drop-in plan (Phase 2 Tier-2; see
//! `designs/2026-06-23-native-tacticm-monad.md`). This is the **ProofState-side
//! core**: combinators that wrap the existing kernel-checked
//! `fn(&mut ProofState) -> TacticResult` tactics and chain with `?`, giving Rust
//! code (the future user-defined-tactic facility and the do-block executor) a
//! single composable API instead of threading `&mut ProofState` by hand.
//!
//! It deliberately needs **no `TacticEval`**: every method here delegates to a
//! tactic that operates purely on the proof state, so it is self-contained and
//! directly testable. The recursive, `eval`-requiring combinators (running a
//! parsed sub-tactic / sequence) are a later step that takes a
//! `&mut dyn TacticEval` callback, layered on top of this core without changing
//! it.
//!
//! ## Soundness
//!
//! `TacticM` closes goals only through the wrapped tactics, which themselves go
//! through the kernel-checked `close_goal`/`exact`/`replace_target_*` paths. It
//! introduces no axioms and no `add_decl_unchecked`.

use clean_kernel::{Expr, FVarId};
use clean_parser::SurfaceTactic;

use super::registry::TacticEval;
use super::{ProofState, TacticError};

/// A fluent handle over a [`ProofState`] for composing tactics in Rust.
///
/// Methods that run a tactic return `Result<&mut Self, TacticError>` so steps
/// chain with `?`: `TacticM::new(ps).intro("h")?.assumption()?`.
pub struct TacticM<'a> {
    ps: &'a mut ProofState,
}

impl<'a> TacticM<'a> {
    /// Wrap a proof state for fluent tactic composition.
    pub fn new(ps: &'a mut ProofState) -> Self {
        Self { ps }
    }

    /// Borrow the underlying proof state (e.g. to inspect goals).
    #[must_use]
    pub fn state(&self) -> &ProofState {
        self.ps
    }

    /// `intro name` — introduce the binder of a `∀`/`→` goal as `name`.
    pub fn intro(&mut self, name: &str) -> Result<&mut Self, TacticError> {
        super::intro(self.ps, name)?;
        Ok(self)
    }

    /// `intro n1 n2 …` — introduce several binders at once, in order.
    pub fn intros(&mut self, names: &[&str]) -> Result<&mut Self, TacticError> {
        super::intros(self.ps, names.iter().map(|s| (*s).to_string()).collect())?;
        Ok(self)
    }

    /// `intro name`, returning the introduced hypothesis's [`FVarId`] so a script
    /// can refer to it later (e.g. `exact`/`apply` that hypothesis). Unlike the
    /// chaining combinators this yields the fvar rather than `&mut Self`.
    pub fn intro_get(&mut self, name: &str) -> Result<FVarId, TacticError> {
        super::intro(self.ps, name)?;
        self.ps
            .current_goal()
            .and_then(|g| {
                g.local_ctx
                    .iter()
                    .rev()
                    .find(|d| d.name == name)
                    .map(|d| d.fvar)
            })
            .ok_or_else(|| TacticError::HypothesisNotFound(name.to_string()))
    }

    /// `assumption` — close the goal with a matching local hypothesis.
    pub fn assumption(&mut self) -> Result<&mut Self, TacticError> {
        super::assumption(self.ps)?;
        Ok(self)
    }

    /// `whnf` — reduce the goal target to weak-head normal form (defeq).
    pub fn whnf(&mut self) -> Result<&mut Self, TacticError> {
        super::whnf(self.ps)?;
        Ok(self)
    }

    /// `exact proof` — close the goal with `proof`, kernel-checked against the
    /// goal type.
    pub fn exact(&mut self, proof: Expr) -> Result<&mut Self, TacticError> {
        super::exact(self.ps, proof)?;
        Ok(self)
    }

    /// `constructor` — apply the unique applicable constructor of the goal's
    /// inductive type.
    pub fn constructor(&mut self) -> Result<&mut Self, TacticError> {
        super::constructor(self.ps)?;
        Ok(self)
    }

    /// `exfalso` — replace the goal with `False`.
    pub fn exfalso(&mut self) -> Result<&mut Self, TacticError> {
        super::exfalso(self.ps)?;
        Ok(self)
    }

    /// `apply f` — apply `f` to the goal, leaving its unfilled premises as new
    /// goals (forward reasoning / modus ponens). Kernel-checked.
    pub fn apply(&mut self, func: Expr) -> Result<&mut Self, TacticError> {
        super::apply(self.ps, func)?;
        Ok(self)
    }

    /// `rfl` — close a reflexivity goal (`a = a`, `a ↔ a`, `HEq a a`, …) when both
    /// sides are definitionally equal.
    pub fn rfl(&mut self) -> Result<&mut Self, TacticError> {
        super::rfl(self.ps)?;
        Ok(self)
    }

    /// Run a parsed sub-tactic through the elaborator's `evaluator` against the
    /// current state — the recursive combinator that lets a `TacticM` script
    /// invoke ANY registered tactic. This is the basis of the do-block executor
    /// and user-defined tactics; layered on the ProofState-side core above.
    pub fn eval(
        &mut self,
        evaluator: &mut dyn TacticEval,
        tac: &SurfaceTactic,
    ) -> Result<&mut Self, TacticError> {
        evaluator.eval(self.ps, tac)?;
        Ok(self)
    }

    /// Run a sequence of parsed sub-tactics left-to-right through `evaluator`.
    pub fn eval_seq(
        &mut self,
        evaluator: &mut dyn TacticEval,
        tacs: &[SurfaceTactic],
    ) -> Result<&mut Self, TacticError> {
        evaluator.eval_seq(self.ps, tacs)?;
        Ok(self)
    }

    /// The current main goal's target, if any goals remain.
    #[must_use]
    pub fn main_target(&self) -> Option<Expr> {
        self.ps.current_goal().map(|g| g.target.clone())
    }

    /// Whether every goal has been closed.
    #[must_use]
    pub fn is_solved(&self) -> bool {
        self.ps.goals.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::TacticM;
    use crate::tactic::registry::{ElaboratedRefine, TacticEval};
    use crate::tactic::tactic_registry::UserTacticRegistry;
    use crate::tactic::{ProofState, TacticError};
    use crate::unify::MetaState;
    use clean_kernel::{Declaration, Environment, Expr, Level, Name};
    use clean_parser::{SurfaceExpr, SurfaceTactic};

    /// Minimal `TacticEval` whose `eval_seq` clears all goals (standing in for a
    /// goal-closing sub-tactic sequence), so a test can verify `TacticM` threads
    /// its `ProofState` to the evaluator and the evaluator's effect persists.
    struct ClearingEval {
        eval_seq_calls: usize,
        metas: MetaState,
    }
    impl TacticEval for ClearingEval {
        fn eval(&mut self, _ps: &mut ProofState, _tac: &SurfaceTactic) -> Result<(), TacticError> {
            unreachable!("test exercises eval_seq only")
        }
        fn eval_seq(
            &mut self,
            ps: &mut ProofState,
            _tacs: &[SurfaceTactic],
        ) -> Result<(), TacticError> {
            self.eval_seq_calls += 1;
            ps.goals.clear();
            Ok(())
        }
        fn elaborate(&mut self, _e: &SurfaceExpr) -> Result<Expr, TacticError> {
            unreachable!("not exercised")
        }
        fn infer_type(&mut self, _e: &Expr) -> Result<Expr, TacticError> {
            unreachable!("not exercised")
        }
        fn elaborate_refine(
            &mut self,
            _ps: &ProofState,
            _e: &SurfaceExpr,
        ) -> Result<ElaboratedRefine, TacticError> {
            unreachable!("not exercised")
        }
        fn metas(&self) -> &MetaState {
            &self.metas
        }
    }

    fn prop_axiom_env(names: &[&str]) -> Environment {
        let mut env = Environment::new();
        for name in names {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("register prop axiom");
        }
        env
    }

    #[test]
    fn tacticm_intro_assumption_proves_p_implies_p() {
        let env = prop_axiom_env(&["P"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let mut ps = ProofState::new(env, Expr::arrow(p.clone(), p));

        let mut tac = TacticM::new(&mut ps);
        tac.intro("h")
            .expect("intro on `P → P`")
            .assumption()
            .expect("assumption closes `P` from `h : P`");

        assert!(
            tac.is_solved(),
            "intro; assumption should solve `P → P`, remaining goals: {}",
            tac.state().current_goal().is_some() as u8
        );
    }

    #[test]
    fn tacticm_intros_multiple_binders_then_exact() {
        let env = prop_axiom_env(&["P", "Q"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let q = Expr::const_(Name::from_string("Q"), vec![]);
        // Goal: `P → Q → P`.
        let goal = Expr::arrow(p.clone(), Expr::arrow(q, p.clone()));
        let mut ps = ProofState::new(env, goal);

        let mut tac = TacticM::new(&mut ps);
        tac.intros(&["hp", "hq"]).expect("intros hp hq");
        let hp = tac
            .state()
            .current_goal()
            .expect("goal `P` remains")
            .local_ctx
            .iter()
            .find(|d| d.name == "hp")
            .expect("hp introduced")
            .fvar;
        tac.exact(Expr::fvar(hp)).expect("exact hp closes P");

        assert!(tac.is_solved(), "intros hp hq; exact hp solves `P → Q → P`");
    }

    #[test]
    fn tacticm_exact_with_introduced_hyp_proves_p_implies_p() {
        let env = prop_axiom_env(&["P"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let mut ps = ProofState::new(env, Expr::arrow(p.clone(), p));

        let mut tac = TacticM::new(&mut ps);
        tac.intro("h").expect("intro on `P → P`");
        // Recover the introduced hypothesis's fvar (FVarId is Copy, so the borrow
        // on `tac` ends before the `exact` call).
        let h = tac
            .state()
            .current_goal()
            .expect("goal `P` remains")
            .local_ctx
            .iter()
            .find(|d| d.name == "h")
            .expect("intro added `h`")
            .fvar;
        tac.exact(Expr::fvar(h))
            .expect("`exact h` closes `P` with `h : P`");

        assert!(tac.is_solved(), "intro; exact h should solve `P → P`");
    }

    #[test]
    fn tacticm_eval_seq_threads_state_through_evaluator() {
        let env = prop_axiom_env(&["P"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let mut ps = ProofState::new(env, Expr::arrow(p.clone(), p));

        let mut tac = TacticM::new(&mut ps);
        let mut ev = ClearingEval {
            eval_seq_calls: 0,
            metas: MetaState::new(),
        };
        tac.eval_seq(&mut ev, &[])
            .expect("eval_seq delegates to the evaluator");

        assert_eq!(
            ev.eval_seq_calls, 1,
            "evaluator.eval_seq invoked exactly once"
        );
        assert!(
            tac.is_solved(),
            "the evaluator's goal-clearing effect threads through TacticM's ProofState",
        );
    }

    #[test]
    fn tacticm_apply_then_assumption_solves_modus_ponens() {
        let env = prop_axiom_env(&["P", "Q"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let q = Expr::const_(Name::from_string("Q"), vec![]);
        // Goal: `P → (P → Q) → Q`.
        let pq = Expr::arrow(p.clone(), q.clone());
        let goal = Expr::arrow(p, Expr::arrow(pq, q));
        let mut ps = ProofState::new(env, goal);

        let mut tac = TacticM::new(&mut ps);
        tac.intro("hp")
            .expect("intro hp : P")
            .intro("h")
            .expect("intro h : P → Q");
        let h = tac
            .state()
            .current_goal()
            .expect("goal `Q` remains")
            .local_ctx
            .iter()
            .find(|d| d.name == "h")
            .expect("h was introduced")
            .fvar;
        // `apply h` reduces goal `Q` to premise `P`; `assumption` closes it with hp.
        tac.apply(Expr::fvar(h))
            .expect("apply h : P → Q to goal Q")
            .assumption()
            .expect("assumption closes premise P with hp");

        assert!(
            tac.is_solved(),
            "intro hp; intro h; apply h; assumption ⊢ Q"
        );
    }

    #[test]
    fn user_tactic_handler_composes_via_tacticm() {
        // A registered user tactic receives `&mut ProofState`; it can wrap it in
        // `TacticM` and compose the kernel-checked combinators. This is the
        // Phase-3 user-defined-tactic path — enabled with NO registry change,
        // because `TacticM` is `pub` and borrows the state the handler already has.
        let mut reg = UserTacticRegistry::new();
        reg.register(
            "intro_assumption",
            |_args: &[SurfaceTactic], ps: &mut ProofState| {
                TacticM::new(ps).intro("h")?.assumption()?;
                Ok(())
            },
            "intro then assumption, composed through TacticM",
        );

        let env = prop_axiom_env(&["P"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let mut ps = ProofState::new(env, Expr::arrow(p.clone(), p));
        reg.dispatch("intro_assumption", &[], &mut ps)
            .expect("user tactic composed through TacticM should run");

        assert!(
            ps.goals.is_empty(),
            "the TacticM-composed user tactic should solve `P → P`",
        );
    }

    #[test]
    fn tacticm_intro_get_returns_hyp_for_exact() {
        let env = prop_axiom_env(&["P"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let mut ps = ProofState::new(env, Expr::arrow(p.clone(), p));

        let mut tac = TacticM::new(&mut ps);
        let h = tac.intro_get("h").expect("intro_get h : P");
        tac.exact(Expr::fvar(h)).expect("exact h closes P");

        assert!(tac.is_solved(), "intro_get + exact should solve `P → P`");
    }

    #[test]
    fn tacticm_rfl_closes_reflexivity_goal() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("a"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
        })
        .unwrap();

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        // Goal: `@Eq Nat a a`.
        let goal = Expr::app(Expr::app(Expr::app(eq, nat), a.clone()), a);

        let mut ps = ProofState::new(env, goal);
        let mut tac = TacticM::new(&mut ps);
        tac.rfl().expect("rfl closes `a = a`");
        assert!(tac.is_solved(), "rfl should solve `@Eq Nat a a`");
    }

    #[test]
    fn user_tactic_runs_imperative_tacticm_script() {
        // The do-block executor's substance: a user tactic runs a multi-step
        // imperative `TacticM` script (intro; intro_get; apply; assumption) to
        // prove modus ponens — every step kernel-checked. Only the Lean-surface
        // `do` syntax (a clean-parser change) is separate from this executor.
        let mut reg = UserTacticRegistry::new();
        reg.register(
            "mp",
            |_args: &[SurfaceTactic], ps: &mut ProofState| {
                let mut tac = TacticM::new(ps);
                tac.intro("hp")?;
                let h = tac.intro_get("h")?;
                tac.apply(Expr::fvar(h))?.assumption()?;
                Ok(())
            },
            "modus ponens via an imperative TacticM script",
        );

        let env = prop_axiom_env(&["P", "Q"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let q = Expr::const_(Name::from_string("Q"), vec![]);
        // Goal: `P → (P → Q) → Q`.
        let goal = Expr::arrow(p.clone(), Expr::arrow(Expr::arrow(p, q.clone()), q));
        let mut ps = ProofState::new(env, goal);

        reg.dispatch("mp", &[], &mut ps)
            .expect("imperative TacticM script should run");
        assert!(
            ps.goals.is_empty(),
            "the script should prove `P → (P → Q) → Q`"
        );
    }

    #[test]
    fn tacticm_main_target_tracks_goal() {
        let env = prop_axiom_env(&["P", "Q"]);
        let p = Expr::const_(Name::from_string("P"), vec![]);
        let q = Expr::const_(Name::from_string("Q"), vec![]);
        let mut ps = ProofState::new(env, Expr::arrow(p, q.clone()));

        let mut tac = TacticM::new(&mut ps);
        // Before intro the target is `P → Q`; after, it is `Q`.
        tac.intro("h").expect("intro on `P → Q`");
        assert_eq!(tac.main_target(), Some(q));
        assert!(!tac.is_solved(), "goal `Q` is not closed by intro alone");
    }
}
