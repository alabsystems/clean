// Added in Clean: the resource budget of a step that expands a bit-vector (see checker/budget.rs).
pub mod budget;
// Added in Clean: the deadline a caller may set on a check (see checker/deadline.rs).
pub(crate) mod deadline;
pub mod error;
mod parallel;
mod rules;
mod sat_refutation;
mod scoping;
mod shared;

use crate::{
    ast::{
        pool::PrimitivePool, rare_rules::Rules, ContextStack, Problem, ProblemPrelude, Proof,
        ProofCommand, ProofIter, ProofStep, Rc, Term,
    },
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    external::{ExternalTool, SatTools},
    CarcaraResult, Error,
};
use carcara_macros::GenerateSetters;
use error::CheckerError;
use indexmap::{IndexMap, IndexSet};
use rules::{Premise, RuleArgs, RuleResult};
use shared::{check_assume_shared, check_step_core, StepCheckContext};
use std::{
    collections::HashSet,
    fmt,
    time::{Duration, Instant},
};

pub use parallel::{scheduler::Scheduler, ParallelProofChecker};

// The elaborator needs to use this function to elaborate `bfun_elim` steps
pub(crate) use rules::clausification::apply_bfun_elim;
pub(crate) use rules::linear_arithmetic::la_generic_partial;

#[derive(Clone)]
pub struct CheckerStatistics<'s, CR: CollectResults + Send + Default> {
    pub file_name: &'s str,
    pub polyeq_time: Duration,
    pub assume_time: Duration,

    // This is the time to compare the `assume` term with the `assert` that matches it. That is,
    // this excludes the time spent searching for the correct `assert` premise.
    pub assume_core_time: Duration,
    pub results: CR,
}

impl<CR: CollectResults + Send + Default> fmt::Debug for CheckerStatistics<'_, CR> {
    // Since `self.results` does not implement `Debug`, we can't just `#[derive(Debug)]` and instead
    // have to implement it manually, removing that field.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckerStatistics")
            .field("file_name", &self.file_name)
            .field("polyeq_time", &self.polyeq_time)
            .field("assume_time", &self.assume_time)
            .field("assume_core_time", &self.assume_core_time)
            .finish()
    }
}

#[derive(Debug, Default, Clone)]
pub enum SatRefConfig {
    #[default]
    None,
    Dedicated(ExternalTool),
    Sat(SatTools),
}

#[derive(Debug, Default, Clone, GenerateSetters)]
pub struct Config {
    /// Added in Clean: opt in to Clean's checked rule extensions. The default
    /// keeps the upstream rule contract (see DOWNSTREAM.md, Dialect).
    #[skip_setter]
    clean_dialect: bool,

    /// Added in Clean: the separately versioned bounded offset-spine rule.
    /// Neither the default nor the older Clean dialect enables it implicitly.
    #[skip_setter]
    bv_offset_spines_v1: bool,

    /// Separately versioned full-width reconstruction; default remains false.
    #[skip_setter]
    bv_reconstruct_v1: bool,
    /// Added in Clean: constant-array read capability. Standard remains off;
    /// the updated explicitly selected Clean dialect implements version one.
    #[skip_setter]
    array_const_select_v1: bool,

    /// If `true`, the checker will assume that the proof is elaborated, and enforce extra
    /// restrictions when checking it.
    ///
    /// Currently, if enabled, the following rules are affected:
    /// - `assume` and `refl`: implicit reordering of equalities is not allowed
    /// - `resolution` and `th_resolution`: the pivots must be provided as arguments
    elaborated: bool,

    /// If `true`, the checker will skip any steps with rules that it does not recognize, and will
    /// consider them as holes. Normally, using an unknown rule is considered an error.
    ignore_unknown_rules: bool,

    /// If `true`, the checker will check resolution steps using only Reverse Unit Propagation
    /// (RUP). Normally, we use a greedy algorithm first, and use RUP as a fallback.
    rup_resolution: bool,

    /// A set of rule names that the checker will allow, considering them holes in the proof.
    #[skip_setter]
    allowed_rules: HashSet<String>,

    rule_checkers: IndexMap<String, ExternalTool>,

    sat_ref_config: SatRefConfig,

    /// Added in Clean: the instant the check must end by, if any. The checker reads the clock
    /// before and after every command, and its comparisons poll it; a command that ends past it
    /// is refused with `CheckerError::DeadlineExceeded` (see checker/deadline.rs).
    #[skip_setter]
    deadline: Option<Instant>,
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }

    /// Added in Clean: the rule configuration paired with
    /// `parser::Config::clean_dialect()`. This is an explicit dialect, not a
    /// claim that the pinned upstream checker implements these extensions.
    pub fn clean_dialect() -> Self {
        Self {
            clean_dialect: true,
            array_const_select_v1: true,
            ..Self::default()
        }
    }

    /// Added in Clean: explicitly consume
    /// `dialect:eq_simplify_bv_offset_spines_v1`. This does not change the
    /// existing `eq_simplify` contract or enable any other rule extension.
    pub fn with_bv_offset_spines_v1(mut self) -> Self {
        self.bv_offset_spines_v1 = true;
        self
    }

    /// Explicitly consume `dialect:bv_reconstruct_v1`, without changing any
    /// default, existing scalar rule or pinned-reader contract.
    pub fn with_bv_reconstruct_v1(mut self) -> Self {
        self.bv_reconstruct_v1 = true;
        self
    }

    /// A set of rule names that the checker will allow, considering them holes in the proof.
    pub fn allowed_rules(mut self, values: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.allowed_rules = values.into_iter().map(Into::into).collect();
        self
    }

    /// Added in Clean: the instant the check must end by (`None`, the default, for none). See
    /// checker/deadline.rs.
    pub fn deadline(mut self, deadline: Option<Instant>) -> Self {
        self.deadline = deadline;
        self
    }
}

/// Added in Clean: the refusal of `command`, which ran past the check's deadline.
fn deadline_exceeded(command: &ProofCommand) -> Error {
    let rule = match command {
        ProofCommand::Step(step) => step.rule.as_str(),
        ProofCommand::Subproof(_) => "anchor",
        ProofCommand::Assume { .. } => "assume",
    };
    Error::Checker {
        inner: CheckerError::DeadlineExceeded,
        rule: rule.into(),
        step: command.id().into(),
    }
}

pub struct ProofChecker<'c> {
    pool: &'c mut PrimitivePool,
    config: Config,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
    rare_rules: &'c Rules,
}

impl<'c> ProofChecker<'c> {
    pub fn new(pool: &'c mut PrimitivePool, rare_rules: &'c Rules, config: Config) -> Self {
        ProofChecker {
            pool,
            config,
            context: ContextStack::new(),
            reached_empty_clause: false,
            is_holey: false,
            rare_rules,
        }
    }

    pub fn check(&mut self, problem: &Problem, proof: &Proof) -> CarcaraResult<bool> {
        self.check_impl(
            problem,
            proof,
            None::<&mut CheckerStatistics<OnlineBenchmarkResults>>,
        )
    }

    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<bool> {
        self.check_impl(problem, proof, Some(stats))
    }

    fn check_impl<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<bool> {
        // Modified in Clean: the deadline is read before and after every command, and a command
        // that ends past it is refused whatever it found (a comparison that saw the deadline pass
        // stopped early); see checker/deadline.rs.
        let _deadline = deadline::arm(self.config.deadline);
        // Similarly to the parser, to avoid stack overflows in proofs with many nested subproofs,
        // we check the subproofs iteratively, instead of recursively
        let mut iter = proof.iter();
        while let Some(command) = iter.next() {
            if deadline::expired_now() {
                return Err(deadline_exceeded(command));
            }
            let outcome = self.check_command(command, &iter, problem, &mut stats);
            if deadline::expired_now() {
                return Err(deadline_exceeded(command));
            }
            outcome?;
        }
        if self.reached_empty_clause {
            Ok(self.is_holey)
        } else {
            Err(Error::DoesNotReachEmptyClause)
        }
    }

    /// One command of `check_impl`'s loop: its step, anchor or assumption is checked.
    fn check_command<CR: CollectResults + Send + Default>(
        &mut self,
        command: &ProofCommand,
        iter: &ProofIter,
        problem: &Problem,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<()> {
        match command {
            ProofCommand::Step(step) => {
                let is_end_of_subproof = iter.is_end_step();

                // If this step ends a subproof, it might need to implicitly reference the
                // previous command in the subproof
                let previous_command = if is_end_of_subproof {
                    let subproof = iter.current_subproof().unwrap();
                    let index = subproof.len() - 2;
                    subproof
                        .get(index)
                        .map(|command| Premise::new((iter.depth(), index), command))
                } else {
                    None
                };
                self.check_step(step, previous_command, iter, stats, &problem.prelude)
                    .map_err(|e| Error::Checker {
                        inner: e,
                        rule: step.rule.as_str().into(),
                        step: step.id.as_str().into(),
                    })?;

                // If this is the last command of a subproof, we have to pop the subproof
                // commands off of the stack. The parser already ensures that the last command
                // in a subproof is always a `step` command
                if is_end_of_subproof {
                    self.context.pop();
                }

                // Note that for the purpose of whether the proof of the input assumptions
                // concludes the empty clause this test must be made only when the context is
                // empty, i.e., when we are not in a subproof
                if step.clause.is_empty() && self.context.is_empty() {
                    self.reached_empty_clause = true;
                }
            }
            ProofCommand::Subproof(s) => {
                let time = Instant::now();
                let step_id = command.id();

                self.context.push(&s.args);

                if let Some(stats) = stats {
                    let rule_name = match s.commands.last() {
                        Some(ProofCommand::Step(step)) => format!("anchor({})", &step.rule),
                        _ => "anchor".to_owned(),
                    };
                    stats.results.add_step_measurement(
                        stats.file_name,
                        step_id,
                        &rule_name,
                        time.elapsed(),
                    );
                }
            }
            ProofCommand::Assume { id, term } => {
                if !self.check_assume(id, term, &problem.premises, iter, stats) {
                    return Err(Error::Checker {
                        inner: CheckerError::Assume(term.clone()),
                        rule: "assume".into(),
                        step: id.as_str().into(),
                    });
                }
            }
        }
        Ok(())
    }

    fn check_assume<'i, CR: CollectResults + Send + Default>(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &IndexSet<Rc<Term>>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> bool {
        check_assume_shared(
            id,
            term,
            premises,
            &self.config,
            iter.is_in_subproof(),
            stats,
        )
    }

    fn check_step<'i, CR: CollectResults + Send + Default>(
        &mut self,
        step: &ProofStep,
        previous_command: Option<Premise>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
        prelude: &ProblemPrelude,
    ) -> RuleResult {
        let mut polyeq_time = Duration::ZERO;

        // Collect premises and discharge - this part is iterator-specific
        let premises: Vec<_> = step
            .premises
            .iter()
            .map(|&p| {
                let command = iter.get_premise(p);
                Premise::new(p, command)
            })
            .collect();
        let discharge: Vec<_> = step
            .discharge
            .iter()
            .map(|&i| iter.get_premise(i))
            .collect();

        // TODO: for now, sat refutation and calling external solvers is only supported in
        // sequential checking mode
        if step.rule == "sat_refutation" && !self.config.allowed_rules.contains("sat_refutation") {
            // Modified in Clean: this path bypasses `check_step_core`, so it applies the same
            // scoping rules (see checker/scoping.rs): premises may not cross an anchor that binds
            // one of their names, and only a context rule may end an anchor with arguments.
            scoping::check_premise_scoping(
                &premises,
                &self.context,
                self.pool,
                iter.is_end_step(),
            )?;
            if iter.is_end_step()
                && self
                    .context
                    .last()
                    .is_some_and(|ctx| ctx.as_ref().is_some_and(|ctx| !ctx.args.is_empty()))
            {
                return Err(CheckerError::Explanation(
                    "rule 'sat_refutation' cannot end a subproof whose anchor has arguments"
                        .to_owned(),
                ));
            }
            let premises_steps: Vec<_> =
                step.premises.iter().map(|&p| iter.get_premise(p)).collect();
            return sat_refutation::sat_refutation(
                self.pool,
                premises_steps,
                prelude,
                &self.config.sat_ref_config,
            );
        }

        // Prepare rule arguments - this is pool-specific
        let rule_args = RuleArgs {
            conclusion: &step.clause,
            premises: &premises,
            args: &step.args,
            pool: self.pool,
            context: &mut self.context,
            previous_command,
            discharge: &discharge,
            polyeq_time: &mut polyeq_time,
            rare_rules: self.rare_rules,
        };

        // Use shared core logic
        let context = StepCheckContext {
            config: &self.config,
            is_end_step: iter.is_end_step(),
            current_subproof: iter.current_subproof(),
            subproof_depth: iter.depth(),
            is_holey: &mut self.is_holey,
        };

        let result = check_step_core(step, rule_args, context, stats);

        // Update polyeq time in stats (this was previously done in the core,
        // but polyeq_time is updated via the mutable reference in rule_args)
        if let Some(s) = stats {
            s.polyeq_time += polyeq_time;
        }

        result
    }
}
