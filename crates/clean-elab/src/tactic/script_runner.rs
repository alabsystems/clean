// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared tactic-script parsing/execution for server handlers and oracle replay.

pub mod comment_strip;

use crate::elaborate;
use crate::tactic as elab_tactic;
use clean_auto::oracle::{OracleCandidate, OracleCandidateRunner, OracleRunError};
use clean_auto::ProofResult;
use clean_kernel::{Environment, Expr, LocalContext, TypeChecker};
use clean_parser::parse_expr;
use std::time::{Duration, Instant};

/// Strip a Lean-style line comment (`-- ...`) from a tactic fragment.
fn strip_line_comment(s: &str) -> &str {
    match s.find("--") {
        Some(pos) => &s[..pos],
        None => s,
    }
}

/// Parse a tactic script into individual tactics.
///
/// Strips `/- ... -/` block comments (including nested), splits by newlines and
/// semicolons, strips `-- ...` line comments, trims whitespace, and filters
/// empty fragments.  This prevents standalone proof comments from becoming
/// spurious `UnknownIdent` errors during replay.
pub fn parse_tactic_script(script: &str) -> Vec<String> {
    let block_stripped = comment_strip::strip_block_comments(script);
    block_stripped
        .lines()
        .flat_map(|line| line.split(';'))
        .map(|s| strip_line_comment(s).trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

fn parse_option_value_literal(raw: &str) -> elab_tactic::OptionValue {
    match raw {
        "true" => elab_tactic::OptionValue::Bool(true),
        "false" => elab_tactic::OptionValue::Bool(false),
        _ => match raw.parse::<u64>() {
            Ok(n) => elab_tactic::OptionValue::Nat(n),
            Err(_) => {
                let unquoted = raw
                    .strip_prefix('"')
                    .and_then(|s| s.strip_suffix('"'))
                    .unwrap_or(raw);
                elab_tactic::OptionValue::String(unquoted.to_string())
            }
        },
    }
}

/// Parse the optional repeat count for `rotate_left` / `rotate_right`.
///
/// Lean's `rotate_left`/`rotate_right` take an optional count that defaults to 1.
fn parse_rotate_count(tactic: &str, raw: Option<&str>) -> Result<usize, elab_tactic::TacticError> {
    match raw {
        Some(s) => s
            .parse::<usize>()
            .map_err(|_| elab_tactic::TacticError::InvalidTarget {
                tactic: tactic.to_string(),
                detail: format!("expected a non-negative count, got `{s}`"),
            }),
        None => Ok(1),
    }
}

/// Parse the optional max-depth argument for `solve_by_elim`.
///
/// Mirrors Lean's `solve_by_elim`, whose backtracking search defaults to a
/// max depth of 6 when no `maxDepth` is supplied.
fn parse_solve_by_elim_depth(raw: Option<&str>) -> Result<usize, elab_tactic::TacticError> {
    match raw {
        Some(s) => s
            .parse::<usize>()
            .map_err(|_| elab_tactic::TacticError::InvalidTarget {
                tactic: "solve_by_elim".to_string(),
                detail: format!("expected a non-negative max depth, got `{s}`"),
            }),
        None => Ok(6),
    }
}

/// Extract the hypothesis named by a Lean-style `at <hyp>` target, if present.
///
/// Returns `Some(hyp)` for token streams like `push_neg at h` or
/// `unfold foo at h`, and `None` when there is no `at` keyword (the tactic then
/// applies to the goal). A bare trailing `at` with no following name yields
/// `None`, falling back to the goal-directed form.
fn at_target<'a>(parts: &[&'a str]) -> Option<&'a str> {
    let idx = parts.iter().position(|&p| p == "at")?;
    parts.get(idx + 1).copied()
}

fn resolve_expr_in_context(
    proof_state: &elab_tactic::ProofState,
    expr_str: &str,
    env: &Environment,
    tactic: &str,
) -> Result<Expr, elab_tactic::TacticError> {
    if !expr_str.chars().any(char::is_whitespace) {
        if let Some(goal) = proof_state.current_goal() {
            if let Some(decl) = goal.local_ctx.iter().find(|decl| decl.name == expr_str) {
                return Ok(Expr::fvar(decl.fvar));
            }
        }
    }

    let surface_expr = parse_expr(expr_str).map_err(|e| elab_tactic::TacticError::ParseFailed {
        tactic: tactic.to_string(),
        detail: format!("{e}"),
    })?;
    elaborate(env, &surface_expr).map_err(elab_tactic::TacticError::from_elab_error)
}

/// Execute a simple tactic (dispatcher for common tactics).
pub fn execute_simple_tactic(
    proof_state: &mut elab_tactic::ProofState,
    tactic_str: &str,
    env: &Environment,
) -> Result<(), elab_tactic::TacticError> {
    use elab_tactic::{abel, ac_rfl, cc, gcongr, group, norm_cast, positivity, solve_by_elim};
    use elab_tactic::{
        admit, aesop, ay_smt, cases, cert_mathverse, cert_simp, constructor, decide, funext,
        induction, linarith, native_decide, nlinarith, norm_num, omega, rewrite, rewrite_ltr,
        rewrite_rtl, ring, ring_nf, simp_all, simp_default, simp_only, sorry, split_, symm, tauto,
        AyConfig,
    };
    use elab_tactic::{apply, exact, intro, rfl, TacticError};
    use elab_tactic::{blast, grind};
    use elab_tactic::{by_contra, clear, contrapose, contrapose_hyp, field_simp, push_neg, rename};
    use elab_tactic::{
        contradiction, exfalso, itauto, left_, right_, rotate, rotate_back, subst, subst_vars, swap,
    };
    use elab_tactic::{convert, discriminate, injection, interval_cases};
    use elab_tactic::{delta, ext, fin_cases, revert, unfold};
    use elab_tactic::{norm_num_at, push_neg_at, unfold_at};

    let parts: Vec<&str> = tactic_str.split_whitespace().collect();
    if parts.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "".to_string(),
            expected: "tactic name".to_string(),
        });
    }

    let result = match parts[0] {
        "intro" => {
            let name = parts
                .get(1)
                .map(|s| s.to_string())
                .unwrap_or_else(|| "h".to_string());
            intro(proof_state, &name)
        }
        "intros" => {
            let names: Vec<String> = parts[1..].iter().map(|s| s.to_string()).collect();
            elab_tactic::intros(proof_state, names)
        }
        "exact" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "exact".to_string(),
                    expected: "expression".to_string(),
                });
            }
            let expr = resolve_expr_in_context(proof_state, &parts[1..].join(" "), env, "exact")?;
            exact(proof_state, expr)
        }
        "apply" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "apply".to_string(),
                    expected: "expression".to_string(),
                });
            }
            let expr = resolve_expr_in_context(proof_state, &parts[1..].join(" "), env, "apply")?;
            apply(proof_state, expr)
        }
        "constructor" => constructor(proof_state),
        "split" => split_(proof_state),
        "rfl" => rfl(proof_state),
        "trivial" => elab_tactic::trivial(proof_state),
        "assumption" => elab_tactic::assumption(proof_state),
        "sorry" => sorry(proof_state),
        "admit" => admit(proof_state),
        "simp" => {
            if parts.len() > 1 && parts[1] == "only" {
                let lemmas: Vec<String> = parts[2..]
                    .iter()
                    .map(|s| {
                        s.trim_matches(|c| c == '[' || c == ']' || c == ',')
                            .to_string()
                    })
                    .filter(|s| !s.is_empty())
                    .collect();
                simp_only(proof_state, lemmas)
            } else {
                simp_default(proof_state)
            }
        }
        "simp_all" => simp_all(proof_state),
        "ring" => ring(proof_state),
        "ring_nf" => ring_nf(proof_state),
        "norm_num" => match at_target(&parts) {
            Some(hyp) => norm_num_at(proof_state, hyp),
            None => norm_num(proof_state),
        },
        "omega" => omega(proof_state),
        "cert_mathverse" => cert_mathverse(proof_state),
        "cert_simp" => cert_simp(proof_state),
        "linarith" => linarith(proof_state),
        "nlinarith" => nlinarith(proof_state),
        "decide" => decide(proof_state),
        "native_decide" => native_decide(proof_state),
        "set_option" => {
            if parts.len() < 3 {
                return Err(TacticError::MissingArgument {
                    tactic: "set_option".to_string(),
                    expected: "<option> <value>".to_string(),
                });
            }
            let key = parts[1];
            let value = parse_option_value_literal(&parts[2..].join(" "));
            elab_tactic::set_option(proof_state, key, value)
        }
        "ay_smt" => ay_smt(proof_state, AyConfig::from_env()),
        "aesop" => aesop(proof_state),
        "tauto" => tauto(proof_state),
        "cases" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "cases".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            cases(proof_state, parts[1])
        }
        "induction" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "induction".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            induction(proof_state, parts[1])
        }
        "rewrite" | "rw" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "rewrite".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            let hyp = parts[1].trim_start_matches('←').trim_start_matches("<-");
            let reverse = parts[1].starts_with('←') || parts[1].starts_with("<-");
            rewrite(proof_state, hyp, reverse)
        }
        "rw_ltr" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "rw_ltr".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            rewrite_ltr(proof_state, parts[1])
        }
        "rw_rtl" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "rw_rtl".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            rewrite_rtl(proof_state, parts[1])
        }
        "symm" => symm(proof_state),
        "funext" => {
            let name = parts
                .get(1)
                .map(|s| s.to_string())
                .unwrap_or_else(|| "x".to_string());
            funext(proof_state, &name)
        }
        "clear" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "clear".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            clear(proof_state, parts[1])
        }
        "rename" => {
            if parts.len() < 3 {
                return Err(TacticError::MissingArgument {
                    tactic: "rename".to_string(),
                    expected: "<old-name> <new-name>".to_string(),
                });
            }
            rename(proof_state, parts[1], parts[2])
        }
        "by_contra" => {
            let name = parts
                .get(1)
                .map(|s| s.to_string())
                .unwrap_or_else(|| "h".to_string());
            by_contra(proof_state, &name)
        }
        "push_neg" => match at_target(&parts) {
            Some(hyp) => push_neg_at(proof_state, hyp),
            None => push_neg(proof_state),
        },
        "contrapose" => {
            if parts.len() > 1 {
                contrapose_hyp(proof_state, parts[1])
            } else {
                contrapose(proof_state)
            }
        }
        "field_simp" => field_simp(proof_state),
        "left" => left_(proof_state),
        "right" => right_(proof_state),
        "exfalso" => exfalso(proof_state),
        "contradiction" => contradiction(proof_state),
        "itauto" => itauto(proof_state),
        "swap" => swap(proof_state),
        "rotate_left" => {
            let n = parse_rotate_count("rotate_left", parts.get(1).copied())?;
            (0..n).try_for_each(|_| rotate(proof_state))
        }
        "rotate_right" => {
            let n = parse_rotate_count("rotate_right", parts.get(1).copied())?;
            (0..n).try_for_each(|_| rotate_back(proof_state))
        }
        "subst" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "subst".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            subst(proof_state, parts[1])
        }
        "subst_vars" => subst_vars(proof_state),
        "ac_rfl" => ac_rfl(proof_state),
        "positivity" => positivity(proof_state),
        "gcongr" => gcongr(proof_state),
        "cc" => cc(proof_state),
        "norm_cast" => norm_cast(proof_state),
        "abel" => abel(proof_state),
        "group" => group(proof_state),
        "solve_by_elim" => {
            let depth = parse_solve_by_elim_depth(parts.get(1).copied())?;
            solve_by_elim(proof_state, depth)
        }
        "delta" => delta(proof_state),
        "revert" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "revert".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            revert(proof_state, parts[1])
        }
        "unfold" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "unfold".to_string(),
                    expected: "definition name".to_string(),
                });
            }
            match at_target(&parts) {
                Some(hyp) => unfold_at(proof_state, parts[1], hyp),
                None => unfold(proof_state, parts[1]),
            }
        }
        "fin_cases" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "fin_cases".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            fin_cases(proof_state, parts[1])
        }
        "ext" => {
            let name = parts
                .get(1)
                .map(|s| s.to_string())
                .unwrap_or_else(|| "x".to_string());
            ext(proof_state, &name)
        }
        "injection" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "injection".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            injection(proof_state, parts[1])
        }
        "discriminate" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "discriminate".to_string(),
                    expected: "hypothesis name".to_string(),
                });
            }
            discriminate(proof_state, parts[1])
        }
        "interval_cases" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "interval_cases".to_string(),
                    expected: "variable name".to_string(),
                });
            }
            interval_cases(proof_state, parts[1])
        }
        "convert" => {
            if parts.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "convert".to_string(),
                    expected: "expression".to_string(),
                });
            }
            let expr = resolve_expr_in_context(proof_state, &parts[1..].join(" "), env, "convert")?;
            convert(proof_state, expr)
        }
        "grind" => grind(proof_state),
        "blast" => blast(proof_state),
        _ => Err(TacticError::UnknownIdent(parts[0].to_string())),
    };

    if result.is_ok() {
        proof_state.prune_solved_goals();
    }

    result
}

/// Oracle candidate runner backed by the elaborator tactic framework.
#[derive(Debug, Default, Clone, Copy)]
pub struct ElabOracleCandidateRunner;

impl OracleCandidateRunner for ElabOracleCandidateRunner {
    fn try_candidate(
        &self,
        env: &Environment,
        local_ctx: Option<&LocalContext>,
        goal: &Expr,
        candidate: &OracleCandidate,
        timeout: Duration,
    ) -> Result<Option<ProofResult>, OracleRunError> {
        let start = Instant::now();
        let mut proof_state = if let Some(local_ctx) = local_ctx {
            let tactic_ctx = kernel_to_tactic_context(local_ctx);
            let mut state =
                elab_tactic::ProofState::with_context(env.clone(), goal.clone(), tactic_ctx);
            // Preserve caller-owned locals as non-tactic FVars so closed_proof()
            // only abstracts the runner's freshly introduced binders.
            state.fvar_base = state.next_fvar;
            state
        } else {
            elab_tactic::ProofState::new(env.clone(), goal.clone())
        };

        for tactic in parse_tactic_script(&candidate.tactic_text) {
            if start.elapsed() >= timeout {
                return Err(OracleRunError::Timeout {
                    timeout_ms: timeout.as_millis() as u64,
                });
            }

            if execute_simple_tactic(&mut proof_state, &tactic, env).is_err() {
                return Ok(None);
            }
            if proof_state.is_complete() {
                break;
            }
        }

        if !proof_state.is_complete() {
            return Ok(None);
        }

        let proof_term = proof_state.closed_proof().ok_or_else(|| {
            OracleRunError::Internal("proof state closed without a proof term".to_string())
        })?;
        let goal_type = proof_state.goal_type().ok_or_else(|| {
            OracleRunError::Internal("proof state closed without an original goal".to_string())
        })?;
        let verified = match local_ctx {
            Some(local_ctx) => TypeChecker::with_context(env, local_ctx.clone())
                .check_type(&proof_term, &goal_type)
                .is_ok(),
            None => TypeChecker::new(env)
                .check_type(&proof_term, &goal_type)
                .is_ok(),
        };
        if !verified {
            return Ok(None);
        }

        Ok(Some(ProofResult::new(
            proof_term,
            candidate.tactic_text.clone(),
            start.elapsed().as_millis() as u64,
            local_ctx.cloned(),
        )))
    }
}

fn kernel_to_tactic_context(local_ctx: &LocalContext) -> Vec<elab_tactic::LocalDecl> {
    local_ctx
        .iter()
        .map(|decl| elab_tactic::LocalDecl {
            fvar: decl.id,
            name: decl.name.to_string(),
            ty: decl.type_.clone(),
            value: decl.value.clone(),
        })
        .collect()
}

#[cfg(test)]
mod tests;
