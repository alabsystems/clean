// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AI proof candidate verification loop for kernel goals.
use crate::env::{ConstantInfo, ConstantKind, Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::tc::{TypeChecker, TypeError};
use std::collections::HashSet;
use std::time::Instant;

#[derive(Debug, Clone)]
pub(crate) struct GoalContext {
    pub(crate) goal_type: Expr,
    pub(crate) goal_type_pretty: String,
    pub(crate) available_lemmas: Vec<LemmaInfo>,
    pub(crate) hint: Option<String>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct LemmaInfo {
    pub(crate) name: Name,
    pub(crate) type_pretty: String,
    pub(crate) kind: ConstantKind,
}

#[derive(Debug, Clone)]
pub(crate) struct VerificationRequest {
    pub(crate) candidate_name: String,
    pub(crate) goal_type: Expr,
    pub(crate) proof_term: Expr,
    pub(crate) level_params: Vec<Name>,
}

#[derive(Debug, Clone)]
pub(crate) enum VerificationDiagnostic {
    TypeMismatch {
        expected: String,
        inferred: String,
    },
    NotAFunction(String),
    UnknownConst(String),
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    InferenceError(String),
    DeclRegistrationError(String),
    Success,
}

#[derive(Debug, Clone)]
pub(crate) struct VerificationResult {
    pub(crate) request_name: String,
    pub(crate) accepted: bool,
    pub(crate) diagnostic: VerificationDiagnostic,
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) elapsed_ns: u64,
}

#[derive(Debug, Clone)]
pub(crate) struct VerificationSession {
    pub(crate) total_candidates: u64,
    pub(crate) accepted_count: u64,
    pub(crate) rejected_count: u64,
    pub(crate) total_elapsed_ns: u64,
}

#[derive(Debug, Clone)]
pub(crate) struct SessionSummary {
    pub(crate) total_candidates: u64,
    pub(crate) accepted_count: u64,
    pub(crate) rejected_count: u64,
    pub(crate) total_elapsed_ns: u64,
    pub(crate) hit_rate: f64,
    pub(crate) avg_verification_ns: u64,
}

impl VerificationSession {
    pub(crate) fn new() -> Self {
        Self {
            total_candidates: 0,
            accepted_count: 0,
            rejected_count: 0,
            total_elapsed_ns: 0,
        }
    }

    pub(crate) fn verify_candidate(
        &mut self,
        env: &Environment,
        req: &VerificationRequest,
    ) -> VerificationResult {
        let started = Instant::now();
        let tc = TypeChecker::with_mode(env, env.mode());

        let diagnostic = match tc.infer_type(&req.proof_term) {
            Ok(inferred_type) => {
                if !tc.is_def_eq(&inferred_type, &req.goal_type) {
                    VerificationDiagnostic::TypeMismatch {
                        expected: req.goal_type.to_string(),
                        inferred: inferred_type.to_string(),
                    }
                } else {
                    let mut scratch = env.clone();
                    match scratch.add_decl(Declaration::Theorem {
                        name: Name::from_string(&req.candidate_name),
                        level_params: req.level_params.clone(),
                        type_: req.goal_type.clone(),
                        value: req.proof_term.clone(),
                    }) {
                        Ok(()) => VerificationDiagnostic::Success,
                        Err(err) => {
                            VerificationDiagnostic::DeclRegistrationError(map_env_error(err))
                        }
                    }
                }
            }
            Err(err) => map_type_error(err),
        };

        let elapsed_ns = duration_ns_u64(started.elapsed().as_nanos());
        let accepted = matches!(diagnostic, VerificationDiagnostic::Success);

        self.total_candidates = self.total_candidates.saturating_add(1);
        self.total_elapsed_ns = self.total_elapsed_ns.saturating_add(elapsed_ns);
        if accepted {
            self.accepted_count = self.accepted_count.saturating_add(1);
        } else {
            self.rejected_count = self.rejected_count.saturating_add(1);
        }

        VerificationResult {
            request_name: req.candidate_name.clone(),
            accepted,
            diagnostic,
            elapsed_ns,
        }
    }

    pub(crate) fn verify_batch(
        &mut self,
        env: &Environment,
        requests: &[VerificationRequest],
    ) -> Vec<VerificationResult> {
        requests
            .iter()
            .map(|req| self.verify_candidate(env, req))
            .collect()
    }

    pub(crate) fn hit_rate(&self) -> f64 {
        if self.total_candidates == 0 {
            0.0
        } else {
            self.accepted_count as f64 / self.total_candidates as f64
        }
    }

    pub(crate) fn avg_verification_ns(&self) -> u64 {
        self.total_elapsed_ns
            .checked_div(self.total_candidates)
            .unwrap_or(0)
    }

    pub(crate) fn summary(&self) -> SessionSummary {
        SessionSummary {
            total_candidates: self.total_candidates,
            accepted_count: self.accepted_count,
            rejected_count: self.rejected_count,
            total_elapsed_ns: self.total_elapsed_ns,
            hit_rate: self.hit_rate(),
            avg_verification_ns: self.avg_verification_ns(),
        }
    }
}

pub(crate) fn build_goal_context(
    env: &Environment,
    goal_type: &Expr,
    max_lemmas: usize,
) -> GoalContext {
    let goal_constants = goal_type.collect_constants();
    let goal_type_pretty = goal_type.to_string();

    let mut ranked_lemmas: Vec<(u32, u8, String, LemmaInfo)> = env
        .constants()
        .map(|info| {
            let score = lemma_relevance_score(&goal_constants, info);
            let name = info.name.to_string();
            let lemma = LemmaInfo {
                name: info.name.clone(),
                type_pretty: lemma_type_pretty(env, info),
                kind: info.kind,
            };
            (score, constant_kind_rank(info.kind), name, lemma)
        })
        .collect();

    ranked_lemmas.sort_by(|left, right| {
        right
            .0
            .cmp(&left.0)
            .then_with(|| left.1.cmp(&right.1))
            .then_with(|| left.2.cmp(&right.2))
    });

    let available_lemmas = ranked_lemmas
        .into_iter()
        .take(max_lemmas)
        .map(|(_, _, _, lemma)| lemma)
        .collect();

    GoalContext {
        goal_type: goal_type.clone(),
        goal_type_pretty,
        available_lemmas,
        hint: build_hint(env, goal_type, &goal_constants),
    }
}

fn map_type_error(err: TypeError) -> VerificationDiagnostic {
    match err {
        TypeError::TypeMismatch {
            expected, inferred, ..
        } => VerificationDiagnostic::TypeMismatch {
            expected: expected.to_string(),
            inferred: inferred.to_string(),
        },
        TypeError::NotAFunction { ty, .. } => VerificationDiagnostic::NotAFunction(ty.to_string()),
        TypeError::UnknownConst(name) => VerificationDiagnostic::UnknownConst(name.to_string()),
        other => VerificationDiagnostic::InferenceError(other.to_string()),
    }
}

fn map_env_error(err: EnvError) -> String {
    err.to_string()
}

fn duration_ns_u64(nanos: u128) -> u64 {
    u64::try_from(nanos).unwrap_or(u64::MAX)
}

fn build_hint(
    env: &Environment,
    goal_type: &Expr,
    goal_constants: &HashSet<Name>,
) -> Option<String> {
    if goal_constants.contains(&Name::from_string("Eq")) {
        Some(
            "Equality goal: try Eq.refl first, then Eq.symm, Eq.trans, or lemmas whose conclusion matches the target."
                .to_string(),
        )
    } else if goal_is_prop(env, goal_type) {
        Some(
            "Propositional goal: prefer theorem and axiom constants whose result type reduces to the target."
                .to_string(),
        )
    } else {
        None
    }
}

fn goal_is_prop(env: &Environment, goal_type: &Expr) -> bool {
    let tc = TypeChecker::with_mode(env, env.mode());
    match tc.infer_type(goal_type) {
        Ok(goal_sort) => tc.is_def_eq(&goal_sort, &Expr::prop()),
        Err(_) => false,
    }
}

fn lemma_relevance_score(goal_constants: &HashSet<Name>, info: &ConstantInfo) -> u32 {
    let lemma_constants = info.type_.collect_constants();
    let overlap = goal_constants
        .iter()
        .filter(|goal_name| lemma_constants.contains(*goal_name))
        .count() as u32;
    let name_hit = u32::from(goal_constants.contains(&info.name));
    let info_name = info.name.to_string();
    let namespace_hit = u32::from(goal_constants.iter().any(|goal_name| {
        let goal_name = goal_name.to_string();
        info_name == goal_name || info_name.starts_with(&(goal_name + "."))
    }));
    let kind_bonus = match info.kind {
        ConstantKind::Theorem => 8,
        ConstantKind::Axiom => 6,
        ConstantKind::Definition => 3,
        ConstantKind::Opaque => 1,
    };

    name_hit * 32 + namespace_hit * 24 + overlap * 8 + kind_bonus
}

fn lemma_type_pretty(env: &Environment, info: &ConstantInfo) -> String {
    let levels = info
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect::<Vec<_>>();
    match env.instantiate_type(&info.name, &levels) {
        Some(type_) => type_.to_string(),
        None => info.type_.to_string(),
    }
}

fn constant_kind_rank(kind: ConstantKind) -> u8 {
    match kind {
        ConstantKind::Theorem => 0,
        ConstantKind::Axiom => 1,
        ConstantKind::Definition => 2,
        ConstantKind::Opaque => 3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_true_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("init_true_false");
        env
    }

    fn make_eq_nat_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat().expect("init_nat");
        env.init_eq().expect("init_eq");
        env
    }

    fn eq_nat_goal(lhs: u64, rhs: u64) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [
                Expr::const_str("Nat"),
                Expr::nat_lit(lhs),
                Expr::nat_lit(rhs),
            ],
        )
    }

    #[test]
    fn test_verify_candidate_accepts_valid_proof() {
        let env = make_true_env();
        let req = VerificationRequest {
            candidate_name: "ai.true_intro".to_string(),
            goal_type: Expr::const_str("True"),
            proof_term: Expr::const_str("True.intro"),
            level_params: vec![],
        };

        let mut session = VerificationSession::new();
        let result = session.verify_candidate(&env, &req);

        assert!(result.accepted);
        assert!(matches!(result.diagnostic, VerificationDiagnostic::Success));
        assert_eq!(result.request_name, "ai.true_intro");
        assert_eq!(session.total_candidates, 1);
        assert_eq!(session.accepted_count, 1);
        assert_eq!(session.rejected_count, 0);
    }

    #[test]
    fn test_verify_candidate_reports_goal_type_mismatch() {
        let env = make_true_env();
        let req = VerificationRequest {
            candidate_name: "ai.false_from_true".to_string(),
            goal_type: Expr::const_str("False"),
            proof_term: Expr::const_str("True.intro"),
            level_params: vec![],
        };

        let mut session = VerificationSession::new();
        let result = session.verify_candidate(&env, &req);

        assert!(!result.accepted);
        match result.diagnostic {
            VerificationDiagnostic::TypeMismatch { expected, inferred } => {
                assert!(expected.contains("False"));
                assert!(inferred.contains("True"));
            }
            other => panic!("expected TypeMismatch, got {other:?}"),
        }
        assert_eq!(session.accepted_count, 0);
        assert_eq!(session.rejected_count, 1);
    }

    #[test]
    fn test_verify_candidate_reports_unknown_const() {
        let env = Environment::new();
        let req = VerificationRequest {
            candidate_name: "ai.unknown".to_string(),
            goal_type: Expr::prop(),
            proof_term: Expr::const_str("Missing.proof"),
            level_params: vec![],
        };

        let mut session = VerificationSession::new();
        let result = session.verify_candidate(&env, &req);

        assert!(!result.accepted);
        match result.diagnostic {
            VerificationDiagnostic::UnknownConst(name) => {
                assert_eq!(name, "Missing.proof");
            }
            other => panic!("expected UnknownConst, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_candidate_reports_not_a_function() {
        let env = Environment::new();
        let req = VerificationRequest {
            candidate_name: "ai.bad_app".to_string(),
            goal_type: Expr::prop(),
            proof_term: Expr::app(Expr::prop(), Expr::prop()),
            level_params: vec![],
        };

        let mut session = VerificationSession::new();
        let result = session.verify_candidate(&env, &req);

        assert!(!result.accepted);
        match result.diagnostic {
            VerificationDiagnostic::NotAFunction(message) => {
                assert!(!message.is_empty());
            }
            other => panic!("expected NotAFunction, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_candidate_uses_decl_registration_check() {
        let mut env = Environment::new();
        env.init_nat().expect("init_nat");

        let req = VerificationRequest {
            candidate_name: "ai.zero_is_a_theorem".to_string(),
            goal_type: Expr::const_str("Nat"),
            proof_term: Expr::nat_lit(0),
            level_params: vec![],
        };

        let mut session = VerificationSession::new();
        let result = session.verify_candidate(&env, &req);

        assert!(!result.accepted);
        match result.diagnostic {
            VerificationDiagnostic::DeclRegistrationError(message) => {
                assert!(message.contains("type must be a Prop"));
            }
            other => panic!("expected DeclRegistrationError, got {other:?}"),
        }
    }

    #[test]
    fn test_build_goal_context_collects_relevant_lemmas() {
        let env = make_eq_nat_env();
        let goal = eq_nat_goal(0, 0);

        let ctx = build_goal_context(&env, &goal, 64);

        assert_eq!(ctx.goal_type, goal);
        assert_eq!(ctx.goal_type_pretty, goal.to_string());
        assert!(ctx.hint.is_some());
        assert!(ctx
            .available_lemmas
            .iter()
            .any(|lemma| lemma.name == Name::from_string("Eq.refl")));
    }

    #[test]
    fn test_verify_batch_updates_session_summary() {
        let env = make_true_env();
        let requests = vec![
            VerificationRequest {
                candidate_name: "ai.true_ok".to_string(),
                goal_type: Expr::const_str("True"),
                proof_term: Expr::const_str("True.intro"),
                level_params: vec![],
            },
            VerificationRequest {
                candidate_name: "ai.true_bad".to_string(),
                goal_type: Expr::const_str("False"),
                proof_term: Expr::const_str("True.intro"),
                level_params: vec![],
            },
        ];

        let mut session = VerificationSession::new();
        let results = session.verify_batch(&env, &requests);
        let summary = session.summary();

        assert_eq!(results.len(), 2);
        assert_eq!(session.total_candidates, 2);
        assert_eq!(session.accepted_count, 1);
        assert_eq!(session.rejected_count, 1);
        assert!((session.hit_rate() - 0.5).abs() < f64::EPSILON);
        assert_eq!(summary.total_candidates, 2);
        assert_eq!(summary.accepted_count, 1);
        assert_eq!(summary.rejected_count, 1);
        assert!((summary.hit_rate - 0.5).abs() < f64::EPSILON);
        assert_eq!(summary.avg_verification_ns, session.avg_verification_ns());
        assert_eq!(summary.total_elapsed_ns, session.total_elapsed_ns);
    }
}
