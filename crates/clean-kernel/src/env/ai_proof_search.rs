// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AI-assisted proof search with a kernel verification loop.

use super::proof_search::try_verify_proof;
use crate::env::{ConstantInfo, ConstantKind, Declaration, EnvError, Environment};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use hashbrown::HashSet;
use serde::Deserialize;
use serde_json::json;
use std::collections::VecDeque;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const DEFAULT_PROMPT_LEMMA_LIMIT: usize = 32;
const DEFAULT_PROMPT_FEEDBACK_LIMIT: usize = 8;

/// Errors raised by AI-backed proof search.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum AiProofSearchError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("environment error: {0}")]
    Env(#[from] EnvError),
    #[error(
        "backend process `{command}` failed with status {status:?}: {stderr}",
        stderr = if stderr.is_empty() { stdout.as_str() } else { stderr.as_str() }
    )]
    BackendProcessFailed {
        command: String,
        status: Option<i32>,
        stderr: String,
        stdout: String,
    },
    #[error("backend output is not valid proof-candidate JSON: {0}")]
    InvalidBackendOutput(String),
    #[error("candidate for theorem {theorem} did not verify against the requested goal")]
    UnverifiedTheorem { theorem: Name },
}

/// Round/candidate budget for AI proof search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AiSearchBudget {
    pub max_rounds: usize,
    pub max_candidates: usize,
}

impl Default for AiSearchBudget {
    fn default() -> Self {
        Self {
            max_rounds: 4,
            max_candidates: 16,
        }
    }
}

/// Search statistics for the verification loop.
#[derive(Debug, Clone, Default)]
pub struct AiSearchStats {
    pub candidates_tried: usize,
    pub verification_time: Duration,
    pub rounds: usize,
    pub hit_rate: f64,
}

/// Summary of a lemma exposed to the LLM prompt.
#[derive(Debug, Clone)]
pub struct AiLemmaSummary {
    pub name: Name,
    pub type_: Expr,
    pub kind: ConstantKind,
}

/// Structured prompt data rendered into the backend input string.
#[derive(Debug, Clone)]
pub struct AiProofPrompt {
    pub round: usize,
    pub requested_candidates: usize,
    pub goal_type: Expr,
    pub available_lemmas: Vec<AiLemmaSummary>,
    pub total_available_lemmas: usize,
    pub error_feedback: Vec<String>,
}

impl AiProofPrompt {
    /// Build a prompt from the current goal and environment.
    pub fn from_env(
        env: &Environment,
        goal_type: &Expr,
        round: usize,
        requested_candidates: usize,
        error_feedback: impl IntoIterator<Item = String>,
    ) -> Self {
        let (available_lemmas, total_available_lemmas) =
            collect_available_lemmas(env, goal_type, DEFAULT_PROMPT_LEMMA_LIMIT);
        Self {
            round,
            requested_candidates,
            goal_type: goal_type.clone(),
            available_lemmas,
            total_available_lemmas,
            error_feedback: error_feedback.into_iter().collect(),
        }
    }

    /// Render the prompt into a single string consumed by an LLM backend.
    pub fn render(&self) -> Result<String, AiProofSearchError> {
        let goal_json = serde_json::to_string_pretty(&self.goal_type)?;
        let examples = prompt_json_examples()?;

        let mut prompt = String::new();
        prompt.push_str("You are generating clean kernel proof candidates.\n");
        prompt.push_str("Return JSON only with the shape {\"candidates\": [<Expr JSON>, ...]}.\n");
        prompt.push_str("Each candidate must deserialize as clean_kernel::Expr.\n");
        prompt.push_str("Use closed terms only: no free variables and no metavariables.\n");
        prompt.push_str(
            "Prefer short proof terms built from the available lemmas and kernel constructors.\n",
        );
        prompt.push('\n');

        prompt.push_str("Goal type\n");
        prompt.push_str(&format!("Round: {}\n", self.round));
        prompt.push_str(&format!(
            "Requested candidates: {}\n",
            self.requested_candidates
        ));
        prompt.push_str(&format!("Display form: {}\n", self.goal_type));
        prompt.push_str("JSON form:\n");
        prompt.push_str(&goal_json);
        prompt.push('\n');
        prompt.push('\n');

        prompt.push_str("Available lemmas\n");
        prompt.push_str(&format!(
            "Showing {} of {} available declarations.\n",
            self.available_lemmas.len(),
            self.total_available_lemmas
        ));
        for lemma in &self.available_lemmas {
            prompt.push_str(&format!(
                "- [{}] {} : {}\n",
                constant_kind_label(lemma.kind),
                lemma.name,
                lemma.type_
            ));
        }
        if self.available_lemmas.is_empty() {
            prompt.push_str("- none\n");
        }
        prompt.push('\n');

        prompt.push_str("Previous verification feedback\n");
        if self.error_feedback.is_empty() {
            prompt.push_str("- none\n");
        } else {
            for line in &self.error_feedback {
                prompt.push_str("- ");
                prompt.push_str(line);
                prompt.push('\n');
            }
        }
        prompt.push('\n');

        prompt.push_str("JSON serialization examples\n");
        for (label, json) in examples {
            prompt.push_str(&format!("{label}:\n{json}\n"));
        }

        Ok(prompt)
    }
}

/// Render a prompt string for the current goal state.
pub fn format_ai_proof_prompt(
    env: &Environment,
    goal_type: &Expr,
    round: usize,
    requested_candidates: usize,
    error_feedback: &[String],
) -> Result<String, AiProofSearchError> {
    AiProofPrompt::from_env(
        env,
        goal_type,
        round,
        requested_candidates,
        error_feedback.iter().cloned(),
    )
    .render()
}

/// Backend interface for LLM-driven candidate generation.
pub trait AiProofBackend {
    fn generate_candidates(&mut self, prompt: &str) -> Result<Vec<Expr>, AiProofSearchError>;
}

/// `AI Model exec` backend for candidate generation.
#[derive(Debug, Clone)]
pub struct AiModelBackend {
    program: String,
    model: Option<String>,
    working_directory: Option<PathBuf>,
}

impl Default for AiModelBackend {
    fn default() -> Self {
        Self {
            program: "AI Model".to_string(),
            model: None,
            working_directory: None,
        }
    }
}

impl AiModelBackend {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_program(mut self, program: impl Into<String>) -> Self {
        self.program = program.into();
        self
    }

    pub fn with_model(mut self, model: impl Into<String>) -> Self {
        self.model = Some(model.into());
        self
    }

    pub fn with_working_directory(mut self, working_directory: impl Into<PathBuf>) -> Self {
        self.working_directory = Some(working_directory.into());
        self
    }
}

impl AiProofBackend for AiModelBackend {
    fn generate_candidates(&mut self, prompt: &str) -> Result<Vec<Expr>, AiProofSearchError> {
        let schema_path = unique_temp_path("clean-ai-proof-search-schema", "json");
        let output_path = unique_temp_path("clean-ai-proof-search-output", "json");
        fs::write(&schema_path, ai_model_output_schema()?)?;

        let mut command = Command::new(&self.program);
        command
            .arg("exec")
            .arg("--ephemeral")
            .arg("--skip-git-repo-check")
            .arg("--sandbox")
            .arg("read-only")
            .arg("--color")
            .arg("never")
            .arg("--output-schema")
            .arg(&schema_path)
            .arg("--output-last-message")
            .arg(&output_path)
            .arg("-");

        if let Some(model) = &self.model {
            command.arg("--model").arg(model);
        }
        if let Some(working_directory) = &self.working_directory {
            command.arg("--cd").arg(working_directory);
        }

        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let mut child = command.spawn()?;
        let Some(mut stdin) = child.stdin.take() else {
            return Err(std::io::Error::new(
                std::io::ErrorKind::BrokenPipe,
                "failed to capture AI Model stdin",
            )
            .into());
        };
        stdin.write_all(prompt.as_bytes())?;
        drop(stdin);

        let output = child.wait_with_output()?;

        let raw_response = match fs::read_to_string(&output_path) {
            Ok(content) if !content.trim().is_empty() => content,
            _ => String::from_utf8_lossy(&output.stdout).into_owned(),
        };

        let _ = fs::remove_file(&schema_path);
        let _ = fs::remove_file(&output_path);

        if !output.status.success() {
            return Err(AiProofSearchError::BackendProcessFailed {
                command: format!("{} exec", self.program),
                status: output.status.code(),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            });
        }

        parse_candidates_from_json(&raw_response)
    }
}

/// Deterministic backend for tests.
#[derive(Debug, Clone, Default)]
pub struct MockBackend {
    responses: VecDeque<Vec<Expr>>,
    prompts: Vec<String>,
}

impl MockBackend {
    pub fn new(responses: impl IntoIterator<Item = Vec<Expr>>) -> Self {
        Self {
            responses: responses.into_iter().collect(),
            prompts: Vec::new(),
        }
    }

    pub fn push_response(&mut self, candidates: Vec<Expr>) {
        self.responses.push_back(candidates);
    }

    pub fn prompts(&self) -> &[String] {
        &self.prompts
    }
}

impl AiProofBackend for MockBackend {
    fn generate_candidates(&mut self, prompt: &str) -> Result<Vec<Expr>, AiProofSearchError> {
        self.prompts.push(prompt.to_string());
        Ok(self.responses.pop_front().unwrap_or_default())
    }
}

/// Result of the AI-backed verification loop.
#[derive(Debug, Clone)]
pub enum AiProofSearchResult {
    Found {
        proof: Expr,
        stats: AiSearchStats,
        feedback: Vec<String>,
    },
    Exhausted {
        stats: AiSearchStats,
        feedback: Vec<String>,
    },
    BudgetExceeded {
        stats: AiSearchStats,
        budget: AiSearchBudget,
        feedback: Vec<String>,
    },
}

/// Run AI proof search with repeated kernel verification and feedback.
pub fn ai_search_proof(
    env: &Environment,
    goal_type: &Expr,
    backend: &mut dyn AiProofBackend,
    budget: AiSearchBudget,
) -> Result<AiProofSearchResult, AiProofSearchError> {
    let mut stats = AiSearchStats::default();
    let mut feedback = Vec::new();
    let mut seen_candidates = HashSet::new();

    if budget.max_rounds == 0 || budget.max_candidates == 0 {
        return Ok(AiProofSearchResult::BudgetExceeded {
            stats,
            budget,
            feedback,
        });
    }

    for round in 1..=budget.max_rounds {
        if stats.candidates_tried >= budget.max_candidates {
            return Ok(AiProofSearchResult::BudgetExceeded {
                stats,
                budget,
                feedback,
            });
        }

        stats.rounds += 1;
        let remaining_candidates = budget.max_candidates - stats.candidates_tried;
        let prompt_feedback = recent_feedback(&feedback);
        let prompt = format_ai_proof_prompt(
            env,
            goal_type,
            round,
            remaining_candidates,
            &prompt_feedback,
        )?;

        let generated_candidates = backend.generate_candidates(&prompt)?;
        if generated_candidates.is_empty() {
            feedback.push(format!(
                "round {round}: backend returned no candidate expressions"
            ));
            stats.hit_rate = 0.0;
            return Ok(AiProofSearchResult::Exhausted { stats, feedback });
        }

        let mut fresh_candidates = Vec::new();
        for candidate in generated_candidates {
            if seen_candidates.insert(candidate.clone()) {
                fresh_candidates.push(candidate);
            }
            if fresh_candidates.len() >= remaining_candidates {
                break;
            }
        }

        if fresh_candidates.is_empty() {
            feedback.push(format!(
                "round {round}: backend only repeated previously rejected candidates"
            ));
            continue;
        }

        for candidate in fresh_candidates {
            let verification_start = Instant::now();
            let verified = try_verify_proof(env, goal_type, &candidate);
            stats.verification_time += verification_start.elapsed();
            stats.candidates_tried += 1;

            if verified {
                stats.hit_rate = 1.0 / stats.candidates_tried as f64;
                return Ok(AiProofSearchResult::Found {
                    proof: candidate,
                    stats,
                    feedback,
                });
            }

            feedback.push(describe_candidate_failure(env, goal_type, &candidate));

            if stats.candidates_tried >= budget.max_candidates {
                stats.hit_rate = 0.0;
                return Ok(AiProofSearchResult::BudgetExceeded {
                    stats,
                    budget,
                    feedback,
                });
            }
        }
    }

    stats.hit_rate = 0.0;
    Ok(AiProofSearchResult::BudgetExceeded {
        stats,
        budget,
        feedback,
    })
}

/// Register a theorem proved by `ai_search_proof`.
pub fn register_ai_proved_theorem(
    env: &mut Environment,
    theorem: Name,
    level_params: Vec<Name>,
    goal_type: Expr,
    proof: Expr,
) -> Result<(), AiProofSearchError> {
    if !try_verify_proof(env, &goal_type, &proof) {
        return Err(AiProofSearchError::UnverifiedTheorem { theorem });
    }

    env.add_decl(Declaration::Theorem {
        name: theorem,
        level_params,
        type_: goal_type,
        value: proof,
    })?;
    Ok(())
}

fn collect_available_lemmas(
    env: &Environment,
    goal_type: &Expr,
    limit: usize,
) -> (Vec<AiLemmaSummary>, usize) {
    let goal_head = goal_head_name(goal_type);
    let goal_head_str = goal_head.as_ref().map(ToString::to_string);

    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_cached_key(|info| {
        (
            relevance_rank(info, goal_head.as_ref(), goal_head_str.as_deref()),
            constant_kind_rank(info.kind),
            info.name.to_string(),
        )
    });

    let total = constants.len();
    let lemmas = constants
        .into_iter()
        .take(limit)
        .map(|info| AiLemmaSummary {
            name: info.name.clone(),
            type_: info.type_.clone(),
            kind: info.kind,
        })
        .collect();
    (lemmas, total)
}

fn goal_head_name(expr: &Expr) -> Option<Name> {
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

fn relevance_rank(
    info: &ConstantInfo,
    goal_head: Option<&Name>,
    goal_head_str: Option<&str>,
) -> u8 {
    let Some(goal_head) = goal_head else {
        return 2;
    };

    if info.name == *goal_head {
        return 0;
    }

    if matches!(info.type_.get_app_fn().kind(), ExprKind::Const(name, _) if name == goal_head) {
        return 0;
    }

    if let Some(goal_head_str) = goal_head_str {
        if info.name.to_string().contains(goal_head_str) {
            return 1;
        }
    }

    2
}

fn constant_kind_rank(kind: ConstantKind) -> u8 {
    match kind {
        ConstantKind::Theorem => 0,
        ConstantKind::Axiom => 1,
        ConstantKind::Opaque => 2,
        ConstantKind::Definition => 3,
    }
}

fn constant_kind_label(kind: ConstantKind) -> &'static str {
    match kind {
        ConstantKind::Theorem => "theorem",
        ConstantKind::Axiom => "axiom",
        ConstantKind::Opaque => "opaque",
        ConstantKind::Definition => "definition",
    }
}

fn prompt_json_examples() -> Result<Vec<(&'static str, String)>, AiProofSearchError> {
    let bvar = serde_json::to_string_pretty(&Expr::from_kind(ExprKind::BVar(0)))?;
    let sort = serde_json::to_string_pretty(&Expr::from_kind(ExprKind::Sort(Level::zero())))?;
    let const_expr = serde_json::to_string_pretty(&Expr::const_str("True.intro"))?;
    let level_param_const = serde_json::to_string_pretty(&Expr::const_str_levels(
        "List",
        vec![Level::param(Name::from_string("u"))],
    ))?;
    let app = serde_json::to_string_pretty(&Expr::app(
        Expr::const_str("Nat.succ"),
        Expr::const_str("Nat.zero"),
    ))?;
    let lam = serde_json::to_string_pretty(&Expr::lam(
        crate::expr::BinderData::default(),
        Expr::const_str("Nat"),
        Expr::from_kind(ExprKind::BVar(0)),
    ))?;
    let pi = serde_json::to_string_pretty(&Expr::pi(
        crate::expr::BinderData::default(),
        Expr::const_str("Nat"),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
    ))?;

    Ok(vec![
        ("BVar(0)", bvar),
        ("Sort(0)", sort),
        ("Const(\"True.intro\")", const_expr),
        ("Const with level param", level_param_const),
        ("App(Nat.succ, Nat.zero)", app),
        ("Lam(default binder, Nat, BVar(0))", lam),
        ("Pi(default binder, Nat, Sort(1))", pi),
    ])
}

fn recent_feedback(feedback: &[String]) -> Vec<String> {
    let start = feedback.len().saturating_sub(DEFAULT_PROMPT_FEEDBACK_LIMIT);
    feedback[start..].to_vec()
}

fn describe_candidate_failure(env: &Environment, goal_type: &Expr, candidate: &Expr) -> String {
    let tc = TypeChecker::with_mode(env, env.mode());
    match tc.infer_type(candidate) {
        Ok(candidate_type) => {
            if tc.is_def_eq(&candidate_type, goal_type) {
                format!(
                    "candidate `{}` appeared definitionally equal to the goal type, but kernel verification still rejected it",
                    candidate
                )
            } else {
                format!(
                    "candidate `{}` has type `{}`, but the goal is `{}`",
                    candidate, candidate_type, goal_type
                )
            }
        }
        Err(error) => format!("candidate `{}` failed type inference: {}", candidate, error),
    }
}

#[derive(Debug, Deserialize)]
struct CandidateEnvelope {
    candidates: Vec<Expr>,
}

#[derive(Debug, Deserialize)]
struct CandidateWrapper {
    expr: Expr,
}

#[derive(Debug, Deserialize)]
struct WrappedCandidateEnvelope {
    candidates: Vec<CandidateWrapper>,
}

fn parse_candidates_from_json(raw: &str) -> Result<Vec<Expr>, AiProofSearchError> {
    let payload = extract_json_payload(raw);

    if let Ok(envelope) = serde_json::from_str::<CandidateEnvelope>(&payload) {
        return Ok(envelope.candidates);
    }
    if let Ok(envelope) = serde_json::from_str::<WrappedCandidateEnvelope>(&payload) {
        return Ok(envelope
            .candidates
            .into_iter()
            .map(|candidate| candidate.expr)
            .collect());
    }
    if let Ok(candidates) = serde_json::from_str::<Vec<Expr>>(&payload) {
        return Ok(candidates);
    }
    if let Ok(candidates) = serde_json::from_str::<Vec<CandidateWrapper>>(&payload) {
        return Ok(candidates
            .into_iter()
            .map(|candidate| candidate.expr)
            .collect());
    }
    if let Ok(candidate) = serde_json::from_str::<Expr>(&payload) {
        return Ok(vec![candidate]);
    }

    let preview = payload.chars().take(512).collect();
    Err(AiProofSearchError::InvalidBackendOutput(preview))
}

fn extract_json_payload(raw: &str) -> String {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return String::new();
    }

    if let Some(stripped) = strip_code_fence(trimmed) {
        return stripped;
    }

    if trimmed.starts_with('{') || trimmed.starts_with('[') {
        return trimmed.to_string();
    }

    let object_range = balanced_range(trimmed, '{', '}');
    let array_range = balanced_range(trimmed, '[', ']');
    match (object_range, array_range) {
        (Some((start, end)), Some((array_start, array_end))) => {
            if start <= array_start {
                trimmed[start..end].to_string()
            } else {
                trimmed[array_start..array_end].to_string()
            }
        }
        (Some((start, end)), None) => trimmed[start..end].to_string(),
        (None, Some((start, end))) => trimmed[start..end].to_string(),
        (None, None) => trimmed.to_string(),
    }
}

fn strip_code_fence(text: &str) -> Option<String> {
    if !text.starts_with("```") {
        return None;
    }

    let mut lines = text.lines();
    let first = lines.next()?;
    if !first.starts_with("```") {
        return None;
    }

    let mut body = String::new();
    for line in lines {
        if line.starts_with("```") {
            break;
        }
        if !body.is_empty() {
            body.push('\n');
        }
        body.push_str(line);
    }

    Some(body.trim().to_string())
}

fn balanced_range(text: &str, open: char, close: char) -> Option<(usize, usize)> {
    let mut depth = 0usize;
    let mut start = None;

    for (idx, ch) in text.char_indices() {
        if ch == open {
            if start.is_none() {
                start = Some(idx);
            }
            depth += 1;
            continue;
        }

        if ch == close && depth > 0 {
            depth -= 1;
            if depth == 0 {
                return start.map(|start_idx| (start_idx, idx + ch.len_utf8()));
            }
        }
    }

    None
}

fn ai_model_output_schema() -> Result<String, AiProofSearchError> {
    Ok(serde_json::to_string_pretty(&json!({
        "type": "object",
        "required": ["candidates"],
        "additionalProperties": false,
        "properties": {
            "candidates": {
                "type": "array",
                "items": {}
            }
        }
    }))?)
}

fn unique_temp_path(prefix: &str, extension: &str) -> PathBuf {
    let nanos = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_nanos(),
        Err(_) => 0,
    };
    std::env::temp_dir().join(format!(
        "{prefix}-{}-{nanos}.{extension}",
        std::process::id()
    ))
}

#[cfg(test)]
mod tests {
    use super::{
        ai_search_proof, format_ai_proof_prompt, register_ai_proved_theorem, AiProofSearchResult,
        AiSearchBudget, MockBackend,
    };
    use crate::env::{ConstantKind, Environment};
    use crate::expr::Expr;
    use crate::level::Level;
    use crate::name::Name;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_nat().expect("init_nat");
        env.init_true_false().expect("init_true_false");
        env
    }

    fn nat() -> Expr {
        Expr::const_str("Nat")
    }

    fn nat_zero() -> Expr {
        Expr::const_str("Nat.zero")
    }

    fn eq_level() -> Level {
        Level::succ(Level::zero())
    }

    fn eq_goal(lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![eq_level()]),
            [nat(), lhs, rhs],
        )
    }

    fn eq_refl_proof(value: Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![eq_level()]),
            [nat(), value],
        )
    }

    #[test]
    fn prompt_contains_goal_lemmas_and_feedback() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let feedback = vec!["candidate had the wrong type".to_string()];
        let prompt =
            format_ai_proof_prompt(&env, &goal, 1, 2, &feedback).expect("prompt render succeeds");

        assert!(prompt.contains("Goal type"));
        assert!(prompt.contains("Available lemmas"));
        assert!(prompt.contains("Previous verification feedback"));
        assert!(prompt.contains("candidate had the wrong type"));
    }

    #[test]
    fn ai_search_proof_uses_feedback_across_rounds() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let mut backend = MockBackend::new(vec![
            vec![Expr::const_str("True.intro")],
            vec![eq_refl_proof(nat_zero())],
        ]);

        let result = ai_search_proof(
            &env,
            &goal,
            &mut backend,
            AiSearchBudget {
                max_rounds: 2,
                max_candidates: 2,
            },
        )
        .expect("ai_search_proof succeeds");

        match result {
            AiProofSearchResult::Found {
                proof,
                stats,
                feedback,
            } => {
                assert_eq!(proof, eq_refl_proof(nat_zero()));
                assert_eq!(stats.rounds, 2);
                assert_eq!(stats.candidates_tried, 2);
                assert_eq!(feedback.len(), 1);
                assert_eq!(backend.prompts().len(), 2);
                assert!(backend.prompts()[1].contains("has type"));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn ai_search_proof_respects_candidate_budget() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let mut backend = MockBackend::new(vec![vec![Expr::const_str("True.intro")]]);

        let result = ai_search_proof(
            &env,
            &goal,
            &mut backend,
            AiSearchBudget {
                max_rounds: 1,
                max_candidates: 1,
            },
        )
        .expect("ai_search_proof succeeds");

        match result {
            AiProofSearchResult::BudgetExceeded { stats, budget, .. } => {
                assert_eq!(stats.rounds, 1);
                assert_eq!(stats.candidates_tried, 1);
                assert_eq!(budget.max_rounds, 1);
                assert_eq!(budget.max_candidates, 1);
            }
            other => panic!("expected BudgetExceeded, got {other:?}"),
        }
    }

    #[test]
    fn register_ai_proved_theorem_adds_theorem() {
        let mut env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let theorem = Name::from_string("AIProofSearch.testEq");
        let proof = eq_refl_proof(nat_zero());

        register_ai_proved_theorem(&mut env, theorem.clone(), vec![], goal, proof)
            .expect("theorem registration succeeds");

        let info = env.get_const(&theorem).expect("theorem registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn ai_search_proof_exhausted_when_backend_returns_empty() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let mut backend = MockBackend::new(vec![vec![]]);

        let result = ai_search_proof(
            &env,
            &goal,
            &mut backend,
            AiSearchBudget {
                max_rounds: 3,
                max_candidates: 10,
            },
        )
        .expect("ai_search_proof succeeds");

        match result {
            AiProofSearchResult::Exhausted { stats, feedback } => {
                assert_eq!(stats.rounds, 1);
                assert_eq!(stats.candidates_tried, 0);
                assert!(
                    feedback.iter().any(|f| f.contains("no candidate")),
                    "feedback should mention no candidates: {feedback:?}"
                );
            }
            other => panic!("expected Exhausted, got {other:?}"),
        }
    }

    #[test]
    fn ai_search_proof_deduplicates_candidates_across_rounds() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        // Both rounds return the same wrong candidate
        let wrong = Expr::const_str("True.intro");
        let mut backend = MockBackend::new(vec![
            vec![wrong.clone()],
            vec![wrong.clone()],
            vec![eq_refl_proof(nat_zero())],
        ]);

        let result = ai_search_proof(
            &env,
            &goal,
            &mut backend,
            AiSearchBudget {
                max_rounds: 3,
                max_candidates: 10,
            },
        )
        .expect("ai_search_proof succeeds");

        match result {
            AiProofSearchResult::Found { stats, .. } => {
                // Only 2 unique candidates tried: True.intro (once, dedup'd) + Eq.refl
                assert_eq!(stats.candidates_tried, 2);
                assert_eq!(stats.rounds, 3);
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_candidates_from_json_envelope() {
        use super::parse_candidates_from_json;

        // Use real Expr serialization so JSON format matches serde's output
        let exprs = vec![Expr::const_str("Nat.zero"), Expr::const_str("True.intro")];
        let json = serde_json::to_string(&serde_json::json!({
            "candidates": exprs
        }))
        .expect("json serialization");

        let candidates = parse_candidates_from_json(&json).expect("parse succeeds");
        assert_eq!(candidates.len(), 2);
    }

    #[test]
    fn test_parse_candidates_from_json_bare_array() {
        use super::parse_candidates_from_json;

        let json = serde_json::to_string(&vec![
            Expr::const_str("Nat.zero"),
            Expr::const_str("True.intro"),
        ])
        .expect("json serialization");

        let candidates = parse_candidates_from_json(&json).expect("parse succeeds");
        assert_eq!(candidates.len(), 2);
    }

    #[test]
    fn test_parse_candidates_from_json_code_fence() {
        use super::parse_candidates_from_json;

        // Wrap real Expr serialization in markdown code fence
        let exprs = vec![Expr::const_str("Nat.zero")];
        let inner = serde_json::to_string(&serde_json::json!({
            "candidates": exprs
        }))
        .expect("json serialization");
        let fenced = format!("```json\n{inner}\n```");

        let candidates = parse_candidates_from_json(&fenced).expect("parse succeeds");
        assert_eq!(candidates.len(), 1);
    }

    #[test]
    fn prompt_includes_json_examples() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let prompt =
            format_ai_proof_prompt(&env, &goal, 0, 5, &[]).expect("prompt render succeeds");

        assert!(
            prompt.contains("BVar(0)"),
            "prompt should include BVar example"
        );
        assert!(
            prompt.contains("True.intro"),
            "prompt should include Const example"
        );
        assert!(
            prompt.contains("App(Nat.succ"),
            "prompt should include App example"
        );
    }

    #[test]
    fn ai_search_proof_immediate_success_first_round() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let mut backend = MockBackend::new(vec![vec![eq_refl_proof(nat_zero())]]);

        let result = ai_search_proof(&env, &goal, &mut backend, AiSearchBudget::default())
            .expect("ai_search_proof succeeds");

        match result {
            AiProofSearchResult::Found { proof, stats, .. } => {
                assert_eq!(proof, eq_refl_proof(nat_zero()));
                assert_eq!(stats.rounds, 1);
                assert_eq!(stats.candidates_tried, 1);
                assert!(stats.hit_rate > 0.0);
                assert!(stats.verification_time.as_nanos() > 0);
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn ai_search_proof_zero_budget_returns_budget_exceeded() {
        let env = make_env();
        let goal = eq_goal(nat_zero(), nat_zero());
        let mut backend = MockBackend::new(vec![]);

        let result = ai_search_proof(
            &env,
            &goal,
            &mut backend,
            AiSearchBudget {
                max_rounds: 0,
                max_candidates: 0,
            },
        )
        .expect("ai_search_proof succeeds");

        assert!(
            matches!(result, AiProofSearchResult::BudgetExceeded { .. }),
            "zero budget should immediately return BudgetExceeded"
        );
    }
}
