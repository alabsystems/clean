// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::derivation::DerivationTrace;
use super::super::geometry::{GeomStep, GoalStep, ProblemToStepsConverter};
use super::super::problem::GeometryProblem;
use super::BenchmarkError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GoalSignature {
    predicate: String,
    args: Vec<String>,
}

impl GoalSignature {
    fn from_goal(goal: &GoalStep) -> Self {
        Self {
            predicate: canonicalize_predicate(&goal.predicate),
            args: goal.args.clone(),
        }
    }

    fn from_step(step: &GeomStep) -> Option<Self> {
        match step {
            GeomStep::Axiom { name, args } => Some(Self {
                predicate: canonicalize_predicate(name),
                args: args.clone(),
            }),
            GeomStep::Apply {
                predicate, args, ..
            } => Some(Self {
                predicate: canonicalize_predicate(predicate),
                args: args.clone(),
            }),
            GeomStep::Given { predicate, args } => Some(Self {
                predicate: canonicalize_predicate(predicate),
                args: args.clone(),
            }),
            GeomStep::Construct { .. } => None,
        }
    }

    pub(super) fn display(&self) -> String {
        format!("{}({})", self.predicate, self.args.join(", "))
    }
}

fn canonicalize_predicate(predicate: &str) -> String {
    match predicate.to_ascii_lowercase().as_str() {
        "coll" => "collinear".to_string(),
        "conc" => "concurrent".to_string(),
        "para" => "parallel".to_string(),
        "perp" | "right_angle" | "rightangle" => "perpendicular".to_string(),
        "midp" => "midpoint".to_string(),
        "oncircle" => "on_circle".to_string(),
        "online" => "on_line".to_string(),
        "onsegment" => "on_segment".to_string(),
        "tang" => "tangent".to_string(),
        "cong" | "congruent" => "congruent_segments".to_string(),
        "sim" | "similar" => "similar_triangles".to_string(),
        "betw" => "between".to_string(),
        "angle" => "angle_measure".to_string(),
        other => other.to_string(),
    }
}

pub(super) fn goal_signature(problem: &GeometryProblem) -> Result<GoalSignature, BenchmarkError> {
    let converted = ProblemToStepsConverter::new(problem.clone())
        .convert()
        .map_err(|e| BenchmarkError::InvalidStructure(format!("Failed to convert goal: {e}")))?;
    Ok(GoalSignature::from_goal(&converted.goal))
}

pub(super) fn final_step_signature(derivation: &DerivationTrace) -> Option<GoalSignature> {
    derivation.steps.last().and_then(GoalSignature::from_step)
}
