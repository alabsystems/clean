// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Problem → GeomStep Converter
//!
//! Converts `GeometryProblem` specifications into `GeomStep` derivation traces
//! that the `GeometryCertGenerator` can process into proof certificates.

use super::super::problem::{
    AngleSpec, Constraint, GeometryProblem, GoalSpec, LineSpec, ObjectDefinition, ObjectType,
};
use super::cert_gen::GeomStep;
use serde::{Deserialize, Serialize};

/// Errors during problem to GeomStep conversion.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ConversionError {
    /// Object not found
    #[error("Object not found: {0}")]
    ObjectNotFound(String),
    /// Unsupported constraint type
    #[error("Unsupported constraint type: {0}")]
    UnsupportedConstraint(String),
    /// Unsupported goal type
    #[error("Unsupported goal type: {0}")]
    UnsupportedGoal(String),
    /// Invalid object definition
    #[error("Invalid definition: {0}")]
    InvalidDefinition(String),
}

/// Converts GeometryProblem to GeomStep derivations.
///
/// This bridges the problem specification format (JSON) with the
/// certificate generator's derivation format.
///
/// ## Conversion Strategy
///
/// 1. **Objects with definitions** → `GeomStep::Construct`
/// 2. **Constraints** → `GeomStep::Given` (problem axioms)
/// 3. **Goal** → Target predicate (what we need to prove)
///
/// The resulting steps form the "given" facts that a solver can use
/// to construct a proof derivation.
pub struct ProblemToStepsConverter {
    /// The problem being converted
    problem: GeometryProblem,
}

impl ProblemToStepsConverter {
    /// Create a new converter for the given problem.
    ///
    /// ENSURES: `self.problem == problem` (stores the problem for conversion)
    pub fn new(problem: GeometryProblem) -> Self {
        Self { problem }
    }

    /// Convert the problem to a list of GeomStep derivations.
    ///
    /// Returns the given facts (constructions + constraints) and the goal.
    ///
    /// REQUIRES: `self.problem` has valid object definitions and constraints
    /// ENSURES: On success, result.problem_id == self.problem.id
    /// ENSURES: On success, result.object_names contains all objects from problem
    /// ENSURES: On success, result.givens contains converted constructions and constraints
    /// ENSURES: Returns Err on failure (InvalidDefinition, ObjectNotFound, UnsupportedConstraint, UnsupportedGoal)
    pub fn convert(&self) -> Result<ProblemSteps, ConversionError> {
        let mut givens = Vec::new();

        // Convert object definitions to constructions
        for (name, obj) in &self.problem.objects {
            if let Some(def) = &obj.definition {
                givens.push(self.definition_to_step(name, obj.obj_type, def)?);
            }
        }

        // Convert constraints to given predicates
        for constraint in &self.problem.constraints {
            if let Some(step) = self.constraint_to_step(constraint)? {
                givens.push(step);
            }
        }

        // Convert goal to target predicate
        let goal = self.goal_to_step(&self.problem.goal)?;

        Ok(ProblemSteps {
            problem_id: self.problem.id.clone(),
            givens,
            goal,
            object_names: self
                .problem
                .all_object_names()
                .into_iter()
                .map(String::from)
                .collect(),
        })
    }

    /// Convert an object definition to a construction step.
    fn definition_to_step(
        &self,
        name: &str,
        _obj_type: ObjectType,
        def: &ObjectDefinition,
    ) -> Result<GeomStep, ConversionError> {
        match def {
            ObjectDefinition::MidpointOf(points) => {
                if points.len() != 2 {
                    return Err(ConversionError::InvalidDefinition(
                        "Midpoint requires exactly 2 points".to_string(),
                    ));
                }
                Ok(GeomStep::Construct {
                    kind: "midpoint".to_string(),
                    name: name.to_string(),
                    from: points.clone(),
                })
            }
            ObjectDefinition::Through(points) => Ok(GeomStep::Construct {
                kind: "line_through".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::Intersection { line1, line2 } => {
                let mut from = Vec::new();
                from.extend(self.line_spec_to_args(line1));
                from.extend(self.line_spec_to_args(line2));
                Ok(GeomStep::Construct {
                    kind: "intersection".to_string(),
                    name: name.to_string(),
                    from,
                })
            }
            ObjectDefinition::CircleThrough(points) => Ok(GeomStep::Construct {
                kind: "circle_through".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::CircleCenterRadius {
                center,
                radius_point,
            } => Ok(GeomStep::Construct {
                kind: "circle_center_radius".to_string(),
                name: name.to_string(),
                from: vec![center.clone(), radius_point.clone()],
            }),
            ObjectDefinition::Circumcenter(points) => Ok(GeomStep::Construct {
                kind: "circumcenter".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::Incenter(points) => Ok(GeomStep::Construct {
                kind: "incenter".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::Orthocenter(points) => Ok(GeomStep::Construct {
                kind: "orthocenter".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::Centroid(points) => Ok(GeomStep::Construct {
                kind: "centroid".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::NinePointCenter(points) => Ok(GeomStep::Construct {
                kind: "nine_point_center".to_string(),
                name: name.to_string(),
                from: points.clone(),
            }),
            ObjectDefinition::Reflection { point, over } => {
                let mut from = vec![point.clone()];
                from.extend(self.line_spec_to_args(over));
                Ok(GeomStep::Construct {
                    kind: "reflection".to_string(),
                    name: name.to_string(),
                    from,
                })
            }
            ObjectDefinition::Perpendicular { from: pt, to } => {
                let mut args = vec![pt.clone()];
                args.extend(self.line_spec_to_args(to));
                Ok(GeomStep::Construct {
                    kind: "perpendicular".to_string(),
                    name: name.to_string(),
                    from: args,
                })
            }
            ObjectDefinition::Parallel { through, to } => {
                let mut args = vec![through.clone()];
                args.extend(self.line_spec_to_args(to));
                Ok(GeomStep::Construct {
                    kind: "parallel".to_string(),
                    name: name.to_string(),
                    from: args,
                })
            }
            ObjectDefinition::AngleBisector { vertex, ray1, ray2 } => Ok(GeomStep::Construct {
                kind: "angle_bisector".to_string(),
                name: name.to_string(),
                from: vec![vertex.clone(), ray1.clone(), ray2.clone()],
            }),
            ObjectDefinition::FootOfAltitude {
                from: pt,
                to_segment,
            } => {
                let mut args = vec![pt.clone()];
                args.extend(to_segment.clone());
                Ok(GeomStep::Construct {
                    kind: "foot_of_altitude".to_string(),
                    name: name.to_string(),
                    from: args,
                })
            }
        }
    }

    /// Convert a constraint to a given predicate step.
    ///
    /// Some constraints (like NotEqual) are non-degeneracy conditions
    /// and don't produce proof steps.
    fn constraint_to_step(
        &self,
        constraint: &Constraint,
    ) -> Result<Option<GeomStep>, ConversionError> {
        match constraint {
            Constraint::Collinear { points } => Ok(Some(GeomStep::Given {
                predicate: "collinear".to_string(),
                args: points.clone(),
            })),
            Constraint::Concurrent { lines } => {
                let args = lines
                    .iter()
                    .flat_map(|l| self.line_spec_to_args(l))
                    .collect();
                Ok(Some(GeomStep::Given {
                    predicate: "concurrent".to_string(),
                    args,
                }))
            }
            Constraint::Cyclic { points } => Ok(Some(GeomStep::Given {
                predicate: "cyclic".to_string(),
                args: points.clone(),
            })),
            Constraint::Parallel { line1, line2 } => {
                let mut args = self.line_spec_to_args(line1);
                args.extend(self.line_spec_to_args(line2));
                Ok(Some(GeomStep::Given {
                    predicate: "parallel".to_string(),
                    args,
                }))
            }
            Constraint::Perpendicular { line1, line2 } => {
                let mut args = self.line_spec_to_args(line1);
                args.extend(self.line_spec_to_args(line2));
                Ok(Some(GeomStep::Given {
                    predicate: "perpendicular".to_string(),
                    args,
                }))
            }
            Constraint::OnLine { point, line } => {
                let mut args = vec![point.clone()];
                args.extend(self.line_spec_to_args(line));
                Ok(Some(GeomStep::Given {
                    predicate: "on_line".to_string(),
                    args,
                }))
            }
            Constraint::OnCircle { point, circle } => Ok(Some(GeomStep::Given {
                predicate: "on_circle".to_string(),
                args: vec![point.clone(), circle.clone()],
            })),
            Constraint::OnSegment { point, segment } => {
                let mut args = vec![point.clone()];
                args.extend(segment.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "on_segment".to_string(),
                    args,
                }))
            }
            Constraint::Between { point, endpoints } => {
                let mut args = vec![point.clone()];
                args.extend(endpoints.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "between".to_string(),
                    args,
                }))
            }
            Constraint::NotEqual { .. } => {
                // Non-degeneracy condition, not a proof fact
                Ok(None)
            }
            Constraint::CongruentSegments { seg1, seg2 } => {
                let mut args = seg1.clone();
                args.extend(seg2.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "congruent_segments".to_string(),
                    args,
                }))
            }
            Constraint::CongruentAngles { angle1, angle2 } => {
                let mut args = self.angle_spec_to_args(angle1);
                args.extend(self.angle_spec_to_args(angle2));
                Ok(Some(GeomStep::Given {
                    predicate: "congruent_angles".to_string(),
                    args,
                }))
            }
            Constraint::CongruentTriangles { tri1, tri2 } => {
                let mut args = tri1.clone();
                args.extend(tri2.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "congruent_triangles".to_string(),
                    args,
                }))
            }
            Constraint::SimilarTriangles { tri1, tri2 } => {
                let mut args = tri1.clone();
                args.extend(tri2.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "similar_triangles".to_string(),
                    args,
                }))
            }
            Constraint::Midpoint { point, of_segment } => {
                let mut args = vec![point.clone()];
                args.extend(of_segment.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "midpoint".to_string(),
                    args,
                }))
            }
            Constraint::Tangent { line, circle } => {
                let mut args = self.line_spec_to_args(line);
                args.push(circle.clone());
                Ok(Some(GeomStep::Given {
                    predicate: "tangent".to_string(),
                    args,
                }))
            }
            Constraint::AngleMeasure { angle, .. } => {
                // Angle measure constraints become angle predicates
                let args = self.angle_spec_to_args(angle);
                Ok(Some(GeomStep::Given {
                    predicate: "angle_measure".to_string(),
                    args,
                }))
            }
            Constraint::SameSide { points, line } => {
                let mut args = points.clone();
                args.extend(self.line_spec_to_args(line));
                Ok(Some(GeomStep::Given {
                    predicate: "same_side".to_string(),
                    args,
                }))
            }
            Constraint::OppositeSide {
                point1,
                point2,
                line,
            } => {
                let mut args = vec![point1.clone(), point2.clone()];
                args.extend(self.line_spec_to_args(line));
                Ok(Some(GeomStep::Given {
                    predicate: "opposite_side".to_string(),
                    args,
                }))
            }
            Constraint::Custom { predicate, args } => Ok(Some(GeomStep::Given {
                predicate: predicate.clone(),
                args: args.clone(),
            })),
        }
    }

    /// Convert the goal to a target GeomStep.
    fn goal_to_step(&self, goal: &GoalSpec) -> Result<GoalStep, ConversionError> {
        match goal {
            GoalSpec::Collinear { points } => Ok(GoalStep {
                predicate: "collinear".to_string(),
                args: points.clone(),
            }),
            GoalSpec::Concurrent { lines } => {
                let args = lines
                    .iter()
                    .flat_map(|l| self.line_spec_to_args(l))
                    .collect();
                Ok(GoalStep {
                    predicate: "concurrent".to_string(),
                    args,
                })
            }
            GoalSpec::Cyclic { points } => Ok(GoalStep {
                predicate: "cyclic".to_string(),
                args: points.clone(),
            }),
            GoalSpec::Parallel { line1, line2 } => {
                let mut args = self.line_spec_to_args(line1);
                args.extend(self.line_spec_to_args(line2));
                Ok(GoalStep {
                    predicate: "parallel".to_string(),
                    args,
                })
            }
            GoalSpec::Perpendicular { line1, line2 } => {
                let mut args = self.line_spec_to_args(line1);
                args.extend(self.line_spec_to_args(line2));
                Ok(GoalStep {
                    predicate: "perpendicular".to_string(),
                    args,
                })
            }
            GoalSpec::CongruentSegments { seg1, seg2 } => {
                let mut args = seg1.clone();
                args.extend(seg2.clone());
                Ok(GoalStep {
                    predicate: "congruent_segments".to_string(),
                    args,
                })
            }
            GoalSpec::CongruentAngles { angle1, angle2 } => {
                let mut args = self.angle_spec_to_args(angle1);
                args.extend(self.angle_spec_to_args(angle2));
                Ok(GoalStep {
                    predicate: "congruent_angles".to_string(),
                    args,
                })
            }
            GoalSpec::CongruentTriangles { tri1, tri2 } => {
                let mut args = tri1.clone();
                args.extend(tri2.clone());
                Ok(GoalStep {
                    predicate: "congruent_triangles".to_string(),
                    args,
                })
            }
            GoalSpec::SimilarTriangles { tri1, tri2 } => {
                let mut args = tri1.clone();
                args.extend(tri2.clone());
                Ok(GoalStep {
                    predicate: "similar_triangles".to_string(),
                    args,
                })
            }
            GoalSpec::PointProperty {
                point,
                property,
                args,
            } => {
                let mut all_args = vec![point.clone()];
                all_args.extend(args.clone());
                Ok(GoalStep {
                    predicate: property.clone(),
                    args: all_args,
                })
            }
            GoalSpec::AngleMeasure { angle, .. } => {
                let args = self.angle_spec_to_args(angle);
                Ok(GoalStep {
                    predicate: "angle_measure".to_string(),
                    args,
                })
            }
            GoalSpec::Custom { predicate, args } => Ok(GoalStep {
                predicate: predicate.clone(),
                args: args.clone(),
            }),
        }
    }

    /// Extract point names from a line specification.
    fn line_spec_to_args(&self, spec: &LineSpec) -> Vec<String> {
        match spec {
            LineSpec::Named(name) => vec![name.clone()],
            LineSpec::Through { through } => through.clone(),
        }
    }

    /// Extract point names from an angle specification.
    fn angle_spec_to_args(&self, spec: &AngleSpec) -> Vec<String> {
        match spec {
            AngleSpec::ThreePoints { points } => points.clone(),
            AngleSpec::Directed { vertex, ray1, ray2 } => {
                vec![ray1.clone(), vertex.clone(), ray2.clone()]
            }
        }
    }
}

/// The result of converting a problem to steps.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProblemSteps {
    /// Problem identifier
    pub problem_id: String,
    /// Given facts (constructions and constraints)
    pub givens: Vec<GeomStep>,
    /// Goal to prove
    pub goal: GoalStep,
    /// All object names from the problem
    pub object_names: Vec<String>,
}

/// A goal predicate to prove.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GoalStep {
    /// Predicate name (e.g., "collinear", "parallel")
    pub predicate: String,
    /// Arguments (object names)
    pub args: Vec<String>,
}

impl ProblemSteps {
    /// Check if all required objects are present in the givens.
    ///
    /// REQUIRES: `self.object_names` contains names of all known objects
    /// ENSURES: On success, all args in `self.goal.args` are in `self.object_names`
    /// ENSURES: Returns Err(ObjectNotFound(name)) if goal references unknown object
    pub fn validate(&self) -> Result<(), ConversionError> {
        // Build set of known objects from object_names
        let known: std::collections::HashSet<&str> =
            self.object_names.iter().map(|s| s.as_str()).collect();

        // Check goal references known objects
        for arg in &self.goal.args {
            if !known.contains(arg.as_str()) {
                return Err(ConversionError::ObjectNotFound(arg.clone()));
            }
        }

        Ok(())
    }

    /// Get givens as axioms (for setting up proof context).
    ///
    /// ENSURES: All items in result are `GeomStep::Given` variants
    /// ENSURES: Result is a subset of `self.givens`
    /// ENSURES: Result preserves order from `self.givens`
    pub fn axiom_steps(&self) -> Vec<&GeomStep> {
        self.givens
            .iter()
            .filter(|s| matches!(s, GeomStep::Given { .. }))
            .collect()
    }

    /// Get construction steps.
    ///
    /// ENSURES: All items in result are `GeomStep::Construct` variants
    /// ENSURES: Result is a subset of `self.givens`
    /// ENSURES: Result preserves order from `self.givens`
    pub fn construction_steps(&self) -> Vec<&GeomStep> {
        self.givens
            .iter()
            .filter(|s| matches!(s, GeomStep::Construct { .. }))
            .collect()
    }
}
