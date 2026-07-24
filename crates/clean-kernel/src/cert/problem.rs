// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Geometry Problem Format Parser
//!
//! This module parses geometry problems from JSON format into internal
//! representations that can be processed by geometry solvers and
//! certificate generators.
//!
//! ## Problem Format
//!
//! Problems are specified in JSON with:
//! - `id`: Unique problem identifier
//! - `objects`: Named geometric objects (points, lines, circles)
//! - `constraints`: Relationships between objects (collinear, parallel, etc.)
//! - `goal`: The target predicate to prove
//! - `metadata`: Optional source info, difficulty, etc.
//!
//! ## Example
//!
//! ```json
//! {
//!   "id": "triangle_midpoint",
//!   "objects": {
//!     "A": {"type": "point"},
//!     "B": {"type": "point"},
//!     "C": {"type": "point"},
//!     "M": {"type": "point", "definition": {"midpoint_of": ["A", "B"]}}
//!   },
//!   "constraints": [
//!     {"type": "not_equal", "a": "A", "b": "B"},
//!     {"type": "not_equal", "a": "B", "b": "C"},
//!     {"type": "not_equal", "a": "A", "b": "C"}
//!   ],
//!   "goal": {
//!     "type": "parallel",
//!     "line1": {"through": ["M", "C"]},
//!     "line2": {"through": ["A", "B"]}
//!   }
//! }
//! ```
//!
//! ## Integration
//!
//! ```text
//! let problem = GeometryProblem::from_json(json_str)?;
//! let derivation = solver.solve(&problem)?;
//! let cert = generator.derivation_to_cert(&derivation)?;
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Errors that can occur during problem parsing.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ProblemParseError {
    /// JSON parsing failed
    #[error("JSON parse error: {0}")]
    JsonError(String),
    /// Invalid object type
    #[error("Invalid object type: {0}")]
    InvalidObjectType(String),
    /// Invalid constraint type
    #[error("Invalid constraint type: {0}")]
    InvalidConstraintType(String),
    /// Missing required field
    #[error("Missing required field: {0}")]
    MissingField(String),
    /// Reference to undefined object
    #[error("Reference to undefined object: {0}")]
    UndefinedObject(String),
    /// Invalid goal specification
    #[error("Invalid goal: {0}")]
    InvalidGoal(String),
    /// Circular object definition
    #[error("Circular definition for: {0}")]
    CircularDefinition(String),
}

/// A geometry problem specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GeometryProblem {
    /// Unique problem identifier
    pub id: String,

    /// Named geometric objects
    pub objects: HashMap<String, GeomObject>,

    /// Constraints between objects
    pub constraints: Vec<Constraint>,

    /// The goal predicate to prove
    pub goal: GoalSpec,

    /// Optional metadata
    #[serde(default)]
    pub metadata: ProblemMetadata,
}

/// A geometric object (point, line, circle, etc.)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GeomObject {
    /// Type of object
    #[serde(rename = "type")]
    pub obj_type: ObjectType,

    /// Optional definition (how the object is constructed)
    #[serde(default)]
    pub definition: Option<ObjectDefinition>,
}

/// Types of geometric objects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObjectType {
    /// A geometric point in 2D space
    Point,
    /// An infinite line
    Line,
    /// A circle defined by center and radius
    Circle,
    /// A line segment between two points
    Segment,
    /// An angle formed by two rays
    Angle,
    /// A triangle defined by three vertices
    Triangle,
    /// A ray starting from a point
    Ray,
    /// An arc of a circle
    Arc,
}

/// How an object is constructed/defined.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObjectDefinition {
    /// Line through two points
    Through(Vec<String>),

    /// Midpoint of two points
    MidpointOf(Vec<String>),

    /// Intersection of two lines
    Intersection {
        /// First line
        line1: LineSpec,
        /// Second line
        line2: LineSpec,
    },

    /// Circle through three points
    CircleThrough(Vec<String>),

    /// Circle with center and radius point
    CircleCenterRadius {
        /// Center point name
        center: String,
        /// Point on the circle defining the radius
        radius_point: String,
    },

    /// Circumcenter of triangle
    Circumcenter(Vec<String>),

    /// Incenter of triangle
    Incenter(Vec<String>),

    /// Orthocenter of triangle
    Orthocenter(Vec<String>),

    /// Centroid of triangle
    Centroid(Vec<String>),

    /// Nine-point center of triangle
    NinePointCenter(Vec<String>),

    /// Reflection of point over line
    Reflection {
        /// Point to reflect
        point: String,
        /// Line to reflect over
        over: LineSpec,
    },

    /// Perpendicular from point to line
    Perpendicular {
        /// Starting point
        from: String,
        /// Line to drop perpendicular to
        to: LineSpec,
    },

    /// Parallel through point
    Parallel {
        /// Point the parallel line passes through
        through: String,
        /// Line to be parallel to
        to: LineSpec,
    },

    /// Angle bisector
    AngleBisector {
        /// Vertex of the angle
        vertex: String,
        /// First ray endpoint
        ray1: String,
        /// Second ray endpoint
        ray2: String,
    },

    /// Foot of altitude
    FootOfAltitude {
        /// Vertex from which the altitude is dropped
        from: String,
        /// Two points defining the base segment
        to_segment: Vec<String>,
    },
}

/// Specification of a line (either by name or construction).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum LineSpec {
    /// Named line object
    Named(String),

    /// Line through two points
    Through {
        /// Point names defining the line
        through: Vec<String>,
    },
}

/// A constraint between geometric objects.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Constraint {
    /// Points are collinear
    Collinear {
        /// Point names that must be collinear
        points: Vec<String>,
    },

    /// Lines are concurrent
    Concurrent {
        /// Lines that must pass through a common point
        lines: Vec<LineSpec>,
    },

    /// Points lie on a circle (cyclic)
    Cyclic {
        /// Point names that must be concyclic
        points: Vec<String>,
    },

    /// Lines are parallel
    Parallel {
        /// First line
        line1: LineSpec,
        /// Second line
        line2: LineSpec,
    },

    /// Lines are perpendicular
    Perpendicular {
        /// First line
        line1: LineSpec,
        /// Second line (perpendicular to first)
        line2: LineSpec,
    },

    /// Point is on a line
    OnLine {
        /// Point name
        point: String,
        /// Line the point lies on
        line: LineSpec,
    },

    /// Point is on a circle
    OnCircle {
        /// Point name
        point: String,
        /// Circle name
        circle: String,
    },

    /// Point is on a segment
    OnSegment {
        /// Point name
        point: String,
        /// Two endpoints defining the segment
        segment: Vec<String>,
    },

    /// Point is between two others (on the segment, not endpoint)
    Between {
        /// Point that lies between the endpoints
        point: String,
        /// Two endpoint names
        endpoints: Vec<String>,
    },

    /// Two objects are not equal
    NotEqual {
        /// First object name
        a: String,
        /// Second object name
        b: String,
    },

    /// Segments are congruent
    CongruentSegments {
        /// First segment endpoints
        seg1: Vec<String>,
        /// Second segment endpoints
        seg2: Vec<String>,
    },

    /// Angles are congruent
    CongruentAngles {
        /// First angle specification
        angle1: AngleSpec,
        /// Second angle specification
        angle2: AngleSpec,
    },

    /// Triangles are congruent
    CongruentTriangles {
        /// First triangle vertices
        tri1: Vec<String>,
        /// Second triangle vertices
        tri2: Vec<String>,
    },

    /// Triangles are similar
    SimilarTriangles {
        /// First triangle vertices
        tri1: Vec<String>,
        /// Second triangle vertices
        tri2: Vec<String>,
    },

    /// Point is the midpoint of a segment
    Midpoint {
        /// Midpoint name
        point: String,
        /// Two endpoints of the segment
        of_segment: Vec<String>,
    },

    /// Line is tangent to circle
    Tangent {
        /// Line specification
        line: LineSpec,
        /// Circle name
        circle: String,
    },

    /// Angle has specific measure (in degrees or as expression)
    AngleMeasure {
        /// Angle specification
        angle: AngleSpec,
        /// The required measure
        measure: AngleMeasure,
    },

    /// Points are on same side of a line
    SameSide {
        /// Point names
        points: Vec<String>,
        /// Separating line
        line: LineSpec,
    },

    /// Points are on opposite sides of a line
    OppositeSide {
        /// First point name
        point1: String,
        /// Second point name
        point2: String,
        /// Separating line
        line: LineSpec,
    },

    /// Custom predicate (for extensibility)
    Custom {
        /// Predicate name
        predicate: String,
        /// Arguments to the predicate
        args: Vec<String>,
    },
}

/// Specification of an angle.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AngleSpec {
    /// Angle specified by three points (vertex is second)
    ThreePoints {
        /// Three point names (vertex is the middle one)
        points: Vec<String>,
    },

    /// Directed angle
    Directed {
        /// Angle vertex
        vertex: String,
        /// First ray endpoint
        ray1: String,
        /// Second ray endpoint
        ray2: String,
    },
}

/// Angle measure specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AngleMeasure {
    /// Degrees (integer)
    Degrees(i32),

    /// Fraction of pi (e.g., "pi/2", "pi/3")
    PiFraction {
        /// Numerator of the pi fraction
        numerator: i32,
        /// Denominator of the pi fraction
        denominator: i32,
    },

    /// Right angle (90 degrees)
    Right,

    /// Straight angle (180 degrees)
    Straight,
}

/// Goal specification - what needs to be proved.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum GoalSpec {
    /// Prove points are collinear
    Collinear {
        /// Point names to prove collinear
        points: Vec<String>,
    },

    /// Prove lines are concurrent
    Concurrent {
        /// Lines to prove concurrent
        lines: Vec<LineSpec>,
    },

    /// Prove points are concyclic
    Cyclic {
        /// Point names to prove concyclic
        points: Vec<String>,
    },

    /// Prove lines are parallel
    Parallel {
        /// First line
        line1: LineSpec,
        /// Second line
        line2: LineSpec,
    },

    /// Prove lines are perpendicular
    Perpendicular {
        /// First line
        line1: LineSpec,
        /// Second line
        line2: LineSpec,
    },

    /// Prove segments are congruent
    CongruentSegments {
        /// First segment endpoints
        seg1: Vec<String>,
        /// Second segment endpoints
        seg2: Vec<String>,
    },

    /// Prove angles are congruent
    CongruentAngles {
        /// First angle
        angle1: AngleSpec,
        /// Second angle
        angle2: AngleSpec,
    },

    /// Prove triangles are congruent
    CongruentTriangles {
        /// First triangle vertices
        tri1: Vec<String>,
        /// Second triangle vertices
        tri2: Vec<String>,
    },

    /// Prove triangles are similar
    SimilarTriangles {
        /// First triangle vertices
        tri1: Vec<String>,
        /// Second triangle vertices
        tri2: Vec<String>,
    },

    /// Prove a point has a specific property
    PointProperty {
        /// Point name
        point: String,
        /// Property name
        property: String,
        /// Additional arguments
        args: Vec<String>,
    },

    /// Prove angle has specific measure
    AngleMeasure {
        /// Angle specification
        angle: AngleSpec,
        /// Expected measure
        measure: AngleMeasure,
    },

    /// Prove a custom predicate
    Custom {
        /// Predicate name
        predicate: String,
        /// Predicate arguments
        args: Vec<String>,
    },
}

/// Problem metadata.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ProblemMetadata {
    /// Source of the problem
    #[serde(default)]
    pub source: Option<String>,

    /// Competition/book the problem is from
    #[serde(default)]
    pub origin: Option<String>,

    /// Year of the problem
    #[serde(default)]
    pub year: Option<i32>,

    /// Difficulty rating (1-10)
    #[serde(default)]
    pub difficulty: Option<u8>,

    /// Problem categories/tags
    #[serde(default)]
    pub tags: Vec<String>,

    /// Whether the problem is known to be solvable
    #[serde(default)]
    pub known_solvable: Option<bool>,

    /// Reference to a known solution
    #[serde(default)]
    pub solution_ref: Option<String>,

    /// Original problem statement (natural language)
    #[serde(default)]
    pub statement: Option<String>,
}

impl GeometryProblem {
    /// Parse a geometry problem from JSON.
    pub fn from_json(json_str: &str) -> Result<Self, ProblemParseError> {
        serde_json::from_str(json_str).map_err(|e| ProblemParseError::JsonError(e.to_string()))
    }

    /// Parse a geometry problem from a JSON file.
    pub fn from_file(path: &std::path::Path) -> Result<Self, ProblemParseError> {
        let contents = std::fs::read_to_string(path)
            .map_err(|e| ProblemParseError::JsonError(format!("Failed to read file: {}", e)))?;
        Self::from_json(&contents)
    }

    /// Serialize the problem to JSON.
    pub fn to_json(&self) -> Result<String, ProblemParseError> {
        serde_json::to_string_pretty(self).map_err(|e| ProblemParseError::JsonError(e.to_string()))
    }

    /// Validate the problem structure.
    ///
    /// Checks that:
    /// - All object references in constraints and goal are defined
    /// - Object definitions don't have circular dependencies
    /// - Constraint types are compatible with object types
    pub fn validate(&self) -> Result<(), ProblemParseError> {
        // Collect all defined object names
        let defined_objects: std::collections::HashSet<&str> =
            self.objects.keys().map(|s| s.as_str()).collect();

        // Validate object definitions
        for (name, obj) in &self.objects {
            if let Some(def) = &obj.definition {
                self.validate_definition(name, def, &defined_objects)?;
            }
        }

        // Validate constraints
        for constraint in &self.constraints {
            self.validate_constraint(constraint, &defined_objects)?;
        }

        // Validate goal
        self.validate_goal(&self.goal, &defined_objects)?;

        Ok(())
    }

    /// Validate an object definition.
    fn validate_definition(
        &self,
        _name: &str,
        def: &ObjectDefinition,
        defined: &std::collections::HashSet<&str>,
    ) -> Result<(), ProblemParseError> {
        match def {
            ObjectDefinition::Through(points)
            | ObjectDefinition::MidpointOf(points)
            | ObjectDefinition::CircleThrough(points)
            | ObjectDefinition::Circumcenter(points)
            | ObjectDefinition::Incenter(points)
            | ObjectDefinition::Orthocenter(points)
            | ObjectDefinition::Centroid(points)
            | ObjectDefinition::NinePointCenter(points) => {
                for p in points {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            ObjectDefinition::CircleCenterRadius {
                center,
                radius_point,
            } => {
                if !defined.contains(center.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(center.clone()));
                }
                if !defined.contains(radius_point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(radius_point.clone()));
                }
            }
            ObjectDefinition::Intersection { line1, line2 } => {
                self.validate_line_spec(line1, defined)?;
                self.validate_line_spec(line2, defined)?;
            }
            ObjectDefinition::Reflection { point, over } => {
                if !defined.contains(point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point.clone()));
                }
                self.validate_line_spec(over, defined)?;
            }
            ObjectDefinition::Perpendicular { from, to }
            | ObjectDefinition::Parallel { through: from, to } => {
                if !defined.contains(from.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(from.clone()));
                }
                self.validate_line_spec(to, defined)?;
            }
            ObjectDefinition::AngleBisector { vertex, ray1, ray2 } => {
                if !defined.contains(vertex.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(vertex.clone()));
                }
                if !defined.contains(ray1.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(ray1.clone()));
                }
                if !defined.contains(ray2.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(ray2.clone()));
                }
            }
            ObjectDefinition::FootOfAltitude { from, to_segment } => {
                if !defined.contains(from.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(from.clone()));
                }
                for p in to_segment {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
        }
        Ok(())
    }

    /// Validate a line specification.
    fn validate_line_spec(
        &self,
        spec: &LineSpec,
        defined: &std::collections::HashSet<&str>,
    ) -> Result<(), ProblemParseError> {
        match spec {
            LineSpec::Named(name) => {
                if !defined.contains(name.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(name.clone()));
                }
            }
            LineSpec::Through { through } => {
                for p in through {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
        }
        Ok(())
    }

    /// Validate a constraint.
    fn validate_constraint(
        &self,
        constraint: &Constraint,
        defined: &std::collections::HashSet<&str>,
    ) -> Result<(), ProblemParseError> {
        match constraint {
            Constraint::Collinear { points }
            | Constraint::Cyclic { points }
            | Constraint::SameSide { points, .. } => {
                for p in points {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            Constraint::Concurrent { lines } => {
                for line in lines {
                    self.validate_line_spec(line, defined)?;
                }
            }
            Constraint::Parallel { line1, line2 } | Constraint::Perpendicular { line1, line2 } => {
                self.validate_line_spec(line1, defined)?;
                self.validate_line_spec(line2, defined)?;
            }
            Constraint::OnLine { point, line } => {
                if !defined.contains(point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point.clone()));
                }
                self.validate_line_spec(line, defined)?;
            }
            Constraint::OnCircle { point, circle } => {
                if !defined.contains(point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point.clone()));
                }
                if !defined.contains(circle.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(circle.clone()));
                }
            }
            Constraint::OnSegment { point, segment }
            | Constraint::Between {
                point,
                endpoints: segment,
            } => {
                if !defined.contains(point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point.clone()));
                }
                for p in segment {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            Constraint::NotEqual { a, b } => {
                if !defined.contains(a.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(a.clone()));
                }
                if !defined.contains(b.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(b.clone()));
                }
            }
            Constraint::CongruentSegments { seg1, seg2 } => {
                for p in seg1.iter().chain(seg2.iter()) {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            Constraint::CongruentAngles { angle1, angle2 } => {
                self.validate_angle_spec(angle1, defined)?;
                self.validate_angle_spec(angle2, defined)?;
            }
            Constraint::CongruentTriangles { tri1, tri2 }
            | Constraint::SimilarTriangles { tri1, tri2 } => {
                for p in tri1.iter().chain(tri2.iter()) {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            Constraint::Midpoint { point, of_segment } => {
                if !defined.contains(point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point.clone()));
                }
                for p in of_segment {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            Constraint::Tangent { line, circle } => {
                self.validate_line_spec(line, defined)?;
                if !defined.contains(circle.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(circle.clone()));
                }
            }
            Constraint::AngleMeasure { angle, .. } => {
                self.validate_angle_spec(angle, defined)?;
            }
            Constraint::OppositeSide {
                point1,
                point2,
                line,
            } => {
                if !defined.contains(point1.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point1.clone()));
                }
                if !defined.contains(point2.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point2.clone()));
                }
                self.validate_line_spec(line, defined)?;
            }
            Constraint::Custom { args, .. } => {
                for arg in args {
                    if !defined.contains(arg.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(arg.clone()));
                    }
                }
            }
        }
        Ok(())
    }

    /// Validate an angle specification.
    fn validate_angle_spec(
        &self,
        angle: &AngleSpec,
        defined: &std::collections::HashSet<&str>,
    ) -> Result<(), ProblemParseError> {
        match angle {
            AngleSpec::ThreePoints { points } => {
                for p in points {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            AngleSpec::Directed { vertex, ray1, ray2 } => {
                if !defined.contains(vertex.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(vertex.clone()));
                }
                if !defined.contains(ray1.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(ray1.clone()));
                }
                if !defined.contains(ray2.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(ray2.clone()));
                }
            }
        }
        Ok(())
    }

    /// Validate a goal specification.
    fn validate_goal(
        &self,
        goal: &GoalSpec,
        defined: &std::collections::HashSet<&str>,
    ) -> Result<(), ProblemParseError> {
        match goal {
            GoalSpec::Collinear { points } | GoalSpec::Cyclic { points } => {
                for p in points {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            GoalSpec::Concurrent { lines } => {
                for line in lines {
                    self.validate_line_spec(line, defined)?;
                }
            }
            GoalSpec::Parallel { line1, line2 } | GoalSpec::Perpendicular { line1, line2 } => {
                self.validate_line_spec(line1, defined)?;
                self.validate_line_spec(line2, defined)?;
            }
            GoalSpec::CongruentSegments { seg1, seg2 } => {
                for p in seg1.iter().chain(seg2.iter()) {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            GoalSpec::CongruentAngles { angle1, angle2 } => {
                self.validate_angle_spec(angle1, defined)?;
                self.validate_angle_spec(angle2, defined)?;
            }
            GoalSpec::CongruentTriangles { tri1, tri2 }
            | GoalSpec::SimilarTriangles { tri1, tri2 } => {
                for p in tri1.iter().chain(tri2.iter()) {
                    if !defined.contains(p.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(p.clone()));
                    }
                }
            }
            GoalSpec::PointProperty { point, args, .. } => {
                if !defined.contains(point.as_str()) {
                    return Err(ProblemParseError::UndefinedObject(point.clone()));
                }
                for arg in args {
                    if !defined.contains(arg.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(arg.clone()));
                    }
                }
            }
            GoalSpec::AngleMeasure { angle, .. } => {
                self.validate_angle_spec(angle, defined)?;
            }
            GoalSpec::Custom { args, .. } => {
                for arg in args {
                    if !defined.contains(arg.as_str()) {
                        return Err(ProblemParseError::UndefinedObject(arg.clone()));
                    }
                }
            }
        }
        Ok(())
    }

    /// Get all object names used in the problem.
    pub fn all_object_names(&self) -> Vec<&str> {
        self.objects.keys().map(|s| s.as_str()).collect()
    }

    /// Get all point objects.
    pub fn points(&self) -> Vec<(&str, &GeomObject)> {
        self.objects
            .iter()
            .filter(|(_, obj)| obj.obj_type == ObjectType::Point)
            .map(|(name, obj)| (name.as_str(), obj))
            .collect()
    }

    /// Get all line objects.
    pub fn lines(&self) -> Vec<(&str, &GeomObject)> {
        self.objects
            .iter()
            .filter(|(_, obj)| obj.obj_type == ObjectType::Line)
            .map(|(name, obj)| (name.as_str(), obj))
            .collect()
    }

    /// Get all circle objects.
    pub fn circles(&self) -> Vec<(&str, &GeomObject)> {
        self.objects
            .iter()
            .filter(|(_, obj)| obj.obj_type == ObjectType::Circle)
            .map(|(name, obj)| (name.as_str(), obj))
            .collect()
    }
}

/// Result of solving a geometry problem.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProblemSolution {
    /// The problem that was solved
    pub problem_id: String,

    /// Whether the solver succeeded
    pub solved: bool,

    /// Time taken to solve (milliseconds)
    pub solve_time_ms: u64,

    /// Derivation trace (for certificate generation)
    pub derivation: Option<Vec<super::geometry::GeomStep>>,

    /// Auxiliary constructions added
    #[serde(default)]
    pub aux_constructions: Vec<AuxConstruction>,

    /// Error message if failed
    #[serde(default)]
    pub error: Option<String>,
}

/// An auxiliary construction added by the solver.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuxConstruction {
    /// Name of the new object
    pub name: String,

    /// Type of construction
    pub construction_type: String,

    /// Objects used in the construction
    pub from_objects: Vec<String>,

    /// Reason for the construction
    #[serde(default)]
    pub justification: Option<String>,
}

/// Benchmark result for a set of problems.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BenchmarkResult {
    /// Total problems attempted
    pub total: usize,

    /// Problems solved
    pub solved: usize,

    /// Problems unsolved (timeout or failure)
    pub unsolved: usize,

    /// Problems with errors
    pub errors: usize,

    /// Total time (milliseconds)
    pub total_time_ms: u64,

    /// Individual results
    pub results: Vec<ProblemSolution>,
}

impl BenchmarkResult {
    /// Calculate solve rate as a percentage.
    pub fn solve_rate(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            (self.solved as f64 / self.total as f64) * 100.0
        }
    }

    /// Average solve time (only for solved problems).
    pub fn avg_solve_time_ms(&self) -> f64 {
        let solved_results: Vec<_> = self.results.iter().filter(|r| r.solved).collect();
        if solved_results.is_empty() {
            0.0
        } else {
            solved_results.iter().map(|r| r.solve_time_ms).sum::<u64>() as f64
                / solved_results.len() as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_problem() {
        let json = r#"
        {
            "id": "test_collinear",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "C": {"type": "point"}
            },
            "constraints": [
                {"type": "not_equal", "a": "A", "b": "B"},
                {"type": "not_equal", "a": "B", "b": "C"}
            ],
            "goal": {
                "type": "collinear",
                "points": ["A", "B", "C"]
            }
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        assert_eq!(problem.id, "test_collinear");
        assert_eq!(problem.objects.len(), 3);
        assert_eq!(problem.constraints.len(), 2);
        problem
            .validate()
            .expect("collinear problem should validate");
    }

    #[test]
    fn test_parse_problem_with_midpoint() {
        let json = r#"
        {
            "id": "midpoint_test",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "M": {"type": "point", "definition": {"midpoint_of": ["A", "B"]}}
            },
            "constraints": [
                {"type": "not_equal", "a": "A", "b": "B"}
            ],
            "goal": {
                "type": "congruent_segments",
                "seg1": ["A", "M"],
                "seg2": ["M", "B"]
            }
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        assert_eq!(problem.objects.len(), 3);

        let m = &problem.objects["M"];
        let _def = m
            .definition
            .as_ref()
            .expect("object M should have a definition");
        problem
            .validate()
            .expect("midpoint problem should validate");
    }

    #[test]
    fn test_parse_problem_with_lines() {
        let json = r#"
        {
            "id": "parallel_test",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "C": {"type": "point"},
                "D": {"type": "point"}
            },
            "constraints": [
                {"type": "parallel", "line1": {"through": ["A", "B"]}, "line2": {"through": ["C", "D"]}}
            ],
            "goal": {
                "type": "perpendicular",
                "line1": {"through": ["A", "C"]},
                "line2": {"through": ["B", "D"]}
            }
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        problem
            .validate()
            .expect("parallel lines problem should validate");
    }

    #[test]
    fn test_undefined_object_error() {
        let json = r#"
        {
            "id": "bad_problem",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"}
            },
            "constraints": [
                {"type": "collinear", "points": ["A", "B", "X"]}
            ],
            "goal": {
                "type": "collinear",
                "points": ["A", "B"]
            }
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        let result = problem.validate();
        assert!(matches!(result, Err(ProblemParseError::UndefinedObject(_))));
    }

    #[test]
    fn test_problem_with_metadata() {
        let json = r#"
        {
            "id": "imo_2019_p1",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "C": {"type": "point"}
            },
            "constraints": [],
            "goal": {"type": "collinear", "points": ["A", "B", "C"]},
            "metadata": {
                "source": "IMO",
                "year": 2019,
                "difficulty": 7,
                "tags": ["geometry", "collinearity"],
                "known_solvable": true
            }
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        assert_eq!(problem.metadata.source.as_deref(), Some("IMO"));
        assert_eq!(problem.metadata.year, Some(2019));
        assert_eq!(problem.metadata.difficulty, Some(7));
        assert_eq!(problem.metadata.tags.len(), 2);
    }

    #[test]
    fn test_points_filter() {
        let json = r#"
        {
            "id": "mixed_objects",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"},
                "l": {"type": "line"},
                "C": {"type": "point"},
                "mathverse": {"type": "circle"}
            },
            "constraints": [],
            "goal": {"type": "collinear", "points": ["A", "B", "C"]}
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        assert_eq!(problem.points().len(), 3);
        assert_eq!(problem.lines().len(), 1);
        assert_eq!(problem.circles().len(), 1);
    }

    #[test]
    fn test_serialize_roundtrip() {
        let json = r#"
        {
            "id": "roundtrip_test",
            "objects": {
                "A": {"type": "point"},
                "B": {"type": "point"}
            },
            "constraints": [
                {"type": "not_equal", "a": "A", "b": "B"}
            ],
            "goal": {"type": "collinear", "points": ["A", "B"]}
        }
        "#;

        let problem = GeometryProblem::from_json(json).unwrap();
        let serialized = problem.to_json().unwrap();
        let reparsed = GeometryProblem::from_json(&serialized).unwrap();

        assert_eq!(problem.id, reparsed.id);
        assert_eq!(problem.objects.len(), reparsed.objects.len());
    }
}
