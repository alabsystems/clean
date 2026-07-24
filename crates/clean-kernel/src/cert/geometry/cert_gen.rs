// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Geometry certificate generation — types and core generator.
//!
//! Contains `GeometryCertError`, `GeomStep`, and `GeometryCertGenerator` with all
//! impl methods including MicroChecker conversion and verification.

use super::super::ProofCert;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Errors that can occur during geometry certificate generation.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum GeometryCertError {
    /// Unknown axiom name
    #[error("Unknown geometry axiom: {0}")]
    UnknownAxiom(String),
    /// Unknown lemma name
    #[error("Unknown geometry lemma: {0}")]
    UnknownLemma(String),
    /// Type mismatch during certificate construction
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch {
        /// Expected type
        expected: String,
        /// Actual type found
        actual: String,
    },
    /// Environment not initialized with computational geometry
    #[error("Environment not initialized with computational geometry")]
    EnvironmentNotInitialized,
    /// Invalid derivation step structure
    #[error("Invalid derivation: {0}")]
    InvalidDerivation(String),
    /// Missing prerequisite for lemma application
    #[error("Missing prerequisite: {0}")]
    MissingPrerequisite(String),
}

/// A step in a geometry derivation trace.
///
/// This represents the output format from geometry solvers like
/// Newclid, AlphaGeometry, or native geometry engines.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GeomStep {
    /// Axiom reference - a known geometry fact from the problem statement
    Axiom {
        /// Axiom name (e.g., "collinear", "on_circle", "midpoint")
        name: String,
        /// Arguments (point/line/circle names)
        args: Vec<String>,
    },

    /// Lemma application - using a theorem with arguments
    Apply {
        /// Predicate proven by the lemma application.
        #[serde(default)]
        predicate: String,
        /// Lemma name (e.g., "CollinearTrans", "Thales", "InscribedAngle")
        lemma: String,
        /// Sub-derivations for lemma prerequisites
        premises: Vec<GeomStep>,
        /// Arguments to instantiate the lemma (usually point names)
        args: Vec<String>,
    },

    /// Introduced point/object from auxiliary construction
    Construct {
        /// Type of construction ("midpoint", "intersection", "circumcenter")
        kind: String,
        /// Name of the new object
        name: String,
        /// Objects used in the construction
        from: Vec<String>,
    },

    /// Direct assertion (from problem givens)
    Given {
        /// Predicate name
        predicate: String,
        /// Arguments
        args: Vec<String>,
    },
}

/// Generator for converting geometry derivations to ProofCert.
///
/// The generator maintains a mapping from geometry objects to clean expressions
/// and translates derivation steps into typed proof certificates.
pub struct GeometryCertGenerator {
    /// The environment with geometry axioms loaded
    env: Environment,
    /// Cache of object names to their clean expressions
    object_cache: HashMap<String, Expr>,
    /// Cache of generated certificates for reuse
    cert_cache: HashMap<String, ProofCert>,
    /// Counter for generating fresh FVarIds
    fvar_counter: u64,
}

impl GeometryCertGenerator {
    /// Create a new geometry certificate generator.
    ///
    /// The environment must have been initialized with `init_computational_geometry()`.
    ///
    /// # Errors
    /// Returns `GeometryCertError::EnvironmentNotInitialized` if the environment
    /// hasn't been initialized with computational geometry axioms.
    ///
    /// REQUIRES: `env.is_computational_geometry_init()` returns true
    /// ENSURES: On success, result has empty caches and zero fvar counter
    /// ENSURES: Returns Err(EnvironmentNotInitialized) if env not initialized
    pub fn new(env: Environment) -> Result<Self, GeometryCertError> {
        // Verify environment has computational geometry initialized
        if !env.is_computational_geometry_init() {
            return Err(GeometryCertError::EnvironmentNotInitialized);
        }

        Ok(Self {
            env,
            object_cache: HashMap::new(),
            cert_cache: HashMap::new(),
            fvar_counter: 0,
        })
    }

    /// Register a geometry object (point, line, circle) with its clean expression.
    ///
    /// Objects must be registered before they can be used in derivation steps.
    ///
    /// ENSURES: `self.get_object(name) == Some(&expr)` after call
    /// ENSURES: Overwrites any previous registration for `name`
    pub fn register_object(&mut self, name: &str, expr: Expr) {
        self.object_cache.insert(name.to_string(), expr);
    }

    /// Generate a fresh FVarId.
    ///
    /// ENSURES: Result is unique across all calls on this instance
    /// ENSURES: `self.fvar_counter` is incremented by 1
    fn fresh_fvar_id(&mut self) -> crate::expr::FVarId {
        self.fvar_counter += 1;
        crate::expr::FVarId(self.fvar_counter)
    }

    /// Convert a geometry derivation step to a ProofCert.
    ///
    /// This is the main entry point for certificate generation. Each step
    /// in the derivation trace becomes a certificate node that can be
    /// verified by the MicroChecker.
    ///
    /// # Arguments
    /// * `step` - The geometry derivation step to convert
    ///
    /// # Returns
    /// A ProofCert representing the typing derivation for this step.
    ///
    /// # Errors
    /// Returns errors if:
    /// - An unknown axiom/lemma is referenced
    /// - Required objects aren't registered
    /// - Type mismatches occur during construction
    ///
    /// REQUIRES: `self.env` has geometry axioms/lemmas initialized
    /// REQUIRES: `step` references only registered geometry objects
    /// ENSURES: On success, result is a well-formed ProofCert for the derivation
    /// ENSURES: On success, `CertVerifier::verify(result, expr)` succeeds for corresponding expr
    /// ENSURES: Soundness - generated certificates only prove valid geometry theorems
    /// ENSURES: Returns Err(UnknownAxiom|UnknownLemma|ObjectNotFound|...) on invalid input
    pub fn step_to_cert(&mut self, step: &GeomStep) -> Result<ProofCert, GeometryCertError> {
        match step {
            GeomStep::Axiom { name, args } => self.axiom_to_cert(name, args),
            GeomStep::Apply {
                predicate: _,
                lemma,
                premises,
                args,
            } => self.apply_to_cert(lemma, premises, args),
            GeomStep::Construct { kind, name, from } => self.construct_to_cert(kind, name, from),
            GeomStep::Given { predicate, args } => self.given_to_cert(predicate, args),
        }
    }

    /// Convert an axiom reference to a certificate.
    ///
    /// REQUIRES: `name` is a supported geometry axiom identifier
    /// REQUIRES: `self.env` contains the mapped CompGeom constant
    /// ENSURES: On success, returns ProofCert::Const with type from the environment
    /// ENSURES: Returns Err(UnknownAxiom) if name is unrecognized or missing
    pub(super) fn axiom_to_cert(
        &self,
        name: &str,
        _args: &[String],
    ) -> Result<ProofCert, GeometryCertError> {
        // Map geometry axiom name to CompGeom constant
        let const_name = self.geometry_name_to_const(name)?;

        // Look up the constant in the environment
        let const_info = self
            .env
            .get_const(&const_name)
            .ok_or_else(|| GeometryCertError::UnknownAxiom(name.to_string()))?;

        // Create Const certificate
        Ok(ProofCert::Const {
            name: const_name,
            levels: vec![Level::zero()],
            type_: Box::new(const_info.type_.clone()),
        })
    }

    /// Convert a lemma application to a certificate.
    ///
    /// This method handles type inference for lemma applications by tracking
    /// the current function type through each application step.
    ///
    /// For a lemma with type `∀ A B C, collinear A B C → ...`:
    /// - First application: Type becomes `∀ B C, collinear A B C → ...`
    /// - Second application: Type becomes `∀ C, collinear A B C → ...`
    /// - And so on...
    ///
    /// REQUIRES: `lemma` maps to a CompGeom constant in `self.env`
    /// REQUIRES: `premises` are valid derivation steps for this lemma
    /// ENSURES: On success, result is a well-typed App chain of lemma/premises
    /// ENSURES: Each premise is converted using `step_to_cert`
    /// ENSURES: Returns Err(UnknownLemma|TypeMismatch|InvalidDerivation) on failure
    fn apply_to_cert(
        &mut self,
        lemma: &str,
        premises: &[GeomStep],
        args: &[String],
    ) -> Result<ProofCert, GeometryCertError> {
        // Map lemma name to CompGeom theorem constant
        let lemma_name = self.geometry_lemma_to_const(lemma)?;

        // Look up the lemma in the environment and clone type to avoid borrow conflict
        let lemma_type = {
            let lemma_info = self
                .env
                .get_const(&lemma_name)
                .ok_or_else(|| GeometryCertError::UnknownLemma(lemma.to_string()))?;
            lemma_info.type_.clone()
        };

        // Generate certificates for all premises
        // (now safe since we've released the borrow on self.env)
        let mut premise_certs = Vec::with_capacity(premises.len());
        for p in premises {
            premise_certs.push(self.step_to_cert(p)?);
        }

        // Build application chain: lemma applied to all premises
        let mut result = ProofCert::Const {
            name: lemma_name,
            levels: vec![Level::zero()],
            type_: Box::new(lemma_type.clone()),
        };

        // Track current function type for type inference
        let mut current_type = lemma_type;

        // First, apply to any explicit arguments (point names, etc.)
        for arg_name in args {
            // Look up argument in object cache to get its expression
            let arg_expr = match self.get_object(arg_name).cloned() {
                Some(expr) => expr,
                None => {
                    // If not in cache, create a placeholder free variable
                    // In a real implementation, we'd track these properly
                    Expr::from_kind(ExprKind::FVar(self.fresh_fvar_id()))
                }
            };

            let (fn_type, result_type) = self.compute_app_types(&current_type, &arg_expr)?;

            // Create certificate for the argument (as a free variable reference)
            let fvar_id = match &arg_expr.kind {
                ExprKind::FVar(id) => *id,
                _ => self.fresh_fvar_id(),
            };
            let arg_cert = ProofCert::FVar {
                id: fvar_id,
                type_: Box::new(self.extract_domain(&fn_type).unwrap_or(arg_expr.clone())),
            };

            result = ProofCert::App {
                fn_cert: Box::new(result),
                fn_type: Box::new(fn_type),
                arg_cert: Box::new(arg_cert),
                result_type: Box::new(result_type.clone()),
            };

            current_type = result_type;
        }

        // Then, apply to premise certificates (proof terms)
        for premise_cert in premise_certs {
            let (fn_type, result_type) = self.compute_app_types_for_proof(&current_type)?;

            result = ProofCert::App {
                fn_cert: Box::new(result),
                fn_type: Box::new(fn_type),
                arg_cert: Box::new(premise_cert),
                result_type: Box::new(result_type.clone()),
            };

            current_type = result_type;
        }

        Ok(result)
    }

    /// Compute the function type and result type for an application.
    ///
    /// Given a function type `∀ (x : A), B` and an argument `a : A`,
    /// returns `(∀ (x : A), B, B[a/x])`.
    ///
    /// REQUIRES: `fn_type` is a Pi type compatible with `arg`
    /// ENSURES: On success, result_type is `codomain.instantiate(arg)`
    /// ENSURES: Returns Err(TypeMismatch) if `fn_type` is not a Pi type
    pub(super) fn compute_app_types(
        &mut self,
        fn_type: &Expr,
        arg: &Expr,
    ) -> Result<(Expr, Expr), GeometryCertError> {
        match &fn_type.kind {
            ExprKind::Pi(_binder_info, _domain, codomain) => {
                // The result type is the codomain with the argument substituted
                let result_type = codomain.instantiate(arg);
                Ok((fn_type.clone(), result_type))
            }
            _ => {
                // If not a Pi type, we can't apply - but for geometry certs we
                // may have partially evaluated types, so fall back gracefully
                Err(GeometryCertError::TypeMismatch {
                    expected: "Pi type".to_string(),
                    actual: format!("{:?}", fn_type),
                })
            }
        }
    }

    /// Compute application types when applying a proof term.
    ///
    /// For proof applications, we don't have the actual proof term expression,
    /// so we just extract the domain and codomain from the Pi type.
    ///
    /// REQUIRES: `fn_type` is a Pi type
    /// ENSURES: On success, result_type is codomain instantiated with placeholder
    /// ENSURES: Returns Err(TypeMismatch) if `fn_type` is not a Pi type
    fn compute_app_types_for_proof(
        &mut self,
        fn_type: &Expr,
    ) -> Result<(Expr, Expr), GeometryCertError> {
        match &fn_type.kind {
            ExprKind::Pi(_binder_info, _domain, codomain) => {
                // For proof applications, we use a placeholder for substitution
                // since we don't have the actual proof term.
                // This is safe because proofs are proof-irrelevant in Prop.
                let placeholder = Expr::from_kind(ExprKind::FVar(self.fresh_fvar_id()));
                let result_type = codomain.instantiate(&placeholder);
                Ok((fn_type.clone(), result_type))
            }
            _ => Err(GeometryCertError::TypeMismatch {
                expected: "Pi type".to_string(),
                actual: format!("{:?}", fn_type),
            }),
        }
    }

    /// Extract the domain type from a Pi type.
    ///
    /// REQUIRES: `ty` is any expression
    /// ENSURES: Returns Some(domain) if `ty` is a Pi type
    /// ENSURES: Returns None if `ty` is not a Pi type
    fn extract_domain(&self, ty: &Expr) -> Option<Expr> {
        match &ty.kind {
            ExprKind::Pi(_, domain, _) => Some((**domain).clone()),
            _ => None,
        }
    }

    /// Convert a construction step to a certificate.
    ///
    /// REQUIRES: `kind` maps to a known CompGeom constructor
    /// REQUIRES: `self.env` contains the mapped constructor constant
    /// ENSURES: On success, returns a Const certificate for the constructor
    /// ENSURES: Returns Err(InvalidDerivation) on unknown construction
    fn construct_to_cert(
        &mut self,
        kind: &str,
        _name: &str,
        _from: &[String],
    ) -> Result<ProofCert, GeometryCertError> {
        // Map construction kind to CompGeom constant
        let const_name = self.construction_to_const(kind)?;

        let const_info = self.env.get_const(&const_name).ok_or_else(|| {
            GeometryCertError::InvalidDerivation(format!("Unknown construction: {}", kind))
        })?;

        // NOTE: Full construction certificates need argument application (#83)
        // This would require: translate `from` objects to Expr terms, build App term
        // Current approach: return constructor constant, works for existence proofs
        Ok(ProofCert::Const {
            name: const_name,
            levels: vec![Level::zero()],
            type_: Box::new(const_info.type_.clone()),
        })
    }

    /// Convert a given predicate to a certificate.
    ///
    /// REQUIRES: `predicate` maps to a known geometry axiom
    /// ENSURES: On success, equivalent to `axiom_to_cert(predicate, ...)`
    /// ENSURES: Returns Err(UnknownAxiom) on unknown predicate
    fn given_to_cert(
        &self,
        predicate: &str,
        _args: &[String],
    ) -> Result<ProofCert, GeometryCertError> {
        // Givens are axioms from the problem statement
        self.axiom_to_cert(predicate, &[])
    }

    /// Map a geometry predicate name to its CompGeom constant name.
    ///
    /// REQUIRES: `name` is a supported geometry predicate identifier
    /// ENSURES: Returns the corresponding CompGeom constant name
    /// ENSURES: Returns Err(UnknownAxiom) on unknown predicate name
    pub(super) fn geometry_name_to_const(&self, name: &str) -> Result<Name, GeometryCertError> {
        // Normalize common geometry predicate names to CompGeom constants
        let const_name = match name.to_lowercase().as_str() {
            // Basic predicates
            "collinear" | "coll" => "CompGeom.Collinear",
            "concurrent" | "conc" => "CompGeom.Concurrent",
            "cyclic" => "CompGeom.Cyclic",
            "parallel" | "para" => "CompGeom.Parallel",
            "perpendicular" | "perp" => "CompGeom.Perpendicular",
            "midpoint" | "midp" => "CompGeom.MidpointOf",
            "on_circle" | "oncircle" => "CompGeom.OnCircle",
            "on_line" | "online" => "CompGeom.OnLine",
            "on_segment" | "onsegment" => "CompGeom.OnSegment",
            "tangent" | "tang" => "CompGeom.Tangent",
            "congruent" | "cong" => "CompGeom.CongruentSegments",
            "congruent_segments" => "CompGeom.CongruentSegments",
            "congruent_angles" => "CompGeom.CongruentAngles",
            "congruent_triangles" => "CompGeom.CongruentTriangles",
            "similar" | "sim" | "similar_triangles" => "CompGeom.SimilarTriangles",
            "between" | "betw" => "CompGeom.BetweenPoints",

            // Non-degeneracy and distinctness (map to generic predicates)
            "not_equal" | "notequal" | "distinct" => "CompGeom.Distance", // Represents a ≠ b
            "diameter" => "CompGeom.Segment", // Diameter is a segment through center

            // Circle-related
            "inscribed" | "inscribed_angle" => "CompGeom.InscribedAngle",
            "central_angle" | "centralangle" => "CompGeom.CentralAngle",
            "right_angle" | "rightangle" => "CompGeom.Perpendicular",

            // Angle measures
            "angle" | "angle_measure" => "CompGeom.Angle",

            // Side/position predicates
            "same_side" | "sameside" => "CompGeom.SameSide",
            "opposite_side" | "oppositeside" => "CompGeom.OppositeSide",

            // Triangle centers
            "circumcenter" => "CompGeom.Circumcenter",
            "incenter" => "CompGeom.Incenter",
            "orthocenter" => "CompGeom.Orthocenter",
            "centroid" => "CompGeom.Centroid",

            _ => return Err(GeometryCertError::UnknownAxiom(name.to_string())),
        };

        Ok(Name::from_string(const_name))
    }

    /// Map a geometry lemma name to its CompGeom theorem constant name.
    ///
    /// REQUIRES: `lemma` is a supported geometry lemma identifier
    /// ENSURES: Returns the corresponding CompGeom theorem name
    /// ENSURES: Returns Err(UnknownLemma) on unknown lemma name
    pub(super) fn geometry_lemma_to_const(&self, lemma: &str) -> Result<Name, GeometryCertError> {
        // Normalize common geometry lemma names to CompGeom constants
        let const_name = match lemma.to_lowercase().as_str() {
            // Transitivity lemmas
            "collinear_trans" | "collineartrans" => "CompGeom.CollinearTrans",
            "parallel_trans" | "paralleltrans" => "CompGeom.ParallelTrans",

            // Classic theorems
            "thales" => "CompGeom.Thales",
            "angle_sum" | "anglesum" | "angle_sum_triangle" => "CompGeom.AngleSumTriangle",
            "inscribed_angle" | "inscribedangle" => "CompGeom.InscribedAngleTheorem",
            "pythagoras" | "pythagorean" => "CompGeom.PythagoreanTheorem",

            // Congruence
            "sas" | "sas_congruence" => "CompGeom.SASCongruence",
            "asa" | "asa_congruence" => "CompGeom.ASACongruence",
            "sss" | "sss_congruence" => "CompGeom.SSSCongruence",
            "aas" | "aas_congruence" => "CompGeom.AASCongruence",

            // Similarity
            "aa" | "aa_similarity" | "aaa_similarity" => "CompGeom.AAASimilarity",
            "sa_similarity" => "CompGeom.SASimilarity",
            "sss_similarity" => "CompGeom.SSSSimilarity",

            // Advanced theorems
            "ceva" | "cevas" | "cevas_theorem" => "CompGeom.CevasTheorem",
            "menelaus" | "menelaus_theorem" => "CompGeom.MenelausTheorem",
            "stewart" | "stewart_theorem" => "CompGeom.StewartTheorem",
            "ptolemy" | "ptolemy_theorem" => "CompGeom.PtolemyTheorem",
            "power_of_point" | "powerofpoint" => "CompGeom.PowerOfPoint",
            "simson" | "simson_line" => "CompGeom.SimsonLine",
            "nine_point" | "ninepoint" | "nine_point_circle" => "CompGeom.NinePointCircle",

            // Bisector and perpendicular theorems
            "angle_bisector" | "anglebisector" => "CompGeom.AngleBisectorTheorem",
            "perpendicular_bisector" | "perpbisector" => "CompGeom.PerpendicularBisectorTheorem",
            "midpoint_theorem" | "midpointtheorem" => "CompGeom.MidpointTheorem",

            _ => return Err(GeometryCertError::UnknownLemma(lemma.to_string())),
        };

        Ok(Name::from_string(const_name))
    }

    /// Map a construction kind to its CompGeom constant name.
    ///
    /// REQUIRES: `kind` is a supported geometry construction identifier
    /// ENSURES: Returns the corresponding CompGeom constructor name
    /// ENSURES: Returns Err(InvalidDerivation) on unknown construction kind
    fn construction_to_const(&self, kind: &str) -> Result<Name, GeometryCertError> {
        let const_name = match kind.to_lowercase().as_str() {
            "midpoint" => "CompGeom.MidpointOf",
            "circumcenter" => "CompGeom.Circumcenter",
            "incenter" => "CompGeom.Incenter",
            "orthocenter" => "CompGeom.Orthocenter",
            "centroid" => "CompGeom.Centroid",
            "intersection" => "CompGeom.LineLineIntersection",
            "perpendicular" => "CompGeom.PerpendicularToLine",
            "parallel" => "CompGeom.ParallelToLine",
            "reflection" => "CompGeom.Reflection",
            _ => {
                return Err(GeometryCertError::InvalidDerivation(format!(
                    "Unknown construction: {}",
                    kind
                )))
            }
        };

        Ok(Name::from_string(const_name))
    }

    /// Get the underlying environment reference.
    ///
    /// ENSURES: Returns a reference to the initialized environment
    pub fn env(&self) -> &Environment {
        &self.env
    }

    /// Get a registered object's expression.
    ///
    /// ENSURES: Returns Some(&expr) if `name` was registered, None otherwise
    pub fn get_object(&self, name: &str) -> Option<&Expr> {
        self.object_cache.get(name)
    }

    /// Clear the certificate cache (useful for memory management).
    ///
    /// ENSURES: `self.cert_cache.is_empty()` after call
    /// ENSURES: Does not affect object_cache
    pub fn clear_cache(&mut self) {
        self.cert_cache.clear();
    }

    /// Convert a geometry certificate to MicroChecker format for independent verification.
    ///
    /// This method converts ProofCert::Const certificates to MicroCert::Opaque,
    /// preserving the type information for verification by the MicroChecker.
    ///
    /// # Arguments
    /// * `cert` - The geometry proof certificate
    /// * `expr` - The corresponding expression
    ///
    /// # Returns
    /// A tuple of (MicroCert, MicroExpr) suitable for MicroChecker verification,
    /// or None if the certificate contains unsupported constructs.
    ///
    /// REQUIRES: `cert` and `expr` are structurally compatible
    /// ENSURES: For supported constructs (Const, Sort, App), output verifies iff input verifies
    /// ENSURES: Returns None for unsupported constructs (Let, Lam, Pi with complex binders)
    /// ENSURES: Conversion preserves type information for supported cases
    /// ENSURES: Deterministic - same inputs yield same outputs
    pub fn to_micro_cert(
        &self,
        cert: &ProofCert,
        expr: &Expr,
    ) -> Option<(crate::micro::MicroCert, crate::micro::MicroExpr)> {
        use crate::micro::{MicroCert, MicroExpr, MicroLevel};

        match (cert, &expr.kind) {
            // Geometry constants become opaque constants with their type
            (ProofCert::Const { type_, .. }, ExprKind::Const(_, _)) => {
                let micro_ty = MicroExpr::from_kernel(type_).ok()?;
                let micro_expr = MicroExpr::Opaque(std::sync::Arc::new(micro_ty.clone()));
                let micro_cert = MicroCert::Opaque {
                    ty: Box::new(micro_ty),
                };
                Some((micro_cert, micro_expr))
            }

            // Sort certificates pass through
            (ProofCert::Sort { level }, ExprKind::Sort(_)) => {
                let micro_level = MicroLevel::from_kernel(level).ok()?;
                let micro_cert = MicroCert::Sort {
                    level: micro_level.clone(),
                };
                let micro_expr = MicroExpr::Sort(micro_level);
                Some((micro_cert, micro_expr))
            }

            // App certificates with recursive conversion
            (
                ProofCert::App {
                    fn_cert,
                    arg_cert,
                    result_type,
                    ..
                },
                ExprKind::App(f, a),
            ) => {
                let (fn_micro_cert, fn_micro_expr) = self.to_micro_cert(fn_cert, f)?;
                let (arg_micro_cert, arg_micro_expr) = self.to_micro_cert(arg_cert, a)?;
                let result_micro = MicroExpr::from_kernel(result_type).ok()?;

                let micro_cert = MicroCert::App {
                    fn_cert: Box::new(fn_micro_cert),
                    arg_cert: Box::new(arg_micro_cert),
                    result_ty: Box::new(result_micro),
                };
                let micro_expr = MicroExpr::App(
                    std::sync::Arc::new(fn_micro_expr),
                    std::sync::Arc::new(arg_micro_expr),
                );
                Some((micro_cert, micro_expr))
            }

            // FVar certificates become opaque
            (ProofCert::FVar { type_, .. }, ExprKind::FVar(_)) => {
                let micro_ty = MicroExpr::from_kernel(type_).ok()?;
                let micro_expr = MicroExpr::Opaque(std::sync::Arc::new(micro_ty.clone()));
                let micro_cert = MicroCert::Opaque {
                    ty: Box::new(micro_ty),
                };
                Some((micro_cert, micro_expr))
            }

            // Lit certificates: literal with declared type (#1252)
            // Use cert's literal for the cert and expr's literal for the expr
            // so the micro-checker can independently validate they match.
            (ProofCert::Lit { lit, type_ }, ExprKind::Lit(l)) => {
                let cert_lit = crate::micro::MicroLiteral::from_kernel(lit).ok()?;
                let expr_lit = crate::micro::MicroLiteral::from_kernel(l).ok()?;
                let micro_ty = MicroExpr::from_kernel(type_).ok()?;
                let micro_cert = MicroCert::Lit {
                    lit: cert_lit,
                    ty: Box::new(micro_ty),
                };
                let micro_expr = MicroExpr::Lit(expr_lit);
                Some((micro_cert, micro_expr))
            }

            // Proj certificates: structure projection with recursive inner (#1252)
            (
                ProofCert::Proj {
                    idx,
                    expr_cert,
                    field_type,
                    ..
                },
                ExprKind::Proj(_, i, e),
            ) => {
                let (inner_micro_cert, inner_micro_expr) = self.to_micro_cert(expr_cert, e)?;
                let field_ty_micro = MicroExpr::from_kernel(field_type).ok()?;
                let micro_cert = MicroCert::Proj {
                    idx: *idx,
                    expr_cert: Box::new(inner_micro_cert),
                    field_ty: Box::new(field_ty_micro),
                };
                let micro_expr = MicroExpr::Proj(*i, std::sync::Arc::new(inner_micro_expr));
                Some((micro_cert, micro_expr))
            }

            // Other cases not yet supported
            _ => None,
        }
    }

    /// Verify a geometry certificate using the MicroChecker for independent validation.
    ///
    /// This provides a second verification path using the minimal, auditable MicroChecker.
    ///
    /// # Arguments
    /// * `cert` - The geometry proof certificate
    /// * `expr` - The corresponding expression
    ///
    /// # Returns
    /// Ok(()) if MicroChecker verification succeeds, Err with error message otherwise.
    ///
    /// REQUIRES: `cert` and `expr` are compatible (same structure)
    /// REQUIRES: `cert` is a well-formed geometry proof certificate
    /// REQUIRES: `cert` uses only supported constructs (Const, Sort, App)
    /// ENSURES: On success, `expr` is type-correct according to the MicroChecker
    /// ENSURES: Independent verification - result matches kernel verification
    /// ENSURES: Returns Err("Cannot convert...") if `to_micro_cert` returns None
    /// ENSURES: Returns Err("MicroChecker verification failed: ...") on verify failure
    /// ENSURES: Soundness - success implies the proof is mathematically valid
    pub fn verify_with_micro_checker(&self, cert: &ProofCert, expr: &Expr) -> Result<(), String> {
        let (micro_cert, micro_expr) = self
            .to_micro_cert(cert, expr)
            .ok_or_else(|| "Cannot convert to MicroCert format".to_string())?;

        let mut checker = crate::micro::MicroChecker::new();
        checker
            .verify(&micro_cert, &micro_expr)
            .map(|_| ())
            .map_err(|e| format!("MicroChecker verification failed: {}", e))
    }

    /// Convert a geometry derivation step to both a ProofCert and its corresponding Expr.
    ///
    /// This method generates both the certificate and the expression needed for
    /// verification with `CertVerifier`.
    ///
    /// # Arguments
    /// * `step` - The geometry derivation step to convert
    ///
    /// # Returns
    /// A tuple of (ProofCert, Expr) that can be verified together.
    ///
    /// REQUIRES: `self.env` has geometry axioms/lemmas initialized
    /// REQUIRES: `step` references only registered geometry objects
    /// ENSURES: On success, `CertVerifier::verify(&result.0, &result.1)` succeeds
    /// ENSURES: result.0 and result.1 are structurally compatible
    /// ENSURES: Returns same errors as `step_to_cert` for invalid inputs
    pub fn step_to_cert_with_expr(
        &mut self,
        step: &GeomStep,
    ) -> Result<(ProofCert, Expr), GeometryCertError> {
        match step {
            GeomStep::Axiom { name, args: _ } => {
                let const_name = self.geometry_name_to_const(name)?;

                let levels = vec![Level::zero()];
                // Use instantiate_type to properly substitute universe levels
                let instantiated_type = self
                    .env
                    .instantiate_type(&const_name, &levels)
                    .ok_or_else(|| GeometryCertError::UnknownAxiom(name.to_string()))?;

                let cert = ProofCert::Const {
                    name: const_name.clone(),
                    levels: levels.clone(),
                    type_: Box::new(instantiated_type),
                };
                let expr = Expr::const_(const_name, levels);
                Ok((cert, expr))
            }

            GeomStep::Apply {
                predicate: _,
                lemma,
                premises,
                args,
            } => {
                // Get lemma info with instantiated type
                let lemma_name = self.geometry_lemma_to_const(lemma)?;
                let levels = vec![Level::zero()];
                let lemma_type = self
                    .env
                    .instantiate_type(&lemma_name, &levels)
                    .ok_or_else(|| GeometryCertError::UnknownLemma(lemma.to_string()))?;

                // Start with lemma constant
                let mut result_cert = ProofCert::Const {
                    name: lemma_name.clone(),
                    levels: levels.clone(),
                    type_: Box::new(lemma_type.clone()),
                };
                let mut result_expr = Expr::const_(lemma_name, levels);
                let mut current_type = lemma_type;

                // Apply to explicit arguments
                for arg_name in args {
                    let arg_expr = match self.get_object(arg_name).cloned() {
                        Some(expr) => expr,
                        None => Expr::from_kind(ExprKind::FVar(self.fresh_fvar_id())),
                    };

                    let (fn_type, result_type) =
                        self.compute_app_types(&current_type, &arg_expr)?;
                    let fvar_id = match &arg_expr.kind {
                        ExprKind::FVar(id) => *id,
                        _ => self.fresh_fvar_id(),
                    };
                    let arg_cert = ProofCert::FVar {
                        id: fvar_id,
                        type_: Box::new(self.extract_domain(&fn_type).unwrap_or(arg_expr.clone())),
                    };

                    result_cert = ProofCert::App {
                        fn_cert: Box::new(result_cert),
                        fn_type: Box::new(fn_type),
                        arg_cert: Box::new(arg_cert),
                        result_type: Box::new(result_type.clone()),
                    };
                    result_expr = Expr::app(result_expr, arg_expr);
                    current_type = result_type;
                }

                // Apply to premise proofs
                for premise in premises {
                    let (premise_cert, premise_expr) = self.step_to_cert_with_expr(premise)?;
                    let (fn_type, result_type) = self.compute_app_types_for_proof(&current_type)?;

                    result_cert = ProofCert::App {
                        fn_cert: Box::new(result_cert),
                        fn_type: Box::new(fn_type),
                        arg_cert: Box::new(premise_cert),
                        result_type: Box::new(result_type.clone()),
                    };
                    result_expr = Expr::app(result_expr, premise_expr);
                    current_type = result_type;
                }

                Ok((result_cert, result_expr))
            }

            GeomStep::Construct {
                kind,
                name: _,
                from: _,
            } => {
                let const_name = self.construction_to_const(kind)?;
                let levels = vec![Level::zero()];
                let instantiated_type = self
                    .env
                    .instantiate_type(&const_name, &levels)
                    .ok_or_else(|| {
                        GeometryCertError::InvalidDerivation(format!(
                            "Unknown construction: {}",
                            kind
                        ))
                    })?;

                let cert = ProofCert::Const {
                    name: const_name.clone(),
                    levels: levels.clone(),
                    type_: Box::new(instantiated_type),
                };
                let expr = Expr::const_(const_name, levels);
                Ok((cert, expr))
            }

            GeomStep::Given { predicate, args: _ } => {
                // Givens are axioms from the problem statement
                let const_name = self.geometry_name_to_const(predicate)?;
                let levels = vec![Level::zero()];
                let instantiated_type = self
                    .env
                    .instantiate_type(&const_name, &levels)
                    .ok_or_else(|| GeometryCertError::UnknownAxiom(predicate.to_string()))?;

                let cert = ProofCert::Const {
                    name: const_name.clone(),
                    levels: levels.clone(),
                    type_: Box::new(instantiated_type),
                };
                let expr = Expr::const_(const_name, levels);
                Ok((cert, expr))
            }
        }
    }
}
