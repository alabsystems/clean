// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computational Geometry module for Environment
//!
//! Axiomatizes the CompGeom.* constants used by the geometry certificate
//! pipeline (`cert/geometry.rs`). Only constants with active call-site
//! references are registered; dormant stubs were pruned in #1558.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Computational Geometry module
    ///
    /// Registers the CompGeom.* axiom constants required by the
    /// `GeometryCertGenerator` in `cert/geometry.rs`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.computational_geometry_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_computational_geometry(&mut self) -> Result<(), EnvError> {
        if self.computational_geometry_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_list()?;
        self.init_set_theory()?;
        self.init_real_complex_analysis()?;
        self.init_algebra_linear()?;
        self.init_metric_space()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Only constants referenced by cert/geometry.rs are registered.
        // See #1558 for rationale (pruned ~332 unreferenced stubs).
        for name in &[
            // Geometric primitives and measurements
            "CompGeom.Segment",
            "CompGeom.Angle",
            "CompGeom.Distance",
            // Predicates
            "CompGeom.Collinear",
            "CompGeom.Concurrent",
            "CompGeom.Cyclic",
            "CompGeom.Parallel",
            "CompGeom.Perpendicular",
            "CompGeom.MidpointOf",
            "CompGeom.OnCircle",
            "CompGeom.OnLine",
            "CompGeom.OnSegment",
            "CompGeom.Tangent",
            "CompGeom.CongruentSegments",
            "CompGeom.CongruentAngles",
            "CompGeom.CongruentTriangles",
            "CompGeom.SimilarTriangles",
            "CompGeom.BetweenPoints",
            "CompGeom.InscribedAngle",
            "CompGeom.CentralAngle",
            "CompGeom.SameSide",
            "CompGeom.OppositeSide",
            // Triangle centers
            "CompGeom.Circumcenter",
            "CompGeom.Incenter",
            "CompGeom.Orthocenter",
            "CompGeom.Centroid",
            // Transitivity / basic theorems
            "CompGeom.CollinearTrans",
            "CompGeom.ParallelTrans",
            "CompGeom.Thales",
            "CompGeom.AngleSumTriangle",
            "CompGeom.InscribedAngleTheorem",
            "CompGeom.PythagoreanTheorem",
            // Congruence theorems
            "CompGeom.SASCongruence",
            "CompGeom.ASACongruence",
            "CompGeom.SSSCongruence",
            "CompGeom.AASCongruence",
            // Similarity theorems
            "CompGeom.AAASimilarity",
            "CompGeom.SASimilarity",
            "CompGeom.SSSSimilarity",
            // Advanced theorems
            "CompGeom.CevasTheorem",
            "CompGeom.MenelausTheorem",
            "CompGeom.StewartTheorem",
            "CompGeom.PtolemyTheorem",
            "CompGeom.PowerOfPoint",
            "CompGeom.SimsonLine",
            "CompGeom.NinePointCircle",
            "CompGeom.AngleBisectorTheorem",
            "CompGeom.PerpendicularBisectorTheorem",
            "CompGeom.MidpointTheorem",
            // Constructions
            "CompGeom.LineLineIntersection",
            "CompGeom.PerpendicularToLine",
            "CompGeom.ParallelToLine",
            "CompGeom.Reflection",
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.computational_geometry_init = true;
        Ok(())
    }

    /// Check if computational geometry module has been initialized.
    ///
    /// Returns true if `init_computational_geometry()` has been called successfully.
    pub fn is_computational_geometry_init(&self) -> bool {
        self.computational_geometry_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    #[test]
    fn test_computational_geometry_init() {
        let mut env = Environment::new();
        env.init_computational_geometry().unwrap();
        assert!(env.computational_geometry_init);
    }

    #[test]
    fn test_computational_geometry_idempotent() {
        let mut env = Environment::new();
        env.init_computational_geometry().unwrap();
        env.init_computational_geometry().unwrap();
        assert!(env.computational_geometry_init);
    }

    #[test]
    fn test_all_cert_constants_exist() {
        let mut env = Environment::new();
        env.init_computational_geometry().unwrap();
        // Every constant referenced by cert/geometry.rs must exist
        let expected = &[
            "CompGeom.Segment",
            "CompGeom.Angle",
            "CompGeom.Distance",
            "CompGeom.Collinear",
            "CompGeom.Concurrent",
            "CompGeom.Cyclic",
            "CompGeom.Parallel",
            "CompGeom.Perpendicular",
            "CompGeom.MidpointOf",
            "CompGeom.OnCircle",
            "CompGeom.OnLine",
            "CompGeom.OnSegment",
            "CompGeom.Tangent",
            "CompGeom.CongruentSegments",
            "CompGeom.CongruentAngles",
            "CompGeom.CongruentTriangles",
            "CompGeom.SimilarTriangles",
            "CompGeom.BetweenPoints",
            "CompGeom.InscribedAngle",
            "CompGeom.CentralAngle",
            "CompGeom.SameSide",
            "CompGeom.OppositeSide",
            "CompGeom.Circumcenter",
            "CompGeom.Incenter",
            "CompGeom.Orthocenter",
            "CompGeom.Centroid",
            "CompGeom.CollinearTrans",
            "CompGeom.ParallelTrans",
            "CompGeom.Thales",
            "CompGeom.AngleSumTriangle",
            "CompGeom.InscribedAngleTheorem",
            "CompGeom.PythagoreanTheorem",
            "CompGeom.SASCongruence",
            "CompGeom.ASACongruence",
            "CompGeom.SSSCongruence",
            "CompGeom.AASCongruence",
            "CompGeom.AAASimilarity",
            "CompGeom.SASimilarity",
            "CompGeom.SSSSimilarity",
            "CompGeom.CevasTheorem",
            "CompGeom.MenelausTheorem",
            "CompGeom.StewartTheorem",
            "CompGeom.PtolemyTheorem",
            "CompGeom.PowerOfPoint",
            "CompGeom.SimsonLine",
            "CompGeom.NinePointCircle",
            "CompGeom.AngleBisectorTheorem",
            "CompGeom.PerpendicularBisectorTheorem",
            "CompGeom.MidpointTheorem",
            "CompGeom.LineLineIntersection",
            "CompGeom.PerpendicularToLine",
            "CompGeom.ParallelToLine",
            "CompGeom.Reflection",
        ];
        for name in expected {
            assert_const(&env, name);
        }
    }

    #[test]
    fn test_pruned_constants_absent() {
        // Constants removed in #1558 should not exist
        let mut env = Environment::new();
        env.init_computational_geometry().unwrap();
        assert!(
            env.get_const(&Name::from_string("CompGeom.Point"))
                .is_none(),
            "pruned constant CompGeom.Point should not exist"
        );
        assert!(
            env.get_const(&Name::from_string("CompGeom.ConvexHull"))
                .is_none(),
            "pruned constant CompGeom.ConvexHull should not exist"
        );
        assert!(
            env.get_const(&Name::from_string("CompGeom.GJKAlgorithm"))
                .is_none(),
            "pruned constant CompGeom.GJKAlgorithm should not exist"
        );
        assert!(
            env.get_const(&Name::from_string("CompGeom.KDTree"))
                .is_none(),
            "pruned constant CompGeom.KDTree should not exist"
        );
        assert!(
            env.get_const(&Name::from_string("CompGeom.RRT")).is_none(),
            "pruned constant CompGeom.RRT should not exist"
        );
    }

    #[test]
    fn test_compgeom_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_computational_geometry().unwrap();
        let tc = TypeChecker::new(&env);

        for name in &[
            "CompGeom.Segment",
            "CompGeom.Collinear",
            "CompGeom.PythagoreanTheorem",
            "CompGeom.SASCongruence",
        ] {
            let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_)),
                "{name}: expected Sort type, got {ty:?}"
            );
        }

        // Verify universe level params on a sample constant
        let seg_info = env
            .get_const(&Name::from_string("CompGeom.Segment"))
            .expect("CompGeom.Segment");
        assert!(
            !seg_info.level_params.is_empty(),
            "CompGeom.Segment should have universe parameters"
        );
    }
}
