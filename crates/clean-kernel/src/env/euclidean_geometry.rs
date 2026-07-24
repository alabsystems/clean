// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Euclidean Geometry module for Environment
//!
//! Mathlib-compatible analytic geometry stubs:
//! - PiLp (Lp product space)
//! - EuclideanSpace (L2 product space over finite type)
//! - InnerProductSpace (typeclass for inner product)
//! - inner (inner product operation)
//! - angle (vector and affine three-point angle)
//!
//! Purpose: Enable MATP-BENCH geometry problems to elaborate.
//! This is DISTINCT from CompGeom.* which is for synthetic geometry proofs.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Euclidean Geometry module
    ///
    /// Adds Mathlib-compatible analytic geometry types:
    /// - PiLp : Lp product space
    /// - EuclideanSpace : L2 product space (EuclideanSpace 𝕜 n = PiLp 2 (fun _ : n => 𝕜))
    /// - InnerProductSpace : typeclass for inner product structure
    /// - inner : inner product operation
    ///
    /// These are needed for MATP-BENCH geometry problems.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.euclidean_geometry_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_euclidean_geometry(&mut self) -> Result<(), EnvError> {
        if self.euclidean_geometry_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin()?;
        self.init_real_complex_analysis()?;
        self.init_set()?; // Needed for Set in geometry (MATP-BENCH Q9)

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));

        // max u v
        let max_uv = Level::max(u_level.clone(), v_level.clone());
        let type_max_uv = Expr::sort(Level::succ(max_uv));

        // ================================================================
        // ENNReal (extended non-negative reals) - stub for PiLp first param
        // ================================================================
        // ENNReal : Type
        let ennreal_type = Expr::sort(Level::succ(Level::zero()));
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ENNReal"),
            level_params: vec![],
            type_: ennreal_type,
        })?;

        let ennreal_const = Expr::const_(Name::from_string("ENNReal"), vec![]);

        // ENNReal.ofNat : Nat -> ENNReal (for literal 2)
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let ennreal_of_nat_type = Expr::pi(BinderInfo::Default, nat_const, ennreal_const.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ENNReal.ofNat"),
            level_params: vec![],
            type_: ennreal_of_nat_type,
        })?;

        // ================================================================
        // PiLp : ENNReal -> (ι -> Type u) -> Type u
        // ================================================================
        // PiLp takes an Lp exponent and a family of types, returns their product with Lp norm
        // Simplified: PiLp p f where f : ι → Type u
        let pilp_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(ennreal_const.clone());
            let (iota_id, iota) = b.fresh_local(type_v.clone());
            let f_ty = Expr::pi(BinderInfo::Default, iota.clone(), type_u.clone());
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, type_u.clone());
            let r = b.mk_pi(iota_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, ennreal_const.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("PiLp"),
            level_params: vec![u.clone(), v.clone()],
            type_: pilp_type,
        })?;

        // ================================================================
        // EuclideanSpace : Type u -> Type v -> Type (max u v)
        // ================================================================
        // EuclideanSpace 𝕜 n = PiLp 2 (fun _ : n => 𝕜)
        // This is an abbreviation but we stub it as an axiom for simplicity
        let euclidean_space_type = Expr::pi(
            BinderInfo::Default, // 𝕜 : Type u (explicit, per Mathlib)
            type_u.clone(),
            Expr::pi(
                BinderInfo::Default, // n : Type v (explicit, per Mathlib)
                type_v.clone(),
                type_max_uv.clone(), // EuclideanSpace 𝕜 n : Type (max u v)
            ),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("EuclideanSpace"),
            level_params: vec![u.clone(), v.clone()],
            type_: euclidean_space_type,
        })?;

        // ================================================================
        // InnerProductSpace : Type u -> Type v -> Type (max u v)
        // ================================================================
        // InnerProductSpace 𝕜 E is a typeclass.
        // The type parameters are EXPLICIT because when we write [InnerProductSpace ℝ P],
        // both ℝ and P are explicitly provided, not inferred.
        let inner_product_space_type = Expr::pi(
            BinderInfo::Default, // 𝕜 : Type u (explicit)
            type_u.clone(),
            Expr::pi(
                BinderInfo::Default, // E : Type v (explicit)
                type_v.clone(),
                type_max_uv.clone(), // InnerProductSpace 𝕜 E : Type (max u v)
            ),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InnerProductSpace"),
            level_params: vec![u.clone(), v.clone()],
            type_: inner_product_space_type,
        })?;

        // ================================================================
        // inner : {𝕜 E : Type*} -> [InnerProductSpace 𝕜 E] -> E -> E -> 𝕜
        // ================================================================
        // The inner product operation ⟪x, y⟫
        let inner_type = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(type_u.clone()); // 𝕜 : Type u
            let (e_id, e) = b.fresh_local(type_v.clone()); // E : Type v
            let inst_ty = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("InnerProductSpace"),
                        vec![u_level.clone(), v_level.clone()],
                    ),
                    k.clone(),
                ),
                e.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(inst_ty.clone());
            let (x_id, _x) = b.fresh_local(e.clone()); // x : E
            let (y_id, _y) = b.fresh_local(e.clone()); // y : E
            let r = b.mk_pi(y_id, BinderInfo::Default, e.clone(), k.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, e.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(e_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("inner"),
            level_params: vec![u.clone(), v.clone()],
            type_: inner_type,
        })?;

        // ================================================================
        // instInnerProductSpaceEuclideanSpace : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n))
        // ================================================================
        // Instance that EuclideanSpace has inner product structure
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let fin_const = Expr::const_(Name::from_string("Fin"), vec![]);

        // For any n : Nat, we have InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n))
        // Real : Type 0, Fin n : Type 0, so universe levels are {0, 0}
        let instance_type = {
            let mut b = EnvDeclBuilder::new();
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n : Nat
            let body = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("InnerProductSpace"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    real_const.clone(),
                ),
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("EuclideanSpace"),
                            vec![Level::zero(), Level::zero()],
                        ),
                        real_const.clone(),
                    ),
                    Expr::app(fin_const.clone(), n),
                ),
            );
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const, body);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instInnerProductSpaceEuclideanSpace"),
            level_params: vec![],
            type_: instance_type,
        })?;

        // ================================================================
        // NormedAddCommGroup : Type u -> Type u
        // ================================================================
        // Another typeclass commonly used with EuclideanSpace.
        // The type parameter is EXPLICIT because when we write [NormedAddCommGroup P],
        // the P is explicitly provided, not inferred.
        let normed_add_comm_group_type = Expr::pi(
            BinderInfo::Default, // E : Type u (explicit, not implicit)
            type_u.clone(),
            type_u.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NormedAddCommGroup"),
            level_params: vec![u.clone()],
            type_: normed_add_comm_group_type,
        })?;

        // ================================================================
        // norm : {E : Type u} -> [NormedAddCommGroup E] -> E -> ℝ
        // ================================================================
        let norm_type = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(type_u.clone()); // E : Type u
            let inst_ty = Expr::app(
                Expr::const_(
                    Name::from_string("NormedAddCommGroup"),
                    vec![u_level.clone()],
                ),
                e.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(inst_ty.clone());
            let (x_id, _x) = b.fresh_local(e.clone()); // x : E
            let r = b.mk_pi(x_id, BinderInfo::Default, e.clone(), real_const.clone());
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("norm"),
            level_params: vec![u.clone()],
            type_: norm_type,
        })?;

        // ================================================================
        // dist : {α : Type u} -> [MetricSpace α] -> α -> α -> ℝ (already may exist)
        // ================================================================
        // Check if dist already exists, if not add it
        if self.get_const(&Name::from_string("dist")).is_none() {
            let dist_type = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(type_u.clone()); // α : Type u
                let inst_ty = Expr::app(
                    Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                    a.clone(),
                );
                let (inst_id, _inst) = b.fresh_local(inst_ty.clone());
                let (x_id, _x) = b.fresh_local(a.clone()); // x : α
                let (y_id, _y) = b.fresh_local(a.clone()); // y : α
                let r = b.mk_pi(y_id, BinderInfo::Default, a.clone(), real_const.clone());
                let r = b.mk_pi(x_id, BinderInfo::Default, a.clone(), r);
                let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
                let r = b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("dist"),
                level_params: vec![u.clone()],
                type_: dist_type,
            })?;
        }

        // ================================================================
        // EuclideanGeometry.Sphere : {P : Type u} -> Type u
        // ================================================================
        // Sphere in Euclidean space (structure with center : P and radius : ℝ)
        // Used in MATP-BENCH Q500 and other geometry problems
        let sphere_type = Expr::pi(
            BinderInfo::Implicit, // P : Type u
            type_u.clone(),
            type_u.clone(), // Sphere P : Type u
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("EuclideanGeometry.Sphere"),
            level_params: vec![u.clone()],
            type_: sphere_type,
        })?;

        // ================================================================
        // EuclideanGeometry.Sphere.center : {P : Type u} -> Sphere P -> P
        // ================================================================
        let sphere_center_type = {
            let mut b = EnvDeclBuilder::new();
            let sphere_const = Expr::const_(
                Name::from_string("EuclideanGeometry.Sphere"),
                vec![u_level.clone()],
            );
            let (p_id, p) = b.fresh_local(type_u.clone()); // P : Type u
            let (s_id, _s) = b.fresh_local(Expr::app(sphere_const.clone(), p.clone())); // s : Sphere P
            let r = b.mk_pi(
                s_id,
                BinderInfo::Default,
                Expr::app(sphere_const.clone(), p.clone()),
                p.clone(),
            );
            let r = b.mk_pi(p_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("EuclideanGeometry.Sphere.center"),
            level_params: vec![u.clone()],
            type_: sphere_center_type,
        })?;

        // ================================================================
        // EuclideanGeometry.Sphere.radius : {P : Type u} -> Sphere P -> ℝ
        // ================================================================
        let sphere_radius_type = {
            let mut b = EnvDeclBuilder::new();
            let sphere_const = Expr::const_(
                Name::from_string("EuclideanGeometry.Sphere"),
                vec![u_level.clone()],
            );
            let (p_id, p) = b.fresh_local(type_u.clone()); // P : Type u
            let (s_id, _s) = b.fresh_local(Expr::app(sphere_const.clone(), p.clone())); // s : Sphere P
            let r = b.mk_pi(
                s_id,
                BinderInfo::Default,
                Expr::app(sphere_const, p.clone()),
                real_const.clone(),
            );
            let r = b.mk_pi(p_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("EuclideanGeometry.Sphere.radius"),
            level_params: vec![u.clone()],
            type_: sphere_radius_type,
        })?;

        // ================================================================
        // Collinear : (k : Type u) → {P : Type v} → Set P → Prop
        // ================================================================
        // Points that lie on a common line (affine subspace of dimension 1)
        // Mathlib: def Collinear (k : Type*) [DivisionRing k] (s : Set P) : Prop
        if self.get_const(&Name::from_string("Collinear")).is_none() {
            let collinear_type = {
                let mut b = EnvDeclBuilder::new();
                let set_const_v = Expr::const_(Name::from_string("Set"), vec![v_level.clone()]);
                let (k_id, _k) = b.fresh_local(type_u.clone()); // k : Type u
                let (p_id, p) = b.fresh_local(type_v.clone()); // P : Type v
                let (s_id, _s) = b.fresh_local(Expr::app(set_const_v.clone(), p.clone())); // s : Set P
                let r = b.mk_pi(
                    s_id,
                    BinderInfo::Default,
                    Expr::app(set_const_v, p),
                    Expr::sort(Level::zero()),
                );
                let r = b.mk_pi(p_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_pi(k_id, BinderInfo::Default, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Collinear"),
                level_params: vec![u.clone(), v.clone()],
                type_: collinear_type,
            })?;
        }

        // ================================================================
        // Concyclic : {P : Type u} -> Set P -> Prop
        // ================================================================
        // Points that lie on a common circle
        if self.get_const(&Name::from_string("Concyclic")).is_none() {
            let concyclic_type = {
                let mut b = EnvDeclBuilder::new();
                let set_const = Expr::const_(Name::from_string("Set"), vec![u_level.clone()]);
                let (p_id, p) = b.fresh_local(type_u.clone()); // P : Type u
                let (s_id, _s) = b.fresh_local(Expr::app(set_const.clone(), p.clone())); // s : Set P
                let r = b.mk_pi(
                    s_id,
                    BinderInfo::Default,
                    Expr::app(set_const, p),
                    Expr::sort(Level::zero()),
                );
                let r = b.mk_pi(p_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Concyclic"),
                level_params: vec![u.clone()],
                type_: concyclic_type,
            })?;
        }

        self.euclidean_geometry_init = true;
        Ok(())
    }

    /// Initialize Euclidean angle functions
    ///
    /// Adds angle computation functions:
    /// - InnerProductGeometry.angle : vector angle via inner product
    /// - EuclideanGeometry.angle : three-point affine angle
    /// - Real.arccos : arc cosine function
    /// - Real.pi : pi constant
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.euclidean_angle_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_euclidean_angle(&mut self) -> Result<(), EnvError> {
        if self.euclidean_angle_init {
            return Ok(());
        }

        // Dependencies
        self.init_euclidean_geometry()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);

        // ================================================================
        // Real.pi : ℝ
        // ================================================================
        if self.get_const(&Name::from_string("Real.pi")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Real.pi"),
                level_params: vec![],
                type_: real_const.clone(),
            })?;
        }

        // ================================================================
        // Real.arccos : ℝ -> ℝ
        // ================================================================
        if self.get_const(&Name::from_string("Real.arccos")).is_none() {
            let arccos_type = Expr::pi(BinderInfo::Default, real_const.clone(), real_const.clone());
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Real.arccos"),
                level_params: vec![],
                type_: arccos_type,
            })?;
        }

        // ================================================================
        // InnerProductGeometry.angle : {V : Type u} -> [InnerProductSpace ℝ V] -> V -> V -> ℝ
        // ================================================================
        // Vector angle: angle x y = arccos(⟪x, y⟫ / (‖x‖ * ‖y‖))
        // InnerProductSpace.{k, v} takes 𝕜 : Type k; Real : Type 0, so k = 0
        let inner_product_angle_type = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(type_u.clone()); // V : Type u
            let inst_ty = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("InnerProductSpace"),
                        vec![Level::zero(), u_level.clone()],
                    ),
                    real_const.clone(),
                ),
                v.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(inst_ty.clone());
            let (x_id, _x) = b.fresh_local(v.clone()); // x : V
            let (y_id, _y) = b.fresh_local(v.clone()); // y : V
            let r = b.mk_pi(y_id, BinderInfo::Default, v.clone(), real_const.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, v.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(v_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InnerProductGeometry.angle"),
            level_params: vec![u.clone()],
            type_: inner_product_angle_type,
        })?;

        // ================================================================
        // EuclideanGeometry.angle : {P : Type u} -> P -> P -> P -> ℝ
        // ================================================================
        // Three-point angle: angle p₁ p₂ p₃ = angle between vectors (p₁ - p₂) and (p₃ - p₂)
        // Simplified signature without full affine space structure
        let euclidean_angle_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(type_u.clone()); // P : Type u
            let (p1_id, _p1) = b.fresh_local(p.clone()); // p₁ : P
            let (p2_id, _p2) = b.fresh_local(p.clone()); // p₂ : P (vertex)
            let (p3_id, _p3) = b.fresh_local(p.clone()); // p₃ : P
            let r = b.mk_pi(p3_id, BinderInfo::Default, p.clone(), real_const.clone());
            let r = b.mk_pi(p2_id, BinderInfo::Default, p.clone(), r);
            let r = b.mk_pi(p1_id, BinderInfo::Default, p.clone(), r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("EuclideanGeometry.angle"),
            level_params: vec![u.clone()],
            type_: euclidean_angle_type,
        })?;

        // ================================================================
        // angle (alias at top level) for convenience
        // ================================================================
        // Some Mathlib code uses just `angle` instead of the namespaced version
        if self.get_const(&Name::from_string("angle")).is_none() {
            let angle_alias_type = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(type_u.clone()); // P : Type u
                let (p1_id, _p1) = b.fresh_local(p.clone()); // p₁ : P
                let (p2_id, _p2) = b.fresh_local(p.clone()); // p₂ : P
                let (p3_id, _p3) = b.fresh_local(p.clone()); // p₃ : P
                let r = b.mk_pi(p3_id, BinderInfo::Default, p.clone(), real_const.clone());
                let r = b.mk_pi(p2_id, BinderInfo::Default, p.clone(), r);
                let r = b.mk_pi(p1_id, BinderInfo::Default, p.clone(), r);
                let r = b.mk_pi(p_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("angle"),
                level_params: vec![u.clone()],
                type_: angle_alias_type,
            })?;
        }

        self.euclidean_angle_init = true;
        Ok(())
    }

    /// Check if Euclidean geometry has been initialized
    pub fn is_euclidean_geometry_init(&self) -> bool {
        self.euclidean_geometry_init
    }

    /// Check if Euclidean angle functions have been initialized
    pub fn is_euclidean_angle_init(&self) -> bool {
        self.euclidean_angle_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    /// Assert that a constant exists and has the expected type.
    /// Panics with a descriptive message if the constant is missing or has wrong type.
    fn assert_const_type(env: &Environment, name: &str, expected: Expr) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("constant '{}' not found in environment", name));
        assert_eq!(
            info.type_, expected,
            "type mismatch for constant '{}'",
            name
        );
    }

    #[test]
    fn test_euclidean_geometry_init() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();
        assert!(env.euclidean_geometry_init);

        // Check ENNReal (extended non-negative reals) stubs
        let ennreal_info = env.get_const(&Name::from_string("ENNReal")).unwrap();
        assert_eq!(ennreal_info.level_params.len(), 0);
        let ennreal_of_nat_info = env.get_const(&Name::from_string("ENNReal.ofNat")).unwrap();
        assert_eq!(ennreal_of_nat_info.level_params.len(), 0);

        // Check key types exist
        let euclidean_space_info = env.get_const(&Name::from_string("EuclideanSpace")).unwrap();
        assert_eq!(euclidean_space_info.level_params.len(), 2);
        let inner_product_space_info = env
            .get_const(&Name::from_string("InnerProductSpace"))
            .unwrap();
        assert_eq!(inner_product_space_info.level_params.len(), 2);
        let pilp_info = env.get_const(&Name::from_string("PiLp")).unwrap();
        assert_eq!(pilp_info.level_params.len(), 2);
        let inner_info = env.get_const(&Name::from_string("inner")).unwrap();
        assert_eq!(inner_info.level_params.len(), 2);
        let inner_product_space_inst_info = env
            .get_const(&Name::from_string("instInnerProductSpaceEuclideanSpace"))
            .unwrap();
        assert_eq!(inner_product_space_inst_info.level_params.len(), 0);
        assert_const(&env, "norm");
        assert_const(&env, "dist");
        // Check Sphere type exists
        let sphere_info = env
            .get_const(&Name::from_string("EuclideanGeometry.Sphere"))
            .unwrap();
        assert_eq!(sphere_info.level_params.len(), 1);
        let sphere_center_info = env
            .get_const(&Name::from_string("EuclideanGeometry.Sphere.center"))
            .unwrap();
        assert_eq!(sphere_center_info.level_params.len(), 1);
        let sphere_radius_info = env
            .get_const(&Name::from_string("EuclideanGeometry.Sphere.radius"))
            .unwrap();
        assert_eq!(sphere_radius_info.level_params.len(), 1);

        // Check Concyclic exists (Phase 17d: MATP-BENCH geometry stub, Issue #589)
        assert_const(&env, "Concyclic");
    }

    #[test]
    fn test_euclidean_geometry_type_signatures() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let max_uv = Level::max(u_level.clone(), v_level.clone());
        let type_max_uv = Expr::sort(Level::succ(max_uv));

        let ennreal_const = Expr::const_(Name::from_string("ENNReal"), vec![]);
        let pilp_type = Expr::pi(
            BinderInfo::Implicit,
            ennreal_const,
            Expr::pi(
                BinderInfo::Implicit,
                type_v.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::bvar(0), type_u.clone()),
                    type_u.clone(),
                ),
            ),
        );
        assert_const_type(&env, "PiLp", pilp_type);

        let euclidean_space_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, type_v.clone(), type_max_uv.clone()),
        );
        assert_const_type(&env, "EuclideanSpace", euclidean_space_type);

        let inner_product_space_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, type_v.clone(), type_max_uv.clone()),
        );
        assert_const_type(&env, "InnerProductSpace", inner_product_space_type);

        let inner_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(
                BinderInfo::Implicit,
                type_v.clone(),
                Expr::pi(
                    BinderInfo::InstImplicit,
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("InnerProductSpace"),
                                vec![u_level.clone(), v_level.clone()],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1),
                        Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(4)),
                    ),
                ),
            ),
        );
        assert_const_type(&env, "inner", inner_type);

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let norm_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(
                BinderInfo::InstImplicit,
                Expr::app(
                    Expr::const_(
                        Name::from_string("NormedAddCommGroup"),
                        vec![u_level.clone()],
                    ),
                    Expr::bvar(0),
                ),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), real_const.clone()),
            ),
        );
        assert_const_type(&env, "norm", norm_type);

        let dist_type = Expr::pi(
            BinderInfo::Implicit,
            type_u,
            Expr::pi(
                BinderInfo::InstImplicit,
                Expr::app(
                    Expr::const_(Name::from_string("MetricSpace"), vec![u_level]),
                    Expr::bvar(0),
                ),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(BinderInfo::Default, Expr::bvar(2), real_const.clone()),
                ),
            ),
        );
        assert_const_type(&env, "dist", dist_type);
    }

    #[test]
    fn test_euclidean_geometry_collinear_concyclic_type_signatures() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));

        let set_const_v = Expr::const_(Name::from_string("Set"), vec![v_level.clone()]);
        let collinear_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(
                BinderInfo::Implicit,
                type_v.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(set_const_v, Expr::bvar(0)),
                    Expr::sort(Level::zero()),
                ),
            ),
        );
        assert_const_type(&env, "Collinear", collinear_type);

        let set_const_u = Expr::const_(Name::from_string("Set"), vec![u_level]);
        let concyclic_type = Expr::pi(
            BinderInfo::Implicit,
            type_u,
            Expr::pi(
                BinderInfo::Default,
                Expr::app(set_const_u, Expr::bvar(0)),
                Expr::sort(Level::zero()),
            ),
        );
        assert_const_type(&env, "Concyclic", concyclic_type);
    }

    #[test]
    fn test_euclidean_geometry_sphere_type_signatures() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);

        let sphere_type = Expr::pi(BinderInfo::Implicit, type_u.clone(), type_u.clone());
        assert_const_type(&env, "EuclideanGeometry.Sphere", sphere_type);

        let sphere_center_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(
                    Expr::const_(
                        Name::from_string("EuclideanGeometry.Sphere"),
                        vec![u_level.clone()],
                    ),
                    Expr::bvar(0),
                ),
                Expr::bvar(1),
            ),
        );
        assert_const_type(&env, "EuclideanGeometry.Sphere.center", sphere_center_type);

        let sphere_radius_type = Expr::pi(
            BinderInfo::Implicit,
            type_u,
            Expr::pi(
                BinderInfo::Default,
                Expr::app(
                    Expr::const_(Name::from_string("EuclideanGeometry.Sphere"), vec![u_level]),
                    Expr::bvar(0),
                ),
                real_const,
            ),
        );
        assert_const_type(&env, "EuclideanGeometry.Sphere.radius", sphere_radius_type);
    }

    #[test]
    fn test_euclidean_geometry_inner_product_instance_type() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let fin_const = Expr::const_(Name::from_string("Fin"), vec![]);
        // Real : Type 0, Fin n : Type 0, so universe levels are {0, 0}
        let instance_type = Expr::pi(
            BinderInfo::Implicit,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("InnerProductSpace"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    real_const.clone(),
                ),
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("EuclideanSpace"),
                            vec![Level::zero(), Level::zero()],
                        ),
                        real_const.clone(),
                    ),
                    Expr::app(fin_const, Expr::bvar(0)),
                ),
            ),
        );
        assert_const_type(&env, "instInnerProductSpaceEuclideanSpace", instance_type);
    }

    #[test]
    fn test_euclidean_geometry_idempotent() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();
        // Calling again should not error
        env.init_euclidean_geometry().unwrap();
        assert!(env.euclidean_geometry_init);
    }

    #[test]
    fn test_euclidean_angle_init() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();
        env.init_euclidean_angle().unwrap();
        assert!(env.euclidean_angle_init);

        // Check angle functions exist
        let euclidean_angle_info = env
            .get_const(&Name::from_string("EuclideanGeometry.angle"))
            .unwrap();
        assert_eq!(euclidean_angle_info.level_params.len(), 1);
        let inner_product_angle_info = env
            .get_const(&Name::from_string("InnerProductGeometry.angle"))
            .unwrap();
        assert_eq!(inner_product_angle_info.level_params.len(), 1);
        let angle_alias_info = env.get_const(&Name::from_string("angle")).unwrap();
        assert_eq!(angle_alias_info.level_params.len(), 1);
        assert_const(&env, "Real.arccos");
        assert_const(&env, "Real.pi");
    }

    #[test]
    fn test_euclidean_angle_idempotent() {
        let mut env = Environment::new();
        env.init_euclidean_angle().unwrap();
        env.init_euclidean_angle().unwrap();
        assert!(env.euclidean_angle_init);
        assert_const(&env, "angle");
    }

    #[test]
    fn test_euclidean_angle_type_signatures() {
        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();
        env.init_euclidean_angle().unwrap();

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);

        // InnerProductSpace.{k, v}: Real : Type 0, so k = 0
        let inner_product_angle_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(
                BinderInfo::InstImplicit,
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("InnerProductSpace"),
                            vec![Level::zero(), u_level.clone()],
                        ),
                        real_const.clone(),
                    ),
                    Expr::bvar(0),
                ),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(BinderInfo::Default, Expr::bvar(2), real_const.clone()),
                ),
            ),
        );
        assert_const_type(&env, "InnerProductGeometry.angle", inner_product_angle_type);

        let euclidean_angle_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(BinderInfo::Default, Expr::bvar(2), real_const.clone()),
                ),
            ),
        );
        assert_const_type(
            &env,
            "EuclideanGeometry.angle",
            euclidean_angle_type.clone(),
        );
        assert_const_type(&env, "angle", euclidean_angle_type);
    }

    #[test]
    fn test_euclidean_angle_requires_geometry() {
        let mut env = Environment::new();
        // init_euclidean_angle should auto-initialize geometry
        env.init_euclidean_angle().unwrap();
        assert!(env.euclidean_geometry_init);
        assert!(env.euclidean_angle_init);
        assert_const(&env, "EuclideanGeometry.angle");
        assert_const(&env, "InnerProductGeometry.angle");
        assert_const(&env, "angle");
    }

    #[test]
    fn test_euclidean_geometry_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_euclidean_geometry().unwrap();
        let tc = TypeChecker::new(&env);

        // ENNReal has 0 level params; EuclideanSpace/PiLp have 2
        for name in &["ENNReal", "EuclideanSpace", "PiLp"] {
            let n = Name::from_string(name);
            let ci = env.get_const(&n).expect(name);
            let levels: Vec<Level> = ci.level_params.iter().map(|_| Level::zero()).collect();
            let expr = Expr::const_(n, levels);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            // ENNReal is a Sort; EuclideanSpace/PiLp are Pi types returning Sorts
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
                "{name}: expected Sort or Pi type, got {ty:?}"
            );
        }
    }
}
