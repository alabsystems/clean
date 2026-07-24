// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful `Rat` scalar interval primitives for the C004 carrier redesign
//! (Phase 1 of #3615).
//!
//! Registers a scalar-valued `NNVerify.Interval` structure whose fields are
//! concrete `Rat` lower/upper bounds (not identity projections over a single
//! carrier). Downstream C004 work (Phase 2 / Phase 3 per
//! `designs/2026-04-20-c004-faithful-carrier-redesign.md`) builds the
//! vector-valued LayerNorm carriers on top of these scalar primitives.
//!
//! This is explicitly the *scalar* analogue of the vector-valued
//! `NNVerify.IntervalBounds d := NNVec d × NNVec d` (see `nn_verify_types.rs`).
//! Vector-valued carrier replacement is out of scope for Phase 1.
//!
//! ## Registered declarations
//!
//! | Name                               | Kind        | Body |
//! |------------------------------------|-------------|------|
//! | `NNVerify.Interval`                | Inductive   | `structure { lo hi : Rat }` |
//! | `NNVerify.Interval.mk`             | Constructor | `fun lo hi => ⟨lo, hi⟩` |
//! | `NNVerify.Interval.lo`             | Definition  | proj 0 (first field) |
//! | `NNVerify.Interval.hi`             | Definition  | proj 1 (second field) |
//! | `NNVerify.Interval.width`          | Definition  | `fun I => Rat.sub I.hi I.lo` |
//! | `NNVerify.Interval.contains`       | Definition  | `fun I x => And (I.lo ≤ x) (x ≤ I.hi)` |
//! | `NNVerify.Interval.add`            | Definition  | `fun I J => mk (I.lo + J.lo) (I.hi + J.hi)` |
//! | `NNVerify.Interval.scalar_mul_pos` | Definition  | `fun s I => mk (s * I.lo) (s * I.hi)` |
//! | `NNVerify.Interval.scalar_mul_neg` | Definition  | `fun s I => mk (s * I.hi) (s * I.lo)` |
//! | `NNVerify.Interval.scalar_mul`     | Definition  | `fun s I => mk (Rat.min (s*I.lo) (s*I.hi)) (Rat.max ...)` |
//!
//! All definitions are `is_reducible = true` so downstream proofs can discharge
//! endpoint equalities via δ-reduction + `Eq.refl`.
//!
//! ## Soundness
//!
//! No `add_decl_unchecked`, no `add_decl_structural`, no domain axioms. Every
//! declaration is type-checked by the kernel via `add_decl` / `add_inductive`.
//! The carrier is *structurally honest*: `Interval.mk a b` has actual fields
//! `lo = a`, `hi = b`, and `width (mk a b) = b - a` by definitional δ-reduction
//! — not by aliasing over a single witness.
//!
//! Part of #3615 (C004 Phase 1). Blocks: carrier replacement in
//! `nn_verify_crown_layernorm.rs` (Phase 2, tracked under #3615 follow-ups).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across the Interval primitive registrations.
struct IConsts {
    rat: Expr,
    type0: Expr,
    prop: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    and: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_mul: Expr,
    rat_min: Expr,
    rat_max: Expr,
    interval: Expr,
    interval_mk: Expr,
}

impl IConsts {
    fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_min: Expr::const_(Name::from_string("Rat.min"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            interval: Expr::const_(Name::from_string("NNVerify.Interval"), vec![]),
            interval_mk: Expr::const_(Name::from_string("NNVerify.Interval.mk"), vec![]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), lhs, rhs],
        )
    }

    fn rat_add_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    fn rat_sub_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }

    fn rat_mul_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    fn rat_min_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_min.clone(), [a, b])
    }

    fn rat_max_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [a, b])
    }

    /// `NNVerify.Interval.mk lo hi`.
    fn mk_app(&self, lo: Expr, hi: Expr) -> Expr {
        Expr::apps(self.interval_mk.clone(), [lo, hi])
    }

    /// Projection `I.lo` (field index 0).
    fn lo_proj(i: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.Interval"), 0, i.clone())
    }

    /// Projection `I.hi` (field index 1).
    fn hi_proj(i: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.Interval"), 1, i.clone())
    }
}

impl Environment {
    /// Initialize faithful `Rat` scalar interval primitives (Phase 1 of #3615).
    ///
    /// Depends on: `init_rat()`, `init_rat_ord()`, `init_and()`, `init_rat_arith()`,
    ///             `init_rat_minmax()` (for `scalar_mul`).
    ///
    /// Idempotent: safe to call multiple times.
    pub fn init_nn_verify_interval_primitives(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_interval_primitives_init {
            return Ok(());
        }
        // Upstream dependencies: Rat + ordering + And + arithmetic + min/max.
        self.init_rat()?;
        self.init_rat_ord()?;
        self.init_and()?;
        self.init_rat_arith()?;
        self.init_rat_minmax()?;

        let c = IConsts::new();
        self.register_interval_prim_structure(&c)?;
        self.register_interval_prim_lo(&c)?;
        self.register_interval_prim_hi(&c)?;
        self.register_interval_prim_width(&c)?;
        self.register_interval_prim_contains(&c)?;
        self.register_interval_prim_add(&c)?;
        self.register_interval_prim_scalar_mul_pos(&c)?;
        self.register_interval_prim_scalar_mul_neg(&c)?;
        self.register_interval_prim_scalar_mul(&c)?;

        self.nn_verify_interval_primitives_init = true;
        Ok(())
    }

    /// `structure NNVerify.Interval where lo : Rat; hi : Rat`
    ///
    /// Registered as a single-constructor inductive with two `Rat` fields.
    /// No parameters (unlike `IntervalBounds d` which is `Nat`-indexed).
    fn register_interval_prim_structure(&mut self, c: &IConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Interval"))
            .is_some()
        {
            return Ok(());
        }
        // Type: Type 0.
        let interval_type = c.type0.clone();
        // Constructor: Rat → Rat → NNVerify.Interval
        let mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (lo_id, _) = b.fresh_local(c.rat.clone());
            let (hi_id, _) = b.fresh_local(c.rat.clone());
            let r = b.mk_pi(
                hi_id,
                BinderInfo::Default,
                c.rat.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(lo_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("NNVerify.Interval"),
                type_: interval_type,
                constructors: vec![Constructor {
                    name: Name::from_string("NNVerify.Interval.mk"),
                    type_: mk_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string("NNVerify.Interval"),
            vec![Name::from_string("lo"), Name::from_string("hi")],
        )
    }

    /// `NNVerify.Interval.lo (I : Interval) : Rat := I.1`
    ///
    /// Registered explicitly (in addition to the structure projection) so that
    /// downstream code may refer to `Interval.lo` as a named function.
    fn register_interval_prim_lo(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.lo");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), c.rat.clone());
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let body = IConsts::lo_proj(&i);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.hi (I : Interval) : Rat := I.2`
    fn register_interval_prim_hi(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.hi");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), c.rat.clone());
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let body = IConsts::hi_proj(&i);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.width (I : Interval) : Rat := Rat.sub I.hi I.lo`
    fn register_interval_prim_width(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.width");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), c.rat.clone());
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let body = c.rat_sub_app(IConsts::hi_proj(&i), IConsts::lo_proj(&i));
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.contains (I : Interval) (x : Rat) : Prop`
    /// `  := And (I.lo ≤ x) (x ≤ I.hi)`
    fn register_interval_prim_contains(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.contains");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let (x_id, _) = b.fresh_local(c.rat.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let lo_le_x = c.rat_le(IConsts::lo_proj(&i), x.clone());
            let x_le_hi = c.rat_le(x.clone(), IConsts::hi_proj(&i));
            let body = Expr::apps(c.and.clone(), [lo_le_x, x_le_hi]);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.add (I J : Interval) : Interval`
    /// `  := Interval.mk (Rat.add I.lo J.lo) (Rat.add I.hi J.hi)`
    fn register_interval_prim_add(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let (j_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                j_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let lo = c.rat_add_app(IConsts::lo_proj(&i), IConsts::lo_proj(&j));
            let hi = c.rat_add_app(IConsts::hi_proj(&i), IConsts::hi_proj(&j));
            let body = c.mk_app(lo, hi);
            let e = b.mk_lam(j_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.scalar_mul_pos (s : Rat) (I : Interval) : Interval`
    /// `  := Interval.mk (Rat.mul s I.lo) (Rat.mul s I.hi)`
    ///
    /// Faithful only when `0 ≤ s`. For arbitrary `s` see `scalar_mul`.
    fn register_interval_prim_scalar_mul_pos(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.scalar_mul_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.rat.clone());
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                i_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let lo = c.rat_mul_app(s.clone(), IConsts::lo_proj(&i));
            let hi = c.rat_mul_app(s.clone(), IConsts::hi_proj(&i));
            let body = c.mk_app(lo, hi);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.scalar_mul_neg (s : Rat) (I : Interval) : Interval`
    /// `  := Interval.mk (Rat.mul s I.hi) (Rat.mul s I.lo)`
    ///
    /// Faithful only when `s ≤ 0` (endpoints swap under sign flip).
    /// For arbitrary `s` see `scalar_mul`.
    fn register_interval_prim_scalar_mul_neg(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.scalar_mul_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.rat.clone());
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                i_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let lo = c.rat_mul_app(s.clone(), IConsts::hi_proj(&i));
            let hi = c.rat_mul_app(s.clone(), IConsts::lo_proj(&i));
            let body = c.mk_app(lo, hi);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Interval.scalar_mul (s : Rat) (I : Interval) : Interval`
    /// `  := Interval.mk (min (s*I.lo) (s*I.hi)) (max (s*I.lo) (s*I.hi))`
    ///
    /// Sound for any `Rat` scalar (positive, zero, or negative) via the
    /// pointwise min/max of endpoint products. When `0 ≤ s` this reduces to
    /// `scalar_mul_pos`; when `s ≤ 0` to `scalar_mul_neg`. Proofs of those
    /// collapses belong in later slices (not Phase 1).
    fn register_interval_prim_scalar_mul(&mut self, c: &IConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Interval.scalar_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.rat.clone());
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                i_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let s_lo = c.rat_mul_app(s.clone(), IConsts::lo_proj(&i));
            let s_hi = c.rat_mul_app(s.clone(), IConsts::hi_proj(&i));
            let lo = c.rat_min_app(s_lo.clone(), s_hi.clone());
            let hi = c.rat_max_app(s_lo, s_hi);
            let body = c.mk_app(lo, hi);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
