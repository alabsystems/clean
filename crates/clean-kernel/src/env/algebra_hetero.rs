// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Heterogeneous algebraic operations for Environment
//!
//! This module contains heterogeneous typeclass initialization functions:
//! - HAdd, HSub, HMul, HDiv, HMod, HPow typeclasses
//! - Pow typeclass
//! - Nat and Int instances for these typeclasses

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

#[derive(Clone, Copy)]
struct HeteroOpFlavor {
    class_name: &'static str,
    ctor_name: &'static str,
    field_name: &'static str,
    projection_name: &'static str,
    register_as_class: bool,
}

const HADD_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HAdd",
    ctor_name: "HAdd.mk",
    field_name: "hAdd",
    projection_name: "HAdd.hAdd",
    register_as_class: true,
};

const HSUB_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HSub",
    ctor_name: "HSub.mk",
    field_name: "hSub",
    projection_name: "HSub.hSub",
    register_as_class: true,
};

const HMUL_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HMul",
    ctor_name: "HMul.mk",
    field_name: "hMul",
    projection_name: "HMul.hMul",
    register_as_class: true,
};

const HDIV_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HDiv",
    ctor_name: "HDiv.mk",
    field_name: "hDiv",
    projection_name: "HDiv.hDiv",
    // Register as a class (like HAdd/HSub/HMul) so instance *synthesis* can
    // discover `instHDivNat`; otherwise `v / w` resolves the projection but
    // leaves the instance arg an unfilled metavariable ("contains free
    // variables"). The result type γ is the outParam. (Track TAC)
    register_as_class: true,
};

const HMOD_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HMod",
    ctor_name: "HMod.mk",
    field_name: "hMod",
    projection_name: "HMod.hMod",
    // See HDIV_FLAVOR: register as a class so `instHModNat` is discoverable by
    // synthesis for `v % w`. (Track TAC)
    register_as_class: true,
};

const HPOW_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HPow",
    ctor_name: "HPow.mk",
    field_name: "hPow",
    projection_name: "HPow.hPow",
    register_as_class: true,
};

const HAND_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HAnd",
    ctor_name: "HAnd.mk",
    field_name: "hAnd",
    projection_name: "HAnd.hAnd",
    register_as_class: true,
};

const HOR_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HOr",
    ctor_name: "HOr.mk",
    field_name: "hOr",
    projection_name: "HOr.hOr",
    register_as_class: true,
};

const HXOR_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HXor",
    ctor_name: "HXor.mk",
    field_name: "hXor",
    projection_name: "HXor.hXor",
    register_as_class: true,
};

const HSHIFTLEFT_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HShiftLeft",
    ctor_name: "HShiftLeft.mk",
    field_name: "hShiftLeft",
    projection_name: "HShiftLeft.hShiftLeft",
    register_as_class: true,
};

const HSHIFTRIGHT_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HShiftRight",
    ctor_name: "HShiftRight.mk",
    field_name: "hShiftRight",
    projection_name: "HShiftRight.hShiftRight",
    register_as_class: true,
};

const HAPPEND_FLAVOR: HeteroOpFlavor = HeteroOpFlavor {
    class_name: "HAppend",
    ctor_name: "HAppend.mk",
    field_name: "hAppend",
    projection_name: "HAppend.hAppend",
    register_as_class: true,
};

#[derive(Clone, Copy)]
struct BinaryOpFlavor {
    class_name: &'static str,
    ctor_name: &'static str,
    field_name: &'static str,
    projection_name: &'static str,
}

const DIV_FLAVOR: BinaryOpFlavor = BinaryOpFlavor {
    class_name: "Div",
    ctor_name: "Div.mk",
    field_name: "div",
    projection_name: "Div.div",
};

const MOD_FLAVOR: BinaryOpFlavor = BinaryOpFlavor {
    class_name: "Mod",
    ctor_name: "Mod.mk",
    field_name: "mod",
    projection_name: "Mod.mod",
};

/// Build the projection type and value for a 3-universe heterogeneous op class.
/// Returns `(projection_type, projection_value)`.
fn build_hetero_projection(
    class_name: &Name,
    class_const: impl Fn(Level, Level, Level) -> Expr,
    type_u: &Expr,
    type_v: &Expr,
    type_w: &Expr,
    u_level: &Level,
    v_level: &Level,
    w_level: &Level,
) -> (Expr, Expr) {
    let projection_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (gamma_id, gamma) = b.fresh_local(type_w.clone());
        let class_ty = Expr::app(
            Expr::app(
                Expr::app(
                    class_const(u_level.clone(), v_level.clone(), w_level.clone()),
                    alpha.clone(),
                ),
                beta.clone(),
            ),
            gamma.clone(),
        );
        let (inst_id, _) = b.fresh_local(class_ty.clone());
        let (lhs_id, _) = b.fresh_local(alpha.clone());
        let (rhs_id, _) = b.fresh_local(beta.clone());

        let r = gamma.clone();
        let r = b.mk_pi(rhs_id, BinderInfo::Default, beta.clone(), r);
        let r = b.mk_pi(lhs_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty.clone(), r);
        let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    let projection_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (gamma_id, gamma) = b.fresh_local(type_w.clone());
        let class_ty = Expr::app(
            Expr::app(
                Expr::app(
                    class_const(u_level.clone(), v_level.clone(), w_level.clone()),
                    alpha.clone(),
                ),
                beta.clone(),
            ),
            gamma.clone(),
        );
        let (inst_id, inst) = b.fresh_local(class_ty.clone());

        let body = Expr::proj(class_name.clone(), 0, inst);
        let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
        let r = b.mk_lam(gamma_id, BinderInfo::Implicit, type_w.clone(), r);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    (projection_type, projection_value)
}

/// Build the projection type and value for a 1-universe binary op class (Div, Mod).
/// Returns `(projection_type, projection_value)`.
fn build_binary_projection(
    class_name: &Name,
    class_const: impl Fn(Level) -> Expr,
    type_u: &Expr,
    u_level: &Level,
) -> (Expr, Expr) {
    let projection_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let class_ty = Expr::app(class_const(u_level.clone()), alpha.clone());
        let (inst_id, _) = b.fresh_local(class_ty.clone());
        let (lhs_id, _) = b.fresh_local(alpha.clone());
        let (rhs_id, _) = b.fresh_local(alpha.clone());
        let r = alpha.clone();
        let r = b.mk_pi(rhs_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(lhs_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    let projection_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let class_ty = Expr::app(class_const(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(class_ty.clone());
        let body = Expr::proj(class_name.clone(), 0, inst);
        let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    (projection_type, projection_value)
}

/// Build the projection type and value for Pow (2-universe class).
/// Returns `(projection_type, projection_value)`.
fn build_pow_projection(
    type_u: &Expr,
    type_v: &Expr,
    u_level: &Level,
    v_level: &Level,
) -> (Expr, Expr) {
    let pow_name = Name::from_string("Pow");
    let pow_const = |u: Level, v: Level| Expr::const_(pow_name.clone(), vec![u, v]);

    let projection_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let class_ty = Expr::app(
            Expr::app(pow_const(u_level.clone(), v_level.clone()), alpha.clone()),
            beta.clone(),
        );
        let (inst_id, _) = b.fresh_local(class_ty.clone());
        let (base_id, _) = b.fresh_local(alpha.clone());
        let (exp_id, _) = b.fresh_local(beta.clone());
        let r = alpha.clone();
        let r = b.mk_pi(exp_id, BinderInfo::Default, beta.clone(), r);
        let r = b.mk_pi(base_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    let projection_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let class_ty = Expr::app(
            Expr::app(pow_const(u_level.clone(), v_level.clone()), alpha.clone()),
            beta.clone(),
        );
        let (inst_id, inst) = b.fresh_local(class_ty.clone());
        let body = Expr::proj(pow_name.clone(), 0, inst);
        let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    (projection_type, projection_value)
}

/// Build the constructor type for a 3-universe heterogeneous op (α → β → γ).
fn build_hetero_ctor_type(
    class_const: impl Fn(Level, Level, Level) -> Expr,
    type_u: &Expr,
    type_v: &Expr,
    type_w: &Expr,
    u_level: &Level,
    v_level: &Level,
    w_level: &Level,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
    let (beta_id, beta) = b.fresh_local(type_v.clone());
    let (gamma_id, gamma) = b.fresh_local(type_w.clone());

    let op_type = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (lhs_id, _) = s.fresh_local(alpha.clone());
        let (rhs_id, _) = s.fresh_local(beta.clone());
        let r = gamma.clone();
        let r = s.mk_pi(rhs_id, BinderInfo::Default, beta.clone(), r);
        let r = s.mk_pi(lhs_id, BinderInfo::Default, alpha.clone(), r);
        s.finish_child(r)
    };
    let (op_id, _) = b.fresh_local(op_type.clone());

    let class_ty = Expr::app(
        Expr::app(
            Expr::app(
                class_const(u_level.clone(), v_level.clone(), w_level.clone()),
                alpha.clone(),
            ),
            beta.clone(),
        ),
        gamma.clone(),
    );
    let r = b.mk_pi(op_id, BinderInfo::Default, op_type, class_ty);
    let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), r);
    let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
    b.finish(r)
}

impl Environment {
    fn init_hetero_op_with_flavor(&mut self, flavor: HeteroOpFlavor) -> Result<(), EnvError> {
        let class_name = Name::from_string(flavor.class_name);
        let ctor_name = Name::from_string(flavor.ctor_name);
        let field_name = Name::from_string(flavor.field_name);
        let projection_name = Name::from_string(flavor.projection_name);

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let w_level = Level::param(w.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let type_w = Expr::sort(Level::succ(w_level.clone()));
        let result_level = Level::max(
            u_level.clone(),
            Level::max(v_level.clone(), w_level.clone()),
        );
        let result_type = Expr::sort(Level::succ(result_level));

        let class_const =
            |u: Level, v: Level, w: Level| Expr::const_(class_name.clone(), vec![u, v, w]);

        #[allow(clippy::needless_borrows_for_generic_args)]
        let ctor_type = build_hetero_ctor_type(
            &class_const,
            &type_u,
            &type_v,
            &type_w,
            &u_level,
            &v_level,
            &w_level,
        );

        let hetero_ind = InductiveDecl {
            level_params: vec![u.clone(), v.clone(), w.clone()],
            num_params: 3,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    type_u.clone(),
                    Expr::pi(
                        BinderInfo::Implicit,
                        type_v.clone(),
                        Expr::pi(BinderInfo::Implicit, type_w.clone(), result_type),
                    ),
                ),
                constructors: vec![Constructor {
                    name: ctor_name,
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(hetero_ind)?;

        self.register_structure_fields(class_name.clone(), vec![field_name])?;

        if flavor.register_as_class {
            self.register_class(KernelClassInfo {
                name: class_name.clone(),
                num_params: 3,
                out_params: vec![2],
                semi_out_params: vec![],
            });
        }

        let (projection_type, projection_value) = build_hetero_projection(
            &class_name,
            class_const,
            &type_u,
            &type_v,
            &type_w,
            &u_level,
            &v_level,
            &w_level,
        );

        self.add_decl(Declaration::Definition {
            name: projection_name,
            level_params: vec![u, v, w],
            type_: projection_type,
            value: projection_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    fn init_binary_op_with_flavor(&mut self, flavor: BinaryOpFlavor) -> Result<(), EnvError> {
        let class_name = Name::from_string(flavor.class_name);
        let ctor_name = Name::from_string(flavor.ctor_name);
        let field_name = Name::from_string(flavor.field_name);
        let projection_name = Name::from_string(flavor.projection_name);

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
        let class_const = |lvl: Level| Expr::const_(class_name.clone(), vec![lvl]);

        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let op_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (lhs_id, _) = s.fresh_local(alpha.clone());
                let (rhs_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(rhs_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(lhs_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (op_id, _) = b.fresh_local(op_type.clone());
            let class_ty = Expr::app(class_const(u_level.clone()), alpha.clone());
            let r = b.mk_pi(op_id, BinderInfo::Default, op_type, class_ty);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let binary_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: Expr::pi(BinderInfo::Implicit, type_u.clone(), type_u.clone()),
                constructors: vec![Constructor {
                    name: ctor_name,
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(binary_ind)?;

        self.register_structure_fields(class_name.clone(), vec![field_name])?;

        let (projection_type, projection_value) =
            build_binary_projection(&class_name, class_const, &type_u, &u_level);

        self.add_decl(Declaration::Definition {
            name: projection_name,
            level_params: vec![u],
            type_: projection_type,
            value: projection_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    fn init_pow_core(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let result_level = Level::max(u_level.clone(), v_level.clone());
        let result_type = Expr::sort(Level::succ(result_level));
        let pow_const = |u: Level, v: Level| Expr::const_(Name::from_string("Pow"), vec![u, v]);

        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let op_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (base_id, _) = s.fresh_local(alpha.clone());
                let (exp_id, _) = s.fresh_local(beta.clone());
                let r = alpha.clone();
                let r = s.mk_pi(exp_id, BinderInfo::Default, beta.clone(), r);
                let r = s.mk_pi(base_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (op_id, _) = b.fresh_local(op_type.clone());
            let class_ty = Expr::app(
                Expr::app(pow_const(u_level.clone(), v_level.clone()), alpha.clone()),
                beta.clone(),
            );
            let r = b.mk_pi(op_id, BinderInfo::Default, op_type, class_ty);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let pow_ind = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Pow"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    type_u.clone(),
                    Expr::pi(BinderInfo::Implicit, type_v.clone(), result_type),
                ),
                constructors: vec![Constructor {
                    name: Name::from_string("Pow.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(pow_ind)?;

        self.register_structure_fields(Name::from_string("Pow"), vec![Name::from_string("pow")])?;

        let (projection_type, projection_value) =
            build_pow_projection(&type_u, &type_v, &u_level, &v_level);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Pow.pow"),
            level_params: vec![u, v],
            type_: projection_type,
            value: projection_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize the HAdd heterogeneous typeclass
    ///
    /// HAdd is a heterogeneous addition typeclass with three type parameters:
    /// ```text
    /// class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hAdd : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hadd_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hadd(&mut self) -> Result<(), EnvError> {
        if self.hadd_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HADD_FLAVOR)?;

        self.hadd_init = true;
        Ok(())
    }

    /// Check if HAdd typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.hadd_init == true`
    pub(crate) fn has_hadd(&self) -> bool {
        self.hadd_init
    }

    /// Initialize the HAppend heterogeneous typeclass
    ///
    /// HAppend is the heterogeneous append typeclass backing the `++`
    /// operator with three type parameters:
    /// ```text
    /// class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hAppend : α → β → γ
    /// ```
    ///
    /// Without this, `a ++ b` had no `HAppend.hAppend` projection to resolve
    /// against; the elaborated body leaked a fresh metavariable and the kernel
    /// rejected the declaration with "contains free variables".
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.happend_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_happend(&mut self) -> Result<(), EnvError> {
        if self.happend_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HAPPEND_FLAVOR)?;

        self.happend_init = true;
        Ok(())
    }

    /// Check if HAppend typeclass has been initialized
    pub(crate) fn has_happend(&self) -> bool {
        self.happend_init
    }

    /// Initialize the instHAppendString instance bridging String append to
    /// the `HAppend` class:
    /// ```text
    /// instance instHAppendString : HAppend String String String where
    ///   hAppend := String.append
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.string_happend_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_string_happend_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // String-cluster content over the import-suppressed v4.8 String/Char
        // shapes (see init_string). Suppressed with them.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.string_happend_inst_init {
            return Ok(());
        }

        self.init_happend()?;
        self.init_string()?;
        self.init_string_append()?;
        self.add_homogeneous_hetero_instance(
            "instHAppendString",
            "HAppend",
            "HAppend.mk",
            "String",
            "String.append",
        )?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAppendString"),
            class_name: Name::from_string("HAppend"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.string_happend_inst_init = true;
        Ok(())
    }

    /// Initialize the parametric `instHAppendListList` instance bridging
    /// `List.append` to the `HAppend` class:
    /// ```text
    /// instance instHAppendListList : {α : Type u} → HAppend (List α) (List α) (List α) where
    ///   hAppend := List.append
    /// ```
    ///
    /// Without this, `xs ++ ys` on lists desugars to `HAppend.hAppend xs ys`
    /// but instance synthesis had only the monomorphic `instHAppendString`;
    /// the `[inst : HAppend (List α) (List α) (List α)]` argument was left an
    /// unfilled metavariable and the kernel rejected the enclosing declaration
    /// with "contains free variables" (trust-ir Aggregate.lean `setUnion` /
    /// `seqConcat`, plus the downstream `*_empty`/`*_length` theorems that hit
    /// "function type FVar(..) is not a function type"). The instance is a
    /// genuine closed term (no axioms, no sorry): the kernel-built
    /// axiom-free `List.append` recursor wrapped in `HAppend.mk`. (Track G)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.list_happend_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_list_happend_inst(&mut self) -> Result<(), EnvError> {
        if self.list_happend_inst_init {
            return Ok(());
        }

        self.init_happend()?;
        // `List.append` lives in `init_list_ops`; pull it in (idempotent) so the
        // instance value below resolves. `init_string_append` is the usual route
        // but call the underlying op directly to keep this self-contained.
        // NOTE: this call must stay UNGATED in import mode — it also registers
        // the non-divergent Option combinators and `List.get?` the import
        // prelude keeps.
        self.init_list_ops()?;

        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): `instHAppendListList` wraps the import-gated
        // `List.append` seed (absent at init time), so the instance is gated
        // with the List.* recursion cluster (see data_collection_ops.rs).
        // Imported oleans carry Lean's own genuine List append instances.
        if self.suppress_lossy_structure_stubs {
            self.list_happend_inst_init = true;
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        // HAppend / HAppend.mk are universe-polymorphic in (u, v, w); for the
        // homogeneous List instance all three carriers live at the same `u`.
        let happend_levels = vec![u_level.clone(), u_level.clone(), u_level.clone()];
        let happend_const = Expr::const_(Name::from_string("HAppend"), happend_levels.clone());
        let happend_mk = Expr::const_(Name::from_string("HAppend.mk"), happend_levels);
        let list_append = Expr::const_(Name::from_string("List.append"), vec![u_level.clone()]);

        // instHAppendListList : {α : Type u} → HAppend (List α) (List α) (List α)
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            // HAppend (List α) (List α) (List α)
            let r = Expr::apps(
                happend_const.clone(),
                [list_alpha.clone(), list_alpha.clone(), list_alpha.clone()],
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // value: λ {α : Type u} => HAppend.mk (List α) (List α) (List α) (List.append α)
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            // List.append α : List α → List α → List α
            let append_applied = Expr::app(list_append.clone(), alpha.clone());
            // HAppend.mk (List α) (List α) (List α) (List.append α)
            let body = Expr::apps(
                happend_mk.clone(),
                [
                    list_alpha.clone(),
                    list_alpha.clone(),
                    list_alpha.clone(),
                    append_applied,
                ],
            );
            let body = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instHAppendListList"),
            level_params: vec![u.clone()],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAppendListList"),
            class_name: Name::from_string("HAppend"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.list_happend_inst_init = true;
        Ok(())
    }

    /// Initialize the HSub heterogeneous typeclass
    ///
    /// HSub is a heterogeneous subtraction typeclass with three type parameters:
    /// ```text
    /// class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hSub : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hsub_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hsub(&mut self) -> Result<(), EnvError> {
        if self.hsub_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HSUB_FLAVOR)?;

        self.hsub_init = true;
        Ok(())
    }

    /// Check if HSub typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.hsub_init == true`
    pub(crate) fn has_hsub(&self) -> bool {
        self.hsub_init
    }

    /// Initialize the HMul heterogeneous typeclass
    ///
    /// HMul is a heterogeneous multiplication typeclass with three type parameters:
    /// ```text
    /// class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hMul : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hmul_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hmul(&mut self) -> Result<(), EnvError> {
        if self.hmul_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HMUL_FLAVOR)?;

        self.hmul_init = true;
        Ok(())
    }

    /// Check if HMul typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.hmul_init == true`
    pub(crate) fn has_hmul(&self) -> bool {
        self.hmul_init
    }

    /// Initialize the HDiv heterogeneous typeclass
    ///
    /// HDiv is a heterogeneous division typeclass with three type parameters:
    /// ```text
    /// class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hDiv : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hdiv_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hdiv(&mut self) -> Result<(), EnvError> {
        if self.hdiv_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HDIV_FLAVOR)?;

        self.hdiv_init = true;
        Ok(())
    }

    /// Check if HDiv typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.hdiv_init == true`
    pub(crate) fn has_hdiv(&self) -> bool {
        self.hdiv_init
    }

    /// Initialize the Div typeclass
    ///
    /// Div is a homogeneous division typeclass:
    /// ```text
    /// class Div (α : Type u) where
    ///   div : α → α → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.div_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_div(&mut self) -> Result<(), EnvError> {
        if self.div_init {
            return Ok(());
        }
        self.init_binary_op_with_flavor(DIV_FLAVOR)?;

        self.div_init = true;
        Ok(())
    }

    /// Check if Div typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.div_init == true`
    pub(crate) fn has_div(&self) -> bool {
        self.div_init
    }

    /// Initialize the HMod heterogeneous typeclass
    ///
    /// HMod is a heterogeneous modulo typeclass with three type parameters:
    /// ```text
    /// class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hMod : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hmod_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_hmod(&mut self) -> Result<(), EnvError> {
        if self.hmod_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HMOD_FLAVOR)?;

        self.hmod_init = true;
        Ok(())
    }

    /// Check if HMod typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.hmod_init == true`
    pub(crate) fn has_hmod(&self) -> bool {
        self.hmod_init
    }

    /// Initialize the Mod typeclass
    ///
    /// Mod is a homogeneous modulo typeclass:
    /// ```text
    /// class Mod (α : Type u) where
    ///   mod : α → α → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.mod_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_mod(&mut self) -> Result<(), EnvError> {
        if self.mod_init {
            return Ok(());
        }
        self.init_binary_op_with_flavor(MOD_FLAVOR)?;

        self.mod_init = true;
        Ok(())
    }

    /// Check if Mod typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.mod_init == true`
    pub(crate) fn has_mod(&self) -> bool {
        self.mod_init
    }

    /// Initialize the HPow heterogeneous typeclass
    ///
    /// HPow is a heterogeneous power typeclass with three type parameters:
    /// ```text
    /// class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hPow : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hpow_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hpow(&mut self) -> Result<(), EnvError> {
        if self.hpow_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HPOW_FLAVOR)?;

        self.hpow_init = true;
        Ok(())
    }

    /// Check if HPow typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.hpow_init == true`
    pub(crate) fn has_hpow(&self) -> bool {
        self.hpow_init
    }

    /// Initialize the Pow typeclass
    ///
    /// Pow is a power typeclass with two type parameters:
    /// ```text
    /// class Pow (α : Type u) (β : Type v) where
    ///   pow : α → β → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.pow_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_pow(&mut self) -> Result<(), EnvError> {
        if self.pow_init {
            return Ok(());
        }
        self.init_pow_core()?;

        self.pow_init = true;
        Ok(())
    }

    /// Check if Pow typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.pow_init == true`
    pub(crate) fn has_pow(&self) -> bool {
        self.pow_init
    }

    pub(crate) fn add_homogeneous_hetero_instance(
        &mut self,
        inst_name: &str,
        class_name: &str,
        ctor_name: &str,
        carrier_name: &str,
        operation_name: &str,
    ) -> Result<(), EnvError> {
        let carrier = Expr::const_(Name::from_string(carrier_name), vec![]);
        let operation = Expr::const_(Name::from_string(operation_name), vec![]);
        let levels = vec![Level::zero(), Level::zero(), Level::zero()];
        let class_const = Expr::const_(Name::from_string(class_name), levels.clone());
        let ctor_const = Expr::const_(Name::from_string(ctor_name), levels);

        let inst_type = Expr::app(
            Expr::app(Expr::app(class_const, carrier.clone()), carrier.clone()),
            carrier.clone(),
        );
        let inst_value = Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctor_const, carrier.clone()), carrier.clone()),
                carrier,
            ),
            operation,
        );

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string(inst_name),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Register a heterogeneous `H<Op> A B C` instance with three *distinct*
    /// carrier types, e.g. `HPow Int Nat Int` backed by `Int.pow : Int → Nat →
    /// Int`. Like [`add_homogeneous_hetero_instance`] but the class/ctor are
    /// applied to three separate carriers. (Track PP)
    fn add_hetero3_instance(
        &mut self,
        inst_name: &str,
        class_name: &str,
        ctor_name: &str,
        a_name: &str,
        b_name: &str,
        c_name: &str,
        operation_name: &str,
    ) -> Result<(), EnvError> {
        let a = Expr::const_(Name::from_string(a_name), vec![]);
        let b = Expr::const_(Name::from_string(b_name), vec![]);
        let c = Expr::const_(Name::from_string(c_name), vec![]);
        let operation = Expr::const_(Name::from_string(operation_name), vec![]);
        let levels = vec![Level::zero(), Level::zero(), Level::zero()];
        let class_const = Expr::const_(Name::from_string(class_name), levels.clone());
        let ctor_const = Expr::const_(Name::from_string(ctor_name), levels);

        let inst_type = Expr::app(
            Expr::app(Expr::app(class_const, a.clone()), b.clone()),
            c.clone(),
        );
        let inst_value = Expr::app(
            Expr::app(Expr::app(Expr::app(ctor_const, a), b), c),
            operation,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string(inst_name),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize the instHAdd instance that bridges Add to HAdd
    ///
    /// ```text
    /// instance instHAdd [Add α] : HAdd α α α where
    ///   hAdd := Add.add
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hadd_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hadd_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): `instHAddNat` wraps the import-gated `Nat.add` seed
        // (absent at init time — Nat core arithmetic cluster, see
        // data_types_nat.rs::init_nat), so the instance is gated with it. The
        // `HAdd` class itself stays in both lanes (init_prelude_core calls
        // init_hadd directly); imported oleans carry Lean's genuine
        // instHAdd/instAddNat chain. SOUNDNESS: withholds a Clean-native seed
        // in the import-only prelude; default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            self.nat_hadd_inst_init = true;
            return Ok(());
        }
        if self.nat_hadd_inst_init {
            return Ok(());
        }

        self.init_hadd()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHAddNat", "HAdd", "HAdd.mk", "Nat", "Nat.add")?;

        // Register the instance with the kernel
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAddNat"),
            class_name: Name::from_string("HAdd"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.nat_hadd_inst_init = true;
        Ok(())
    }

    /// Check if Nat HAdd instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_hadd_inst_init == true`
    pub(crate) fn has_nat_hadd_inst(&self) -> bool {
        self.nat_hadd_inst_init
    }

    /// Initialize the instHAddInt instance
    ///
    /// ```text
    /// instance instHAddInt : HAdd Int Int Int where
    ///   hAdd := Int.add
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_hadd_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_hadd_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_hadd_inst_init {
            return Ok(());
        }

        self.init_hadd()?;
        self.init_int_arith()?;
        self.add_homogeneous_hetero_instance("instHAddInt", "HAdd", "HAdd.mk", "Int", "Int.add")?;

        // Register with the kernel's instance table so `a + b` over `Int`
        // resolves its `[HAdd Int Int Int]` argument (mirrors the Nat path).
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAddInt"),
            class_name: Name::from_string("HAdd"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.int_hadd_inst_init = true;
        Ok(())
    }

    /// Check if Int HAdd instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_hadd_inst_init == true`
    pub(crate) fn has_int_hadd_inst(&self) -> bool {
        self.int_hadd_inst_init
    }

    /// Initialize the instHSubNat instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hsub_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hsub_inst(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate —
        // `instHSubNat` wraps the import-gated `Nat.sub` seed (see
        // init_nat_hadd_inst above / data_types_nat.rs::init_nat).
        if self.suppress_lossy_structure_stubs {
            self.nat_hsub_inst_init = true;
            return Ok(());
        }
        if self.nat_hsub_inst_init {
            return Ok(());
        }

        self.init_hsub()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHSubNat", "HSub", "HSub.mk", "Nat", "Nat.sub")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHSubNat"),
            class_name: Name::from_string("HSub"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.nat_hsub_inst_init = true;
        Ok(())
    }

    /// Check if Nat HSub instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_hsub_inst_init == true`
    pub(crate) fn has_nat_hsub_inst(&self) -> bool {
        self.nat_hsub_inst_init
    }

    /// Initialize the instHSubInt instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_hsub_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_hsub_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_hsub_inst_init {
            return Ok(());
        }

        self.init_hsub()?;
        self.init_int_arith()?;
        self.add_homogeneous_hetero_instance("instHSubInt", "HSub", "HSub.mk", "Int", "Int.sub")?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHSubInt"),
            class_name: Name::from_string("HSub"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.int_hsub_inst_init = true;
        Ok(())
    }

    /// Check if Int HSub instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_hsub_inst_init == true`
    pub(crate) fn has_int_hsub_inst(&self) -> bool {
        self.int_hsub_inst_init
    }

    /// Initialize the instHMulNat instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hmul_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_nat_hmul_inst(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate —
        // `instHMulNat` wraps the import-gated `Nat.mul` seed (see
        // init_nat_hadd_inst above / data_types_nat.rs::init_nat).
        if self.suppress_lossy_structure_stubs {
            self.nat_hmul_inst_init = true;
            return Ok(());
        }
        if self.nat_hmul_inst_init {
            return Ok(());
        }

        self.init_hmul()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHMulNat", "HMul", "HMul.mk", "Nat", "Nat.mul")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHMulNat"),
            class_name: Name::from_string("HMul"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.nat_hmul_inst_init = true;
        Ok(())
    }

    /// Check if Nat HMul instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_hmul_inst_init == true`
    pub(crate) fn has_nat_hmul_inst(&self) -> bool {
        self.nat_hmul_inst_init
    }

    /// Initialize the `instHModNat : HMod Nat Nat Nat` instance.
    ///
    /// Mirrors `init_nat_hadd_inst`/`init_nat_hmul_inst` but backs the `%`
    /// notation over `Nat` with the newly-registered `Nat.mod` constant.
    /// Without this instance (and `init_hmod`) the prelude had `HMod`
    /// completely absent, so `v % 256` failed to resolve `HMod`/`HMod.hMod`.
    /// Idempotent via the constant-presence guard (no dedicated init flag).
    /// (Track TAC)
    pub(crate) fn init_nat_hmod_inst(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate —
        // `instHModNat` wraps the import-gated `Nat.mod` seed (see
        // init_nat_hadd_inst above / data_types_nat.rs::init_nat).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("instHModNat")).is_some() {
            return Ok(());
        }
        self.init_hmod()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHModNat", "HMod", "HMod.mk", "Nat", "Nat.mod")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHModNat"),
            class_name: Name::from_string("HMod"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Initialize the `instHDivNat : HDiv Nat Nat Nat` instance.
    ///
    /// Backs the `/` notation over `Nat` with the `Nat.div` constant. See
    /// `init_nat_hmod_inst` for the rationale. (Track TAC)
    pub(crate) fn init_nat_hdiv_inst(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate —
        // `instHDivNat` wraps the import-gated `Nat.div` seed (see
        // init_nat_hadd_inst above / data_types_nat.rs::init_nat).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("instHDivNat")).is_some() {
            return Ok(());
        }
        self.init_hdiv()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHDivNat", "HDiv", "HDiv.mk", "Nat", "Nat.div")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHDivNat"),
            class_name: Name::from_string("HDiv"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Initialize the `instHPowNat : HPow Nat Nat Nat` instance.
    ///
    /// Backs the `^` notation over `Nat` with the `Nat.pow` constant. `HPow` is
    /// already registered as a class and `Nat.pow` already exists, but no Nat
    /// HPow *instance* was registered, so `256 ^ n` resolved `HPow.hPow` yet
    /// left the instance arg unfilled ("contains free variables"). Idempotent
    /// via the constant-presence guard. (Track TAC)
    pub(crate) fn init_nat_hpow_inst(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate —
        // `instHPowNat` wraps the import-gated `Nat.pow` seed (see
        // init_nat_hadd_inst above / data_types_nat.rs::init_nat).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("instHPowNat")).is_some() {
            return Ok(());
        }
        self.init_hpow()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHPowNat", "HPow", "HPow.mk", "Nat", "Nat.pow")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHPowNat"),
            class_name: Name::from_string("HPow"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Initialize the instHMulInt instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_hmul_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_hmul_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_hmul_inst_init {
            return Ok(());
        }

        self.init_hmul()?;
        self.init_int_arith()?;
        self.add_homogeneous_hetero_instance("instHMulInt", "HMul", "HMul.mk", "Int", "Int.mul")?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHMulInt"),
            class_name: Name::from_string("HMul"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.int_hmul_inst_init = true;
        Ok(())
    }

    /// Check if Int HMul instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_hmul_inst_init == true`
    pub(crate) fn has_int_hmul_inst(&self) -> bool {
        self.int_hmul_inst_init
    }

    /// Initialize the `instHDivInt : HDiv Int Int Int` instance.
    ///
    /// Backs the `/` notation over `Int` with the `Int.div` constant (registered
    /// as an `Opaque` data declaration by `init_int_arith`, evaluated by the
    /// `Int.div` native reducer). Mirrors `init_nat_hdiv_inst`. Idempotent via
    /// the constant-presence guard (no dedicated init flag). (Track PP)
    pub(crate) fn init_int_hdiv_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("instHDivInt")).is_some() {
            return Ok(());
        }
        self.init_hdiv()?;
        self.init_int_arith()?;
        self.add_homogeneous_hetero_instance("instHDivInt", "HDiv", "HDiv.mk", "Int", "Int.div")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHDivInt"),
            class_name: Name::from_string("HDiv"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Initialize the `instHModInt : HMod Int Int Int` instance.
    ///
    /// Backs the `%` notation over `Int` with the `Int.mod` constant. See
    /// `init_int_hdiv_inst` for the rationale. Mirrors `init_nat_hmod_inst`.
    /// (Track PP)
    pub(crate) fn init_int_hmod_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("instHModInt")).is_some() {
            return Ok(());
        }
        self.init_hmod()?;
        self.init_int_arith()?;
        self.add_homogeneous_hetero_instance("instHModInt", "HMod", "HMod.mk", "Int", "Int.mod")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHModInt"),
            class_name: Name::from_string("HMod"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Register the `Float.add`/`Float.sub`/`Float.mul`/`Float.div` (binary) and
    /// `Float.neg` (unary) operation constants used by the Float arithmetic
    /// instances below.
    ///
    /// Mirrors the `Int.div`/`Int.mod` treatment in `init_int_arith`
    /// (`data_types_arithmetic.rs`): each is a `Declaration::Opaque` with a
    /// type-correct placeholder body the kernel never unfolds. Concrete IEEE-754
    /// evaluation is supplied by the already-registered `Float.add`/`Float.sub`/…
    /// native reducers (`native_reducers_float.rs`). `Opaque` is NOT an `Axiom`,
    /// so a term referencing these gains no axiom dependency (`env.axiom_deps`
    /// only counts `ConstantKind::Axiom`). This unblocks the Float `HAdd`/`HSub`/
    /// `HMul`/`HDiv`/`Neg` instances — without them, `lhs + rhs`/`-operand` over
    /// `Float` (trust-ir `Semantics/Arith.lean` `semFloatBinOp`/`semFloatUnOp`)
    /// left every instance argument unfilled ("contains free variables").
    /// (Track EF)
    pub(crate) fn init_float_arith_ops(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float cluster content — references the import-suppressed Clean
        // Float/UInt carrier stubs (see init_float / init_uint8..64).
        // Suppressed with them; the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_arith_ops_init {
            return Ok(());
        }
        self.init_float()?;
        // `Bool` / `Bool.false` are the result type and placeholder body of the
        // `Float.isNaN`/`isInf`/`isFinite` predicate ops added below; ensure they
        // exist (idempotent — already initialized in the standard prelude setup).
        self.init_bool()?;

        let float_const = Expr::const_(Name::from_string("Float"), vec![]);
        // A closed `Float` value: `Float.mk Nat.zero` (init_float gives
        // `Float.mk : Nat → Float`). Used only as the never-unfolded placeholder.
        let float_zero = Expr::app(
            Expr::const_(Name::from_string("Float.mk"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );

        // Binary ops: Float → Float → Float
        let binop_ty = Expr::pi(
            BinderInfo::Default,
            float_const.clone(),
            Expr::pi(
                BinderInfo::Default,
                float_const.clone(),
                float_const.clone(),
            ),
        );
        let binop_placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(float_const.clone());
            let (b_id, _b) = b.fresh_local(float_const.clone());
            let e = b.mk_lam(
                b_id,
                BinderInfo::Default,
                float_const.clone(),
                float_zero.clone(),
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, float_const.clone(), e);
            b.finish(e)
        };
        for op in ["Float.add", "Float.sub", "Float.mul", "Float.div"] {
            self.add_decl_if_absent(Declaration::Opaque {
                name: Name::from_string(op),
                level_params: vec![],
                type_: binop_ty.clone(),
                value: binop_placeholder.clone(),
            })?;
        }

        // Unary op: Float → Float
        let unop_ty = Expr::pi(
            BinderInfo::Default,
            float_const.clone(),
            float_const.clone(),
        );
        let unop_placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(float_const.clone());
            let e = b.mk_lam(
                a_id,
                BinderInfo::Default,
                float_const.clone(),
                float_zero.clone(),
            );
            b.finish(e)
        };
        // `Float.neg` (prefix `-`) and `Float.round` (dot method `x.round`, used
        // in trust-ir `semFloatBinOp`'s FRem case `(lhs / rhs).round`). Both are
        // `Float → Float`. `Float.round`'s concrete IEEE rounding is supplied by
        // the `reduce_float_round` native reducer.
        for op in ["Float.neg", "Float.round"] {
            self.add_decl_if_absent(Declaration::Opaque {
                name: Name::from_string(op),
                level_params: vec![],
                type_: unop_ty.clone(),
                value: unop_placeholder.clone(),
            })?;
        }

        // `Float.isNaN` / `Float.isInf` / `Float.isFinite` — `Float → Bool`
        // IEEE-754 classification predicates. `Float.isNaN` is used by trust-ir
        // `Semantics/Compare.lean` `semFCmp` (`lhs.isNaN || rhs.isNaN`) for
        // ordered/unordered NaN gating. Each is an `Opaque` op (NOT an axiom):
        // the never-unfolded placeholder body `Bool.false` makes the declaration
        // type-correct, while concrete IEEE classification is supplied by the
        // already-registered `reduce_float_is_nan`/`is_inf`/`is_finite` native
        // reducers (`native_reducers_float.rs`), exactly mirroring the
        // `Float.round` treatment above. Without these, the dot-notation method
        // call `f.isNaN` fails with "Unknown projection field isNaN on structure
        // Float" (the elaborator's `elab_dot_notation` needs a real `Float.isNaN`
        // constant to resolve against).
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let pred_ty = Expr::pi(BinderInfo::Default, float_const.clone(), bool_const.clone());
        let pred_placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(float_const.clone());
            let e = b.mk_lam(
                a_id,
                BinderInfo::Default,
                float_const.clone(),
                bool_false.clone(),
            );
            b.finish(e)
        };
        for op in ["Float.isNaN", "Float.isInf", "Float.isFinite"] {
            self.add_decl_if_absent(Declaration::Opaque {
                name: Name::from_string(op),
                level_params: vec![],
                type_: pred_ty.clone(),
                value: pred_placeholder.clone(),
            })?;
        }

        // `Float.ofNat : Nat → Float` and `Float.ofScientific : Nat → Bool → Nat
        // → Float` — the numeric-literal lowering targets. Lean 4 lowers a bare
        // float literal (`0.0`, `3.14`) to `Float.ofScientific mantissa expSign
        // decExp` (see `elab_float_literal_with_expected` in
        // `clean-elab/src/infer/coercion.rs`); `Float.ofNat` is the integral
        // companion. Without these constants registered, any source containing a
        // Float literal — e.g. trust-ir `Semantics/Memory.lean` `decodeValue`'s
        // axiomatized `some (.float 0.0)` placeholders — fails the kernel check
        // with `UnknownConst(Float.ofScientific)`.
        //
        // Each is a `Declaration::Opaque` (NOT an `Axiom`, so no
        // `env.axiom_deps` contribution) with a type-correct, never-unfolded
        // placeholder body `Float.mk Nat.zero`, exactly mirroring the
        // `Float.add`/`Float.round` treatment above. Concrete evaluation, when a
        // term is reduced, is supplied by the already-registered
        // `reduce_float_of_nat`/`reduce_float_of_scientific` native reducers
        // (`native_reducers_float.rs`). The placeholder bodies guarantee
        // type-correctness for the kernel; reduction is opt-in via the native
        // reducer table.
        let of_nat_ty = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            float_const.clone(),
        );
        let of_nat_placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _n) = b.fresh_local(Expr::const_(Name::from_string("Nat"), vec![]));
            let e = b.mk_lam(
                n_id,
                BinderInfo::Default,
                Expr::const_(Name::from_string("Nat"), vec![]),
                float_zero.clone(),
            );
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Opaque {
            name: Name::from_string("Float.ofNat"),
            level_params: vec![],
            type_: of_nat_ty,
            value: of_nat_placeholder,
        })?;

        // `Float.ofScientific : Nat → Bool → Nat → Float`.
        let nat_const2 = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_const2 = Expr::const_(Name::from_string("Bool"), vec![]);
        let of_scientific_ty = Expr::pi(
            BinderInfo::Default,
            nat_const2.clone(),
            Expr::pi(
                BinderInfo::Default,
                bool_const2.clone(),
                Expr::pi(BinderInfo::Default, nat_const2.clone(), float_const.clone()),
            ),
        );
        let of_scientific_placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const2.clone());
            let (s_id, _s) = b.fresh_local(bool_const2.clone());
            let (e_id, _e) = b.fresh_local(nat_const2.clone());
            let body = b.mk_lam(
                e_id,
                BinderInfo::Default,
                nat_const2.clone(),
                float_zero.clone(),
            );
            let body = b.mk_lam(s_id, BinderInfo::Default, bool_const2.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const2.clone(), body);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Opaque {
            name: Name::from_string("Float.ofScientific"),
            level_params: vec![],
            type_: of_scientific_ty,
            value: of_scientific_placeholder,
        })?;

        // `Float.toUInt8 : Float → UInt8`, `Float.toUInt16`, `Float.toUInt32`,
        // `Float.toUInt64`. Lean 4 ships these as the canonical float→unsigned
        // truncations; trust-ir `Semantics/Cast.lean` `semCast` lowers an
        // `FPToUI`/`FPToSI` cast through `v.toUInt64.toNat` (axiomatized: "use
        // Lean's Float conversions"). Without the constant the dot-notation
        // `v.toUInt64` failed structure-field resolution with "Unknown
        // projection field toUInt64 on structure Float" — only the *native
        // reducer* names (`reduce_float_to_uint{8,16,32,64}`,
        // `native_reducers_float.rs`) were registered, never a constant the
        // elaborator could resolve.
        //
        // Each is a `Declaration::Opaque` (NOT an `Axiom`, so no
        // `env.axiom_deps` contribution) with a type-correct, never-unfolded
        // placeholder body `UIntN.ofNat Nat.zero`, exactly mirroring the
        // `Float.ofNat`/`Float.ofScientific` treatment above. Concrete
        // evaluation, when a ground term is reduced, is supplied by the already
        // registered native reducers — the placeholder only guarantees
        // type-correctness for the kernel; it never feeds an unsound Float
        // reduction (the placeholder is a constant 0, never a fabricated
        // conversion law). The matching trust-ir axiomatization is identical:
        // an opaque `Float → UIntN` whose meaning is Lean's runtime cast.
        //
        // CARRIER: `UIntN.mk : Fin UIntN.size → UIntN` (Lean 4.8.0), so the
        // placeholder builds the zero via `UIntN.ofNat 0` (= `mk (Fin.ofNat 0)`)
        // rather than the old `mk Nat.zero` (which is ill-typed now).
        self.init_uint_types()?;
        for width in ["UInt8", "UInt16", "UInt32", "UInt64"] {
            let uint_const = Expr::const_(Name::from_string(width), vec![]);
            let to_uint_ty = Expr::pi(BinderInfo::Default, float_const.clone(), uint_const.clone());
            // Placeholder body: `fun (_ : Float) => UIntN.ofNat Nat.zero`.
            let uint_zero = Expr::app(
                Expr::const_(Name::from_string(&format!("{width}.ofNat")), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            );
            let to_uint_placeholder = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _f) = b.fresh_local(float_const.clone());
                let e = b.mk_lam(f_id, BinderInfo::Default, float_const.clone(), uint_zero);
                b.finish(e)
            };
            self.add_decl_if_absent(Declaration::Opaque {
                name: Name::from_string(&format!("Float.to{width}")),
                level_params: vec![],
                type_: to_uint_ty,
                value: to_uint_placeholder,
            })?;
        }

        self.float_arith_ops_init = true;
        Ok(())
    }

    /// Initialize the `instHAddFloat : HAdd Float Float Float` instance.
    /// Backs `+` over `Float` with the `Float.add` constant. (Track EF)
    pub(crate) fn init_float_hadd_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float cluster content — references the import-suppressed Clean
        // Float/UInt carrier stubs (see init_float / init_uint8..64).
        // Suppressed with them; the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_hadd_inst_init {
            return Ok(());
        }
        self.init_hadd()?;
        self.init_float_arith_ops()?;
        self.add_homogeneous_hetero_instance(
            "instHAddFloat",
            "HAdd",
            "HAdd.mk",
            "Float",
            "Float.add",
        )?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAddFloat"),
            class_name: Name::from_string("HAdd"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.float_hadd_inst_init = true;
        Ok(())
    }

    /// Initialize the `instHSubFloat : HSub Float Float Float` instance.
    /// Backs `-` (binary) over `Float` with the `Float.sub` constant. (Track EF)
    pub(crate) fn init_float_hsub_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float cluster content — references the import-suppressed Clean
        // Float/UInt carrier stubs (see init_float / init_uint8..64).
        // Suppressed with them; the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_hsub_inst_init {
            return Ok(());
        }
        self.init_hsub()?;
        self.init_float_arith_ops()?;
        self.add_homogeneous_hetero_instance(
            "instHSubFloat",
            "HSub",
            "HSub.mk",
            "Float",
            "Float.sub",
        )?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHSubFloat"),
            class_name: Name::from_string("HSub"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.float_hsub_inst_init = true;
        Ok(())
    }

    /// Initialize the `instHMulFloat : HMul Float Float Float` instance.
    /// Backs `*` over `Float` with the `Float.mul` constant. (Track EF)
    pub(crate) fn init_float_hmul_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float cluster content — references the import-suppressed Clean
        // Float/UInt carrier stubs (see init_float / init_uint8..64).
        // Suppressed with them; the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_hmul_inst_init {
            return Ok(());
        }
        self.init_hmul()?;
        self.init_float_arith_ops()?;
        self.add_homogeneous_hetero_instance(
            "instHMulFloat",
            "HMul",
            "HMul.mk",
            "Float",
            "Float.mul",
        )?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHMulFloat"),
            class_name: Name::from_string("HMul"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.float_hmul_inst_init = true;
        Ok(())
    }

    /// Initialize the `instHDivFloat : HDiv Float Float Float` instance.
    /// Backs `/` over `Float` with the `Float.div` constant. (Track EF)
    pub(crate) fn init_float_hdiv_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float cluster content — references the import-suppressed Clean
        // Float/UInt carrier stubs (see init_float / init_uint8..64).
        // Suppressed with them; the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_hdiv_inst_init {
            return Ok(());
        }
        self.init_hdiv()?;
        self.init_float_arith_ops()?;
        self.add_homogeneous_hetero_instance(
            "instHDivFloat",
            "HDiv",
            "HDiv.mk",
            "Float",
            "Float.div",
        )?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHDivFloat"),
            class_name: Name::from_string("HDiv"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.float_hdiv_inst_init = true;
        Ok(())
    }

    /// Initialize the `instNegFloat : Neg Float` instance.
    ///
    /// Backs prefix `-` over `Float` (which the parser desugars to `Neg.neg`)
    /// with the `Float.neg` constant. Without it, `-operand` over `Float`
    /// (trust-ir `semFloatUnOp`) left its `[Neg Float]` argument unfilled
    /// ("contains free variables"). Mirrors the homogeneous `Neg`/`Int`
    /// `instNegInt` shape in `algebra_basic_instances_int.rs`. (Track EF)
    pub(crate) fn init_float_neg_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float cluster content — references the import-suppressed Clean
        // Float carrier stubs. Suppressed with them.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_neg_inst_init {
            return Ok(());
        }
        self.init_neg()?;
        self.init_float_arith_ops()?;

        let float_const = Expr::const_(Name::from_string("Float"), vec![]);
        let float_neg = Expr::const_(Name::from_string("Float.neg"), vec![]);
        let neg_mk = Expr::const_(Name::from_string("Neg.mk"), vec![Level::zero()]);

        // instNegFloat : Neg Float := Neg.mk Float.neg
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Neg"), vec![Level::zero()]),
            float_const.clone(),
        );
        let inst_value = Expr::app(Expr::app(neg_mk, float_const), float_neg);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instNegFloat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instNegFloat"),
            class_name: Name::from_string("Neg"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.float_neg_inst_init = true;
        Ok(())
    }

    /// Initialize the `instHPowIntNat : HPow Int Nat Int` instance.
    ///
    /// Backs `(b : Int) ^ (n : Nat)` with the `Int.pow : Int → Nat → Int`
    /// constant (a real `Nat.rec` recursion registered by `init_int_arith`).
    /// This is the heterogeneous shape trust-ir's Arith.lean uses pervasively
    /// (`(2 : Int) ^ width`, `2 ^ shamt.toNat`). Idempotent via the
    /// constant-presence guard. Axiom-free (`Int.pow` is a Definition). (Track PP)
    pub(crate) fn init_int_hpow_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self
            .get_const(&Name::from_string("instHPowIntNat"))
            .is_some()
        {
            return Ok(());
        }
        self.init_hpow()?;
        self.init_int_arith()?;
        self.init_nat()?;
        self.add_hetero3_instance(
            "instHPowIntNat",
            "HPow",
            "HPow.mk",
            "Int",
            "Nat",
            "Int",
            "Int.pow",
        )?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHPowIntNat"),
            class_name: Name::from_string("HPow"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Initialize the HAnd heterogeneous typeclass
    ///
    /// ```text
    /// class HAnd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hAnd : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hand_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hand(&mut self) -> Result<(), EnvError> {
        if self.hand_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HAND_FLAVOR)?;
        self.hand_init = true;
        Ok(())
    }

    /// Check if HAnd typeclass has been initialized
    pub(crate) fn has_hand(&self) -> bool {
        self.hand_init
    }

    /// Initialize the HOr heterogeneous typeclass
    ///
    /// ```text
    /// class HOr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hOr : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hor_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hor(&mut self) -> Result<(), EnvError> {
        if self.hor_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HOR_FLAVOR)?;
        self.hor_init = true;
        Ok(())
    }

    /// Check if HOr typeclass has been initialized
    pub(crate) fn has_hor(&self) -> bool {
        self.hor_init
    }

    /// Initialize the HXor heterogeneous typeclass
    ///
    /// ```text
    /// class HXor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hXor : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hxor_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hxor(&mut self) -> Result<(), EnvError> {
        if self.hxor_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HXOR_FLAVOR)?;
        self.hxor_init = true;
        Ok(())
    }

    /// Check if HXor typeclass has been initialized
    pub(crate) fn has_hxor(&self) -> bool {
        self.hxor_init
    }

    /// Initialize the HShiftLeft heterogeneous typeclass
    ///
    /// ```text
    /// class HShiftLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hShiftLeft : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hshiftleft_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hshiftleft(&mut self) -> Result<(), EnvError> {
        if self.hshiftleft_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HSHIFTLEFT_FLAVOR)?;
        self.hshiftleft_init = true;
        Ok(())
    }

    /// Check if HShiftLeft typeclass has been initialized
    pub(crate) fn has_hshiftleft(&self) -> bool {
        self.hshiftleft_init
    }

    /// Initialize the HShiftRight heterogeneous typeclass
    ///
    /// ```text
    /// class HShiftRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    ///   hShiftRight : α → β → γ
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hshiftright_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_hshiftright(&mut self) -> Result<(), EnvError> {
        if self.hshiftright_init {
            return Ok(());
        }
        self.init_hetero_op_with_flavor(HSHIFTRIGHT_FLAVOR)?;
        self.hshiftright_init = true;
        Ok(())
    }

    /// Check if HShiftRight typeclass has been initialized
    pub(crate) fn has_hshiftright(&self) -> bool {
        self.hshiftright_init
    }

    /// Initialize the instHAndNat instance: `HAnd Nat Nat Nat` backed by `Nat.land`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hand_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hand_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_hand_inst_init {
            return Ok(());
        }
        self.init_hand()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHAndNat", "HAnd", "HAnd.mk", "Nat", "Nat.land")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAndNat"),
            class_name: Name::from_string("HAnd"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.nat_hand_inst_init = true;
        Ok(())
    }

    /// Check if Nat HAnd instance has been initialized
    pub(crate) fn has_nat_hand_inst(&self) -> bool {
        self.nat_hand_inst_init
    }

    /// Initialize the instHOrNat instance: `HOr Nat Nat Nat` backed by `Nat.lor`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hor_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hor_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_hor_inst_init {
            return Ok(());
        }
        self.init_hor()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHOrNat", "HOr", "HOr.mk", "Nat", "Nat.lor")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHOrNat"),
            class_name: Name::from_string("HOr"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.nat_hor_inst_init = true;
        Ok(())
    }

    /// Check if Nat HOr instance has been initialized
    pub(crate) fn has_nat_hor_inst(&self) -> bool {
        self.nat_hor_inst_init
    }

    /// Initialize the instHXorNat instance: `HXor Nat Nat Nat` backed by `Nat.xor`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hxor_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hxor_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_hxor_inst_init {
            return Ok(());
        }
        self.init_hxor()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance("instHXorNat", "HXor", "HXor.mk", "Nat", "Nat.xor")?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHXorNat"),
            class_name: Name::from_string("HXor"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.nat_hxor_inst_init = true;
        Ok(())
    }

    /// Check if Nat HXor instance has been initialized
    pub(crate) fn has_nat_hxor_inst(&self) -> bool {
        self.nat_hxor_inst_init
    }

    /// Initialize the instHShiftLeftNat instance: `HShiftLeft Nat Nat Nat`
    /// backed by `Nat.shiftLeft`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hshiftleft_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hshiftleft_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_hshiftleft_inst_init {
            return Ok(());
        }
        self.init_hshiftleft()?;
        self.init_nat()?;
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): `instHShiftLeftNat` wraps the import-gated
        // `Nat.shiftLeft` seed (absent at init time; Clean's multiply-last
        // Nat.rec spelling is not defeq to Lean's brecOn multiply-first
        // tower), so the instance is gated with it (see data_types_nat.rs).
        // The `HShiftLeft` class itself stays in both lanes; imported oleans
        // carry Lean's own genuine Nat shift instances.
        if !self.suppress_lossy_structure_stubs {
            self.add_homogeneous_hetero_instance(
                "instHShiftLeftNat",
                "HShiftLeft",
                "HShiftLeft.mk",
                "Nat",
                "Nat.shiftLeft",
            )?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instHShiftLeftNat"),
                class_name: Name::from_string("HShiftLeft"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }
        self.nat_hshiftleft_inst_init = true;
        Ok(())
    }

    /// Check if Nat HShiftLeft instance has been initialized
    pub(crate) fn has_nat_hshiftleft_inst(&self) -> bool {
        self.nat_hshiftleft_inst_init
    }

    /// Initialize the instHShiftRightNat instance: `HShiftRight Nat Nat Nat`
    /// backed by `Nat.shiftRight`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_hshiftright_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_hshiftright_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_hshiftright_inst_init {
            return Ok(());
        }
        self.init_hshiftright()?;
        self.init_nat()?;
        self.add_homogeneous_hetero_instance(
            "instHShiftRightNat",
            "HShiftRight",
            "HShiftRight.mk",
            "Nat",
            "Nat.shiftRight",
        )?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHShiftRightNat"),
            class_name: Name::from_string("HShiftRight"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        self.nat_hshiftright_inst_init = true;
        Ok(())
    }

    /// Check if Nat HShiftRight instance has been initialized
    pub(crate) fn has_nat_hshiftright_inst(&self) -> bool {
        self.nat_hshiftright_inst_init
    }
}
