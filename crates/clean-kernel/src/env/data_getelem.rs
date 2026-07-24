// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `GetElem` / `GetElem?` indexing classes (Brick P1 — unregistered
//! prelude heads).
//!
//! Registers the Lean 4 core classes behind `xs[i]` / `xs[i]?` / `xs[i]!` /
//! `xs[i]'h` as fully kernel-checked single-constructor structures (no
//! axioms) plus their projections:
//!
//! ```text
//! class GetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
//!               (valid : outParam (coll → idx → Prop)) where
//!   getElem (xs : coll) (i : idx) (h : valid xs i) : elem
//!
//! class GetElem? (coll : Type u) (idx : Type v) (elem : outParam (Type w))
//!     (valid : outParam (coll → idx → Prop)) extends GetElem coll idx elem valid where
//!   getElem? : coll → idx → Option elem
//!   getElem! [Inhabited elem] (xs : coll) (i : idx) : elem
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`): `Init/GetElem.lean:69`
//! (`GetElem`), `:94` (`GetElem?`). `elem` and `valid` are outParams in both.
//!
//! Instances are DESCOPED here: Lean's `instance : GetElem (List α) Nat α
//! fun as i => i < as.length` (`Init/GetElem.lean:293`) is backed by
//! `List.get : (as : List α) → Fin as.length → α`, which Clean's prelude does
//! not carry (only `List.get?` exists — verified by grep), so an honest
//! instance body is not constructible today. With classes + projections
//! registered, `xs[i]`-family probes fail LOUD at instance resolution instead
//! of `TooManyArguments { Sort(u) }` (audit rows c01–c04 in
//! `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`), and the no-proof `xs[0]`
//! z-probe stays rejected.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The shared `{coll} {idx} {elem} {valid}` telescope: allocates the four
/// param locals in `b` and returns them (with their types) for reuse.
struct GetElemParams {
    coll_id: crate::expr::FVarId,
    coll: Expr,
    idx_id: crate::expr::FVarId,
    idx: Expr,
    elem_id: crate::expr::FVarId,
    elem: Expr,
    valid_id: crate::expr::FVarId,
    valid: Expr,
    type_u: Expr,
    type_v: Expr,
    type_w: Expr,
    valid_ty: Expr,
}

fn getelem_params(b: &mut EnvDeclBuilder, u: &Level, v: &Level, w: &Level) -> GetElemParams {
    let type_u = Expr::sort(Level::succ(u.clone()));
    let type_v = Expr::sort(Level::succ(v.clone()));
    let type_w = Expr::sort(Level::succ(w.clone()));
    let (coll_id, coll) = b.fresh_local(type_u.clone());
    let (idx_id, idx) = b.fresh_local(type_v.clone());
    let (elem_id, elem) = b.fresh_local(type_w.clone());
    // valid : coll → idx → Prop
    let valid_ty = Expr::pi(
        BinderInfo::Default,
        coll.clone(),
        Expr::pi(BinderInfo::Default, idx.clone(), Expr::sort(Level::zero())),
    );
    let (valid_id, valid) = b.fresh_local(valid_ty.clone());
    GetElemParams {
        coll_id,
        coll,
        idx_id,
        idx,
        elem_id,
        elem,
        valid_id,
        valid,
        type_u,
        type_v,
        type_w,
        valid_ty,
    }
}

/// Close `body` under the four implicit class-parameter binders.
fn close_params_pi(b: &mut EnvDeclBuilder, p: &GetElemParams, body: Expr) -> Expr {
    let r = b.mk_pi(p.valid_id, BinderInfo::Implicit, p.valid_ty.clone(), body);
    let r = b.mk_pi(p.elem_id, BinderInfo::Implicit, p.type_w.clone(), r);
    let r = b.mk_pi(p.idx_id, BinderInfo::Implicit, p.type_v.clone(), r);
    b.mk_pi(p.coll_id, BinderInfo::Implicit, p.type_u.clone(), r)
}

/// Close `body` under the four implicit class-parameter LAMBDA binders.
fn close_params_lam(b: &mut EnvDeclBuilder, p: &GetElemParams, body: Expr) -> Expr {
    let r = b.mk_lam(p.valid_id, BinderInfo::Implicit, p.valid_ty.clone(), body);
    let r = b.mk_lam(p.elem_id, BinderInfo::Implicit, p.type_w.clone(), r);
    let r = b.mk_lam(p.idx_id, BinderInfo::Implicit, p.type_v.clone(), r);
    b.mk_lam(p.coll_id, BinderInfo::Implicit, p.type_u.clone(), r)
}

/// `(xs : coll) → (i : idx) → valid xs i → elem` — the `getElem` field type.
fn getelem_field_ty(parent: &EnvDeclBuilder, p: &GetElemParams) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (xs_id, xs) = c.fresh_local(p.coll.clone());
    let (i_id, i) = c.fresh_local(p.idx.clone());
    let valid_xs_i = Expr::apps(p.valid.clone(), [xs, i]);
    let (h_id, _h) = c.fresh_local(valid_xs_i.clone());
    let r = p.elem.clone();
    let r = c.mk_pi(h_id, BinderInfo::Default, valid_xs_i, r);
    let r = c.mk_pi(i_id, BinderInfo::Default, p.idx.clone(), r);
    let r = c.mk_pi(xs_id, BinderInfo::Default, p.coll.clone(), r);
    c.finish_child(r)
}

/// `coll → idx → Option elem` — the `getElem?` field type.
fn getelem_opt_field_ty(parent: &EnvDeclBuilder, p: &GetElemParams, w: &Level) -> Expr {
    let option_elem = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![w.clone()]),
        p.elem.clone(),
    );
    let mut c = EnvDeclBuilder::child_of(parent);
    let (xs_id, _xs) = c.fresh_local(p.coll.clone());
    let (i_id, _i) = c.fresh_local(p.idx.clone());
    let r = option_elem;
    let r = c.mk_pi(i_id, BinderInfo::Default, p.idx.clone(), r);
    let r = c.mk_pi(xs_id, BinderInfo::Default, p.coll.clone(), r);
    c.finish_child(r)
}

/// `[Inhabited elem] → coll → idx → elem` — the `getElem!` field type.
fn getelem_bang_field_ty(parent: &EnvDeclBuilder, p: &GetElemParams, w: &Level) -> Expr {
    // elem : Type w = Sort (w+1), so `Inhabited elem` instantiates the
    // `Sort u`-polymorphic Inhabited at level w+1.
    let inhabited_elem = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), vec![Level::succ(w.clone())]),
        p.elem.clone(),
    );
    let mut c = EnvDeclBuilder::child_of(parent);
    let (inst_id, _inst) = c.fresh_local(inhabited_elem.clone());
    let (xs_id, _xs) = c.fresh_local(p.coll.clone());
    let (i_id, _i) = c.fresh_local(p.idx.clone());
    let r = p.elem.clone();
    let r = c.mk_pi(i_id, BinderInfo::Default, p.idx.clone(), r);
    let r = c.mk_pi(xs_id, BinderInfo::Default, p.coll.clone(), r);
    let r = c.mk_pi(inst_id, BinderInfo::InstImplicit, inhabited_elem, r);
    c.finish_child(r)
}

impl Environment {
    /// Register the `GetElem` and `GetElem?` classes and their projections
    /// (`GetElem.getElem`, `GetElem?.toGetElem`, `GetElem?.getElem?`,
    /// `GetElem?.getElem!`), all as fully-checked declarations.
    ///
    /// Lean fidelity: `Init/GetElem.lean:69/94` — four parameters with `elem`
    /// and `valid` outParams; `GetElem?` extends `GetElem` (mirrored as the
    /// leading `toGetElem` constructor field, Lean's own encoding); the
    /// `getElem!` field carries the `[Inhabited elem]` instance binder (its
    /// Lean default value only affects `where` blocks that omit the field,
    /// not the constructor arity mirrored here). `GetElem?.toGetElem` is
    /// registered as a projection Definition but NOT entered in the kernel
    /// instance table (no premise-carrying synthesis today; staged with the
    /// descoped instances).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.getelem_classes_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_getelem_classes(&mut self) -> Result<(), EnvError> {
        if self.getelem_classes_init {
            return Ok(());
        }

        // getElem? references Option, getElem! references Inhabited.
        self.init_option()?;
        self.init_inhabited()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let w_level = Level::param(w.clone());
        let level_params = vec![u.clone(), v.clone(), w.clone()];
        let levels = vec![u_level.clone(), v_level.clone(), w_level.clone()];
        // Type (max u v w) — result universe of both class formers.
        let result_sort = Expr::sort(Level::succ(Level::max(
            u_level.clone(),
            Level::max(v_level.clone(), w_level.clone()),
        )));

        let getelem_name = Name::from_string("GetElem");
        let getelem_opt_name = Name::from_string("GetElem?");
        let getelem_const = Expr::const_(getelem_name.clone(), levels.clone());
        let getelem_opt_const = Expr::const_(getelem_opt_name.clone(), levels.clone());

        // Class former: (coll : Type u) → (idx : Type v) → (elem : Type w) →
        //               (valid : coll → idx → Prop) → Type (max u v w)
        let class_former_ty = |b_result: Expr| {
            let mut b = EnvDeclBuilder::new();
            let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
            let r = b.mk_pi(
                p.valid_id,
                BinderInfo::Default,
                p.valid_ty.clone(),
                b_result,
            );
            let r = b.mk_pi(p.elem_id, BinderInfo::Default, p.type_w.clone(), r);
            let r = b.mk_pi(p.idx_id, BinderInfo::Default, p.type_v.clone(), r);
            let r = b.mk_pi(p.coll_id, BinderInfo::Default, p.type_u.clone(), r);
            b.finish(r)
        };

        // ---- GetElem ----
        let getelem_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
            let field_ty = getelem_field_ty(&b, &p);
            let (field_id, _) = b.fresh_local(field_ty.clone());
            let class_ty = Expr::apps(
                getelem_const.clone(),
                [
                    p.coll.clone(),
                    p.idx.clone(),
                    p.elem.clone(),
                    p.valid.clone(),
                ],
            );
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_ty);
            let r = close_params_pi(&mut b, &p, r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: level_params.clone(),
            num_params: 4,
            types: vec![InductiveType {
                name: getelem_name.clone(),
                type_: class_former_ty(result_sort.clone()),
                constructors: vec![Constructor {
                    name: Name::from_string("GetElem.mk"),
                    type_: getelem_ctor_type,
                }],
            }],
        })?;

        self.register_structure_fields(getelem_name.clone(), vec![Name::from_string("getElem")])?;
        self.register_class(KernelClassInfo {
            name: getelem_name.clone(),
            num_params: 4,
            out_params: vec![2, 3],
            semi_out_params: vec![],
        });

        // GetElem.getElem : {coll idx elem valid} → [self] → (xs) → (i) → (h) → elem
        {
            let proj_type = {
                let mut b = EnvDeclBuilder::new();
                let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
                let class_ty = Expr::apps(
                    getelem_const.clone(),
                    [
                        p.coll.clone(),
                        p.idx.clone(),
                        p.elem.clone(),
                        p.valid.clone(),
                    ],
                );
                let (inst_id, _) = b.fresh_local(class_ty.clone());
                let field_ty = getelem_field_ty(&b, &p);
                let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, field_ty);
                let r = close_params_pi(&mut b, &p, r);
                b.finish(r)
            };
            let proj_value = {
                let mut b = EnvDeclBuilder::new();
                let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
                let class_ty = Expr::apps(
                    getelem_const.clone(),
                    [
                        p.coll.clone(),
                        p.idx.clone(),
                        p.elem.clone(),
                        p.valid.clone(),
                    ],
                );
                let (inst_id, inst) = b.fresh_local(class_ty.clone());
                let body = Expr::proj(getelem_name.clone(), 0, inst);
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
                let r = close_params_lam(&mut b, &p, r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("GetElem.getElem"),
                level_params: level_params.clone(),
                type_: proj_type,
                value: proj_value,
                is_reducible: true,
            })?;
        }

        // ---- GetElem? (extends GetElem) ----
        let getelem_opt_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
            let parent_ty = Expr::apps(
                getelem_const.clone(),
                [
                    p.coll.clone(),
                    p.idx.clone(),
                    p.elem.clone(),
                    p.valid.clone(),
                ],
            );
            let (parent_id, _) = b.fresh_local(parent_ty.clone());
            let opt_ty = getelem_opt_field_ty(&b, &p, &w_level);
            let (opt_id, _) = b.fresh_local(opt_ty.clone());
            let bang_ty = getelem_bang_field_ty(&b, &p, &w_level);
            let (bang_id, _) = b.fresh_local(bang_ty.clone());
            let class_ty = Expr::apps(
                getelem_opt_const.clone(),
                [
                    p.coll.clone(),
                    p.idx.clone(),
                    p.elem.clone(),
                    p.valid.clone(),
                ],
            );
            let r = b.mk_pi(bang_id, BinderInfo::Default, bang_ty, class_ty);
            let r = b.mk_pi(opt_id, BinderInfo::Default, opt_ty, r);
            let r = b.mk_pi(parent_id, BinderInfo::Default, parent_ty, r);
            let r = close_params_pi(&mut b, &p, r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: level_params.clone(),
            num_params: 4,
            types: vec![InductiveType {
                name: getelem_opt_name.clone(),
                type_: class_former_ty(result_sort),
                constructors: vec![Constructor {
                    name: Name::from_string("GetElem?.mk"),
                    type_: getelem_opt_ctor_type,
                }],
            }],
        })?;

        self.register_structure_fields(
            getelem_opt_name.clone(),
            vec![
                Name::from_string("toGetElem"),
                Name::from_string("getElem?"),
                Name::from_string("getElem!"),
            ],
        )?;
        self.register_class(KernelClassInfo {
            name: getelem_opt_name.clone(),
            num_params: 4,
            out_params: vec![2, 3],
            semi_out_params: vec![],
        });

        // Projections over GetElem?.
        for (proj_name, field_idx) in [
            ("GetElem?.toGetElem", 0u32),
            ("GetElem?.getElem?", 1u32),
            ("GetElem?.getElem!", 2u32),
        ] {
            let proj_type = {
                let mut b = EnvDeclBuilder::new();
                let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
                let class_ty = Expr::apps(
                    getelem_opt_const.clone(),
                    [
                        p.coll.clone(),
                        p.idx.clone(),
                        p.elem.clone(),
                        p.valid.clone(),
                    ],
                );
                let (inst_id, _) = b.fresh_local(class_ty.clone());
                let field_ty = match field_idx {
                    0 => Expr::apps(
                        getelem_const.clone(),
                        [
                            p.coll.clone(),
                            p.idx.clone(),
                            p.elem.clone(),
                            p.valid.clone(),
                        ],
                    ),
                    1 => getelem_opt_field_ty(&b, &p, &w_level),
                    _ => getelem_bang_field_ty(&b, &p, &w_level),
                };
                let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, field_ty);
                let r = close_params_pi(&mut b, &p, r);
                b.finish(r)
            };
            let proj_value = {
                let mut b = EnvDeclBuilder::new();
                let p = getelem_params(&mut b, &u_level, &v_level, &w_level);
                let class_ty = Expr::apps(
                    getelem_opt_const.clone(),
                    [
                        p.coll.clone(),
                        p.idx.clone(),
                        p.elem.clone(),
                        p.valid.clone(),
                    ],
                );
                let (inst_id, inst) = b.fresh_local(class_ty.clone());
                let body = Expr::proj(getelem_opt_name.clone(), field_idx, inst);
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
                let r = close_params_lam(&mut b, &p, r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(proj_name),
                level_params: level_params.clone(),
                type_: proj_type,
                value: proj_value,
                is_reducible: true,
            })?;
        }

        self.getelem_classes_init = true;
        Ok(())
    }
}
