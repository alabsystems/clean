// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! if-then-else (`ite`) definition
//!
//! Split from `logic_decidable.rs` for maintainability and to keep logic env
//! files under the 500-line limit.

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize `ite : {α : Sort u} → (c : Prop) → [Decidable c] → α → α → α`.
    ///
    /// The body is the standard reducible definition:
    /// `Decidable.casesOn c (fun _ => α) (fun _ => b) (fun _ => a) h`.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.ite_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub fn init_ite(&mut self) -> Result<(), EnvError> {
        if self.ite_init {
            return Ok(());
        }

        self.init_decidable()?;

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);
        let ite_type = build_ite_type(&sort_u, &prop, &decidable_const);
        let ite_value = self.build_ite_value(&u, &sort_u, &prop, &decidable_const)?;

        self.add_decl(Declaration::Definition {
            name: Name::from_string("ite"),
            level_params: vec![u],
            type_: ite_type,
            value: ite_value,
            is_reducible: true,
        })?;

        self.ite_init = true;
        Ok(())
    }

    /// Check if `ite` has been initialized.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_ite()` has completed successfully
    #[cfg(test)]
    pub(crate) fn has_ite(&self) -> bool {
        self.ite_init
    }

    /// Initialize `dite : {α : Sort u} → (c : Prop) → [Decidable c] →
    /// (t : c → α) → (e : ¬c → α) → α`.
    ///
    /// Body (v4.30-faithful): `@Decidable.casesOn.{u} c (fun _ => α) h e t`.
    /// Backs the UInt `decLe`/`decLt` and `Char.ofNat` dite forms. Idempotent.
    pub(crate) fn init_dite(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("dite")).is_some() {
            return Ok(());
        }
        self.init_decidable()?;
        self.init_true_false()?; // Not / False

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let not_c = |c: Expr| Expr::app(Expr::const_(Name::from_string("Not"), vec![]), c);

        // type: {α}(c)[h : Decidable c](t : c → α)(e : ¬c → α) → α
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (c_id, c) = b.fresh_local(prop.clone());
            let dec_c = Expr::app(dec.clone(), c.clone());
            let (h_id, _h) = b.fresh_local(dec_c.clone());
            let t_ty = Expr::pi(BinderInfo::Default, c.clone(), alpha.clone());
            let (t_id, _t) = b.fresh_local(t_ty.clone());
            let e_ty = Expr::pi(BinderInfo::Default, not_c(c.clone()), alpha.clone());
            let (e_id, _e) = b.fresh_local(e_ty.clone());
            let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, alpha.clone());
            let r = b.mk_pi(t_id, BinderInfo::Default, t_ty, r);
            let r = b.mk_pi(h_id, BinderInfo::InstImplicit, dec_c, r);
            let r = b.mk_pi(c_id, BinderInfo::Default, prop.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };
        // value: fun {α} c h t e => @Decidable.casesOn.{u} c (fun _ => α) h e t
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (c_id, c) = b.fresh_local(prop.clone());
            let dec_c = Expr::app(dec.clone(), c.clone());
            let (h_id, h) = b.fresh_local(dec_c.clone());
            let t_ty = Expr::pi(BinderInfo::Default, c.clone(), alpha.clone());
            let (t_id, t) = b.fresh_local(t_ty.clone());
            let e_ty = Expr::pi(BinderInfo::Default, not_c(c.clone()), alpha.clone());
            let (e_id, e) = b.fresh_local(e_ty.clone());
            let motive = {
                let mut child = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = child.fresh_local(dec_c.clone());
                child.finish_child(child.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    dec_c.clone(),
                    alpha.clone(),
                ))
            };
            let body = Expr::apps(
                Expr::const_(
                    Name::from_string("Decidable.casesOn"),
                    vec![Level::param(u.clone())],
                ),
                [c.clone(), motive, h, e, t],
            );
            let r = b.mk_lam(e_id, BinderInfo::Default, e_ty, body);
            let r = b.mk_lam(t_id, BinderInfo::Default, t_ty, r);
            let r = b.mk_lam(h_id, BinderInfo::InstImplicit, dec_c, r);
            let r = b.mk_lam(c_id, BinderInfo::Default, prop.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("dite"),
            level_params: vec![u],
            type_: ty,
            value,
            is_reducible: true,
        })?;
        Ok(())
    }

    fn decidable_is_false_argument_type(&self, cond: &Expr) -> Result<Expr, EnvError> {
        let decl_name = Name::from_string("Decidable.isFalse");
        let is_false =
            self.get_const(&decl_name)
                .ok_or_else(|| EnvError::MissingRequiredDeclaration {
                    init: "init_ite",
                    decl: decl_name.clone(),
                })?;
        let after_param = match is_false.type_.kind() {
            ExprKind::Pi(_, _, body) => body.instantiate(cond),
            _ => {
                return Err(EnvError::InvalidDeclarationShape {
                    init: "init_ite",
                    decl: decl_name.clone(),
                    detail: "Π (p : Prop), Π (_ : p → False), Decidable p",
                });
            }
        };
        match after_param.kind() {
            ExprKind::Pi(_, domain, _) => Ok(domain.as_ref().clone()),
            _ => Err(EnvError::InvalidDeclarationShape {
                init: "init_ite",
                decl: decl_name,
                detail: "Π (p : Prop), Π (_ : p → False), Decidable p",
            }),
        }
    }

    fn build_ite_value(
        &self,
        u: &Name,
        sort_u: &Expr,
        prop: &Expr,
        decidable_const: &Expr,
    ) -> Result<Expr, EnvError> {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
        let (cond_id, cond) = b.fresh_local(prop.clone());
        let decidable_cond = Expr::app(decidable_const.clone(), cond.clone());
        let (inst_id, inst) = b.fresh_local(decidable_cond.clone());
        let (then_id, then_val) = b.fresh_local(alpha.clone());
        let (else_id, else_val) = b.fresh_local(alpha.clone());

        let false_case_arg_ty = self.decidable_is_false_argument_type(&cond)?;
        let motive = ite_motive(&b, &decidable_cond, &alpha);
        let false_case = ite_branch_lambda(&b, &false_case_arg_ty, &else_val);
        let true_case = ite_branch_lambda(&b, &cond, &then_val);
        let body = ite_cases_on_body(u, &cond, motive, false_case, true_case, inst);

        let value = b.mk_lam(else_id, BinderInfo::Default, alpha.clone(), body);
        let value = b.mk_lam(then_id, BinderInfo::Default, alpha.clone(), value);
        let value = b.mk_lam(inst_id, BinderInfo::InstImplicit, decidable_cond, value);
        let value = b.mk_lam(cond_id, BinderInfo::Default, prop.clone(), value);
        let value = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), value);
        Ok(b.finish(value))
    }
}

fn build_ite_type(sort_u: &Expr, prop: &Expr, decidable_const: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
    let (cond_id, cond) = b.fresh_local(prop.clone());
    let decidable_cond = Expr::app(decidable_const.clone(), cond);
    let (inst_id, _) = b.fresh_local(decidable_cond.clone());
    let (then_id, _) = b.fresh_local(alpha.clone());
    let (else_id, _) = b.fresh_local(alpha.clone());
    let ty = b.mk_pi(else_id, BinderInfo::Default, alpha.clone(), alpha.clone());
    let ty = b.mk_pi(then_id, BinderInfo::Default, alpha.clone(), ty);
    let ty = b.mk_pi(inst_id, BinderInfo::InstImplicit, decidable_cond, ty);
    let ty = b.mk_pi(cond_id, BinderInfo::Default, prop.clone(), ty);
    b.finish(b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty))
}

fn ite_motive(b: &EnvDeclBuilder, decidable_cond: &Expr, alpha: &Expr) -> Expr {
    let mut child = EnvDeclBuilder::child_of(b);
    let (major_id, _major) = child.fresh_local(decidable_cond.clone());
    let lam = child.mk_lam(
        major_id,
        BinderInfo::Default,
        decidable_cond.clone(),
        alpha.clone(),
    );
    child.finish_child(lam)
}

fn ite_cases_on_body(
    u: &Name,
    cond: &Expr,
    motive: Expr,
    false_case: Expr,
    true_case: Expr,
    inst: Expr,
) -> Expr {
    // Lean-faithful casesOn order: motive, major (inst), then minors.
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Decidable.casesOn"),
                            vec![Level::param(u.clone())],
                        ),
                        cond.clone(),
                    ),
                    motive,
                ),
                inst,
            ),
            false_case,
        ),
        true_case,
    )
}

fn ite_branch_lambda(b: &EnvDeclBuilder, proof_ty: &Expr, branch_val: &Expr) -> Expr {
    let mut child = EnvDeclBuilder::child_of(b);
    let (proof_id, _proof) = child.fresh_local(proof_ty.clone());
    let lam = child.mk_lam(
        proof_id,
        BinderInfo::Default,
        proof_ty.clone(),
        branch_val.clone(),
    );
    child.finish_child(lam)
}
