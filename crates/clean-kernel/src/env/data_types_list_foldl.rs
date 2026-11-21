// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Canonical, universe-polymorphic equation for the actual List.foldl body.
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn foldl_cons(changed: bool) -> Declaration {
    let u_name = Name::from_string("u");
    let v_name = Name::from_string("v");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let type_u = Expr::sort(Level::succ(u.clone()));
    let type_v = Expr::sort(Level::succ(v.clone()));
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
    let (beta_id, beta) = b.fresh_local(type_v.clone());
    let (a_id, a) = b.fresh_local(alpha.clone());
    let list_alpha = Expr::app(
        Expr::const_(Name::from_string("List"), vec![u.clone()]),
        alpha.clone(),
    );
    let (l_id, l) = b.fresh_local(list_alpha.clone());
    let f_ty = Expr::pi(
        BinderInfo::Default,
        beta.clone(),
        Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone()),
    );
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (acc_id, acc) = b.fresh_local(beta.clone());
    let cons = Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![u.clone()]),
        [alpha.clone(), a.clone(), l.clone()],
    );
    // foldl's accumulator comes first; this theorem's element parameter
    // comes first. Both type and universe arguments must therefore reverse.
    let foldl = Expr::const_(Name::from_string("List.foldl"), vec![v.clone(), u]);
    let lhs = Expr::apps(
        foldl.clone(),
        [beta.clone(), alpha.clone(), f.clone(), acc.clone(), cons],
    );
    let next = if changed {
        acc.clone()
    } else {
        Expr::apps(f.clone(), [acc, a])
    };
    let rhs = Expr::apps(foldl, [beta.clone(), alpha.clone(), f, next, l]);
    let eq_level = Level::succ(v);
    let mut type_ = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![eq_level.clone()]),
        [beta.clone(), lhs.clone(), rhs],
    );
    let mut value = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![eq_level]),
        [beta.clone(), lhs],
    );
    for (id, domain) in [
        (acc_id, beta),
        (f_id, f_ty),
        (l_id, list_alpha),
        (a_id, alpha),
        (beta_id, type_v),
        (alpha_id, type_u),
    ] {
        type_ = b.mk_pi(id, BinderInfo::Implicit, domain.clone(), type_);
        value = b.mk_lam(id, BinderInfo::Implicit, domain, value);
    }
    Declaration::Theorem {
        name: Name::from_string("List.foldl_cons"),
        level_params: vec![u_name, v_name],
        type_: b.finish(type_),
        value: b.finish(value),
    }
}
impl Environment {
    pub(crate) fn register_list_foldl_cons(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_list()?;
        self.init_eq()?;
        self.ensure_exact_checked_decl(foldl_cons(false))
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::ReferenceKernel;
    #[test]
    fn foldl_cons_is_checked_axiom_free_and_idempotent() {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("List.foldl_cons");
        let info = env.get_const(&name).expect("actual fold equation");
        assert!(info.value.is_some());
        assert_eq!(
            info.level_params,
            vec![Name::from_string("u"), Name::from_string("v")]
        );
        assert!(env.axiom_deps(&name).expect("closure").is_empty());
        let before = (env.num_constants(), env.num_instances());
        env.register_list_foldl_cons()
            .expect("idempotent registration");
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
    #[test]
    fn foldl_cons_preserves_checked_import_ownership() {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        env.register_list_foldl_cons().expect("import suppression");
        assert!(env
            .get_const(&Name::from_string("List.foldl_cons"))
            .is_none());
    }
    #[test]
    fn reference_replays_polymorphic_fold_and_refuses_original_proof_without_step() {
        let mut reference =
            ReferenceKernel::new(Environment::with_prelude()).expect("reference theory");
        let Declaration::Theorem {
            name,
            level_params,
            type_,
            ..
        } = foldl_cons(false)
        else {
            unreachable!()
        };
        let levels = level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>();
        let alias = Name::from_string("foldl_cons_reference");
        reference
            .add_checked(Declaration::Theorem {
                name: alias.clone(),
                level_params: level_params.clone(),
                type_,
                value: Expr::const_(name.clone(), levels.clone()),
            })
            .expect("actual universe-polymorphic proof");
        assert!(reference
            .environment()
            .axiom_deps(&alias)
            .expect("closure")
            .is_empty());
        let Declaration::Theorem { type_, .. } = foldl_cons(true) else {
            unreachable!()
        };
        let before = (
            reference.environment().num_constants(),
            reference.environment().num_instances(),
        );
        let mutant = Name::from_string("foldl_cons_dropped_step");
        assert!(reference
            .add_checked(Declaration::Theorem {
                name: mutant.clone(),
                level_params,
                type_,
                value: Expr::const_(name, levels),
            })
            .is_err());
        assert!(reference.environment().get_const(&mutant).is_none());
        assert_eq!(
            (
                reference.environment().num_constants(),
                reference.environment().num_instances()
            ),
            before
        );
    }
}
