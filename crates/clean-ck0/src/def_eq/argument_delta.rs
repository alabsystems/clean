//! Exact checked argument-only delta/beta before expensive height scheduling.
use super::*;
use crate::validate::Transparency;

/// A checked transparent `fun ... => argument` can take one exact delta/beta
/// step before unfolding a higher definition opposite it. This avoids forcing
/// an expensive argument merely to remove a definitionally trivial wrapper.
pub(super) fn reduce(
    env: &dyn Env,
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Const(c) = head.kind() else {
        return Ok(None);
    };
    let Some(def) = env.const_def(c.name()) else {
        return Ok(None);
    };
    if def.transparency != Transparency::Transparent {
        return Ok(None);
    }
    let mut body = &def.body;
    let mut binders = 0usize;
    while let TermKind::Lam(_, _, next) = body.kind() {
        budget.step()?;
        binders = binders.checked_add(1).ok_or(BudgetError::OutOfBudget)?;
        body = next;
    }
    let TermKind::BVar(index) = body.kind() else {
        return Ok(None);
    };
    let index = usize::try_from(*index).unwrap_or(usize::MAX);
    if args.len() < binders || index >= binders {
        return Ok(None);
    }
    let Some(position) = binders.checked_sub(1).and_then(|n| n.checked_sub(index)) else {
        return Ok(None);
    };
    Ok(Some(Term::apply(args[position].clone(), &args[binders..])))
}

#[cfg(all(test, feature = "export"))]
mod tests {
    use super::*;
    use crate::{Level, MinimalEnv};

    #[test]
    fn argument_wrapper_does_not_force_its_expensive_argument() {
        let a = Name::from_dotted("A");
        let x = Name::from_dotted("x");
        let y = Name::from_dotted("y");
        let ty = Term::native_const(a.clone());
        let mut env = MinimalEnv::new()
            .with_const_typed(a, 0, Term::sort(Level::nat(1)))
            .with_const_typed(x.clone(), 0, ty.clone())
            .with_const_typed(y.clone(), 0, ty.clone());
        let mut last = x;
        for i in 0..600 {
            let name = Name::from_dotted(&format!("expensive{i}"));
            env = env.with_def(
                name.clone(),
                0,
                ty.clone(),
                Term::native_const(last),
                Transparency::Transparent,
            );
            env.set_delta_priority(name.clone(), 2);
            last = name;
        }
        let wrapper = Name::from_dotted("wrapper");
        env = env.with_def(
            wrapper.clone(),
            0,
            Term::pi(BinderInfo::Default, ty.clone(), ty.clone()),
            Term::lam(BinderInfo::Default, ty, Term::bvar(0)),
            Transparency::Transparent,
        );
        env.set_delta_priority(wrapper.clone(), 1);
        let expensive = Term::native_const(last);
        let wrap = |arg| Term::app(Term::native_const(wrapper.clone()), arg);
        assert_eq!(
            is_def_eq(
                &env,
                &expensive,
                &wrap(expensive.clone()),
                &mut Budget::new(512)
            ),
            Ok(true)
        );
        // The same checked reduction still exposes distinct data as distinct.
        assert_eq!(
            is_def_eq(
                &env,
                &expensive,
                &wrap(Term::native_const(y)),
                &mut Budget::new(100_000)
            ),
            Ok(false)
        );
    }
    #[test]
    fn argument_wrapper_exposes_beta_redex_before_comparison() {
        let a = Name::from_dotted("A");
        let x = Name::from_dotted("x");
        let high = Name::from_dotted("high");
        let wrapper = Name::from_dotted("wrapper");
        let ty = Term::native_const(a.clone());
        let mut env = MinimalEnv::new()
            .with_const_typed(a, 0, Term::sort(Level::nat(1)))
            .with_const_typed(x.clone(), 0, ty.clone())
            .with_def(
                high.clone(),
                0,
                ty.clone(),
                Term::native_const(x.clone()),
                Transparency::Transparent,
            )
            .with_def(
                wrapper.clone(),
                0,
                Term::pi(BinderInfo::Default, ty.clone(), ty.clone()),
                Term::lam(BinderInfo::Default, ty.clone(), Term::bvar(0)),
                Transparency::Transparent,
            );
        env.set_delta_priority(high.clone(), 2);
        env.set_delta_priority(wrapper.clone(), 1);
        let beta = Term::app(
            Term::lam(BinderInfo::Default, ty, Term::bvar(0)),
            Term::native_const(x),
        );
        assert_eq!(
            is_def_eq(
                &env,
                &Term::native_const(high),
                &Term::app(Term::native_const(wrapper), beta),
                &mut Budget::new(512)
            ),
            Ok(true)
        );
    }
}
