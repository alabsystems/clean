//! Pair-directed delta scheduling, following pinned Lean's kernel.
use super::*;
use crate::validate::Transparency;
use crate::whnf::{conversion_native, conversion_whnf, try_delta};

fn priority(env: &dyn Env, term: &Term) -> Option<u64> {
    let (head, _) = term.unfold_apps();
    let TermKind::Const(c) = head.kind() else {
        return None;
    };
    let def = env.const_def(c.name())?;
    (def.transparency == Transparency::Transparent).then(|| env.delta_priority(c.name()))
}

pub(super) enum Reduced {
    Answer(bool),
    Retry(Term, Term),
    Stuck(Term, Term),
}

pub(super) fn reduce(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Reduced, BudgetError> {
    let mut a = conversion_whnf(env, ctx, a, budget)?;
    let mut b = conversion_whnf(env, ctx, b, budget)?;
    loop {
        budget.step()?;
        if a == b {
            return Ok(Reduced::Answer(true));
        }
        // Compare a common head's arguments without reducing its body. Never
        // recursively unfold unrelated function heads as an eager congruence
        // prepass: that loses the definitional-height scheduling below.
        let (ah, _) = a.unfold_apps();
        let (bh, _) = b.unfold_apps();
        let (pa, pb) = (priority(env, &a), priority(env, &b));
        // Exact delta/beta on an argument-only wrapper is cheaper than
        // forcing the higher definition opposite it. The body's checked
        // syntax, not an exported hint, licenses this reduction.
        if pa.is_some() && pb.is_some() && pa > pb {
            if let Some(next) = argument_delta::reduce(env, &b, budget)? {
                b = conversion_whnf(env, ctx, &next, budget)?;
                continue;
            }
        }
        if pa.is_some() && pb.is_some() && pb > pa {
            if let Some(next) = argument_delta::reduce(env, &a, budget)? {
                a = conversion_whnf(env, ctx, &next, budget)?;
                continue;
            }
        }
        // Lean's pre-delta argument shortcut is for regular definitions only.
        // A constructor must not force unrelated fields before a projection.
        if ah == bh
            && pa.is_some_and(|p| p > 0 && p < u64::MAX)
            && regular_args_equal(env, ctx, &a, &b, budget)?
        {
            return Ok(Reduced::Answer(true));
        }
        // Offset cancellation is a tail step, not a native recursive call.
        if let Some(step) = offset::step(&a, &b, budget)? {
            return Ok(match step {
                ConversionStep::Answer(answer) => Reduced::Answer(answer),
                ConversionStep::Retry(a, b) => Reduced::Retry(a, b),
            });
        }
        if let Some(next) = conversion_native(env, ctx, &a, budget)? {
            a = conversion_whnf(env, ctx, &next, budget)?;
            continue;
        }
        if let Some(next) = conversion_native(env, ctx, &b, budget)? {
            b = conversion_whnf(env, ctx, &next, budget)?;
            continue;
        }
        if pa.is_none() && pb.is_none() {
            return Ok(Reduced::Stuck(a, b));
        }
        // Pinned Lean's try_unfold_proj_app: expose a method projection on
        // the stuck side before unfolding an expensive definition opposite it.
        // Otherwise a common Nat.sub head can be lost to well-founded recursion.
        if pa.is_some() && pb.is_none() && matches!(bh.kind(), TermKind::Proj(..)) {
            let next = crate::whnf::conversion_project(env, ctx, &b, budget)?;
            if next != b {
                b = next;
                continue;
            }
        }
        if pb.is_some() && pa.is_none() && matches!(ah.kind(), TermKind::Proj(..)) {
            let next = crate::whnf::conversion_project(env, ctx, &a, budget)?;
            if next != a {
                a = next;
                continue;
            }
        }
        if pa.is_some() && (pb.is_none() || pa >= pb) {
            if let Some(next) = try_delta(env, &a)? {
                a = conversion_whnf(env, ctx, &next, budget)?;
            }
        }
        if pb.is_some() && (pa.is_none() || pb >= pa) {
            if let Some(next) = try_delta(env, &b)? {
                b = conversion_whnf(env, ctx, &next, budget)?;
            }
        }
    }
}

// Lean's regular-definition shortcut compares the application spine from
// the outside inward (last argument first), unlike final app congruence.
fn regular_args_equal(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    let (_, aa) = a.unfold_apps();
    let (_, ba) = b.unfold_apps();
    if aa.len() != ba.len() {
        return Ok(false);
    }
    for (x, y) in aa.iter().rev().zip(ba.iter().rev()) {
        if !is_def_eq_at(env, ctx, x, y, budget)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(all(test, feature = "export"))]
mod tests {
    use super::*;
    use crate::{Level, MinimalEnv};

    #[test]
    fn regular_shortcut_checks_last_argument_before_expensive_first() {
        let a = Name::from_dotted("A");
        let x = Name::from_dotted("x");
        let y = Name::from_dotted("y");
        let nat = Term::native_const(Name::from_dotted("Nat"));
        let a_ty = Term::native_const(a.clone());
        let mut env = MinimalEnv::new()
            .with_const_typed(a, 0, Term::sort(Level::nat(1)))
            .with_const_typed(Name::from_dotted("Nat"), 0, Term::sort(Level::nat(1)))
            .with_const_typed(x.clone(), 0, a_ty.clone())
            .with_const_typed(y.clone(), 0, a_ty.clone());
        let mut left = x.clone();
        let mut right = y;
        for i in 0..600 {
            let l = Name::from_dotted(&format!("argLeft{i}"));
            let r = Name::from_dotted(&format!("argRight{i}"));
            env = env
                .with_def(
                    l.clone(),
                    0,
                    a_ty.clone(),
                    Term::native_const(left),
                    Transparency::Transparent,
                )
                .with_def(
                    r.clone(),
                    0,
                    a_ty.clone(),
                    Term::native_const(right),
                    Transparency::Transparent,
                );
            left = l;
            right = r;
        }
        let f = Name::from_dotted("ignoreBoth");
        env = env.with_def(
            f.clone(),
            0,
            Term::pi(
                BinderInfo::Default,
                a_ty.clone(),
                Term::pi(BinderInfo::Default, nat.clone(), a_ty.clone()),
            ),
            Term::lam(
                BinderInfo::Default,
                a_ty,
                Term::lam(BinderInfo::Default, nat, Term::native_const(x)),
            ),
            Transparency::Transparent,
        );
        env.set_delta_priority(f.clone(), 1);
        let apply = |arg, n| {
            Term::apply(
                Term::native_const(f.clone()),
                &[
                    Term::native_const(arg),
                    Term::lit(crate::term::Lit::Nat(crate::BigNat::from_u64(n))),
                ],
            )
        };
        assert_eq!(
            is_def_eq(
                &env,
                &apply(left, 0),
                &apply(right, 1),
                &mut Budget::new(512)
            ),
            Ok(true)
        );
    }

    #[test]
    fn height_scheduling_stops_at_a_common_checked_body() {
        let a = Name::from_dotted("A");
        let x = Name::from_dotted("x");
        let y = Name::from_dotted("y");
        let mut env = MinimalEnv::new()
            .with_const_typed(a.clone(), 0, Term::sort(Level::nat(1)))
            .with_const_typed(x.clone(), 0, Term::native_const(a.clone()))
            .with_const_typed(y.clone(), 0, Term::native_const(a.clone()));
        let mut last = x;
        for i in 0..600 {
            let name = Name::from_dotted(&format!("long{i}"));
            env = env.with_def(
                name.clone(),
                0,
                Term::native_const(a.clone()),
                Term::native_const(last),
                Transparency::Transparent,
            );
            last = name;
        }
        let base = Name::from_dotted("base");
        let wrapper = Name::from_dotted("wrapper");
        env = env
            .with_def(
                base.clone(),
                0,
                Term::native_const(a.clone()),
                Term::native_const(last),
                Transparency::Transparent,
            )
            .with_def(
                wrapper.clone(),
                0,
                Term::native_const(a),
                Term::native_const(base.clone()),
                Transparency::Transparent,
            );
        env.set_delta_priority(base.clone(), 1);
        env.set_delta_priority(wrapper.clone(), 2);
        let w = Term::native_const(wrapper);
        let b = Term::native_const(base);
        assert_eq!(is_def_eq(&env, &w, &b, &mut Budget::new(512)), Ok(true));
        // Even an extreme untrusted scheduling priority cannot equate data.
        env.set_delta_priority(y.clone(), u64::MAX);
        assert_eq!(
            is_def_eq(&env, &w, &Term::native_const(y), &mut Budget::new(100_000)),
            Ok(false)
        );
    }
}

/// Compare only the selected constructor fields after lazy unfolding of the
/// subjects. Comparing the entire pair/record first can force an unused below
/// field, which Lean's lazy_delta_proj_reduction explicitly avoids.
pub(super) fn project_pair(
    env: &dyn Env,
    ctx: &mut Ctx,
    owner: &Name,
    index: u32,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    let (a, b) = match reduce(env, ctx, a, b, budget)? {
        Reduced::Answer(answer) => return Ok(answer),
        Reduced::Retry(a, b) => return is_def_eq_at(env, ctx, &a, &b, budget),
        Reduced::Stuck(a, b) => (a, b),
    };
    if let (Some(x), Some(y)) = (
        crate::whnf::try_proj_ctor(env, owner, index, &a),
        crate::whnf::try_proj_ctor(env, owner, index, &b),
    ) {
        return is_def_eq_at(env, ctx, &x, &y, budget);
    }
    is_def_eq_at(env, ctx, &a, &b, budget)
}

#[cfg(all(test, feature = "export"))]
mod projection_tests {
    use super::*;
    use crate::{add_inductive, Constructor, InductiveDecl, Level, MinimalEnv};

    #[test]
    fn lazy_projection_does_not_compare_unselected_record_fields() {
        let a = Name::from_dotted("A");
        let x = Name::from_dotted("x");
        let y = Name::from_dotted("y");
        let pair = Name::from_dotted("ProjectionPair");
        let ctor = pair.str("mk");
        let a_ty = Term::native_const(a.clone());
        let pair_ty = Term::native_const(pair.clone());
        let mut env = MinimalEnv::new()
            .with_const_typed(a, 0, Term::sort(Level::nat(1)))
            .with_const_typed(x.clone(), 0, a_ty.clone())
            .with_const_typed(y.clone(), 0, a_ty.clone());
        add_inductive(
            &mut env,
            InductiveDecl {
                name: pair.clone(),
                num_level_params: 0,
                num_params: 0,
                type_: Term::sort(Level::nat(1)),
                constructors: vec![Constructor {
                    name: ctor.clone(),
                    type_: Term::pi(
                        BinderInfo::Default,
                        a_ty.clone(),
                        Term::pi(BinderInfo::Default, a_ty.clone(), pair_ty.clone()),
                    ),
                }],
            },
        )
        .unwrap();
        let mut left = x.clone();
        let mut right = y;
        for i in 0..600 {
            let l = Name::from_dotted(&format!("unusedLeft{i}"));
            let r = Name::from_dotted(&format!("unusedRight{i}"));
            env = env
                .with_def(
                    l.clone(),
                    0,
                    a_ty.clone(),
                    Term::native_const(left),
                    Transparency::Transparent,
                )
                .with_def(
                    r.clone(),
                    0,
                    a_ty.clone(),
                    Term::native_const(right),
                    Transparency::Transparent,
                );
            left = l;
            right = r;
        }
        let record = |last| {
            Term::apply(
                Term::native_const(ctor.clone()),
                &[Term::native_const(x.clone()), Term::native_const(last)],
            )
        };
        let l = Name::from_dotted("leftRecord");
        let r = Name::from_dotted("rightRecord");
        env = env
            .with_def(
                l.clone(),
                0,
                pair_ty.clone(),
                record(left),
                Transparency::Transparent,
            )
            .with_def(
                r.clone(),
                0,
                pair_ty,
                record(right),
                Transparency::Transparent,
            );
        env.set_delta_priority(l.clone(), 1);
        env.set_delta_priority(r.clone(), 1);
        let l = Term::native_const(l);
        let r = Term::native_const(r);
        assert_eq!(
            is_def_eq(
                &env,
                &Term::proj(pair.clone(), 0, l.clone()),
                &Term::proj(pair.clone(), 0, r.clone()),
                &mut Budget::new(512)
            ),
            Ok(true)
        );
        // Selecting the different data field must still refuse equality.
        assert_eq!(
            is_def_eq(
                &env,
                &Term::proj(pair.clone(), 1, l),
                &Term::proj(pair, 1, r),
                &mut Budget::new(100_000)
            ),
            Ok(false)
        );
    }
}
