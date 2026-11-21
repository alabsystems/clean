// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime discriminant of the conditional in the checked environment.

use super::{lower::collect_app_args, rec_ih::peel_lams, LcnfContext};
use clean_kernel::{Expr, ExprKind, Name};

pub(super) enum DecisionLayout {
    Constructors,
    BoolField,
}

fn call<'a>(e: &'a Expr, expected: &str) -> Option<Vec<&'a Expr>> {
    let (f, args) = collect_app_args(e.strip_mdata());
    matches!(f.kind(), ExprKind::Const(n, _) if *n == Name::interned(expected)).then_some(args)
}

fn forwards_branches(value: &Expr) -> bool {
    let Some(body) = peel_lams(value, 5) else {
        return false;
    };
    let Some(args) = call(&body, "dite") else {
        return false;
    };
    let [ty, p, inst, yes, no] = args.as_slice() else {
        return false;
    };
    **ty == Expr::bvar(4)
        && **p == Expr::bvar(3)
        && **inst == Expr::bvar(2)
        && peel_lams(yes, 1) == Some(Expr::bvar(2))
        && peel_lams(no, 1) == Some(Expr::bvar(1))
}

fn selects_on_decide(value: &Expr) -> bool {
    let Some(body) = peel_lams(value, 5) else {
        return false;
    };
    let Some(args) = call(&body, "Bool.casesOn") else {
        return false;
    };
    let [_, decide, no, yes, proof] = args.as_slice() else {
        return false;
    };
    let p = Expr::bvar(3);
    let inst = Expr::bvar(2);
    **no == Expr::bvar(0)
        && **yes == Expr::bvar(1)
        && call(decide, "Decidable.decide").as_deref() == Some(&[&p, &inst][..])
        && call(proof, "Decidable.reflects_decide").as_deref() == Some(&[&p, &inst][..])
}

/// Lean 4.36 stores a Boolean and its erased reflection proof in
/// `Decidable.intro`. The earlier inductive instead has two constructors.
pub fn decidable_projects_bool(env: &clean_kernel::Environment) -> bool {
    let decidable = Name::from_string("Decidable");
    let Some(layout) = crate::to_mono::has_trivial_structure(&decidable, env) else {
        return false;
    };
    if layout.ctor_name != decidable.clone().str("intro")
        || layout.num_params != 1
        || layout.field_idx != 0
    {
        return false;
    }
    let Some(decide) = env.get_const(&decidable.clone().str("decide")) else {
        return false;
    };
    let instance = Expr::app(Expr::const_(decidable.clone(), vec![]), Expr::bvar(0));
    let decision_type = Expr::pi(
        clean_kernel::BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            clean_kernel::BinderInfo::InstImplicit,
            instance.clone(),
            Expr::const_str("Bool"),
        ),
    );
    let projection = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            clean_kernel::BinderInfo::InstImplicit,
            instance,
            Expr::proj(decidable, 0, Expr::bvar(0)),
        ),
    );
    decide.type_ == decision_type && decide.value.as_ref() == Some(&projection)
}

pub(super) fn for_conditional(ctx: &LcnfContext<'_>, nondependent: bool) -> Option<DecisionLayout> {
    let env = ctx.env;
    let dec = env.get_inductive(&Name::interned("Decidable"))?;
    if dec.constructor_names
        == [
            Name::interned("Decidable.isFalse"),
            Name::interned("Decidable.isTrue"),
        ]
    {
        return Some(DecisionLayout::Constructors);
    }

    // The one-constructor representation uses a Bool field and a proof. Match
    // the actual stored eliminator so a replacement cannot change which
    // branch runs. The ordinary call remains available for other definitions.
    if !decidable_projects_bool(env) {
        return None;
    }
    let ordinary = |s: &str| {
        let n = Name::interned(s);
        !env.is_extern(&n)
            && !env.has_implemented_by(&n)
            && !env.is_unsafe(&n)
            && !env.is_partial(&n)
            && !env.is_noncomputable(&n)
            && !clean_kernel::env::csimp::has_replacement(env, &n)
    };
    if !([
        "dite",
        "Bool.casesOn",
        "Decidable.decide",
        "Decidable.reflects_decide",
    ]
    .into_iter()
    .all(ordinary)
        && (!nondependent || ordinary("ite")))
    {
        return None;
    }
    let body = |s: &str| {
        env.get_const(&Name::interned(s))
            .and_then(|i| i.value.as_ref())
    };
    if nondependent && !forwards_branches(body("ite")?) {
        return None;
    }
    if !selects_on_decide(body("dite")?) {
        return None;
    }
    Some(DecisionLayout::BoolField)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lcnf::{Code, DeclValue};
    use clean_kernel::{Environment, LeanWorld};

    #[test]
    fn historical_ite_and_dite_switch_on_the_decidable_constructors() {
        let env = Environment::with_prelude();
        let ctx = LcnfContext::new(&env);
        for nondependent in [false, true] {
            assert!(matches!(
                for_conditional(&ctx, nondependent),
                Some(DecisionLayout::Constructors)
            ));
        }
    }

    #[test]
    #[ignore = "requires CLEAN_LEAN436_LIB pointing to the stable Lean distribution"]
    fn stable_ite_switches_on_the_real_bool_field_and_refuses_changed_eliminators() {
        let lib = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::new();
        clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).unwrap();
        for nondependent in [false, true] {
            assert!(matches!(
                for_conditional(&LcnfContext::new(&env), nondependent),
                Some(DecisionLayout::BoolField)
            ));
        }
        let ite = Name::interned("ite");
        let closure =
            crate::RuntimeBindingClosure::check_executable(&env, std::slice::from_ref(&ite))
                .unwrap();
        let compiled = crate::constant_to_decl_in_runtime_closure(
            &env,
            env.get_const(&ite).unwrap(),
            &closure,
        )
        .unwrap()
        .unwrap();
        let DeclValue::Code(original_body) = &compiled.body else {
            panic!("missing body")
        };
        let mut body = original_body.as_ref();
        while let Code::Let(_, rest) = body {
            body = rest.as_ref();
        }
        let Code::Cases(cases) = body else {
            panic!("expected switch: {body:?}")
        };
        assert_eq!(cases.type_name, Name::interned("Bool"));

        for changed in ["dite", "Decidable.decide", "Bool.casesOn"] {
            let mut other = env.clone();
            other.register_extern(Name::interned(changed), "other_implementation".to_owned());
            assert!(
                for_conditional(&LcnfContext::new(&other), false).is_none(),
                "{changed}"
            );
        }
    }
}
