// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inline a monad operation applied to a CLOSED instance, before the native
//! pipeline lowers a declaration.
//!
//! `Pure.pure` / `Bind.bind` are Lean's class projections (the prelude
//! soundness fix of 2026-09-28; until then they were instance-less axioms that
//! proved `False`), so a `do` block over `IO` elaborates to
//! `@Bind.bind IO (@Monad.toBind IO instMonadIO) α β x k`. Lowering that
//! literally would compile the `instMonadIO` DICTIONARY — whose default
//! `map` / `seq` fields are closures returning actions, which the eager IO
//! model refuses (`native_eager_io_check`) — and would route every monad
//! through the `l_Bind_bind` shim, whose "apply the continuation" semantics is
//! `IO`'s and `Id`'s only.
//!
//! Lean's compiler specializes instances away instead. This pass does the
//! same, as a pure reduction: `@Bind.bind m inst` with `m` and `inst` closed is
//! reduced at instance transparency — δ on the projection and registered
//! instance definitions, projection of a
//! constructor, β — to what the instance's field IS: `IO.bind`, or
//! `fun ma f => Option.bind ma f`, or `fun x f => f x` for `Id`, which is then
//! applied to the remaining arguments and head-β-reduced. The result is
//! definitionally equal to the input (every step is a kernel reduction), so the
//! lowering computes the same value; what changes is only that no dictionary
//! is built at run time. An operation over a monad that is not closed — a
//! `[Monad m]` binder of a generic definition — is left alone, and the eager
//! IO audit refuses it as before (`native-monad-shim`).
//!
//! The reduction never unfolds a constant whose COMPILED meaning is not its
//! value: an `@[implemented_by]` declaration runs another body, and an
//! `@[extern]` one a symbol. It runs in [`inlining_env`], where such
//! constants are hidden, so a reference to one survives the inlining and is
//! substituted (or refused) where the native path lowers references. Not
//! only reducible constants are at stake: the kernel reduces the major
//! premise of a `casesOn` (a `match`) with full δ, so an ordinary
//! `@[implemented_by]` constant taken apart by an instance unfolded too
//! (battery row `attr_implemented_by_iota`: Lean prints `1`, the inlining
//! printed the kernel body's `2` at exit 0).

use std::borrow::Cow;
use std::collections::HashSet;

use clean_kernel::env::ConstantOrigin;
use clean_kernel::{Environment, Expr, ExprKind, Name, TransparencyMode, TypeChecker};

/// Bound on nested inlining rounds: each round replaces one operation with
/// its instance's field, whose body may carry the operations of an INNER
/// monad (`StateT.bind` is spelled over its base's `bind`).
const MAX_ROUNDS: usize = 64;

/// Hide definitions whose logical bodies the compiler may replace or refuse.
/// A body that mentions a csimp source must keep its own compilation point:
/// moving that reference across the dictionary projection could change the
/// replacement visible when the containing source body is compiled.
pub(crate) fn inlining_env(env: &Environment) -> Cow<'_, Environment> {
    let replacements = clean_kernel::env::csimp::replacement_sources(env);
    let mut references = HashSet::new();
    let attributed: Vec<Name> = env
        .constants()
        .filter(|info| {
            let name = &info.name;
            if env.has_implemented_by(name)
                || env.is_extern(name)
                || env.is_unsafe(name)
                || env.is_partial(name)
                || env.is_noncomputable(name)
                || replacements.contains(name)
            {
                return true;
            }
            if replacements.is_empty() {
                return false;
            }
            info.value.as_ref().is_some_and(|body| {
                references.clear();
                body.used_constants_dag(
                    clean_kernel::expr::UsedConstants::WithProjectionStructures,
                    &mut references,
                );
                !references.is_disjoint(&replacements)
            })
        })
        .map(|info| info.name.clone())
        .collect();
    if attributed.is_empty() {
        return Cow::Borrowed(env);
    }
    let mut hidden = env.clone();
    for name in &attributed {
        hidden.forget_decl(name);
    }
    Cow::Owned(hidden)
}

/// Specialize supported operations with closed class parameters and dictionary.
/// An open dictionary or monad parameter stays in the original expression.
pub(crate) fn inline_monad_instances(env: &Environment, value: &Expr) -> Expr {
    let tc = TypeChecker::new(env);
    let world = stable_world_domain(env);
    let mut cur = value.clone();
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        let next = walk(env, &tc, world.as_ref(), &cur, &mut changed);
        if !changed {
            return next;
        }
        cur = next;
    }
    cur
}

fn operation_prefix(e: &Expr, stable_state: bool) -> Option<(usize, TransparencyMode)> {
    let ExprKind::Const(name, _) = e.kind() else {
        return None;
    };
    let clean_kernel::name::NameInner::Str(parent, last) = name.inner() else {
        return None;
    };
    let mode = TransparencyMode::Instances;
    match last.as_ref() {
        "pure" if **parent == Name::interned("Pure") => Some((2, mode)),
        "bind" if **parent == Name::interned("Bind") => Some((2, mode)),
        "liftM" if stable_state && parent.is_anon() => Some((3, mode)),
        "monadLift"
            if stable_state
                && (**parent == Name::interned("MonadLiftT")
                    || **parent == Name::interned("MonadLift")) =>
        {
            Some((3, mode))
        }
        // Both exception classes take the exception type and monad before
        // their dictionary. Reduce only through all three closed arguments.
        "throw"
            if parent.is_anon()
                || **parent == Name::interned("MonadExcept")
                || **parent == Name::interned("MonadExceptOf") =>
        {
            Some((3, mode))
        }
        "throwThe" if parent.is_anon() => Some((3, mode)),
        "forM" if **parent == Name::interned("List") => Some((2, TransparencyMode::Reducible)),
        _ => None,
    }
}

fn is_closed(e: &Expr) -> bool {
    e.loose_bvar_range() == 0 && !e.has_fvar_quick()
}

/// `(λ x₁ … xₙ. b) a₁ … aₖ`, β-reducing as many leading binders as there are
/// arguments.
fn head_beta(head: Expr, args: Vec<Expr>) -> Expr {
    let mut cur = head;
    let mut rest = args.into_iter();
    loop {
        match cur.kind() {
            ExprKind::Lam(_, _, body) => match rest.next() {
                Some(a) => {
                    let body = body.as_ref().clone();
                    cur = body.instantiate(&a);
                }
                None => return cur,
            },
            _ => return Expr::apps(cur, rest),
        }
    }
}

fn stable_world_domain(env: &Environment) -> Option<Expr> {
    if clean_olean::environment_world(env) != Some(clean_kernel::LeanWorld::Lean436.tag()) {
        return None;
    }
    for (name, module) in [
        ("Void", "Init.System.ST"),
        ("IO.RealWorld", "Init.System.IO"),
    ] {
        let name = Name::interned(name);
        if env.get_const(&name).is_none()
            || clean_olean::import::lean_declaration_artifact(env, &name).as_deref() != Some(module)
        {
            return None;
        }
    }
    Some(Expr::app(
        Expr::const_str("Void"),
        Expr::const_str("IO.RealWorld"),
    ))
}

/// Expose the state lambda that the checked stable action actually returns.
/// Its body supplies the world to the selected operation.
fn expose_state_action(
    tc: &TypeChecker<'_>,
    world: &Expr,
    head: &Expr,
    args: &[Expr],
) -> Option<Expr> {
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let clean_kernel::name::NameInner::Str(parent, last) = name.inner() else {
        return None;
    };
    let (closed, arity) = match last.as_ref() {
        "bind" if **parent == Name::interned("Bind") => (2, 6),
        "liftM" if parent.is_anon() => (3, 5),
        "monadLift"
            if **parent == Name::interned("MonadLiftT")
                || **parent == Name::interned("MonadLift") =>
        {
            (3, 5)
        }
        "print" | "println" | "eprint" | "eprintln" if **parent == Name::interned("IO") => (2, 3),
        "throw" if **parent == Name::interned("EIO") => (2, 3),
        _ => return None,
    };
    if args.len() < arity || !args[..closed].iter().all(is_closed) {
        return None;
    }
    let applied = Expr::apps(head.clone(), args[..arity].iter().cloned());
    let action = tc.whnf(&applied);
    let ExprKind::Lam(_, domain, _) = action.kind() else {
        return None;
    };
    if domain.as_ref() != world {
        return None;
    }
    Some(head_beta(action, args[arity..].to_vec()))
}

/// A fully applied local wrapper over bind can receive a suspended action.
/// Without specialization the historical eager guard must reject that argument.
/// Expand the selected source lambda only when its entire body is the ordinary
/// bind operation over those parameters. The protected environment has already
/// hidden compiler overrides and definitions that depend on a scoped csimp rule.
fn local_bind_wrapper(env: &Environment, head: &Expr, args: &[Expr]) -> Option<Expr> {
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    let info = env.get_const(name)?;
    if info.kind != clean_kernel::ConstantKind::Definition
        || info.level_params.len() != levels.len()
    {
        return None;
    }
    let value = info.value.as_ref()?;
    let mut body = value;
    for _ in args {
        let ExprKind::Lam(_, _, rest) = body.kind() else {
            return None;
        };
        body = rest;
    }
    if !matches!(body.get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::interned("Bind.bind"))
    {
        return None;
    }
    let bind = body.get_app_args();
    if bind.len() != 6
        || !bind[..2].iter().all(|arg| is_closed(arg))
        || !bind[4..]
            .iter()
            .all(|arg| matches!(arg.kind(), ExprKind::BVar(_)))
        || matches!(
            env.get_constant_origin(name),
            Some(ConstantOrigin::Olean { .. } | ConstantOrigin::CleanPayload { .. })
        )
    {
        return None;
    }
    let mut result = &info.type_;
    let mut receives_action = false;
    for _ in args {
        let ExprKind::Pi(_, domain, codomain) = result.kind() else {
            return None;
        };
        receives_action |= crate::native_eager_io::is_action_type(env, domain);
        result = codomain;
    }
    if !receives_action || !crate::native_eager_io::is_action_type(env, result) {
        return None;
    }
    let value = value.instantiate_level_params_direct(&info.level_params, levels);
    Some(head_beta(value, args.to_vec()))
}

fn walk(
    env: &Environment,
    tc: &TypeChecker<'_>,
    world: Option<&Expr>,
    e: &Expr,
    changed: &mut bool,
) -> Expr {
    match e.kind() {
        ExprKind::App(..) => {
            let head = e.get_app_fn().clone();
            let args: Vec<Expr> = e
                .get_app_args()
                .into_iter()
                .map(|a| walk(env, tc, world, a, changed))
                .collect();
            if let Some(action) =
                world.and_then(|world| expose_state_action(tc, world, &head, &args))
            {
                *changed = true;
                return action;
            }
            if world.is_some() {
                if let Some(body) = local_bind_wrapper(env, &head, &args) {
                    *changed = true;
                    return body;
                }
            }
            // A for-loop applies the raw field of the ForIn instance chosen by
            // elaboration. Expose that method before auditing its callback.
            // Only the dictionary must be closed: the list and step can use
            // local variables. Attributed implementations stay masked here.
            if let ExprKind::Proj(class, 0, instance) = head.kind() {
                if class == &Name::from_string("ForIn") && is_closed(instance) {
                    let method = tc.whnf_with_transparency(&head, TransparencyMode::Reducible);
                    if !matches!(method.kind(), ExprKind::Proj(..)) {
                        *changed = true;
                        return head_beta(method, args);
                    }
                }
            }
            if let Some((count, mode)) =
                operation_prefix(&head, world.is_some()).filter(|(count, _)| {
                    args.get(..*count)
                        .is_some_and(|prefix| prefix.iter().all(is_closed))
                })
            {
                let partial = Expr::apps(head.clone(), args[..count].iter().cloned());
                let reduced = tc.whnf_with_transparency(&partial, mode);
                if operation_prefix(reduced.get_app_fn(), world.is_some()).is_none()
                    && reduced != partial
                {
                    *changed = true;
                    return head_beta(reduced, args[count..].to_vec());
                }
            }
            let head = match head.kind() {
                ExprKind::Const(..) => head,
                _ => walk(env, tc, world, &head, changed),
            };
            Expr::apps(head, args)
        }
        ExprKind::Lam(bd, ty, body) => Expr::lam(
            *bd,
            walk(env, tc, world, ty, changed),
            walk(env, tc, world, body, changed),
        ),
        ExprKind::Pi(bd, ty, body) => Expr::pi(
            *bd,
            walk(env, tc, world, ty, changed),
            walk(env, tc, world, body, changed),
        ),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            walk(env, tc, world, ty, changed),
            walk(env, tc, world, val, changed),
            walk(env, tc, world, body, changed),
            *non_dep,
        ),
        ExprKind::Proj(s, i, inner) => {
            Expr::proj(s.clone(), *i, walk(env, tc, world, inner, changed))
        }
        _ => e.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level, Name};

    fn c(n: &str, l: Vec<Level>) -> Expr {
        Expr::const_(Name::from_string(n), l)
    }

    /// `@Bind.bind IO (Monad.toBind IO instMonadIO) Unit Unit x k` inlines to
    /// `IO.bind Unit Unit x k`, and an operation over a BOUND monad is left
    /// alone.
    #[test]
    fn test_inline_io_bind_to_io_bind_and_leave_generic_alone() {
        let mut env = Environment::with_prelude();
        env.init_io_ops().expect("io ops");
        let z = || vec![Level::zero(), Level::zero()];
        let io = c("IO", vec![]);
        let unit = c("Unit", vec![]);
        let inst = Expr::apps(
            c("Monad.toBind", z()),
            [io.clone(), c("instMonadIO", vec![])],
        );
        let x = Expr::app(c("IO.println", vec![]), Expr::str_lit("a"));
        let k = Expr::lam(
            BinderInfo::Default,
            unit.clone(),
            Expr::app(c("IO.println", vec![]), Expr::str_lit("b")),
        );
        let bind = Expr::apps(
            c("Bind.bind", z()),
            [io, inst, unit.clone(), unit.clone(), x.clone(), k.clone()],
        );
        let out = inline_monad_instances(&env, &bind);
        let expected = Expr::apps(c("IO.bind", vec![]), [unit.clone(), unit, x, k]);
        assert_eq!(out, expected, "got {out}");

        // Under a binder the monad is `BVar`, not closed: untouched.
        let generic = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::succ(Level::zero())),
            Expr::apps(c("Pure.pure", z()), [Expr::bvar(0), Expr::bvar(0)]),
        );
        assert_eq!(inline_monad_instances(&env, &generic), generic);
    }

    /// `do` over `IO`, as `@Bind.bind IO (Monad.toBind IO instMonadIO) …`.
    fn io_bind() -> Expr {
        let z = || vec![Level::zero(), Level::zero()];
        let io = c("IO", vec![]);
        let unit = c("Unit", vec![]);
        let inst = Expr::apps(
            c("Monad.toBind", z()),
            [io.clone(), c("instMonadIO", vec![])],
        );
        let x = Expr::app(c("IO.println", vec![]), Expr::str_lit("a"));
        let k = Expr::lam(BinderInfo::Default, unit.clone(), x.clone());
        Expr::apps(c("Bind.bind", z()), [io, inst, unit.clone(), unit, x, k])
    }

    #[test]
    fn registered_semireducible_io_dictionary_exposes_its_bind_method() {
        use clean_kernel::env::{KernelInstanceInfo, Reducibility, TrustedEnvExt};

        let mut env = Environment::with_prelude();
        env.init_io_ops().expect("io ops");
        let inst = Name::from_string("instMonadIO");
        assert!(env.set_reducibility(&inst, Reducibility::SEMIREDUCIBLE));
        env.register_instance(KernelInstanceInfo {
            name: inst.clone(),
            class_name: Name::from_string("Monad"),
            priority: 1000,
            type_: None,
            value: None,
        });
        let bind = io_bind();
        let args = bind.get_app_args();
        let expected = Expr::apps(c("IO.bind", vec![]), args[2..].iter().map(|a| (*a).clone()));
        assert_eq!(inline_monad_instances(&env, &bind), expected);
    }

    #[test]
    fn exception_operations_require_an_exact_name_and_a_closed_dictionary() {
        let env = Environment::new();
        let impostor = Expr::const_(Name::anon().str("MonadExcept.throw"), vec![]);
        assert!(operation_prefix(&impostor, true).is_none());
        let throw = Expr::const_str("MonadExcept.throw");
        assert_eq!(
            operation_prefix(&throw, true).map(|(count, _)| count),
            Some(3)
        );
        let lift = c("MonadLiftT.monadLift", vec![]);
        assert!(operation_prefix(&lift, false).is_none());
        assert_eq!(
            operation_prefix(&lift, true).map(|(count, _)| count),
            Some(3)
        );
        let generic = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::apps(
                throw,
                [
                    Expr::const_str("IO.Error"),
                    Expr::const_str("IO"),
                    Expr::bvar(0),
                ],
            ),
        );
        assert_eq!(inline_monad_instances(&env, &generic), generic);
    }

    fn mentions(e: &Expr, name: &str) -> bool {
        let mut used = std::collections::HashSet::new();
        e.used_constants_dag(clean_kernel::expr::UsedConstants::ConstantsOnly, &mut used);
        used.contains(&Name::from_string(name))
    }

    /// In [`inlining_env`] an instance carrying `@[implemented_by]` or
    /// `@[extern]` is never unfolded: the inlined value still names it (so
    /// the lowering substitutes or refuses it) and never its kernel field
    /// `IO.bind`. Without the attribute the same term inlines to `IO.bind`,
    /// in the very environment `inlining_env` hands back.
    #[test]
    fn test_inlining_env_never_unfolds_a_compiler_attr() {
        // The attribute-free fast path remains borrowed. Admission is explicit
        // in the runtime-extern fixture below.
        let bare = Environment::default();
        assert!(matches!(inlining_env(&bare), Cow::Borrowed(_)));
        let mut env = Environment::with_prelude();
        env.init_io_ops().expect("io ops");
        let sorry = Name::from_string("sorryAx");
        assert!(
            env.get_const(&sorry).is_none(),
            "IO does not opt into admission"
        );
        env.init_admission_stub_theory()
            .expect("explicit admission fixture");
        assert!(
            env.is_extern(&sorry),
            "opted-in admission retains its runtime abort"
        );
        let plain = inlining_env(&env);
        assert!(
            matches!(plain, Cow::Owned(_)),
            "compiler attributes are hidden"
        );
        assert!(plain.get_const(&sorry).is_none(), "the extern is hidden");
        assert!(
            env.get_const(&sorry).is_some(),
            "the source env is unchanged"
        );
        let out = inline_monad_instances(&plain, &io_bind());
        assert!(mentions(&out, "IO.bind"), "got {out}");

        for attr in [
            "implemented_by",
            "extern",
            "unsafe",
            "partial",
            "noncomputable",
        ] {
            let mut env = Environment::with_prelude();
            env.init_io_ops().expect("io ops");
            let inst = Name::from_string("instMonadIO");
            match attr {
                "extern" => env.register_extern(inst.clone(), "my_monad_io".to_owned()),
                "unsafe" => env.mark_unsafe(inst.clone()),
                "partial" => env.mark_partial(inst.clone()),
                "noncomputable" => env.mark_noncomputable(inst.clone()),
                _ => env.register_implemented_by(inst.clone(), inst.clone()),
            }
            let hidden = inlining_env(&env);
            assert!(hidden.get_const(&inst).is_none(), "{attr}: must be hidden");
            assert!(
                env.get_const(&inst).is_some(),
                "{attr}: the build's env keeps it"
            );
            let out = inline_monad_instances(&hidden, &io_bind());
            assert!(mentions(&out, "instMonadIO"), "{attr}: got {out}");
            assert!(
                !mentions(&out, "IO.bind"),
                "{attr}: unfolded through it: {out}"
            );
        }
    }

    #[test]
    fn a_projected_field_preserves_its_compilers_local_csimp_scope() {
        use clean_kernel::env::{csimp, Declaration};

        let mut env = Environment::with_prelude();
        let nat = Expr::const_str("Nat");
        let original = Name::interned("originalField");
        let replacement = Name::interned("replacementField");
        let dictionary = Name::interned("compiledDictionary");
        let unrelated = Name::interned("unrelatedMethod");
        for (name, value) in [
            (original.clone(), Expr::nat_lit(5)),
            (replacement.clone(), Expr::nat_lit(5)),
            (dictionary.clone(), Expr::const_(original.clone(), vec![])),
            (unrelated.clone(), Expr::nat_lit(5)),
        ] {
            env.add_decl(Declaration::Definition {
                name,
                level_params: vec![],
                type_: nat.clone(),
                value,
                is_reducible: true,
            })
            .expect("checked definition");
        }
        let theorem = Name::interned("fieldEquality");
        let universe = vec![Level::succ(Level::zero())];
        let field = Expr::const_(original.clone(), vec![]);
        env.add_decl(Declaration::Theorem {
            name: theorem.clone(),
            level_params: vec![],
            type_: Expr::apps(
                Expr::const_str_levels("Eq", universe.clone()),
                [
                    nat.clone(),
                    field.clone(),
                    Expr::const_(replacement, vec![]),
                ],
            ),
            value: Expr::apps(Expr::const_str_levels("Eq.refl", universe), [nat, field]),
        })
        .expect("checked definitional equality");
        let token = csimp::register_local(&mut env, &theorem).expect("checked compiler rule");
        csimp::record_compiled(&mut env, [dictionary.clone()]);
        csimp::retire_local(&mut env, token);
        assert!(csimp::rules_for(&env, None).is_empty());
        assert_eq!(csimp::rules_for(&env, Some(&dictionary)).len(), 1);

        let hidden = inlining_env(&env);
        assert!(hidden.get_const(&original).is_none());
        assert!(hidden.get_const(&dictionary).is_none());
        assert!(hidden.get_const(&unrelated).is_some());
    }

    #[test]
    fn test_inline_list_form_over_io_and_leave_generic_alone() {
        let mut env = Environment::with_prelude();
        env.init_io_ops().expect("io ops");
        let z3 = vec![Level::zero(), Level::zero(), Level::zero()];
        let io = c("IO", vec![]);
        let string = c("String", vec![]);
        let nil = Expr::app(c("List.nil", vec![Level::zero()]), string.clone());
        let f = Expr::lam(
            BinderInfo::Default,
            string.clone(),
            Expr::app(c("IO.println", vec![]), Expr::bvar(0)),
        );
        let call = Expr::apps(
            c("List.forM", z3.clone()),
            [io, c("instMonadIO", vec![]), string, nil, f],
        );
        let out = inline_monad_instances(&env, &call);
        assert!(
            !mentions(&out, "List.forM"),
            "closed-monad List.forM must unfold: {out}"
        );
        assert!(
            !mentions(&out, "instMonadIO"),
            "instMonadIO dictionary must be specialized away: {out}"
        );
        assert!(
            mentions(&out, "IO.bind"),
            "inner Bind.bind must inline to IO.bind in subsequent round: {out}"
        );

        let generic = Expr::lam(
            BinderInfo::Default,
            Expr::pi(
                BinderInfo::Default,
                Expr::sort(Level::succ(Level::zero())),
                Expr::sort(Level::succ(Level::zero())),
            ),
            Expr::apps(c("List.forM", z3), [Expr::bvar(0), Expr::bvar(0)]),
        );
        assert_eq!(inline_monad_instances(&env, &generic), generic);
    }

    #[test]
    fn test_inline_for_in_projection_preserves_open_and_attributed_dictionaries() {
        let mut env = Environment::with_prelude();
        env.init_list_for_in_inst().expect("ForIn list instance");
        env.init_io_ops().expect("IO ops");
        let io = c("IO", vec![]);
        let string = c("String", vec![]);
        let list = Expr::app(c("List", vec![Level::zero()]), string.clone());
        let class = Expr::apps(
            c("ForIn", vec![Level::zero(); 4]),
            [io.clone(), list, string.clone()],
        );
        let apply = |dict| {
            Expr::app(
                Expr::proj(Name::from_string("ForIn"), 0, dict),
                c("Unit", vec![]),
            )
        };
        let open = Expr::lam(BinderInfo::InstImplicit, class, apply(Expr::bvar(0)));
        assert_eq!(inline_monad_instances(&env, &open), open);

        let dict = Expr::apps(c("instForInList", vec![Level::zero(); 2]), [io, string]);
        let call = apply(dict);
        let out = inline_monad_instances(&env, &call);
        assert!(!mentions(&out, "instForInList"), "{out}");
        assert!(TypeChecker::new(&env).is_def_eq(&call, &out));

        env.register_extern(
            Name::from_string("instForInList"),
            "other_iterator".to_string(),
        );
        let masked = inlining_env(&env);
        assert_eq!(inline_monad_instances(&masked, &call), call);
    }
}
