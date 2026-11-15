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
//! reduced at REDUCIBLE transparency — δ on the projection and the instance
//! definitions (all `@[reducible]` in the prelude), projection of a
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

use clean_kernel::{Environment, Expr, ExprKind, Name, TransparencyMode, TypeChecker};

/// Bound on nested inlining rounds: each round replaces one operation with
/// its instance's field, whose body may carry the operations of an INNER
/// monad (`StateT.bind` is spelled over its base's `bind`).
const MAX_ROUNDS: usize = 64;

/// The environment [`inline_monad_instances`] reduces in: `env` itself when
/// no constant carries `@[implemented_by]` or `@[extern]`, else a copy with
/// every such constant removed (module doc). A reduction in the copy is a
/// reduction in `env` (removing a constant only removes δ steps), so the
/// inlined value is still definitionally equal to the input.
pub(crate) fn inlining_env(env: &Environment) -> Cow<'_, Environment> {
    let attributed: Vec<Name> = env
        .constants()
        .filter(|info| env.has_implemented_by(&info.name) || env.is_extern(&info.name))
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

/// Inline every `Pure.pure` / `Bind.bind` applied to a closed monad and a
/// closed instance (module doc). Terms without such an application come back
/// structurally unchanged.
pub(crate) fn inline_monad_instances(env: &Environment, value: &Expr) -> Expr {
    let tc = TypeChecker::new(env);
    let mut cur = value.clone();
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        let next = walk(&tc, &cur, &mut changed);
        if !changed {
            return next;
        }
        cur = next;
    }
    cur
}

fn is_monad_op(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, _)
        if matches!(name.to_string().as_str(), "Pure.pure" | "Bind.bind"))
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

fn walk(tc: &TypeChecker<'_>, e: &Expr, changed: &mut bool) -> Expr {
    match e.kind() {
        ExprKind::App(..) => {
            let head = e.get_app_fn().clone();
            let args: Vec<Expr> = e
                .get_app_args()
                .into_iter()
                .map(|a| walk(tc, a, changed))
                .collect();
            if is_monad_op(&head) && args.len() >= 2 && is_closed(&args[0]) && is_closed(&args[1]) {
                let partial = Expr::apps(head.clone(), [args[0].clone(), args[1].clone()]);
                let reduced = tc.whnf_with_transparency(&partial, TransparencyMode::Reducible);
                if !is_monad_op(reduced.get_app_fn()) && reduced != partial {
                    *changed = true;
                    return head_beta(reduced, args[2..].to_vec());
                }
            }
            let head = match head.kind() {
                ExprKind::Const(..) => head,
                _ => walk(tc, &head, changed),
            };
            Expr::apps(head, args)
        }
        ExprKind::Lam(bd, ty, body) => {
            Expr::lam(*bd, walk(tc, ty, changed), walk(tc, body, changed))
        }
        ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, walk(tc, ty, changed), walk(tc, body, changed)),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            walk(tc, ty, changed),
            walk(tc, val, changed),
            walk(tc, body, changed),
            *non_dep,
        ),
        ExprKind::Proj(s, i, inner) => Expr::proj(s.clone(), *i, walk(tc, inner, changed)),
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

        for attr in ["implemented_by", "extern"] {
            let mut env = Environment::with_prelude();
            env.init_io_ops().expect("io ops");
            let inst = Name::from_string("instMonadIO");
            if attr == "extern" {
                env.register_extern(inst.clone(), "my_monad_io".to_owned());
            } else {
                env.register_implemented_by(inst.clone(), Name::from_string("instMonadIO"));
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
}
