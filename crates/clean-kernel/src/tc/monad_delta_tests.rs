// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monad reductions after the kernel's monad hook was RETIRED (2026-09-28).
//!
//! `tc/monad_reduce.rs` gave content to the value-less, instance-less
//! `Bind.bind` / `Pure.pure` AXIOMS by name: it rewrote `bind (pure v) f` to
//! `f v` for the monads it classified. Those axioms proved `False`
//! (`docs/issues/2026-09-28-prelude-pure-proves-false.md`) and are now Lean's
//! class projections, applied to a genuine instance; the kernel reduces them by
//! ORDINARY δ / projection-of-constructor / β / ι, exactly as Lean's kernel
//! does, and there is no by-name monad rule left. These pins replace the hook's
//! own test files and keep both of their halves:
//!
//! * SOUNDNESS (was `monad_reduce_transformer_tests.rs`): over an OPAQUE monad
//!   — an axiom `M` with an axiom instance `Monad M`, which carries no
//!   lawfulness — `bind (pure v) k` is NOT `k v`, neither directly nor through
//!   `StateT σ M` / `ExceptT ε M`; the kernel refuses `rfl` for all three.
//! * COMPLETENESS (was `monad_reduce_tests.rs`): over the concrete monads —
//!   `Id`, `Option`, `Except ε`, and `StateT` / `ExceptT` over `Id` — the left
//!   identity IS definitional and `rfl` is accepted, with a wrong-value
//!   control beside each so a pin cannot pass by deciding everything.

use crate::env::monad_term::MonadInst;
use crate::env::{Declaration, Environment};
use crate::tc::TypeChecker;
use crate::{BinderInfo, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::<Level>::new())
}

fn c0(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero()])
}

fn c00(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()])
}

fn nat() -> Expr {
    c("Nat")
}

fn lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

fn axiom(env: &mut Environment, name: &str, type_: Expr) -> Expr {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap_or_else(|e| panic!("add axiom {name}: {e:?}"));
    c(name)
}

/// `@Eq.{1} ty a b` / `@Eq.refl.{1} ty a` — every carrier here is in `Type`.
fn eq1(ty: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), a.clone(), b.clone()],
    )
}

fn refl1(ty: &Expr, a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty.clone(), a.clone()],
    )
}

fn refused(tc: &TypeChecker<'_>, ty: &Expr, lhs: &Expr, rhs: &Expr, what: &str) {
    assert!(
        !tc.is_def_eq(lhs, rhs),
        "kernel must NOT decide {what} definitionally"
    );
    assert!(
        tc.check_type(&refl1(ty, rhs), &eq1(ty, lhs, rhs)).is_err(),
        "kernel must reject rfl : {what}"
    );
}

fn decided(tc: &TypeChecker<'_>, ty: &Expr, lhs: &Expr, rhs: &Expr, what: &str) {
    assert!(tc.is_def_eq(lhs, rhs), "kernel must decide {what}");
    assert!(
        tc.check_type(&refl1(ty, rhs), &eq1(ty, lhs, rhs)).is_ok(),
        "kernel must accept rfl : {what}"
    );
}

/// `bind (pure v) k` and `k v` over `mi`, with `k := fun x => <body x>`.
fn left_identity(mi: &MonadInst, v: &Expr, k: &Expr) -> (Expr, Expr) {
    let lhs = mi.bind(nat(), nat(), mi.pure(nat(), v.clone()), k.clone());
    (lhs, Expr::app(k.clone(), v.clone()))
}

/// The default prelude plus an OPAQUE monad `M : Type → Type` with an OPAQUE
/// instance `instM : Monad M` (axioms: no bind or pure body, no lawfulness),
/// an opaque continuation `k : Nat → M Nat` and an opaque `v : Nat`.
fn opaque_env() -> (Environment, MonadInst, Expr, Expr) {
    let mut env = Environment::with_prelude();
    let m = axiom(
        &mut env,
        "ScratchOpaqueM",
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
    let inst = axiom(
        &mut env,
        "scratchOpaqueInst",
        Expr::app(c00("Monad"), m.clone()),
    );
    let v = axiom(&mut env, "scratchVal", nat());
    let k = axiom(
        &mut env,
        "scratchK",
        Expr::pi(BinderInfo::Default, nat(), Expr::app(m.clone(), nat())),
    );
    let mi = MonadInst {
        u: Level::zero(),
        v: Level::zero(),
        m,
        inst,
    };
    (env, mi, v, k)
}

/// SOUNDNESS: the left-identity LAW is not definitional for an opaque monad.
/// This is the retired hook's Defect 1 (`bind (pure v) f → f v` for ANY
/// monad), stated over the class-based terms; with no hook it holds by
/// construction, and this pins that nothing re-introduces a by-name rule.
#[test]
fn opaque_monad_left_identity_is_not_definitional() {
    let (env, mi, v, k) = opaque_env();
    let tc = TypeChecker::new(&env);
    let (lhs, rhs) = left_identity(&mi, &v, &k);
    refused(
        &tc,
        &mi.at(nat()),
        &lhs,
        &rhs,
        "bind (pure v) k ≡ k v over an opaque monad",
    );
}

/// SOUNDNESS: over `StateT σ M` / `ExceptT ε M` with an opaque base, the
/// transformer's left identity reduces only as far as `bind_M (pure_M …)`,
/// which is stuck — the hook's transformer residual (items (a)/(b)).
#[test]
fn transformer_left_identity_over_opaque_base_is_not_definitional() {
    let (env, base, v, _) = opaque_env();
    let tc = TypeChecker::new(&env);
    for (name, carrier, inst) in [
        (
            "StateT Nat M",
            Expr::apps(c00("StateT"), [nat(), base.m.clone()]),
            Expr::apps(
                c00("StateT.instMonad"),
                [nat(), base.m.clone(), base.inst.clone()],
            ),
        ),
        (
            "ExceptT Nat M",
            Expr::apps(c00("ExceptT"), [nat(), base.m.clone()]),
            Expr::apps(
                c00("ExceptT.instMonad"),
                [nat(), base.m.clone(), base.inst.clone()],
            ),
        ),
    ] {
        let mi = MonadInst {
            u: Level::zero(),
            v: if name.starts_with("StateT") {
                Level::max(Level::zero(), Level::zero())
            } else {
                Level::zero()
            },
            m: carrier,
            inst,
        };
        // k := fun x => pure (x + 0) — any continuation that is not itself stuck.
        let k = Expr::lam(BinderInfo::Default, nat(), mi.pure(nat(), Expr::bvar(0)));
        let (lhs, rhs) = left_identity(&mi, &v, &k);
        refused(
            &tc,
            &mi.at(nat()),
            &lhs,
            &rhs,
            &format!("bind (pure v) k ≡ k v over {name} with an opaque M"),
        );
    }
}

/// COMPLETENESS over the concrete monads: the left identity holds by
/// ordinary δ/proj/β/ι, and a wrong value is refused.
#[test]
fn concrete_monad_left_identity_is_definitional() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let id_mi = MonadInst {
        u: Level::zero(),
        v: Level::zero(),
        m: c0("Id"),
        inst: c0("Id.instMonad"),
    };
    let cases: Vec<(&str, MonadInst)> = vec![
        ("Id", id_mi.clone()),
        (
            "Option",
            MonadInst {
                u: Level::zero(),
                v: Level::zero(),
                m: c0("Option"),
                inst: c0("instMonadOption"),
            },
        ),
        (
            "Except Nat",
            MonadInst {
                u: Level::zero(),
                v: Level::zero(),
                m: Expr::app(c00("Except"), nat()),
                inst: Expr::app(c00("Except.instMonad"), nat()),
            },
        ),
        (
            "ExceptT Nat Id",
            MonadInst {
                u: Level::zero(),
                v: Level::zero(),
                m: Expr::apps(c00("ExceptT"), [nat(), c0("Id")]),
                inst: Expr::apps(
                    c00("ExceptT.instMonad"),
                    [nat(), c0("Id"), c0("Id.instMonad")],
                ),
            },
        ),
    ];
    for (name, mi) in cases {
        // k := fun x => pure (Nat.succ x)
        let k = Expr::lam(
            BinderInfo::Default,
            nat(),
            mi.pure(nat(), Expr::app(c("Nat.succ"), Expr::bvar(0))),
        );
        let (lhs, rhs) = left_identity(&mi, &lit(3), &k);
        decided(
            &tc,
            &mi.at(nat()),
            &lhs,
            &rhs,
            &format!("bind (pure 3) k ≡ k 3 over {name}"),
        );
        let wrong = mi.pure(nat(), lit(3));
        refused(
            &tc,
            &mi.at(nat()),
            &lhs,
            &wrong,
            &format!("bind (pure 3) (pure ∘ succ) ≡ pure 3 over {name}"),
        );
    }
}

/// COMPLETENESS over `StateT Nat Id`: run from a state, the left identity and
/// `get` / `set` compute to the expected pairs.
#[test]
fn state_t_over_id_computes() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let carrier = Expr::apps(c00("StateT"), [nat(), c0("Id")]);
    let inst = Expr::apps(
        c00("StateT.instMonad"),
        [nat(), c0("Id"), c0("Id.instMonad")],
    );
    let mi = MonadInst {
        u: Level::zero(),
        v: Level::max(Level::zero(), Level::zero()),
        m: carrier,
        inst,
    };
    let get = Expr::apps(c00("StateT.get"), [nat(), c0("Id"), c0("Id.instMonad")]);
    // do let s ← get; pure (s + 1)  run at 41  ≡  (42, 41)
    let k = Expr::lam(
        BinderInfo::Default,
        nat(),
        mi.pure(nat(), Expr::app(c("Nat.succ"), Expr::bvar(0))),
    );
    let prog = mi.bind(nat(), nat(), get, k);
    let ran = Expr::app(prog, lit(41));
    let pair = |a: u64, b: u64| Expr::apps(c00("Prod.mk"), [nat(), nat(), lit(a), lit(b)]);
    let prod_ty = Expr::apps(c00("Prod"), [nat(), nat()]);
    decided(
        &tc,
        &prod_ty,
        &ran,
        &pair(42, 41),
        "(get >>= pure ∘ succ) 41 ≡ (42, 41)",
    );
    refused(
        &tc,
        &prod_ty,
        &ran,
        &pair(41, 41),
        "(get >>= pure ∘ succ) 41 ≡ (41, 41)",
    );
}
