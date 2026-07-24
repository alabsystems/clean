// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in Bool and Prop simproc implementations.
//!
//! Extracted from `simproc_builtins.rs` to keep file sizes within limits.
//! Bool simprocs handle short-circuit evaluation of Bool.and, Bool.or, Bool.not,
//! and BNe.bne. Prop simprocs evaluate decidable propositions by reducing the
//! `Decidable` instance to head normal form (`ite.reduceDecidable`,
//! `Decidable.reduceDecide`).

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::tactic::core::{Goal, ProofState};

use super::simproc::{Simproc, SimprocResult, SimprocSet};
use super::types::SimpResult;

/// Build a Bool constant expression.
fn mk_bool_const(val: bool) -> Expr {
    Expr::const_(
        Name::from_string(if val { "Bool.true" } else { "Bool.false" }),
        vec![],
    )
}

/// Try to interpret an expression as a ground Bool value.
///
/// Returns `Some(true)` for `Bool.true`, `Some(false)` for `Bool.false`,
/// `None` for anything else.
fn get_bool_const_value(expr: &Expr) -> Option<bool> {
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        if s == "Bool.true" {
            return Some(true);
        }
        if s == "Bool.false" {
            return Some(false);
        }
    }
    None
}

/// Register built-in Bool simprocs into the given set.
///
/// ENSURES: Registers simprocs for not, and, or, bne
pub(crate) fn register_bool_simprocs(set: &mut SimprocSet) {
    // Bool.reduceNot — matches on Bool.not and not
    for disc in &["Bool.not", "not"] {
        set.register(Simproc {
            name: Name::from_string("Bool.reduceNot"),
            discriminant: Name::from_string(disc),
            proc: simproc_bool_reduce_not,
            priority: 800,
        });
    }

    // Bool.reduceAnd
    set.register(Simproc {
        name: Name::from_string("Bool.reduceAnd"),
        discriminant: Name::from_string("Bool.and"),
        proc: simproc_bool_reduce_and,
        priority: 800,
    });

    // Bool.reduceOr
    set.register(Simproc {
        name: Name::from_string("Bool.reduceOr"),
        discriminant: Name::from_string("Bool.or"),
        proc: simproc_bool_reduce_or,
        priority: 800,
    });

    // Bool.reduceBNe — matches on bne and BNe.bne
    for disc in &["bne", "BNe.bne"] {
        set.register(Simproc {
            name: Name::from_string("Bool.reduceBNe"),
            discriminant: Name::from_string(disc),
            proc: simproc_bool_reduce_bne,
            priority: 800,
        });
    }
}

/// Bool.reduceNot: evaluate `not b` for ground Bool values.
fn simproc_bool_reduce_not(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    let Some(arg) = args.last() else {
        return SimprocResult::Continue;
    };
    let Some(val) = get_bool_const_value(arg) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_bool_const(!val),
        proof: None,
    })
}

/// Bool.reduceAnd: simplify `Bool.and a b` when either operand is a ground Bool.
///
/// Short-circuit rules: true && b = b, false && b = false,
/// a && true = a, a && false = false.
fn simproc_bool_reduce_and(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return SimprocResult::Continue;
    }
    let lhs = &args[args.len() - 2];
    let rhs = &args[args.len() - 1];
    let lhs_val = get_bool_const_value(lhs);
    let rhs_val = get_bool_const_value(rhs);

    let result = match (lhs_val, rhs_val) {
        (Some(true), _) => (*rhs).clone(),
        (Some(false), _) => mk_bool_const(false),
        (_, Some(true)) => (*lhs).clone(),
        (_, Some(false)) => mk_bool_const(false),
        _ => return SimprocResult::Continue,
    };

    SimprocResult::Done(SimpResult {
        expr: result,
        proof: None,
    })
}

/// Bool.reduceOr: simplify `Bool.or a b` when either operand is a ground Bool.
///
/// Short-circuit rules: true || b = true, false || b = b,
/// a || true = true, a || false = a.
fn simproc_bool_reduce_or(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return SimprocResult::Continue;
    }
    let lhs = &args[args.len() - 2];
    let rhs = &args[args.len() - 1];
    let lhs_val = get_bool_const_value(lhs);
    let rhs_val = get_bool_const_value(rhs);

    let result = match (lhs_val, rhs_val) {
        (Some(true), _) => mk_bool_const(true),
        (Some(false), _) => (*rhs).clone(),
        (_, Some(true)) => mk_bool_const(true),
        (_, Some(false)) => (*lhs).clone(),
        _ => return SimprocResult::Continue,
    };

    SimprocResult::Done(SimpResult {
        expr: result,
        proof: None,
    })
}

/// Bool.reduceBNe: evaluate `bne a b` for ground Bool values.
fn simproc_bool_reduce_bne(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return SimprocResult::Continue;
    }
    let Some(a) = get_bool_const_value(args[args.len() - 2]) else {
        return SimprocResult::Continue;
    };
    let Some(b) = get_bool_const_value(args[args.len() - 1]) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_bool_const(a != b),
        proof: None,
    })
}

/// Register built-in Prop simprocs into the given set.
///
/// ENSURES: Registers simprocs for decide / Decidable.decide
pub(crate) fn register_prop_simprocs(set: &mut SimprocSet) {
    set.register(Simproc {
        name: Name::from_string("ite.reduceDecidable"),
        discriminant: Name::from_string("ite"),
        proc: simproc_ite_reduce_decidable,
        priority: 600,
    });

    for disc in &["decide", "Decidable.decide"] {
        set.register(Simproc {
            name: Name::from_string("Decidable.reduceDecide"),
            discriminant: Name::from_string(disc),
            proc: simproc_decidable_reduce_decide,
            priority: 500,
        });
    }
}

/// Outcome of forcing a `Decidable p` instance to a constructor head.
///
/// `IsTrue` / `IsFalse` carry the decision once full WHNF exposes the
/// `Decidable.isTrue` / `Decidable.isFalse` constructor. `Stuck` means the
/// instance is genuinely irreducible under the kernel's full-delta/iota/native
/// WHNF (a free variable, an opaque constant, or a metavariable), so no sound
/// rewrite is possible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DecidableHead {
    IsTrue,
    IsFalse,
    Stuck,
}

/// Force a `Decidable p` instance to its constructor head.
///
/// Runs the kernel's full WHNF (`state.whnf`), which performs beta / iota /
/// zeta / projection reduction, unfolds every non-`@[irreducible]` definition
/// (delta), and fires native reducers such as `Nat.decEq`, `Nat.decLe`, and
/// `Nat.decLt`. This is strictly more than a syntactic head inspection: a
/// `Decidable` instance that is a *defined* decision procedure (e.g.
/// `Nat.decEq 2 2`) reduces to `Decidable.isTrue …` here even though its
/// syntactic head is `Nat.decEq`, not a constructor.
///
/// SOUNDNESS: the result is reported as `IsTrue`/`IsFalse` only when WHNF lands
/// on a genuine `Decidable.isTrue`/`Decidable.isFalse` constructor. Because the
/// `Decidable` instance *is* the decision, `isTrue` witnesses that `p` holds and
/// `isFalse` that it does not — independent of the (possibly `sorryAx`) proof
/// payload, which neither `decide`'s nor `ite`'s iota reduction inspects. Any
/// other head yields `Stuck`, so callers leave the term untouched.
fn force_decidable_head(state: &ProofState, goal: &Goal, inst: &Expr) -> DecidableHead {
    let inst_whnf = state.whnf(goal, inst);
    let inst_head = inst_whnf.get_app_fn();
    let ExprKind::Const(name, _) = inst_head.kind() else {
        return DecidableHead::Stuck;
    };
    match name.to_string().as_str() {
        "Decidable.isTrue" => DecidableHead::IsTrue,
        "Decidable.isFalse" => DecidableHead::IsFalse,
        _ => DecidableHead::Stuck,
    }
}

/// Decidable.reduceDecide: evaluate `decide p` / `Decidable.decide p` by
/// reducing the `Decidable p` instance to head normal form.
///
/// Given `@decide p inst` (or `@Decidable.decide p inst`), the instance is the
/// final explicit argument. Forcing it to a constructor head (via full WHNF —
/// see [`force_decidable_head`]) exposes the `Decidable.isTrue` or
/// `Decidable.isFalse` constructor, which determines the `Bool` value:
/// `isTrue _ ⇒ Bool.true`, `isFalse _ ⇒ Bool.false`. A genuinely irreducible
/// instance (opaque / free variable) leaves the term untouched via `Continue`.
fn simproc_decidable_reduce_decide(state: &ProofState, goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    // `@decide p inst` carries the proposition then the `Decidable p` instance.
    let Some(&inst) = args.last() else {
        return SimprocResult::Continue;
    };

    match force_decidable_head(state, goal, inst) {
        DecidableHead::IsTrue => SimprocResult::Done(SimpResult {
            expr: mk_bool_const(true),
            proof: None,
        }),
        DecidableHead::IsFalse => SimprocResult::Done(SimpResult {
            expr: mk_bool_const(false),
            proof: None,
        }),
        DecidableHead::Stuck => SimprocResult::Continue,
    }
}

/// ite.reduceDecidable: collapse `@ite α p inst t e` to `t` / `e` once the
/// `Decidable p` instance reduces to a constructor.
///
/// Forces the instance through full WHNF (see [`force_decidable_head`]) so that
/// defined decision procedures — not just literal `Decidable.isTrue`/`isFalse`
/// constructors — drive the branch selection. `isTrue ⇒ then`, `isFalse ⇒
/// else`; a stuck instance yields `Continue`. The rewrite carries `proof: None`
/// because, once the instance is a constructor, `ite` iota-reduces to the
/// selected branch, making the change definitional (`Eq.refl`).
fn simproc_ite_reduce_decidable(state: &ProofState, goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    if args.len() < 5 {
        return SimprocResult::Continue;
    }

    let inst = &args[args.len() - 3];
    let then_branch = &args[args.len() - 2];
    let else_branch = &args[args.len() - 1];

    match force_decidable_head(state, goal, inst) {
        DecidableHead::IsTrue => SimprocResult::Done(SimpResult {
            expr: (*then_branch).clone(),
            proof: None,
        }),
        DecidableHead::IsFalse => SimprocResult::Done(SimpResult {
            expr: (*else_branch).clone(),
            proof: None,
        }),
        DecidableHead::Stuck => SimprocResult::Continue,
    }
}

#[cfg(test)]
mod reduce_decide_simp_tests {
    use super::*;
    use crate::tactic::simp::simproc::builtin_simprocs;
    use clean_kernel::{BinderInfo, Environment};

    /// A throwaway proposition placeholder used as the first `decide` argument.
    fn dummy_prop() -> Expr {
        Expr::const_(Name::from_string("DummyProp"), vec![])
    }

    /// A throwaway proof term placeholder for the `isTrue`/`isFalse` payload.
    fn dummy_proof() -> Expr {
        Expr::const_(Name::from_string("dummyProof"), vec![])
    }

    /// Build `@decide DummyProp inst`.
    fn mk_decide(inst: Expr) -> Expr {
        mk_decide_with_head("decide", inst)
    }

    /// Build `@<head> DummyProp inst` for an arbitrary head constant.
    fn mk_decide_with_head(head: &str, inst: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(head), vec![]), dummy_prop()),
            inst,
        )
    }

    /// `Decidable.isTrue DummyProp dummyProof` — already in head-normal form.
    fn is_true_inst() -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                dummy_prop(),
            ),
            dummy_proof(),
        )
    }

    /// `Decidable.isFalse DummyProp dummyProof` — already in head-normal form.
    fn is_false_inst() -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                dummy_prop(),
            ),
            dummy_proof(),
        )
    }

    /// Run the simproc against `expr` in a fresh empty proof state.
    fn run(expr: &Expr) -> SimprocResult {
        let state = ProofState::new(Environment::new(), Expr::prop());
        let goal = state
            .current_goal()
            .expect("fresh proof state has a main goal")
            .clone();
        simproc_decidable_reduce_decide(&state, &goal, expr)
    }

    #[test]
    fn test_reduce_decide_istrue_instance_reduces_to_bool_true_simp() {
        let result = run(&mk_decide(is_true_inst()));
        match result {
            SimprocResult::Done(r) => {
                assert_eq!(
                    r.expr,
                    mk_bool_const(true),
                    "isTrue instance should yield Bool.true"
                );
                assert!(
                    r.proof.is_none(),
                    "definitional reduction carries no explicit proof"
                );
            }
            other => panic!("expected Done(Bool.true), got {other:?}"),
        }
    }

    #[test]
    fn test_reduce_decide_isfalse_instance_reduces_to_bool_false_simp() {
        let result = run(&mk_decide(is_false_inst()));
        match result {
            SimprocResult::Done(r) => {
                assert_eq!(
                    r.expr,
                    mk_bool_const(false),
                    "isFalse instance should yield Bool.false"
                );
            }
            other => panic!("expected Done(Bool.false), got {other:?}"),
        }
    }

    /// The instance head is a lambda, not a constructor, so only a real WHNF
    /// step (beta reduction) can expose `Decidable.isTrue`. This distinguishes
    /// the implemented simproc from the old constructor-head-only stub.
    #[test]
    fn test_reduce_decide_beta_redex_instance_whnf_reduces_simp() {
        let redex = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), is_true_inst()),
            dummy_prop(),
        );
        // Sanity: before WHNF the instance head is the lambda, not a constant.
        assert!(
            !matches!(redex.get_app_fn().kind(), ExprKind::Const(_, _)),
            "beta-redex head should not already be a constructor const"
        );
        let result = run(&mk_decide(redex));
        match result {
            SimprocResult::Done(r) => {
                assert_eq!(
                    r.expr,
                    mk_bool_const(true),
                    "beta-reducible isTrue instance should yield Bool.true"
                );
            }
            other => panic!("expected Done(Bool.true) after WHNF, got {other:?}"),
        }
    }

    /// An opaque constant instance with no definition cannot reduce to a
    /// `Decidable` constructor, so the simproc must leave the term unchanged.
    #[test]
    fn test_reduce_decide_opaque_instance_stays_continue_simp() {
        let opaque = Expr::const_(Name::from_string("OpaqueDecidableInst"), vec![]);
        let result = run(&mk_decide(opaque));
        assert!(
            matches!(result, SimprocResult::Continue),
            "opaque non-reducible instance should not rewrite, got {result:?}"
        );
    }

    /// A bare `decide` with no instance argument is malformed; the simproc must
    /// not panic and must decline to rewrite.
    #[test]
    fn test_reduce_decide_no_instance_arg_stays_continue_simp() {
        let bare = Expr::const_(Name::from_string("decide"), vec![]);
        let result = run(&bare);
        assert!(
            matches!(result, SimprocResult::Continue),
            "bare decide with no args should stay Continue, got {result:?}"
        );
    }

    /// The reduceDecide simproc is wired into the built-in registry for both
    /// the `decide` and `Decidable.decide` discriminants.
    #[test]
    fn test_reduce_decide_registered_in_builtin_simprocs_simp() {
        let set = builtin_simprocs();
        for disc in ["decide", "Decidable.decide"] {
            let probe = mk_decide_with_head(disc, is_true_inst());
            let matching = set.get_matching(&probe);
            assert!(
                matching
                    .iter()
                    .any(|sp| sp.name == Name::from_string("Decidable.reduceDecide")),
                "Decidable.reduceDecide should be registered for discriminant `{disc}`"
            );
        }
    }

    // =====================================================================
    // Deep-reduction tests: a `Decidable` instance that is a *defined*
    // decision procedure (`Nat.decEq`, `Nat.decLe`) — not a literal
    // `isTrue`/`isFalse` constructor — must still drive the rewrite once
    // forced through full WHNF. These previously fell through to `Continue`
    // for the `ite` simproc, and exercise the native-reducer delta path for
    // `decide`. Each case asserts the rewrite is *definitional* (the kernel
    // agrees `lhs` and the rewritten `rhs` are def-eq, with no trusted-axiom
    // fallback recorded), which is the soundness witness for `proof: None`.
    // =====================================================================

    use clean_kernel::level::Level;

    /// Standard Nat + Eq + Decidable environment used by the deep-reduction
    /// tests. `Nat.decEq` / `Nat.decLe` are backed by native reducers.
    fn nat_decidable_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat().expect("init_nat");
        env.init_eq().expect("init_eq");
        env.init_decidable().expect("init_decidable");
        env
    }

    /// `@Eq.{1} Nat a b`.
    fn nat_eq(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::const_(Name::from_string("Nat"), vec![]), a, b],
        )
    }

    /// `@<head> a b` for a binary Nat decision procedure (e.g. `Nat.decEq`).
    fn nat_dec(head: &str, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string(head), vec![]), [a, b])
    }

    /// Run a single simproc against `expr` in a state over the given env, and
    /// return both the result and the resulting proof state (for trust checks).
    fn run_in_env(
        env: Environment,
        expr: &Expr,
        proc: fn(&ProofState, &Goal, &Expr) -> SimprocResult,
    ) -> (SimprocResult, ProofState) {
        let state = ProofState::new(env, Expr::prop());
        let goal = state
            .current_goal()
            .expect("fresh proof state has a main goal")
            .clone();
        let result = proc(&state, &goal, expr);
        (result, state)
    }

    /// `decide (2 = 2)` with the `Nat.decEq 2 2` instance reduces to
    /// `Bool.true`. The rewrite is definitional: the kernel confirms
    /// `decide (2 = 2) (Nat.decEq 2 2)` is def-eq to `Bool.true`.
    #[test]
    fn test_reduce_decide_nat_deceq_true_is_definitional_simp() {
        let env = nat_decidable_env();
        let two = Expr::nat_lit(2);
        let inst = nat_dec("Nat.decEq", two.clone(), two.clone());
        let decide_expr = Expr::apps(
            Expr::const_(Name::from_string("decide"), vec![]),
            [nat_eq(two.clone(), two.clone()), inst],
        );

        let (result, state) = run_in_env(env, &decide_expr, simproc_decidable_reduce_decide);
        let SimprocResult::Done(r) = result else {
            panic!("Nat.decEq 2 2 decide should reduce, got {result:?}");
        };
        assert_eq!(r.expr, mk_bool_const(true), "2 = 2 decides to Bool.true");
        assert!(
            r.proof.is_none(),
            "deep WHNF reduction is definitional, no explicit proof"
        );

        // Soundness witness: the claimed definitional rewrite is kernel-valid.
        let goal = state.current_goal().expect("goal").clone();
        assert!(
            state.is_def_eq(&goal, &decide_expr, &mk_bool_const(true)),
            "kernel must agree decide (2 = 2) ≡ Bool.true"
        );
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "reducing a real decEq instance records no trusted-axiom fallback"
        );
    }

    /// `decide (1 ≤ 3)` with the `Nat.decLe 1 3` instance reduces to
    /// `Bool.true`, and the rewrite is kernel-definitional.
    #[test]
    fn test_reduce_decide_nat_decle_true_is_definitional_simp() {
        let env = nat_decidable_env();
        let le_inst = nat_dec("Nat.decLe", Expr::nat_lit(1), Expr::nat_lit(3));
        // The proposition shape is irrelevant to the simproc (it dispatches on
        // the instance); use `Nat.le 1 3` as a placeholder prop.
        let prop = nat_dec("Nat.le", Expr::nat_lit(1), Expr::nat_lit(3));
        let decide_expr = Expr::apps(
            Expr::const_(Name::from_string("decide"), vec![]),
            [prop, le_inst.clone()],
        );

        let (result, state) = run_in_env(env, &decide_expr, simproc_decidable_reduce_decide);
        let SimprocResult::Done(r) = result else {
            panic!("Nat.decLe 1 3 decide should reduce, got {result:?}");
        };
        assert_eq!(r.expr, mk_bool_const(true), "1 ≤ 3 decides to Bool.true");
        assert!(r.proof.is_none(), "deep reduction is definitional");

        let goal = state.current_goal().expect("goal").clone();
        assert!(
            state.is_def_eq(&goal, &decide_expr, &mk_bool_const(true)),
            "kernel must agree decide (1 ≤ 3) ≡ Bool.true"
        );
        assert_eq!(state.trusted_axiom_count(), 0);
    }

    /// `decide` over a *false* native decision (`Nat.decEq 2 3`) reduces to
    /// `Bool.false`, definitionally.
    #[test]
    fn test_reduce_decide_nat_deceq_false_is_definitional_simp() {
        let env = nat_decidable_env();
        let inst = nat_dec("Nat.decEq", Expr::nat_lit(2), Expr::nat_lit(3));
        let decide_expr = Expr::apps(
            Expr::const_(Name::from_string("decide"), vec![]),
            [nat_eq(Expr::nat_lit(2), Expr::nat_lit(3)), inst],
        );

        let (result, state) = run_in_env(env, &decide_expr, simproc_decidable_reduce_decide);
        let SimprocResult::Done(r) = result else {
            panic!("Nat.decEq 2 3 decide should reduce, got {result:?}");
        };
        assert_eq!(r.expr, mk_bool_const(false), "2 = 3 decides to Bool.false");

        let goal = state.current_goal().expect("goal").clone();
        assert!(
            state.is_def_eq(&goal, &decide_expr, &mk_bool_const(false)),
            "kernel must agree decide (2 = 3) ≡ Bool.false"
        );
        assert_eq!(state.trusted_axiom_count(), 0);
    }

    /// REGRESSION (the core fix): `ite Nat (2 = 2) (Nat.decEq 2 2) t e` now
    /// selects the `then` branch. Before forcing the instance through WHNF,
    /// the `ite` simproc inspected the *syntactic* head (`Nat.decEq`) and
    /// fell through to `Continue`.
    #[test]
    fn test_reduce_ite_nat_deceq_true_selects_then_simp() {
        let env = nat_decidable_env();
        let two = Expr::nat_lit(2);
        let inst = nat_dec("Nat.decEq", two.clone(), two.clone());
        let then_branch = Expr::nat_lit(10);
        let else_branch = Expr::nat_lit(20);
        let ite_expr = Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                nat_eq(two.clone(), two.clone()),
                inst,
                then_branch.clone(),
                else_branch,
            ],
        );

        let (result, _state) = run_in_env(env, &ite_expr, simproc_ite_reduce_decidable);
        match result {
            SimprocResult::Done(r) => {
                assert_eq!(
                    r.expr, then_branch,
                    "ite with a true decEq instance selects the then-branch"
                );
                assert!(r.proof.is_none(), "iota reduction is definitional");
            }
            other => panic!("expected then-branch (10), got {other:?}"),
        }
    }

    /// `ite Nat (2 = 3) (Nat.decEq 2 3) t e` selects the `else` branch via the
    /// deep-reduced `isFalse` instance.
    #[test]
    fn test_reduce_ite_nat_deceq_false_selects_else_simp() {
        let env = nat_decidable_env();
        let inst = nat_dec("Nat.decEq", Expr::nat_lit(2), Expr::nat_lit(3));
        let then_branch = Expr::nat_lit(10);
        let else_branch = Expr::nat_lit(20);
        let ite_expr = Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                nat_eq(Expr::nat_lit(2), Expr::nat_lit(3)),
                inst,
                then_branch,
                else_branch.clone(),
            ],
        );

        let (result, _state) = run_in_env(env, &ite_expr, simproc_ite_reduce_decidable);
        match result {
            SimprocResult::Done(r) => {
                assert_eq!(
                    r.expr, else_branch,
                    "ite with a false decEq instance selects the else-branch"
                );
            }
            other => panic!("expected else-branch (20), got {other:?}"),
        }
    }

    /// NEGATIVE CONTROL: an opaque / free-variable `Decidable` instance is
    /// genuinely irreducible — neither the `decide` nor the `ite` simproc may
    /// guess. Both must yield `Continue`. Here the instance is a local FVar of
    /// type `Decidable (2 = 2)`, which the kernel cannot reduce.
    #[test]
    fn test_reduce_decide_and_ite_opaque_instance_stays_continue_simp() {
        let env = nat_decidable_env();
        let two = Expr::nat_lit(2);
        let prop = nat_eq(two.clone(), two.clone());
        // An axiom-typed instance constant with no value: irreducible.
        let mut env = env;
        env.add_decl(clean_kernel::env::Declaration::Axiom {
            name: Name::from_string("opaqueDecInst"),
            level_params: vec![],
            type_: Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                prop.clone(),
            ),
        })
        .expect("add opaque instance axiom");
        let opaque = Expr::const_(Name::from_string("opaqueDecInst"), vec![]);

        let decide_expr = Expr::apps(
            Expr::const_(Name::from_string("decide"), vec![]),
            [prop.clone(), opaque.clone()],
        );
        let (dec_result, _s1) =
            run_in_env(env.clone(), &decide_expr, simproc_decidable_reduce_decide);
        assert!(
            matches!(dec_result, SimprocResult::Continue),
            "opaque decide instance must not rewrite, got {dec_result:?}"
        );

        let ite_expr = Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                prop,
                opaque,
                Expr::nat_lit(10),
                Expr::nat_lit(20),
            ],
        );
        let (ite_result, _s2) = run_in_env(env, &ite_expr, simproc_ite_reduce_decidable);
        assert!(
            matches!(ite_result, SimprocResult::Continue),
            "opaque ite instance must not rewrite, got {ite_result:?}"
        );
    }
}
