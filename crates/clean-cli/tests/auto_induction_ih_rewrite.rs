// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Integration test for the IH-REWRITING induction step of the structural-
// induction lane in `clean-auto` (`engine_induction_rewrite`).
//
// The base induction lane proves base/structural lemmas (`n+0=n`, `l++[]=l`)
// whose constructor case closes by reflexivity or by congruence that bottoms out
// directly in the IH. This test exercises the step that REWRITES WITH THE IH —
// where the minor premise's conclusion is itself a `∀ ys, l = r` and the IH is
// the matching `∀ ys, l' = r'` telescope:
//
//   * `add_assoc`    `∀ n m k, (n+m)+k = n+(m+k)`        (induct on the THIRD var)
//   * `append_assoc` `∀ l₁ l₂ l₃, (l₁++l₂)++l₃ = l₁++(l₂++l₃)` (induct outermost)
//
// SOUNDNESS (load-bearing): the lane is on the SEARCH side, not the TCB. Every
// test re-checks the emitted proof term through the kernel (`infer_type` +
// `is_def_eq` against the goal), asserts the genuine recursor (`Nat.rec` /
// `List.rec`) is present, and asserts the term is `sorry`/axiom-free. A wrong
// IH-rewrite or a mis-built recursor would fail the kernel re-check and never be
// returned as success.
//
// `add_comm` now SOLVES via AUXILIARY-LEMMA SYNTHESIS (`engine_induction_aux`):
// `Nat.add` recurses on its SECOND argument, so the base/step are stuck on
// `0+m` / `succ k + m`; the lane synthesises, proves, kernel-checks, and rewrites
// with the bridging lemmas (`zero_add` / `succ_add`). `mul_comm` stays an honest
// negative (it additionally needs `add_comm` as a rewrite lemma plus a
// `succ_mul`/`mul_zero` whose ABSORBING base shape the identity-only synthesis
// does not conjecture). See the per-test notes.
//
// NOTE: this file is `include!`d by `bench-runner/tests/ih_rewrite_regression.rs`
// (a standalone trust-ir-free workspace) so it RUNS inside a worktree, where the
// full-workspace lockfile collides. Keep the header as regular `//` comments.

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, TypeChecker};

const TIMEOUT: Duration = Duration::from_secs(30);

fn lvl0() -> Level {
    Level::zero()
}
fn lvl1() -> Level {
    Level::succ(Level::zero())
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}
fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mul"), [a, b])
}
/// `@Eq.{1} Nat lhs rhs`.
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![lvl1()]),
        [nat(), lhs, rhs],
    )
}
/// `List Nat` (`List.{0} Nat`).
fn list_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List", vec![lvl0()]), [nat()])
}
/// `@List.nil Nat`.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn nil_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List.nil", vec![lvl0()]), [nat()])
}
/// `@List.cons Nat h t`.
fn cons_nat(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("List.cons", vec![lvl0()]),
        [nat(), h, t],
    )
}
/// `@Eq.{1} (List Nat) l r`.
fn eq_list(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![lvl1()]),
        [list_nat(), l, r],
    )
}
/// `List.append a b`.
fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("List.append"), [a, b])
}

/// `∀ (x₀ : T) … (x_{n-1} : T), body` where `body` references the binders by
/// de Bruijn index (outermost = highest index).
fn forall_n(dom: Expr, n: usize, body: Expr) -> Expr {
    (0..n).fold(body, |acc, _| {
        Expr::pi(BinderInfo::Default, dom.clone(), acc)
    })
}

/// Environment with `Nat`, `Eq`, `List`, the classical bootstrap, and a reducible
/// `List.append` recursing on its first argument.
fn ih_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_list().expect("init_list");
    env.init_classical().expect("init_classical");
    register_append(&mut env);
    env
}

/// `List.append := fun xs ys => @List.rec.{1,0} Nat (fun _ => List Nat) ys
/// (fun h t ih => List.cons Nat h ih) xs` (recurses on the first argument).
fn register_append(env: &mut Environment) {
    let list_nat = list_nat();
    let ty = Expr::pi(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::pi(BinderInfo::Default, list_nat.clone(), list_nat.clone()),
    );
    let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), list_nat.clone());
    let cons_body = cons_nat(Expr::bvar(2), Expr::bvar(0));
    let cons_case = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            list_nat.clone(),
            Expr::lam(BinderInfo::Default, list_nat.clone(), cons_body),
        ),
    );
    let body = Expr::apps(
        Expr::const_str_levels("List.rec", vec![lvl1(), lvl0()]),
        [nat(), motive, Expr::bvar(0), cons_case, Expr::bvar(1)],
    );
    let value = Expr::lam(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::lam(BinderInfo::Default, list_nat, body),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("List.append"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("register List.append");
}

/// Kernel-check `term : goal` (`infer_type` + `is_def_eq`).
fn assert_kernel_checks(env: &Environment, term: &Expr, goal: &Expr, what: &str) {
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(term)
        .unwrap_or_else(|e| panic!("[{what}] proof term failed to type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, goal),
        "[{what}] inferred type is not def-eq to the goal\n  inferred: {inferred:?}\n  goal: {goal:?}"
    );
}

/// `true` iff `term` mentions a `Const` named `name` anywhere in its tree.
fn mentions_const(term: &Expr, name: &str) -> bool {
    match term.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => mentions_const(f, name) || mentions_const(a, name),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            mentions_const(t, name) || mentions_const(b, name)
        }
        ExprKind::Let(_, t, v, b, _) => {
            mentions_const(t, name) || mentions_const(v, name) || mentions_const(b, name)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => mentions_const(e, name),
        _ => false,
    }
}

/// Assert the proof is a genuine, `sorry`/axiom-free recursor proof: it mentions
/// `recursor` and mentions no sorry constant.
fn assert_genuine_recursor(term: &Expr, recursor: &str, what: &str) {
    assert!(
        mentions_const(term, recursor),
        "[{what}] proof does not mention the recursor {recursor} (not a genuine induction proof)"
    );
    for forbidden in ["sorryAx", "Sorry", "sorry"] {
        assert!(
            !mentions_const(term, forbidden),
            "[{what}] proof mentions a forbidden constant {forbidden}"
        );
    }
}

/// `add_assoc` — `∀ n m k, (n+m)+k = n+(m+k)`. The IH-rewriting step plus
/// induction-VARIABLE SELECTION (induct on the third variable `k`) closes it; the
/// proof is a genuine `Nat.rec` term (wrapped in a binder-reordering adapter)
/// that KERNEL-CHECKS.
#[test]
fn test_ih_rewrite_add_assoc_kernel_checks() {
    let env = ih_env();
    let goal = forall_n(
        nat(),
        3,
        nat_eq(
            nat_add(nat_add(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
            nat_add(Expr::bvar(2), nat_add(Expr::bvar(1), Expr::bvar(0))),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, TIMEOUT)
        .expect("add_assoc should be provable by the IH-rewriting induction lane");

    assert_kernel_checks(&env, result.proof_term(), &goal, "add_assoc");
    assert_genuine_recursor(result.proof_term(), "Nat.rec", "add_assoc");
}

/// `add_assoc` via the full `auto_prove` pipeline (router → induction lane).
#[test]
fn test_ih_rewrite_add_assoc_auto_prove() {
    let env = ih_env();
    let goal = forall_n(
        nat(),
        3,
        nat_eq(
            nat_add(nat_add(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
            nat_add(Expr::bvar(2), nat_add(Expr::bvar(1), Expr::bvar(0))),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove(&env, &goal, TIMEOUT, None)
        .expect("auto_prove should solve add_assoc via the induction lane");

    assert_kernel_checks(&env, result.proof_term(), &goal, "add_assoc auto_prove");
    assert_genuine_recursor(result.proof_term(), "Nat.rec", "add_assoc auto_prove");
}

/// `append_assoc` — `∀ l₁ l₂ l₃, (l₁++l₂)++l₃ = l₁++(l₂++l₃)`. `List.append`
/// recurses on its first argument, so induction on the OUTERMOST variable closes
/// it: the step's `congrArg (cons h)` residual is the specialised IH `ih l₂ l₃`.
/// The proof head is the genuine `List.rec` recursor and KERNEL-CHECKS.
#[test]
fn test_ih_rewrite_append_assoc_kernel_checks() {
    let env = ih_env();
    let goal = forall_n(
        list_nat(),
        3,
        eq_list(
            append(append(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
            append(Expr::bvar(2), append(Expr::bvar(1), Expr::bvar(0))),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, TIMEOUT)
        .expect("append_assoc should be provable by the IH-rewriting induction lane");

    assert_kernel_checks(&env, result.proof_term(), &goal, "append_assoc");
    assert_genuine_recursor(result.proof_term(), "List.rec", "append_assoc");
    // Induction is on the outermost variable, so the head is `List.rec` directly.
    assert!(
        matches!(result.proof_term().get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "List.rec"),
        "append_assoc proof head should be List.rec"
    );
}

/// `append_assoc` via the full `auto_prove` pipeline (router → induction lane).
#[test]
fn test_ih_rewrite_append_assoc_auto_prove() {
    let env = ih_env();
    let goal = forall_n(
        list_nat(),
        3,
        eq_list(
            append(append(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
            append(Expr::bvar(2), append(Expr::bvar(1), Expr::bvar(0))),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove(&env, &goal, TIMEOUT, None)
        .expect("auto_prove should solve append_assoc via the induction lane");

    assert_kernel_checks(&env, result.proof_term(), &goal, "append_assoc auto_prove");
    assert_genuine_recursor(result.proof_term(), "List.rec", "append_assoc auto_prove");
}

/// `add_comm` — `∀ n m, n+m = m+n`. NEWLY SOLVES via AUXILIARY-LEMMA SYNTHESIS
/// (`engine_induction_aux`). `Nat.add` recurses on its SECOND argument, so the
/// base case (`0+m = m+0`) is stuck on `0+m` and the inductive step
/// (`succ k + m = m + succ k`) is stuck on `succ k + m`: the IH `k+m = m+k`
/// cannot bridge `succ k + m` because that term does not reduce. The lane DETECTS
/// each stuck `Nat.add (ctor _) _`, SYNTHESISES the bridging lemma
/// (`zero_add : 0+y = y`, `succ_add : succ x + y = succ (x+y)`), PROVES it by its
/// OWN induction, KERNEL-CHECKS it, and registers it as a directed rewrite fact:
/// `zero_add` closes the base case, and `succ_add` + the IH-rewrite close the
/// step. The whole proof is a genuine `@Nat.rec` term (with the kernel-checked
/// aux-lemma `@Nat.rec` terms inlined) that KERNEL-CHECKS and is `sorry`/axiom-
/// free — nothing here is admitted.
#[test]
fn test_ih_rewrite_add_comm_solves_via_synthesis() {
    let env = ih_env();
    let goal = forall_n(
        nat(),
        2,
        nat_eq(
            nat_add(Expr::bvar(1), Expr::bvar(0)),
            nat_add(Expr::bvar(0), Expr::bvar(1)),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, TIMEOUT)
        .expect("add_comm should be provable via auxiliary-lemma synthesis");

    assert_kernel_checks(&env, result.proof_term(), &goal, "add_comm");
    assert_genuine_recursor(result.proof_term(), "Nat.rec", "add_comm");
}

/// `add_comm` via the full `auto_prove` pipeline (router → induction lane →
/// aux-lemma synthesis). The synthesised, kernel-checked proof KERNEL-CHECKS.
#[test]
fn test_ih_rewrite_add_comm_auto_prove() {
    let env = ih_env();
    let goal = forall_n(
        nat(),
        2,
        nat_eq(
            nat_add(Expr::bvar(1), Expr::bvar(0)),
            nat_add(Expr::bvar(0), Expr::bvar(1)),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove(&env, &goal, TIMEOUT, None)
        .expect("auto_prove should solve add_comm via the induction lane + synthesis");

    assert_kernel_checks(&env, result.proof_term(), &goal, "add_comm auto_prove");
    assert_genuine_recursor(result.proof_term(), "Nat.rec", "add_comm auto_prove");
}

/// `mul_comm` — `∀ n m, n*m = m*n`. NEWLY SOLVES via the EXTENDED aux-lemma
/// synthesis + CHAINING (`engine_induction_aux` + `engine_induction_match`),
/// strictly harder than `add_comm`. The base case `0*m = m*0` needs the left-
/// ABSORBING bridge `0*y = 0` (the synthesis now tries `op c₀ y = c₀` alongside
/// the left-IDENTITY `op c₀ y = y`, keeping whichever kernel-proves); the step
/// needs the left-DISTRIBUTE bridge `succ_mul`, whose own inductive step chains
/// an `add_right_comm` pre-proved by the lane. Every synthesised lemma AND the
/// final `@Nat.rec` term KERNEL-CHECK. This is the direct-`prove_by_induction`
/// companion of the paragon bench's `mul_comm` row (both pinned `Solved`).
#[test]
fn test_ih_rewrite_mul_comm_solves_via_chained_synthesis() {
    let env = ih_env();
    let goal = forall_n(
        nat(),
        2,
        nat_eq(
            nat_mul(Expr::bvar(1), Expr::bvar(0)),
            nat_mul(Expr::bvar(0), Expr::bvar(1)),
        ),
    );

    let engine = AutomationEngine::new();
    let proof = engine
        .prove_by_induction(&env, &goal, TIMEOUT)
        .expect("mul_comm should solve via chained aux-lemma synthesis");
    assert_kernel_checks(&env, proof.proof_term(), &goal, "mul_comm");
}
