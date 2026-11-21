// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The eager-IO audit refuses, by name and through the production emit path,
//! every shape the eager model cannot run in Lean's order — and leaves the
//! faithful shapes alone.

use std::path::PathBuf;

use crate::native_build::emit_entry_c_with_type;

fn emit(source: &str) -> anyhow::Result<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let file: PathBuf = dir.path().join("eager_io_check_fixture.lean");
    std::fs::write(&file, source).expect("write fixture");
    emit_entry_c_with_type(&file, "main", 0).map(|(c, _)| c)
}

fn refusal(source: &str) -> String {
    let err = emit(source).expect_err("the eager-IO audit must refuse this program");
    format!("{err:#}")
}

/// `[IO.println "x1", IO.println "x2"]`: both actions ran while the list was
/// BUILT. Pinned Lean runs them only where the program binds them.
#[test]
fn test_eager_io_check_action_in_a_list_is_refused() {
    let msg = refusal(
        "def main : IO Unit := do\n  \
         let acts : List (IO Unit) := [IO.println \"x1\", IO.println \"x2\"]\n  \
         IO.println \"before\"\n  for act in acts.reverse do act\n",
    );
    assert!(msg.contains("native-eager-io"), "{msg}");
    assert!(msg.contains("an action is passed as an argument"), "{msg}");
}

/// `twice (IO.println "x")`: the argument ran once, at the call; Lean prints
/// `x` twice. The callee's own body names an action that already ran.
#[test]
fn test_eager_io_check_action_parameter_is_refused() {
    let msg = refusal(
        "def twice (a : IO Unit) : IO Unit := do\n  a\n  a\n\
         def main : IO Unit := twice (IO.println \"x\")\n",
    );
    assert!(msg.contains("native-eager-io"), "{msg}");
}

/// A projected or let-bound function can ignore its second argument. The
/// eager call would still print, so the diagnostic must locate the action.
#[test]
fn test_eager_io_check_locates_an_action_passed_to_an_applied_term() {
    use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

    let mut env = Environment::with_prelude();
    env.init_io_ops().expect("IO ops");
    let constant = |name| Expr::const_(Name::from_string(name), vec![]);
    let nat = constant("Nat");
    let io_unit = Expr::app(constant("IO"), constant("Unit"));
    let consumer = Expr::arrow(nat.clone(), Expr::arrow(io_unit.clone(), nat.clone()));
    let prod = Name::from_string("Prod");
    let pair = Expr::apps(
        Expr::const_(prod.clone(), vec![Level::zero(), Level::zero()]),
        [nat.clone(), consumer.clone()],
    );
    let projected = Expr::proj(prod, 1, Expr::bvar(0));
    let ignore = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, io_unit, Expr::nat_lit(0)),
    );
    let local = Expr::let_named(
        Name::from_string("selected"),
        consumer,
        ignore,
        Expr::bvar(0),
        false,
    );
    let action = Expr::app(constant("IO.println"), Expr::str_lit("early"));
    let outer = Expr::let_named(
        Name::from_string("outer"),
        Expr::arrow(nat.clone(), nat.clone()),
        Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
        Expr::bvar(0),
        false,
    );
    for (head, description) in [
        (projected, "projection `Prod` field 1 (zero-based)"),
        (local, "let binding `selected`"),
    ] {
        let value = Expr::lam(
            BinderInfo::Default,
            pair.clone(),
            Expr::app(
                outer.clone(),
                Expr::apps(head, [Expr::nat_lit(7), action.clone()]),
            ),
        );
        let checker = TypeChecker::new(&env);
        let inferred = checker.infer_type(&value).expect("typed call");
        assert!(checker.is_def_eq(&inferred, &Expr::arrow(pair.clone(), constant("Nat"))));
        let error = super::check_eager_io(&env, &Name::from_string("call"), &value)
            .expect_err("an argument that runs early");
        let message = error.to_string();
        assert!(
            message.contains("an action is passed as an argument to `an applied term`"),
            "{message}"
        );
        assert!(
            message.contains(&format!("while checking argument 2 of {description}")),
            "{message}"
        );
        assert!(message.contains("native-eager-io"), "{message}");
        assert!(!message.contains("outer"), "{message}");
    }
}

/// `["a", "b"].map IO.println`: `List.map` applies the function where nothing
/// sequences the action. Pinned Lean prints only `done`.
#[test]
fn test_eager_io_check_action_function_to_generic_callee_is_refused() {
    let msg = refusal(
        "def main : IO Unit := do\n  \
         let acts := [\"a\", \"b\"].map IO.println\n  IO.println \"done\"\n",
    );
    assert!(msg.contains("native-eager-io"), "{msg}");
    assert!(msg.contains("`List.map`"), "{msg}");
}

/// A callee that DECLARES a function-returning-an-action parameter is audited
/// in its own body, so passing it `IO.println` is accepted.
#[test]
fn test_eager_io_check_declared_action_function_parameter_is_accepted() {
    emit(
        "def each : List String → (String → IO Unit) → IO Unit\n  \
         | [], _ => pure ()\n  \
         | x :: xs, f => do\n    f x\n    each xs f\n\
         def main : IO Unit := each [\"a\", \"b\"] IO.println\n",
    )
    .expect("a callee that declares `String → IO Unit` may be handed `IO.println`");
}

/// The faithful shapes compile: a `do` block, a final `if`, `pure`.
#[test]
fn test_eager_io_check_faithful_shapes_are_accepted() {
    emit(
        "def check (n : Nat) : IO Unit :=\n  \
         if n % 2 == 0 then IO.println \"even\" else IO.println \"odd\"\n\
         def main : IO Unit := do\n  IO.println \"start\"\n  check 3\n  pure ()\n",
    )
    .expect("sequenced actions and a final `if` are faithful under the eager model");
}

/// `do` in `Except String`. Until 2026-09-28 the prelude's `Bind.bind` was an
/// instance-free axiom (which proved `False`) and the only way to run it
/// natively was the `l_Bind_bind` shim, whose "apply the continuation"
/// semantics is `IO`'s and `Id`'s — so this was refused (`native-monad-shim`).
/// `Bind.bind` is Lean's class projection now, and an application over a
/// CLOSED instance is inlined to the instance's field before lowering
/// (`native_monad_inline.rs`): here `Except.bind`, a real definition, so the
/// program compiles with `Except`'s own semantics. Its output is pinned
/// byte-for-byte against Lean by the native execution battery
/// (`monad_except_do`: `ok 5\nerror too big`).
#[test]
fn test_eager_io_check_bind_at_a_closed_foreign_monad_is_inlined() {
    let c = emit(
        "def step (x : Nat) : Except String Nat :=\n  \
         if x > 3 then .error \"too big\" else .ok (x + 1)\n\
         def run2 (x : Nat) : Except String Nat := do\n  \
         let a ← step x\n  let b ← step a\n  pure (a + b)\n\
         def main : IO Unit := IO.println (match run2 1 with | .ok v => toString v | .error e => e)\n",
    )
    .expect("a bind over the closed `Except String` instance is inlined, not refused");
    assert!(
        !c.contains("l_Bind_bind("),
        "an `Except` bind must not reach the IO-semantics bind shim: {c}"
    );
}

/// A bind over a monad that is NOT closed — a `[Monad m]` binder of a generic
/// definition — cannot be inlined, and the native `Bind.bind` shim implements
/// `IO`'s and `Id`'s semantics only, so the build is refused
/// (`native-monad-shim`) rather than run with the wrong semantics. The generic
/// definition is used at `Id` so that no `IO` dictionary is built: at `IO` the
/// `instMonadIO` argument is refused first, as an action-returning function
/// handed to `Functor.mk` (`native-eager-io`) — fail-closed either way.
#[test]
fn test_eager_io_check_bind_at_a_generic_monad_is_refused() {
    let msg = refusal(
        "def pureTwice [Monad m] (n : Nat) : m Nat := do\n  \
         let a ← pure n\n  let b ← pure n\n  pure (a + b)\n\
         def main : IO Unit := IO.println (toString (Id.run (pureTwice 3)))\n",
    );
    assert!(msg.contains("native-monad-shim"), "{msg}");
    assert!(msg.contains("`pureTwice`"), "{msg}");
}

/// `skip (IO.println "a")` where `skip` ignores its action: `main`'s value
/// names only `skip` and `IO.println`, no `IO` and no bind, so the syntactic
/// trigger scan skipped it and the eager model ran the argument. Measured
/// 2026-09-25 through `clean run`: `a` at exit 0; pinned Lean v4.30.0-rc2
/// prints nothing.
#[test]
fn test_eager_io_check_action_passed_to_an_ignoring_callee_is_refused() {
    let msg = refusal(
        "def skip (a : IO Unit) : IO Unit := pure ()\n\
         def main : IO Unit := skip (IO.println \"a\")\n",
    );
    assert!(msg.contains("native-eager-io"), "{msg}");
    assert!(msg.contains("`skip`"), "{msg}");
}
