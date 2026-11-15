// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `attribute [implemented_by f] d` AFTER code that reaches `d` was added.
//!
//! Pinned Lean v4.30.0-rc2 compiles a declaration when it is added, and
//! `applyImplementedBy?` reads the environment at that moment, so code added
//! before the command keeps running what `d` ran then -- unless Lean's
//! inliner later copies it into code compiled after the command. Measured
//! with `lean --run` (the `attr_implemented_by_order*` battery rows): a small
//! caller added first prints `2` (inlined into `main`), its `@[noinline]` twin
//! prints `3`, a `main` added before the command prints `3`. Clean compiles
//! every reached declaration together, after the file, and does not model
//! that inliner; before this check it printed the new target's answer for
//! all of them at exit 0.
//!
//! Which body such code runs cannot be read off the kernel values either:
//! the native path rewrites a value before its walk (`native_monad_inline`
//! reduces a `match` on an ordinary constant with full delta), so a check of
//! what the walk reaches misses constants the rewrite removes
//! (`attr_implemented_by_order_iota`, where Lean prints the old `2`). So the
//! elaborator records in the environment, over the values as written, every
//! earlier constant that reaches a rebound declaration
//! (`clean_compiler::implemented_by_order`), and when that record is not
//! empty no root of the program is compiled (`native-implemented-by-order`).

use super::implemented_by_tests::{compile_c, mentions_symbol, refusal};

const TAG: &str = "(native-implemented-by-order)";

/// The refusal names the tag, the rebound declaration and the recorded
/// referrer.
fn assert_order_refusal(source: &str, root: &str, rebound: &str, referrer: &str) {
    let err = refusal(source, root);
    assert!(err.contains(TAG), "{err}");
    assert!(err.contains(&format!("`{rebound}`")), "{err}");
    assert!(err.contains(&format!("`{referrer}`")), "{err}");
}

const BOX: &str = "structure Box (α : Type) where\n  val : α\n  tag : Nat\n\
    def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := \
    ⟨(f x.val).val, x.tag + 2⟩\n\
    def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := \
    ⟨(f x.val).val, x.tag + 1⟩\n";

const BOX_MAIN: &str =
    "def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))\n";

/// `attr_implemented_by_order_noinline`: Lean runs `slow`'s own body through
/// the `@[noinline]` caller compiled before the command, `3`.
#[test]
fn test_compile_implemented_by_after_a_noinline_caller_refused() {
    assert_order_refusal(
        "def fast (n : Nat) : Nat := n + 1\n\
         @[noinline] def slow (n : Nat) : Nat := n + 2\n\
         @[noinline] def caller (n : Nat) : Nat := slow n\n\
         attribute [implemented_by fast] slow\n\
         def main : IO Unit := IO.println (toString (caller 1))\n",
        "main",
        "slow",
        "caller",
    );
}

/// `attr_implemented_by_order`: the plain caller prints `2` in Lean only
/// because the inliner copies it into `main`; refused all the same.
#[test]
fn test_compile_implemented_by_after_a_plain_caller_refused() {
    assert_order_refusal(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow n\n\
         attribute [implemented_by fast] slow\n\
         def main : IO Unit := IO.println (toString (caller 1))\n",
        "main",
        "slow",
        "caller",
    );
}

/// `attr_implemented_by_order_entry`: the entry itself predates the command;
/// Lean prints `3`.
#[test]
fn test_compile_implemented_by_after_the_entry_refused() {
    assert_order_refusal(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def main : IO Unit := IO.println (toString (slow 1))\n\
         attribute [implemented_by fast] slow\n",
        "main",
        "slow",
        "main",
    );
}

/// A `where` helper is a constant of its own, compiled with its parent.
#[test]
fn test_compile_implemented_by_after_a_where_helper_refused() {
    assert_order_refusal(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := go n\n  \
         where go (k : Nat) : Nat := slow k\n\
         attribute [implemented_by fast] slow\n\
         def main : IO Unit := IO.println (toString (caller 1))\n",
        "main",
        "slow",
        "caller.go",
    );
}

/// `attr_implemented_by_order_chain`: a link added to a chain later. Lean
/// prints `3` from the earlier caller and `2` from `main`.
#[test]
fn test_compile_implemented_by_link_added_later_refused() {
    assert_order_refusal(
        "def fastest (n : Nat) : Nat := n + 1\n\
         def middle (n : Nat) : Nat := n + 2\n\
         @[implemented_by middle] def slow (n : Nat) : Nat := n + 3\n\
         @[noinline] def caller (n : Nat) : Nat := slow n\n\
         attribute [implemented_by fastest] middle\n\
         def main : IO Unit := do\n  \
         IO.println (toString (caller 1))\n  \
         IO.println (toString (slow 1))\n",
        "main",
        "middle",
        "caller",
    );
}

/// `attr_implemented_by_order_instance`: `main` and the instance whose field
/// is `slowBind` both predate the command; Lean prints `2`.
#[test]
fn test_compile_implemented_by_after_an_instance_user_refused() {
    let source = format!(
        "{BOX}instance instBindBox : Bind Box := ⟨slowBind⟩\n{BOX_MAIN}\
         attribute [implemented_by fastBind] slowBind\n"
    );
    assert_order_refusal(&source, "main", "slowBind", "instBindBox");
}

/// `attr_implemented_by_order_instance_inline`: `@[inline] slowBind` and the
/// instance predate the command, `main` follows it; Lean prints `2` because
/// the instance's code already holds the old body.
#[test]
fn test_compile_implemented_by_inlined_body_in_an_instance_refused() {
    let source = BOX.replace("def slowBind", "@[inline] def slowBind")
        + "instance instBindBox : Bind Box := ⟨fun x f => slowBind x f⟩\n\
           attribute [implemented_by fastBind] slowBind\n"
        + BOX_MAIN;
    assert_order_refusal(&source, "main", "slowBind", "instBindBox");
}

/// `attr_implemented_by_order_instance_after`: the same without `@[inline]`
/// prints `1` in Lean (its instance inlining meets `slowBind` after the
/// command). Which body runs is the inliner's choice: refused too.
#[test]
fn test_compile_implemented_by_instance_used_after_the_command_refused() {
    let source = format!(
        "{BOX}instance instBindBox : Bind Box := ⟨slowBind⟩\n\
         attribute [implemented_by fastBind] slowBind\n{BOX_MAIN}"
    );
    assert_order_refusal(&source, "main", "slowBind", "instBindBox");
}

/// `attr_implemented_by_order_iota`: `wrapper` (compiled before the command)
/// is reached only through `pairW`, an ordinary constant added after it that
/// the instance takes apart with a `match`. The monad inlining reduces that
/// `match` with full delta, so neither constant survives into what the walk
/// reads; Lean prints the old `2`, and Clean printed `1` at exit 0.
#[test]
fn test_compile_implemented_by_hidden_behind_a_match_refused() {
    let source = format!(
        "{BOX}@[reducible, noinline] def wrapper {{α β : Type}} (x : Box α) (f : α → Box β) : \
         Box β := slowBind x f\n\
         attribute [implemented_by fastBind] slowBind\n\
         def pairW : Prod (Bind Box) Nat := (⟨wrapper⟩, 0)\n\
         instance instBindBox : Bind Box := match pairW with | (b, _) => b\n{BOX_MAIN}"
    );
    assert_order_refusal(&source, "main", "slowBind", "wrapper");
}

/// The refusal is the whole program's: a root that reaches nothing recorded
/// is refused too, naming the rebound declaration. Clean cannot tell which
/// body Lean's inliner leaves in code compiled after the command, so it does
/// not guess per root.
#[test]
fn test_compile_implemented_by_order_refuses_every_root() {
    let err = refusal(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow n\n\
         attribute [implemented_by fast] slow\n\
         def other (n : Nat) : Nat := n * 3\n",
        "other",
    );
    assert!(err.contains(TAG), "{err}");
    assert!(err.contains("`other`"), "{err}");
    assert!(err.contains("`slow`"), "{err}");
}

/// NEGATIVE CONTROL: the command form with every caller added after it runs
/// the target everywhere when the rebound declaration is `@[noinline]` (Lean
/// prints `2`, `attr_implemented_by_command`), and a theorem about `slow`
/// added before the command is no reason to refuse: a proof never runs.
#[test]
fn test_compile_implemented_by_command_before_callers_runs_target() {
    let c = compile_c(
        "def fast (n : Nat) : Nat := n + 1\n\
         @[noinline] def slow (n : Nat) : Nat := n + 2\n\
         theorem slow_one : slow 1 = 3 := rfl\n\
         attribute [implemented_by fast] slow\n\
         @[noinline] def caller (n : Nat) : Nat := slow n\n\
         def main : IO Unit := IO.println (toString (caller 1))\n",
        "main",
    )
    .unwrap_or_else(|e| panic!("nothing earlier reaches `slow`; it must compile: {e:#}"));
    assert!(mentions_symbol(&c, "l_fast"), "{c}");
    assert!(!mentions_symbol(&c, "l_slow"), "{c}");
}

/// NEGATIVE CONTROL: the command before the instance, `slowBind` being
/// `@[noinline]` (Lean prints `1`).
#[test]
fn test_compile_implemented_by_command_before_an_instance_runs_target() {
    let source = format!(
        "{}attribute [implemented_by fastBind] slowBind\n\
         instance instBindBox : Bind Box := ⟨slowBind⟩\n{BOX_MAIN}",
        BOX.replace("def slowBind", "@[noinline] def slowBind")
    );
    let c = compile_c(&source, "main")
        .unwrap_or_else(|e| panic!("nothing earlier reaches `slowBind`; it must compile: {e:#}"));
    assert!(mentions_symbol(&c, "l_fastBind"), "{c}");
    assert!(!mentions_symbol(&c, "l_slowBind"), "{c}");
}

/// `attr_implemented_by_command_small`: nothing reaches `slow` before the
/// command, but `slow`'s own pre-binding code is an inline candidate (LCNF
/// size at most `compiler.small`), and Lean copies it into `main`, compiled
/// after the command: Lean prints `1` (the old body), and Clean printed `101`
/// at exit 0 before the declaration was recorded for itself.
#[test]
fn test_compile_implemented_by_command_on_a_small_declaration_refused() {
    assert_order_refusal(
        "def fast (n : Nat) : Nat := Nat.add n 100\n\
         def slow (n : Nat) : Nat := n\n\
         attribute [implemented_by fast] slow\n\
         def main : IO Unit := IO.println (toString (slow 1))\n",
        "main",
        "slow",
        "slow",
    );
}

/// `attr_implemented_by_command_inline`: an `@[inline]` declaration rebound
/// before any caller; Lean inlines its pre-binding body into `main` and
/// prints `3`, where Clean printed `2` at exit 0.
#[test]
fn test_compile_implemented_by_command_on_an_inline_declaration_refused() {
    let err = refusal(
        "def fast (n : Nat) : Nat := Nat.add n 1\n\
         @[inline] def slow (n : Nat) : Nat := Nat.add n 2\n\
         attribute [implemented_by fast] slow\n\
         def main : IO Unit := IO.println (toString (slow 1))\n",
        "main",
    );
    assert!(err.contains(TAG), "{err}");
    assert!(
        err.contains("`slow` itself was compiled before the binding"),
        "{err}"
    );
}

/// `attr_implemented_by_macro_inline`: a `@[macro_inline]` declaration's body
/// is expanded at every call site and Lean never runs the implementation
/// (`3`); the binding is not registered, so the body compiles and nothing is
/// refused.
#[test]
fn test_compile_implemented_by_macro_inline_compiles_the_body() {
    let c = compile_c(
        "def fast (n : Nat) : Nat := Nat.add n 1\n\
         @[macro_inline, implemented_by fast] def slow (n : Nat) : Nat := Nat.add n 2\n\
         def main : IO Unit := IO.println (toString (slow 1))\n",
        "main",
    )
    .unwrap_or_else(|e| panic!("the body of a `@[macro_inline]` declaration compiles: {e:#}"));
    assert!(!mentions_symbol(&c, "l_fast"), "{c}");
}
