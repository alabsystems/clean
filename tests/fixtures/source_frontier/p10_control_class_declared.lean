-- p10 — CLASS I CONTROL (PASS). The `class` keyword vs the `def` alias.
--
-- PROVES: p09's shape with `DecidableEq` replaced by a `class`-declared class
-- passes. The caller's `[MyC α]` binder is found, matched and applied.
--
-- RULES OUT: "instance synthesis cannot see a local instance binder at all",
-- and "the failure is about the CALLEE's signature shape". Neither: the only
-- difference from p09 is that `MyC` is registered by the `class` keyword and
-- so answers `is_class` (`instances.rs`), while `DecidableEq` is a `def` and
-- does not — and whnf'ing the local's type turns it into a Pi that
-- `extract_class_app` cannot name either.
class MyC (α : Type) where
  w : Nat

def callee2 {α : Type} [MyC α] (a : α) : Nat := 0

theorem probe_control {α : Type} [MyC α] (a : α) : callee2 a = 0 := rfl
