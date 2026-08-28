-- p30 — THIRD MASK, the REFUSAL half. A real binder over-applied is NOT named.
--
-- PROVES the boundary of the 2026-08-27 repair. p15/p16 alone are satisfied by
-- an implementation that names EVERY over-applied head — which would be an
-- over-broad reading of the mask and would rewrite a message that is already
-- correct. `nOverApplied` below over-applies `n`, a binder the source WRITES,
-- so nothing was swallowed and nothing is unresolved: the pre-existing message
-- must survive byte-for-byte.
--
--   pinned:  Too many arguments: function type Const(Name { … "Nat" … }, [])
--            is not a function type, but 1 argument(s) remain
--
-- That is the `TooManyArguments` Display, with the SAME `{func_type:?}` dump
-- it always carried. `ElabError::AutoBoundHeadOverApplied` is raised only when
-- the head of the application spine is a free variable this declaration's
-- auto-implicit table introduced (`ElabCtx::auto_bound_head_name`), and a
-- user-written binder is a local but never an auto-implicit.
--
-- WHY IT IS A SEPARATE FILE and not a second declaration in p15: the two
-- messages must be measured in the same run for the same reason p19/p20 are a
-- pair — "name every head" satisfies p15 alone, "name no head" satisfies p30
-- alone, and only both together pin the boundary.
--
-- CONTROL (in-file, PASSES): `usesBinder` uses the same `(n : Nat)` binder the
-- way it is meant to be used. Without it this file is also satisfied by "a
-- `Nat`-typed binder breaks elaboration", which is not what is being claimed.
theorem usesBinder (n : Nat) : n = n := rfl

theorem nOverApplied (n : Nat) (h : n n) : True := trivial
