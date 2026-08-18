-- P29 — auto-bound universe with NO `universe` declaration.
--
-- p02 is the RIGID twin of this probe: it writes `universe u` first, which
-- routes through `set_decl_universe_params` and lands `u` in the rigid set.
-- This file omits that line, so `u` is first seen as an undeclared level name
-- and takes the AUTO-BOUND path (infer/elab_core.rs:1391-1393), which pushes
-- it into `universe_params` WITHOUT registering it as rigid.
--
-- Pinning the observed behavior; rung 4 (levelMVarToParam generalization)
-- owns any change here.
def k {A : Type u} (a : A) : A := a

-- Force arity: if `u` were dropped rather than generalized, `k.{0}` would not
-- accept a universe argument at all.
def kAt : Nat := @k.{0} Nat Nat.zero
