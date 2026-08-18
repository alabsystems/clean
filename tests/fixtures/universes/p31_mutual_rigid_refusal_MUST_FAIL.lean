-- P31 — p06's body inside a `mutual` block. Must FAIL identically.
--
-- p06 (`def bad.{u} : Sort u := Nat`) is FAIL-pinned. Wrapping the SAME
-- declaration in `mutual` must not change whether it is rejected: `u` is
-- explicitly declared either way.
--
-- THE BUG THIS PROBE WAS ADDED TO CATCH (measured 2026-08-14, fixed same day):
-- the mutual and inductive paths assigned `self.universe_params =
-- universe_params.clone()` DIRECTLY (4 sites in infer/elab_mutual.rs, 2 in
-- infer/elaborate_decl.rs), bypassing `set_decl_universe_params` — the only
-- thing that populates the rigid set. So a DECLARED `.{u}` inside `mutual` was
-- not rigid and was free to solve, and this file was accepted while p06 was
-- rejected.
--
-- Found by asking whether the auto-bound bug (p30) had siblings: many code
-- paths write `universe_params`, but only ONE ever wrote the rigid set. That
-- asymmetry was the tell.
--
-- Worse than p30 in one respect: there the universe was merely inferred; here
-- it is written down by the user and still ignored.
mutual
  def badMut.{u} : Sort u := Nat
end
