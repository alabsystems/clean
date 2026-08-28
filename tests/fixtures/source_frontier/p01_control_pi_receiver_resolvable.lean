-- p01 — CLASS II CONTROL (PASS). The capability half, ruled in.
--
-- PROVES: a receiver whose type is a `def`-based Prop alias — the SAME shape
-- p03 fails on — does dot notation correctly when the target RESOLVES.
-- `h.elim` finds `MyInj.elim` through the un-reduced head `MyInj`
-- (`infer/elab_proj.rs`, the Track-UU pre-whnf head try), which runs BEFORE the
-- `get_type_name` bail p03 reaches.
--
-- RULES OUT: "class II is a missing feature (dot notation on non-`Const`-headed
-- receivers)". It is not: this is the same receiver shape, and it works. Class
-- II is an UNRESOLVED IDENTIFIER wearing an NYI mask, which is why the repair
-- is a message repair and not a resolution change.
--
-- `control_named` is the in-file baseline: the same term written without dot
-- notation. If it ever fails, this fixture is measuring the lemma, not the dot.
def MyInj (f : Nat → Nat) : Prop := ∀ a b : Nat, f a = f b → a = b

theorem MyInj.elim {f : Nat → Nat} (h : MyInj f) (a b : Nat) (e : f a = f b) : a = b := h a b e

theorem control_named {f : Nat → Nat} (h : MyInj f) (a b : Nat) (e : f a = f b) : a = b :=
  MyInj.elim h a b e

theorem probe_dot {f : Nat → Nat} (h : MyInj f) (a b : Nat) (e : f a = f b) : a = b := h.elim a b e
