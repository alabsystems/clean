-- p13 — CLASS II CONTROL (PASS). The strict-implicit alias shape.
--
-- PROVES: the `Function.Injective` shape specifically — a `def`-based alias
-- whose body opens with STRICT-implicit binders `⦃a b⦄`, which is what the
-- corpus entry `Function.Injective.of_comp_iff'` reports as a
-- `StrictImplicit` Pi chain. With a resolvable target it passes.
--
-- RULES OUT: "the strict-implicit Pi chain is a different, harder sub-shape
-- than p03's default-binder Pi chain." It is not — the binder info of the
-- unfolded body is irrelevant, because the head is recovered before unfolding.
namespace Fn

def Inj (f : Nat → Nat) : Prop := ∀ ⦃a b : Nat⦄, f a = f b → a = b

theorem Inj.elim {f : Nat → Nat} (h : Inj f) {a b : Nat} (e : f a = f b) : a = b := h e

theorem control_named {f : Nat → Nat} (h : Inj f) {a b : Nat} (e : f a = f b) : a = b := Inj.elim h e

theorem probe_dot {f : Nat → Nat} (h : Inj f) {a b : Nat} (e : f a = f b) : a = b := h.elim e

end Fn
