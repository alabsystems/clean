-- p04 — CLASS II CONTROL (PASS). The namespaced variant of p01.
--
-- PROVES: the p01 result is not an artefact of root-namespace resolution. The
-- alias and its lemma live inside `namespace Fn`, so the head that must be
-- recovered is the QUALIFIED `Fn.Surj`, and dot notation still resolves
-- `Fn.Surj.forallb` through it.
--
-- RULES OUT: "the pre-whnf head try only works at the root namespace, so the
-- corpus entries (all namespaced: `Function.Surjective.*`) are a genuine
-- capability gap after all." They are not.
namespace Fn

def Surj (f : Nat → Nat) : Prop := ∀ b : Nat, ∃ a : Nat, f a = b

theorem Surj.forallb {f : Nat → Nat} (hf : Surj f) : ∀ b : Nat, ∃ a : Nat, f a = b := hf

theorem probe {f : Nat → Nat} (hf : Surj f) : ∀ b : Nat, ∃ a : Nat, f a = b := hf.forallb

end Fn
