-- CONTROL for p28. Same Pi-typed instance goal, but the premise is ALREADY in
-- the class the Pi instance asks for, so no derivation under the binder is
-- needed. This MUST pass: without it, p28's refusal would be explained by "the
-- Pi instance never applies at all" rather than by the binder-crossing step it
-- is written to pin.
universe u

class MyLE (a : Type u) where
  le : a -> a -> Prop

instance piLE (i : Type u) (p : i -> Type u) [h : forall k, MyLE (p k)] :
    MyLE (forall k, p k) where
  le x y := forall k, MyLE.le (x k) (y k)

def controlDirect (i : Type u) (p : i -> Type u) [h : forall k, MyLE (p k)]
    (a b : forall k, p k) : Prop := MyLE.le a b
