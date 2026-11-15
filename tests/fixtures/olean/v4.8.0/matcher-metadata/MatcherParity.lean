prelude
import Init.Prelude
namespace MatcherParity
inductive Flag where
  | off
  | on
inductive Box where
  | empty
  | wrap (flag : Flag)
def choose {α : Sort u} (b : Box) (fallback off on : α) : α :=
  match b with
  | .empty => fallback
  | .wrap .off => off
  | .wrap .on => on
def ordinary {α : Sort u} (value : α) : α := value
def chooseEq {α : Sort u} (b : Box) (fallback off on : α) : α :=
  match h : b with
  | .empty => fallback
  | .wrap .off => off
  | .wrap .on => on
def chooseTwo {α : Sort u} (a b : Flag) (aa ab ba bb : α) : α :=
  match a, b with
  | .off, .off => aa
  | .off, .on => ab
  | .on, .off => ba
  | .on, .on => bb
def ordinary.match_1 {α : Sort u} (value : α) : α := value
end MatcherParity
