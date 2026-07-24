-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: user-defined PARAMETRIC inductives with shorthand constructors.
--
-- Before the parser fix, a constructor that omitted its return type (`| nothing`)
-- defaulted to the bare inductive name `Maybe`, dropping the parameter — so the
-- kernel's inductive check rejected every parametric inductive declared with the
-- shorthand ("Constructor return type parameter at index 0 does not match declared
-- parameter of Maybe"). The omitted return type now defaults to the inductive
-- applied to its parameters (`Maybe α`), identical to the explicit
-- `| nothing : Maybe α` form, so `add_inductive` accepts it. The kernel check is
-- unchanged and still rejects malformed constructors (e.g. swapped parameters).

inductive Maybe (α : Type) where
  | nothing
  | just (val : α)
  deriving Repr

inductive Pair (α β : Type) where
  | mk (fst : α) (snd : β)

-- recursive parametric inductive, shorthand constructors
inductive Lst (α : Type) where
  | nil
  | cons (head : α) (tail : Lst α)

-- dot-notation + an equational proof over a user parametric inductive
def empty : Maybe Nat := .nothing
def full  : Maybe Nat := .just 7

theorem empty_is_nothing : empty = Maybe.nothing := rfl
