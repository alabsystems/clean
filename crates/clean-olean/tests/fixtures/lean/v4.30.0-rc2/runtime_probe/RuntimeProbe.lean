-- RuntimeProbe: the module-system runtime fixture shared by
-- crates/clean-olean/tests/runtime_declarations.rs, crates/clean-olean/src/expr/bvar_tests.rs
-- and crates/clean-compiler/src/runtime_lcnf (CLEAN_RUNTIME_LCNF_FIXTURE).
-- README.md beside this file records the recipe and every measured number.
--
-- Shape constraints (each one is asserted by a consumer; see README.md):
-- * `module` header, so Lean writes the base/.server/.private triple and exports
--   non-exposed bodies as value-less axiom stubs.
-- * `prelude` + `public import Init.Prelude`: the whole reference closure of this
--   module lives in Init.Prelude, the one library module the compiler tests pair
--   it with; it also keeps `SizeOf` (Init.SizeOf) and `Eq.propIntro` (Init.Core)
--   out of scope, so no `_sizeOf_*`/`sizeOf_spec`/`inj`/`injEq` auxiliaries are
--   generated and the exported part holds exactly 24 constants.
-- * No other declaration name may contain the string "Unary": the base part must
--   intern "Unary\0" exactly once.
-- * Exactly one private-only constant: the matcher generated for `count`,
--   `_private.RuntimeProbe.0.RuntimeProbe.count.match_1`.
module

prelude
public import Init.Prelude

public inductive Unary
  | zero
  | succ (n : Unary)

public partial def RuntimeProbe.count : Unary → Unary
  | .zero => .zero
  | .succ n => .succ (count n)

public def RuntimeProbe.«count._unsafe_rec» : Unary → Unary := fun x => x

public def RuntimeProbe.safe._unsafe_rec : Unary → Unary := fun x => x

public opaque RuntimeProbe.sealed : Nat

public axiom RuntimeProbe.postulate : Nat
