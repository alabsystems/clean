-- ImportPassesStubs: consumed by
-- crates/clean-olean/src/import/tests_import_passes_fixture.rs.
-- README.md beside this file records the recipe and what each shape pins.
--
-- The ONE shape in which Lean writes projection functions as value-free stubs
-- that a later part of the same artifact completes. A structure-LIKE
-- `inductive` has no structure-extension entry, so its field table can only be
-- recovered from its projection functions. Under the `module` header a public
-- `def` that is not `@[expose]` is exported as an `axiom` (no value) in the
-- `.olean` and `.olean.server` parts, and only the `.olean.private` part states
-- it as a definition with its `Expr.proj` body. (A `structure`'s own
-- projections are exported WITH their values in every part, so they never
-- arrive this way.)
module
prelude
public import ImportPassesCarrier

public inductive StubParts.Pair : Type where
  | mk (x y : StubParts.N) : StubParts.Pair

public def StubParts.Pair.first (p : StubParts.Pair) : StubParts.N := p.1
public def StubParts.Pair.second (p : StubParts.Pair) : StubParts.N := p.2
