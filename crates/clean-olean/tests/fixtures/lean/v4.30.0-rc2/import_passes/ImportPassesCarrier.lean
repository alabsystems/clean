-- ImportPassesCarrier: imported by ImportPassesStubs.lean beside this file;
-- README.md records the recipe and what each shape pins.
--
-- A module-system artifact (`module`, so Lean writes the triple
-- `.olean{,.server,.private}`) that loads BEFORE ImportPassesStubs. Its only
-- job is to be a whole earlier artifact: the importer decides projection field
-- tables only in the part an artifact is read through (a module-system
-- artifact's `.olean.private`), so by the time ImportPassesStubs loads, this
-- artifact's decision has already run and the projection index is the
-- incremental one, not a fresh whole-environment rebuild.
module
prelude

public inductive StubParts.N : Type where
  | zero : StubParts.N
