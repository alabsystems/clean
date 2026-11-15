-- InstanceParity: fixture family [F8], consumed by
-- crates/clean-olean/src/import/load_register/instance_metadata_tests.rs (6 sites).
-- README.md beside this file records the recipe, the two oracle invocations
-- and every measured number.
--
-- Shape constraints (each one is asserted by a consumer; see README.md):
-- * `prelude` with NO imports: the module references no constant outside
--   itself (measured: every type_refs/value_refs name is in const_names), so
--   the direct loader can register it into an empty `Environment` and the env
--   oracle's `importModules` needs nothing but this file.
-- * No `module` header: a single base `InstanceParity.olean` is written, which
--   is all `parse_load_module` reads.
-- * `Type`-valued classes, so the two `instance`s are `definition`s (a
--   `Prop`-valued class turns its instances into `theorem`s) and nothing
--   generates a `SizeOf` instance (`SizeOf` is not in scope without Init).
-- * Exactly two `Lean.Meta.instanceExtension` rows: `«registered.dot»` at
--   the explicit priority 731 and `removed` at Lean's default 1000. Exactly
--   two `Lean.classExtension` rows: `Actual` and `Removed`.
-- * The negatives are ordinary values whose type is a class (`plainActual`,
--   `plainRemoved` — `@[reducible]` only silences `warn.classDefReducibility`,
--   `Lean/Elab/MutualDef.lean:1241-1248`; it registers nothing), a plain
--   `structure Plain` that is not a class, and `plainValue : Plain`.
prelude

class InstanceParity.Actual : Type where
class InstanceParity.Removed : Type where

instance (priority := 731) InstanceParity.«registered.dot» : Actual := ⟨⟩
instance InstanceParity.removed : Removed := ⟨⟩

@[reducible] def InstanceParity.plainActual : Actual := ⟨⟩
@[reducible] def InstanceParity.plainRemoved : Removed := ⟨⟩

structure InstanceParity.Plain : Type where
def InstanceParity.plainValue : Plain := ⟨⟩
