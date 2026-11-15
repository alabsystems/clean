module

/-!
# CompanionProbe — fixture [F7]

Consumed by `crates/clean-olean/src/import/load_parse/companion_extension_tests.rs`
(7 sites). Compiled by the pinned `leanprover/lean4:v4.30.0-rc2` as module
`CompanionProbe` (`lean --root . -o CompanionProbe.olean CompanionProbe.lean`,
cwd = this directory), so the `module` header makes Lean write the three-part
triple `CompanionProbe.olean{,.server,.private}` and every `private` name
mangles to `_private.CompanionProbe.0.CompanionProbe.*`
(`Lean/PrivateName.lean:29-30`, `mkPrivateNameCore mainModule n =
Name.mkNum (_private ++ mainModule) 0 ++ n`).

Every shape below is load-bearing for a literal in the test file; see
`README.md` beside this file for the measured numbers.

* Under the `module` header a declaration with no visibility modifier is
  PRIVATE (`Lean/Elab/DeclModifiers.lean:68-69`,
  `Visibility.isInferredPublic`), so the four public rows carry an explicit
  `public` and the four private rows an explicit `private`.
* The classes are `Prop`-valued on purpose. A `Type`-valued structure makes
  Lean register `<class>._sizeOf_inst` through `registerInstance`
  (`Lean/Meta/SizeOf.lean:493-528`, skipped for an inductive predicate) and
  tag `<class>.mk.injEq` `@[simp]`; either would add rows to the very two
  extensions whose row counts the tests pin (exactly 2
  `Lean.Meta.instanceExtension` rows in the private part; recognized rows
  `[5, 5, 7]`).
* `Lean.Meta.instanceExtension` and `Lean.Meta.simpExtension` export a
  private name only at `OLeanLevel.private` (`Lean/Meta/Instances.lean:95-96`,
  `Lean/Meta/Tactic/Simp/SimpTheorems.lean:664-675`); `Lean.classExtension`
  and `Lean.aliasExtension` export uniformly to all three parts
  (`registerSimplePersistentEnvExtension`, `Lean/EnvExtension.lean:51-53`,
  `.uniform`). That split is what makes the private part carry two more
  recognized rows than the base and server parts.
-/

namespace CompanionProbe

public class «public.class» : Prop where
  holds : True

private class «private.class» : Prop where
  holds : True

public instance «public.instance» : «public.class» := ⟨trivial⟩

private instance «private.instance» : «private.class» := ⟨trivial⟩

@[simp] public theorem «public.lemma» : (0 : Nat) + 0 = 0 := rfl

@[simp] private theorem «private.lemma» : (1 : Nat) + 0 = 1 := rfl

namespace PublicExports

public def «target.dot» : Nat := 0

end PublicExports

-- Registers the `Lean.aliasExtension` row
-- `CompanionProbe.«target.dot» ↦ CompanionProbe.PublicExports.«target.dot»`
-- (`Lean/Elab/BuiltinCommand.lean:294-306`, `currNamespace ++ id`).
export PublicExports («target.dot»)

end CompanionProbe
