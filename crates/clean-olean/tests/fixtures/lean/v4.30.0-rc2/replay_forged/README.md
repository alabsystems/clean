# `replay_forged` — `.olean`s Lean's kernel never admitted (package P0_SOUND)

`GenReplayForged.lean` is a `lean --run` **generator**, not a module source. Each family builds
an environment from a small import, names the main module, adds its declarations through
`Lean.Environment.addDeclCore`, and writes the result with `Lean.writeModule`, the serializer
behind every stdlib `.olean`. The `forged*` families pass `doCheck := false`, which is the
kernel bypass `set_option debug.skipKernelTC true` uses. So their `.olean`s carry declarations
Lean's kernel never checked. The `honest*` families pass `doCheck := true`, so Lean's kernel
admits every declaration before it is written.

These are the light-import twins of the audit forgeries (`Forged.lean`, `Forged3.lean` and
`Forged4.lean`, measured 2026-09-23, which `import Lean` and so pull in over 1,500 modules).
The declarations are the same; only the import differs, which keeps the closure small enough
for a debug-build test.

| Output | Import | Declarations | `leanchecker` (pinned v4.30.0-rc2, 2026-09-24) |
|---|---|---|---|
| `ReplayForged.olean` | `Init.Prelude` | `forged_self : False := forged_self`; `forged_cycA := forged_cycB`, `forged_cycB := forged_cycA`; `forged_bad : False := True.intro` | rc 1: `(kernel) declaration type mismatch, 'forged_bad'`. `leanchecker` stops at the first failure it replays. |
| `ReplayForged3.olean` | `Init.Prelude` | the self-reference and the two-cycle only | rc 1: `(kernel) unknown constant 'forged3_self'` |
| `ReplayForged4.olean` | `Init.System.Platform` (28 modules) | `isOSX = true`, `isOSX = false`, `isWindows = false`, `isEmscripten = false`, each `:= Eq.refl _` | rc 1: `(kernel) declaration type mismatch` (the `@[extern] opaque` platform queries are stuck in Lean's kernel) |
| `ReplayForged5.olean` | `Init.Prelude` | `forged5_unsafe : False := @unsafeCast True False True.intro` | rc 1: `(kernel) invalid declaration, it uses unsafe declaration 'unsafeCast'` |
| `ReplayCrossA.olean` | `Init.Prelude` | `cross_forged : False := cross_forged`; `cross_honest : True := True.intro` | rc 1: `(kernel) unknown constant 'cross_forged'` |
| `ReplayCrossB.olean` | `ReplayCrossA` | CHECKED by Lean's kernel with `ReplayCrossA` as a trusted import: `cross_uses_forged : False := cross_forged`; `cross_uses_honest : True := cross_honest` | rc 0 (imports are trusted); `leanchecker --fresh ReplayCrossB` rc 1: `unknown constant 'cross_forged'` |
| `ReplayHonest.olean` | `Init.Prelude` | `honest_t : True`; `honest_chain := honest_t`; `honest_one : Nat`; `honest_one_eq : honest_one = 1 := rfl` | rc 0 |
| `ReplayHonestUnsafe.olean` | `Init.Prelude` | CHECKED: `unsafe def honest_unsafe_val : Nat := Nat.zero`; `honest_safe : True := True.intro` | rc 0 (`Lean.Environment.replay` leaves the unsafe definition out of `remaining`) |
| `ReplayHonest4.olean` | `Init.System.Platform` | `honest4_osx_refl : isOSX = isOSX := rfl` | rc 0 |
| `ReplayPrelude.olean` | `Init.Prelude` | `prelude_sorry : False := @sorry False`, `prelude_arith`/`prelude_ay` the same through `trustedArith`/`trustedAy` (Clean-prelude axioms `{α : Sort u} → α`, no Lean constant); `Nat.not_succ_lt_zero : False := True.intro` (a name only Clean's prelude holds); `prelude_honest : True` | rc 1: `(kernel) unknown constant 'trustedArith'`. Per constant (`Lean.Environment.replay`): each of `sorry`/`trustedArith`/`trustedAy` unknown, `Nat.not_succ_lt_zero` type mismatch, `prelude_honest` ok |
| `ReplayPreludeUse.olean` | `Init.Prelude` | `Nat.not_succ_lt_zero : True := True.intro`; `prelude_shadow_use : ∀ n, Nat.lt (n+1) 0 → False := Nat.not_succ_lt_zero` (the type of Clean's prelude theorem of that name) | rc 1: `(kernel) declaration type mismatch, 'prelude_shadow_use'` |
| `ReplayRedeclare.olean` | `Init.Prelude` | `Nat.pred := fun _ => 7` (a redeclaration of an `Init.Prelude` constant); `redecl_pred : Nat.pred 0 = 7 := rfl` | rc 1: `(kernel) constant has already been declared 'Nat.pred'` (both constants, per constant); `--fresh` rc 1: `import ReplayRedeclare failed, environment already contains 'Nat.pred' from Init.Prelude` (measured 2026-09-28) |
| `ReplayForgedRec.olean` | `Init.Prelude` | `inductive FRT \| a \| b` admitted by Lean's kernel, then `FRT.rec` overwritten with NO minor premises (`{motive} → (t : FRT) → motive t`); `forged_rec_false : False := @FRT.rec (fun _ => False) FRT.a` | rc 1: `(kernel) application type mismatch` for `forged_rec_false`; per constant `FRT.rec`: `Invalid recursor FRT.rec` |
| `ReplayForgedRule.olean` | `Init.Prelude` | `inductive FRR \| a \| b`, then `FRR.rec`'s rule for `FRR.b` overwritten with the rule for `FRR.a`; `forged_rule_eq : @FRR.rec (fun _ => Bool) true false FRR.b = true := rfl` | rc 1: `(kernel) declaration type mismatch, 'forged_rule_eq'`; per constant `FRR.rec`: `Invalid recursor FRR.rec` |
| `ReplayForgedCtor.olean` | `Init.Prelude` | `inductive FRC \| a`, then the constructor `FRC.a` overwritten with type `False`; `forged_ctor_false : False := FRC.a` | rc 1: `(kernel) invalid return type for 'FRC.a'` (the block is rebuilt from the stored constructor type); per constant `FRC.a`: `No such constructor FRC.a` |
| `ReplayForgedQuot.olean` | `Init.Prelude` | `Quot.ind` stored as a `quotInfo` typed `∀ p : Prop, p`; `forged_quot_false : False := Quot.ind False` | rc 1: `(kernel) incorrect number of universe levels parameters for 'Quot.ind'` (replay installs the kernel's canonical quotient) |
| `ReplayForgedStr.olean` | `Init.Data.String.TakeDrop`, `Init.Data.String.Modify` | five `rfl` equations false in Lean 4.30: `"abc".drop 1 = "xbc".drop 1` and `"abc".take 1 = "abd".take 1` (a `String.Slice` remembers its string), `"\u3000x".trimLeft = "x"` (ASCII-only trim), `"Ä".toLower = "ä"`, `"ß".toUpper = "SS"` (ASCII-only case maps) | rc 1: `(kernel) declaration type mismatch`, each of the five per constant |
| `ReplayHonestStr.olean` | same | CHECKED: `"abc".drop 1 = "abc".drop 1`, `"AB".toLower = "AB".toLower` | rc 0 |
| `ReplayForgedIte.olean` | `Init.Prelude` | `forged_ite_overapp : (ITE 1) = (ITE 0) := rfl` where `ITE := @ite (Nat → Nat) True (isTrue ..) (fun n => n) (fun _ => 0)`; `ITE k` should reduce to `k`, so the equation is `1 = 0` | rc 1: `(kernel) declaration type mismatch, 'forged_ite_overapp'` (`ITE 1` reduces to `1`, `ITE 0` to `0`) |
| `ReplayHonestIte.olean` | `Init.Prelude` | CHECKED: the same over-applied `ite`, `honest_ite_overapp : (ITE 1) = 1 := rfl` | rc 0 |
| `ReplayHonestDeltaProp.olean` | `Init.Prelude` | CHECKED: `def hdp_prop : Type := Prop`; `inductive HDP : hdp_prop \| t \| f`, a `Prop` family only up to whnf, added through `addDeclCore` (the `inductive` command fails at `HDP.ctorIdx`), whose kernel-generated `HDP.rec` eliminates only into `Prop`; `honest_dp_irrel : HDP.t = HDP.f := Eq.refl HDP.t` (proof irrelevance); `honest_dp_elim : True` by `HDP.rec` into `True` | rc 0 (`--fresh` rc 0) (measured 2026-10-16) |
| `ReplayForgedDeltaPropLargeElim.olean` | `Init.Prelude` | the same block over `fdp_prop`, admitted by Lean's kernel, then `FDP.rec` overwritten with a LARGE eliminator (universe parameter `u`, motive `FDP → Sort u`, the same minors and rules); `forged_dp_false : False` through `FDP.rec.{1}` into `Bool` (`Eq.rec` along `FDP.t = FDP.f`) | rc 1: `(kernel) incorrect number of universe levels parameters for 'FDP.rec', #0 expected, #1 provided` while replaying `forged_dp_false` (`--fresh` the same) (measured 2026-10-16) |
| `ReplayHonestSortU.olean` | `Init.Prelude` | CHECKED: `inductive HSU.{u} : Sort u \| t \| f`, added through `addDeclCore` (the `inductive` command refuses a resulting universe that may be `Prop` unless `bootstrap.inductiveCheckResultingUniverse` is off), whose kernel-generated `HSU.rec` has no motive universe (`u` is not provably nonzero); `honest_su_irrel : HSU.t.{0} = HSU.f.{0}` by proof irrelevance; `honest_su_elim : True` by `HSU.rec.{0}` into `True` | rc 0 (`--fresh` rc 0) (measured 2026-10-17) |
| `ReplayForgedSortULargeElim.olean` | `Init.Prelude` | the same block over `FSU`, admitted by Lean's kernel, then `FSU.rec` overwritten with a LARGE eliminator (universe parameters `[u_1, u]`, motive `FSU → Sort u_1`); `forged_su_false : False` through `FSU.rec.{1, 0}` into `Bool` at `u := 0` | rc 1: `(kernel) incorrect number of universe levels parameters for 'FSU.rec', #1 expected, #2 provided` while replaying `forged_su_false` (`--fresh` the same) (measured 2026-10-17) |
| `ReplayHonestInd.olean` | `Init.Core` | COMPILED from `ReplayHonestInd.lean` by `lean -o`: an enumeration, a recursive type, a parameterised structure, an indexed family, a K-like `Prop` family, a mutual pair and a nested type, each with the auxiliary definitions Lean's elaborator generates, and theorems computing through their recursors | rc 0 (every constant, per constant) |
| `ReplayHonestSortDefBase.olean` | `Init.Core` | COMPILED from `ReplayHonestSortDefBase.lean` by `lean -o`: `def HSDSort : Type 1 := Type` | inside `leanchecker --fresh ReplayHonestSortDef`'s closure, rc 0; a release `clean olean replay --exact` admits its 1 declaration (measured 2026-10-19) |
| `ReplayHonestSortDef.olean` | `ReplayHonestSortDefBase` | COMPILED from `ReplayHonestSortDef.lean` by `lean -o`: `inductive HSD : HSDSort \| mk : Bool → HSD`, a `Type` family only up to whnf through the IMPORTED `HSDSort`, with its auxiliary definitions, `hsd_use`, `hsd_bit` (by `HSD.rec`) and `hsd_bit_mk := rfl` | rc 0 (`--fresh` rc 0); a release `clean olean replay --exact` admits all 17 declarations, and `--fresh` all 4,385 of the closure (measured 2026-10-19). Before R147 `per-constant-verify` refused all 14 value-bearing declarations (`Invalid recursor HSD.rec`) |
| `ReplayForgedThmType.olean` | `Init.Prelude` | `forged_thm_nat : Nat := Nat.zero`, stored as a `thmInfo` (a theorem whose type is a type) | rc 1: `(kernel) type of theorem 'forged_thm_nat' is not a proposition` (`--fresh` the same) |
| `ReplayForgedUniv.olean` | `Init.Prelude` | `forged_univ : ∀ (α : Sort u) (a : α), a = a := fun α a => Eq.refl a` with NO universe parameters (`u` undeclared) | rc 1: `(kernel) invalid reference to undefined universe level parameter 'u'` (`--fresh` the same) |
| `ReplayForgedDupUniv.olean` | `Init.Prelude` | the same theorem with universe parameters `[u, u]` | rc 1: `(kernel) failed to add declaration to environment, duplicate universe level parameter: 'u'` (`--fresh` the same) |
| `ReplayHonestUniv.olean` | `Init.Prelude` | CHECKED: `honest_univ.{u}`, the same theorem with `[u]` | rc 0 (`--fresh` rc 0) |
| `ReplayForgedLamType.olean` | `Init.Prelude` | `forged_lam_ax : fun (h : True) => h` (a "type" that is a lambda) and `forged_lam_thm : fun h => h := forged_lam_ax` | rc 1: `(kernel) type expected` for `forged_lam_ax` (`--fresh` the same) |
| `ReplayHonestBoolAx.olean` | `Init.Prelude` | CHECKED: `axiom bool_ax_b : Bool`, `axiom bool_ax_hb : bool_ax_b = false` | rc 0 (`--fresh` rc 0) |
| `ReplayForgedBoolDef.olean` | `ReplayHonestBoolAx` | `def bool_ax_b := true` over the imported axiom, and `forged_bool_false : False` by `Eq.rec` over `bool_ax_hb`, well typed only if `bool_ax_b` unfolds to `true` | rc 1: `(kernel) application type mismatch` for `forged_bool_false` (checked against the imported axiom); `--fresh` rc 1: `import ReplayForgedBoolDef failed, environment already contains 'bool_ax_b' from ReplayHonestBoolAx` |
| `ReplayForgedQuotRedecl.olean` | `Init.Core` | `axiom Quot.sound` with its own statement, which `Init.Core` already declares | rc 1: `(kernel) constant has already been declared 'Quot.sound'`; `--fresh` rc 0 (the two axioms merge) |
| `ReplayForgedQuotIndAxiom.olean` | `Init.Prelude` | `axiom Quot.ind` with the canonical statement of `Init.Prelude`'s quotient | rc 1: `(kernel) constant has already been declared 'Quot.ind'`; `--fresh` rc 1: `environment already contains 'Quot.ind' from Init.Prelude` |
| `ReplayHonestPropAx.olean` | `Init.Prelude` | CHECKED: `axiom prop_ax_p : True` | rc 0 (`--fresh` rc 0) |
| `ReplayForgedThmOverAx.olean` | `ReplayHonestPropAx` | `theorem prop_ax_p : True := True.intro` over the imported axiom | rc 1: `(kernel) constant has already been declared 'prop_ax_p'`; `--fresh` rc 0 (the import merges them: the theorem subsumes the axiom) |
| `ReplayHonestIndAx.olean` | `Init.Prelude` | CHECKED: `axiom ind_ax_t : Prop`, `axiom ind_ax_not : ¬ind_ax_t` (jointly consistent: `ind_ax_t := False`) | rc 0 (`--fresh` rc 0) (measured 2026-09-28) |
| `ReplayForgedIndOverAx.olean` | `ReplayHonestIndAx` | `inductive ind_ax_t : Prop \| mk` over the imported axiom (the block admitted by Lean's kernel without the import, then inserted unchecked); `forged_ind_false : False := ind_ax_not ind_ax_t.mk` | rc 1: `(kernel) constant has already been declared 'ind_ax_t'`; `--fresh` rc 1: `import ReplayForgedIndOverAx failed, environment already contains 'ind_ax_t' from ReplayHonestIndAx` (measured 2026-09-28) |
| `ReplayForgedPriv.olean` (+ `.olean.server`, `.olean.private`) | `Init.Prelude` | a `module`-system artifact written part by part: `_private.ReplayForgedPriv.0.priv_self : False := priv_self`, in `.olean.private` only, and the public `priv_user : False := priv_self` | rc 1: `(kernel) unknown constant '_private.ReplayForgedPriv.0.priv_self'` (measured 2026-09-29) |
| `ReplayForgedPrivBad.olean` (+ parts) | `Init.Prelude` | the same shape with no self-reference: the private `priv_bad : False := True.intro` and the public `priv_bad_user : False := priv_bad` | rc 1: `(kernel) declaration type mismatch, '_private.ReplayForgedPrivBad.0.priv_bad'` (measured 2026-09-29) |
| `ReplayHonestPriv.olean` (+ parts) | `Init.Prelude` | CHECKED: the private `priv_ok : True := True.intro` and the public `priv_ok_user : True := priv_ok` | rc 0 (measured 2026-09-29) |
| `ReplayHonestOpaqueAx.olean` | `Init.Prelude` | CHECKED: `opaque op_b : Bool` (value `false`) and `axiom op_hb : op_b = false` | rc 0 (measured 2026-09-29) |
| `ReplayForgedOpaqueDef.olean` | `ReplayHonestOpaqueAx` | `def op_b := true` over the imported opaque, and `forged_op_false : False` by `Eq.rec` over `op_hb`, well typed only if `op_b` unfolds to `true` | rc 1: `(kernel) constant has already been declared 'op_b'`; `--fresh` rc 1: `environment already contains 'op_b' from ReplayHonestOpaqueAx` (measured 2026-09-29) |
| `ReplayForgedOpaqueUse.olean` | `ReplayHonestOpaqueAx`, and `ReplayForgedOpaqueDef` in its header only | the same proof of `False`, `forged_op_use`, built over `ReplayHonestOpaqueAx` alone | rc 1: `import ReplayForgedOpaqueDef failed, environment already contains 'op_b' from ReplayHonestOpaqueAx` (measured 2026-09-29) |
| `ReplayForgedQuotDef.olean` | `Init.Core` | the KERNEL's `Quot` redefined as `def Quot := fun {α} _ => α` at `Quot`'s own type, and `quot_def_false : False` from `Quot.ind` and `Quot.sound` (every `b : Bool` is `Quot.mk r true` once `Quot r` unfolds to `Bool`) | rc 1: `(kernel) constant has already been declared 'Quot'`; `--fresh` rc 1: `environment already contains 'Quot' from Init.Prelude` (measured 2026-09-29) |
| `ReplayForgedAllGhost.olean` | `Init.Prelude` | `FAG : Prop` with the NEGATIVE constructor `FAG.mk : (FAG → False) → FAG` (Lean's kernel refuses it), inserted unchecked with `all := [FAG_ghost]` (no such constant) and no recursor; `forged_all_ghost_false : False := (fun x : FAG => x.1 x) (FAG.mk (fun x => x.1 x))` | rc 1: its replay panics (`key is not present in hash table`, looking up `FAG_ghost`), then `(kernel) unknown constant '_inhabitedExprDummy'` while replaying `FAG` (`--fresh` the same) (measured 2026-10-22) |
| `ReplayForgedAllOther.olean` | `Init.Prelude` | CHECKED `inductive FAH \| a`, then the same negative `FAO : Prop` inserted unchecked with `all := [FAH, FAO]` (the honest type first) and no recursor; `forged_all_other_false : False` the same way | rc 1: `(kernel) constant has already been declared 'FAH'` while replaying `FAO` (`--fresh` the same) (measured 2026-10-22) |
| `ReplayForgedIsRec.olean` | `Init.Prelude` | `inductive FIR : Type \| mk : FIR → FIR` admitted by Lean's kernel, then its `inductInfo` overwritten with `isRec := false`; `forged_isrec_eta : ∀ x : FIR, FIR.mk x.1 = x := fun x => rfl` (structure eta, which Lean grants only a non-recursive structure) | rc 1: `(kernel) declaration type mismatch, 'forged_isrec_eta'` (`--fresh` the same) (measured 2026-10-22) |
| `ReplayForgedMutualEta.olean` | `Init.Prelude` | CHECKED `mutual inductive HMA \| a : HMA; inductive HMB \| b : HMA → HMB end` (Lean stores `isRec := true` on both: the flag is block-level), then `forged_hma_eta : ∀ x y : HMA, x = y := fun x y => rfl` (unit-like eta on `HMA`) | rc 1: `(kernel) declaration type mismatch, 'forged_hma_eta'` (`--fresh` the same) (measured 2026-10-22) |
| `ReplayHonestIndFlags.olean` | `Init.Prelude` | CHECKED: the mutual `HMA`/`HMB` (stored `isRec := true` on the non-recursive `HMA`); `structure HBox (α : Type) where f : Nat → α` and `inductive HNR \| mk : HBox HNR → HNR`, nested (stored `isReflexive := true`, `numNested := 1`: Lean reads reflexivity off the auxiliary declaration); `inductive HWT \| leaf \| branch : (Nat → HWT) → HWT` (reflexive); two definitions over them | rc 0 (`--fresh` rc 0) (measured 2026-10-22) |
| `ReplayHonestDepNested.olean` | `Init.Core` | CHECKED: blocks nested through a DEPENDENT container whose family argument is a lambda: `SGS \| mk : (Σ _ : Nat, Nat → SGS) → SGS`, `SG \| mk : (Σ n : Nat, Fin n → SG) → SG`, `SGP` (the same through `PSigma`), the user container `structure DBox (α : Type) (β : α → Type)` with `DB \| mk : DBox Nat (fun n => Fin n → DB) → DB`, and `SJ \| leaf \| node : (Σ _ : Nat, SJ) → SJ` (a single-level stand-in for the redex in `Lean.Json`'s map field; `ReplayHonestDepNestedDeep` has its real shape); `honest_sgs_elim` through `SGS.rec`, and `honest_sj_depth : SJ.rec … (SJ.node ⟨0, SJ.leaf⟩) = 1 := rfl`. Lean's elimination instantiates the container without a β step, so each auxiliary constructor's field is a redex (`(fun _ => Nat → SGS) fst`): Lean stores `isReflexive := false` on `SGS`/`SG`/`SGP`/`DB` and the redexes in every recursor | rc 0 (`--fresh` rc 0); per constant all 26 accepted (measured 2026-10-23) |
| `ReplayForgedDepNestedRefl.olean` | `Init.Core` | the CHECKED `SGS` block with its `inductInfo` then overwritten with `isReflexive := true` (the value a β-reducing checker computes), and the CHECKED `forged_sgs_elim` over it | rc 0 (`--fresh` rc 0): Lean's replay installs the regenerated value and never reads the stored flag. Clean refuses the block (`reflexive flag (isReflexive)`, R112: Clean checks later declarations against the STORED value) |
| `ReplayForgedPowCap.olean` | `Init.Prelude` | CHECKED `pow_one_at_cap : Nat.pow 1 16777216 = 1 := rfl` (the exponent `2^24`, which Lean's `reduce_pow` still folds) and `pow_small : Nat.pow 2 10 = 1024`; FORGED `pow_one_over_cap : Nat.pow 1 16777217 = 1` and `pow_zero_over_cap : Nat.pow 0 16777217 = 0`, each `:= rfl` | rc 1: `while replaying declaration 'pow_one_over_cap': (kernel) deep recursion detected` (`--fresh` the same); per constant both forgeries `deep recursion detected`, both controls accepted (measured 2026-10-23) |
| `ReplayForgedLevelJoin.olean` | `Init.Prelude` | CHECKED `axiom LJA.{u,v} : Sort (max (u+1) (max (v+1) (imax (v+1) u)))`, `def LJC : Sort <that level> := LJA`, `axiom LJK.{a,b} : Sort (max a b)` and `def LJF.{u,v} : Sort (max u (imax v u)) := LJK.{u, imax v u}`; FORGED `def LJB.{u,v} : Sort (max (u+1) (v+1)) := LJA`, `def LJD.{v,w} : Sort (succ (max v (succ w))) := Sort (max (max v (imax v w)) (succ w))` and `def LJE.{u,v} : Sort (imax v u) := LJK.{u, imax v u}`: each states a level semantically equal to the inferred one but not `is_equivalent` to it (an `imax` argument dominated only by the join of the others) | rc 1: `while replaying declaration 'LJB': (kernel) declaration type mismatch` (`--fresh` the same); per constant `LJB`, `LJD` and `LJE` `declaration type mismatch`, the four controls accepted (measured 2026-10-23) |
| `ReplayHonestLevelAssoc.olean` | `Init.Prelude` | CHECKED: `axiom X.{a,b} : Sort (imax a b)`, `axiom Y.{a,b} : Sort (max a (b+1))`, `def P1 : Sort (max (max (imax a b) a) (b+1)) := X → Y`, `axiom A1 : Sort (max a (max (b+1) (imax a b)))`, `def B1 : Sort (max (max a (b+1)) (imax a b)) := A1`, `axiom LA.{u,v} : Sort (max u (max v (imax u v)))` and `def LB : Sort (max (max u v) (imax u v)) := LA`: each states a level `is_equivalent` to the inferred one, spelled so that Clean's `Level::max`/`Level::imax` (which simplify by semantic `is_geq` in the decoder, in instantiation and in Pi inference) build the two sides differently | rc 0; per constant all seven accepted (measured 2026-10-24). A Lean-theory level check by `is_equivalent` over the levels Clean built refused `B1` and `P1` (review K3; `reports/kernel-fidelity-2026-10-24/level-assoc/`); Clean refused `LB` in every theory until R150. Since R150 every lane admits all seven |
| `ReplayForgedLevelAssoc.olean` | `Init.Prelude` | CHECKED `axiom LJA2.{u,v} : Sort (max (max (u+1) (v+1)) (imax (v+1) u))` and `axiom LJS1.{u,v} : Sort (succ (imax u (v+1)))`; FORGED `def LJB2 : Sort (max (u+1) (v+1)) := LJA2` (`LJB` re-associated) and `def LJS2 : Sort (succ (max u (v+1))) := LJS1` | rc 1: `while replaying declaration 'LJB2': (kernel) declaration type mismatch` (`--fresh` the same); per constant `LJB2` and `LJS2` `declaration type mismatch`, both axioms accepted (measured 2026-10-24). Clean admitted all four (review K4) until R150; every lane now refuses `LJB2` as a mismatch and `LJS2` by R150's sharing rule (`LevelSharingDependent`: `LJS1`'s stored `imax u (v+1)` is one Lean's `mk_imax` rebuilds) |
| `ReplayForgedMutualLevel.olean` | `Init.Prelude` | the CHECKED mutual block `MA \| a`, `MB \| b`, both at `Sort (max (u+1) (v+1))`, with `MB`'s stored `inductInfo` type then overwritten with `Sort (max (u+1) (max (v+1) (imax (v+1) u)))`: equal at every assignment, not `is_equivalent` | rc 1: `while replaying declaration 'MA': (kernel) mutually inductive types must live in the same universe` (measured 2026-10-24). Clean admitted the block (review K5: `is_geq` both ways) until R150; every lane now refuses it (`mutual member MB lives in a different universe`) |
| `ReplayForgedPowCapOuter.olean` | `Init.Prelude` | CHECKED `mul_at_zero : Nat.mul (1^16777216) 0 = 0` and `add_at_zero : Nat.add (1^16777216) 0 = 1^16777216`; FORGED the same over `1^16777217` (`mul_over_zero`, `add_over_zero`, `sub_over_zero`), `pow_over_exp0 : Nat.pow (1^16777217) 0 = 1` and `mul_over2_zero : Nat.mul (2^16777217) 0 = 0`, each `:= rfl` (`^` is `Nat.pow`) | rc 1: `while replaying declaration 'mul_over_zero': (kernel) deep recursion detected`; per constant the five forgeries `deep recursion detected`, both controls accepted (measured 2026-10-24). Clean admits all seven: the outer operation δ-reduces past the stuck over-cap `Nat.pow` (review K1; a known gap) |
| `ReplayForgedShlCap.olean` | `Init.Data.Nat.Bitwise.Basic` | CHECKED `shl_zero_base : Nat.shiftLeft 0 4294967296 = 0` and `shl_cong_small : Nat.shiftLeft 1 2000 = Nat.shiftLeft 1 (1999 + 1)`; FORGED the same congruence at shift `2^32` (`shl_cong`) and `2^64` (`shl_cong64`), each `:= rfl` | `INTERNAL PANIC: Nat.shiftl exponent is too big`, exit 1 (measured 2026-10-24): Lean's kernel aborts the process. Clean admits all four by congruence (review K2; a known gap) |
| `ReplayHonestDepNestedDeep.olean` | `Init.Core` | COMPILED from `ReplayHonestDepNestedDeep.lean` by `lean -o`: `Lean.Json`'s nesting shape in small, a structure `DR` over the RECURSIVE dependent container `DM (α) (β : α → Type)`, used as `RJ \| leaf \| obj (r : DR RJ)` (so `DM Nat (fun _ => RJ)`), with `honest_rj_obj` and `honest_rj_ne` | rc 0, all 80 constants (measured 2026-10-24). The base kernel refused the block and every user (`Invalid recursor RJ.rec_2`, 40 of 80) |
| `ReplayMisplacedServer.olean` (+ parts) | `Init.Prelude` | a `module`-system artifact whose CHECKED `inductive SO : Type \| mk : Nat → SO` (with its kernel recursor `SO.rec`) is written to `.olean.server` ALONE; `.olean` and `.olean.private` hold only `so_use : SO.mk 0 = SO.mk 0 := Eq.refl _`. `writeModule` never does this — every name of its `.olean`/`.olean.server` is a name of its `.olean.private` (measured over the pinned `lib/lean`: 2,302 artifacts, 314,344 names, 0 misplaced) | rc 1: `while replaying declaration 'so_use': (kernel) unknown constant 'SO'` (`lean` reads the private part, where `SO` does not exist) |
| `ReplayMisplacedServerPlain.olean` (+ parts) | `Init.Prelude` | the same `SOP`/`sop_use`, written WITHOUT the module system (`isModule` false); `SOP` is in `.olean.server` only (the generator also leaves it out of `.olean.private`) | rc 1: `while replaying declaration 'sop_use': (kernel) unknown constant 'SOP'` — the default mode replays the LAST part, `.olean.private`, which lacks `SOP`; `--fresh` (an importer) reads the `.olean` alone, which lacks it too |
| `ReplayHonestServerParts.olean` (+ parts) | `Init.Prelude` | CHECKED control: the same `SH`/`sh_use` block written as `writeModule` writes a `module` (every part holds the public names) plus a private `_private.…sh_priv`; every `.olean`/`.olean.server` name is a `.olean.private` name | rc 0 |
| `ReplayMisplacedOlean.olean` (+ parts) | `Init.Prelude` | a `module`-system artifact whose CHECKED `SX \| mk : Nat → SX` is in `.olean` and `.olean.server` but NOT `.olean.private`; `sx_use : SX.mk 0 = SX.mk 0` in every part (review finding P7, the `.olean` half of the misplaced rule) | rc 1: `while replaying declaration 'sx_use': (kernel) unknown constant 'SX'` (measured 2026-10-22) |
| `ReplayPartsValDis.olean` (+ parts) | `Init.Prelude` | a `module`: `pv_X := 1` in `.olean`/`.olean.server`, `pv_X := 0` in `.olean.private`; the CHECKED `pv_u : pv_X = 1` in every part (P2) | rc 1: `while replaying declaration 'pv_u': (kernel) declaration type mismatch` (default and `--fresh`) |
| `ReplayPartsValDep.olean` (+ parts, `.ir`) | `Init.Prelude` | the dependency form: `pd_X := 1` in `.olean`/`.olean.server`, `pd_X := 0` in `.olean.private` | rc 0 alone (nothing uses `pd_X`); Clean refuses it (its parts disagree), stricter than Lean |
| `ReplayPartsValDepUser.olean` | `ReplayPartsValDep` | non-module: `pd_t : pd_X = 1 := Eq.refl 1`, unchecked | rc 1: `while replaying declaration 'pd_t': (kernel) declaration type mismatch` (`lean` reads `pd_X := 0`) |
| `ReplayPartsImpE.olean`, `ReplayPartsImpF.olean` (+ parts, `.ir`) | `Init.Prelude` | CHECKED: `pi_Y := 0` (E) and `pi_Y := 1` (F) | rc 0 each |
| `ReplayPartsImpD.olean` (+ parts, `.ir`) | `ReplayPartsImpE` | a `module` whose `.olean`/`.olean.server` IMPORT `ReplayPartsImpF` and whose `.olean.private` imports `ReplayPartsImpE` (P3) | rc 0 alone; Clean refuses it (its parts state different imports), stricter than Lean |
| `ReplayPartsImpT.olean` | `ReplayPartsImpD` | non-module: `pi_t : pi_Y = 1`, unchecked | rc 1: `while replaying declaration 'pi_t': (kernel) declaration type mismatch` (`lean` follows the private part's import to `ReplayPartsImpE`, `pi_Y := 0`) |
| `ReplayMisplacedDep.olean` (+ parts, `.ir`) | `Init.Prelude` | a `module` whose CHECKED `MD \| mk : Nat → MD` (and `md_self`) is in `.olean`/`.olean.server` only; `.olean.private` holds `md_ok : True` (P1, honest content) | rc 0 alone; Clean refuses it (misplaced declaration), stricter than Lean |
| `ReplayMisplacedDepUser.olean` | `ReplayMisplacedDep` | non-module: `md_use : MD.mk 0 = MD.mk 0`, unchecked, written without extension entries | rc 1: `while replaying declaration 'md_use': (kernel) unknown constant 'MD'` (default and `--fresh`) |
| `ReplayHonestDep.olean` (+ parts, `.ir`), `ReplayHonestDepUser.olean` | `Init.Prelude` / `ReplayHonestDep` | CHECKED controls: `MD` in every part of the dependency, and the user's `md_use` checked | rc 0 each |
| `ReplayStubRefused.olean` (+ parts, `.ir`) | `Init.Prelude` | a `module` in `writeModule`'s own public-theorem layout (`Lean.addDecl` exports a theorem as an `axiomInfo` of its type): `.olean` and `.olean.server` hold the value-free stubs `axiom sr_t : 1 = 1` and `axiom sr_u : 1 = 1`; `.olean.private` holds `theorem sr_t : 1 = 1 := Eq.refl 2` (unchecked: Lean's kernel refuses the value) and the CHECKED `theorem sr_u : 1 = 1 := sr_t` (R131, review finding S1) | rc 1: `while replaying declaration 'sr_t': (kernel) declaration type mismatch` (default and `--fresh`) (measured 2026-10-23) |
| `ReplayStubHonest.olean` (+ parts, `.ir`) | `Init.Prelude` | CHECKED control in the same layout: `sh_t : 1 = 1 := Eq.refl 1`, `sh_u : 1 = 1 := sh_t` | rc 0 (default and `--fresh`) |
| `ReplayStubRefusedDep.olean` (+ parts, `.ir`) | `Init.Prelude` | the dependency form: the stub `srd_t : 1 = 1`, its private value `Eq.refl 2` unchecked | rc 1: `while replaying declaration 'srd_t': (kernel) declaration type mismatch` (default and `--fresh`) |
| `ReplayStubRefusedDepUser.olean` | `ReplayStubRefusedDep` | non-module: the CHECKED `srd_use : 1 = 1 := srd_t` | rc 0 (the default mode trusts the import); `--fresh` rc 1: `while replaying declaration 'srd_t': (kernel) declaration type mismatch` |
| `ReplayStubPlainDep.olean` (+ `.olean.server`) | `Init.Prelude` | NOT a `module`: `.olean` holds the stub `axiom spd_X : Nat`, `.olean.server` the CHECKED `def spd_X : Nat := 1` (review finding S2). Every importer reads a non-module artifact's `.olean` (`getData?`), and `writeModule` writes no companion for one | rc 0 (default and `--fresh`); Clean refuses it (its parts state `spd_X` differently), stricter than Lean |
| `ReplayStubPlainDepUser.olean` | `ReplayStubPlainDep` | non-module: `spd_t : spd_X = 1 := Eq.refl 1`, unchecked | rc 1: `while replaying declaration 'spd_t': (kernel) declaration type mismatch` (default and `--fresh`: `spd_X` is the axiom) |
| `ReplayStubPlainPrivDep.olean` (+ `.olean.private`), `ReplayStubPlainPrivDepUser.olean` | `Init.Prelude` / `ReplayStubPlainPrivDep` | the same with the definition `sppd_X := 1` in a `.olean.private` and no `.olean.server` (a part no Lean reader opens: `findOLeanParts` looks for it only beside a server part), and the user `sppd_t : sppd_X = 1`, unchecked | rc 0 on the dependency; rc 1 on the user (`declaration type mismatch, 'sppd_t'`, default and `--fresh`) |
| `ReplayStubPlainHonest.olean` (+ `.olean.server`), `ReplayStubPlainHonestUser.olean` | `Init.Prelude` / `ReplayStubPlainHonest` | CHECKED controls: not a `module`, `def sph_X : Nat := 1` in both parts, and the user `sph_t : sph_X = 1 := Eq.refl 1` | rc 0 each |
| `ReplayStubPlainTgt.olean` (+ `.olean.server`) | `Init.Prelude` | NOT a `module`: `.olean` holds the stub `axiom spt_f : 1 = 1` and the CHECKED `theorem spt_u : 1 = 1 := spt_f`; `.olean.server` holds `theorem spt_f : 1 = 1 := Eq.refl 2` (unchecked) and the same `spt_u` (review finding S3) | rc 1: `while replaying declaration 'spt_f': (kernel) declaration type mismatch` (the default mode replays the last part); `--fresh` rc 0 (an importer reads the `.olean`'s axiom) |
| `ReplayMisplacedOleanOnlyDep.olean` (+ parts, `.ir`), `ReplayMisplacedOleanOnlyDepUser.olean` | `Init.Prelude` / `ReplayMisplacedOleanOnlyDep` | a `module` whose CHECKED `MO \| mk : Nat → MO` (and `mo_self`) is in its `.olean` ALONE (`.olean.server` and `.olean.private` hold `mo_ok`), and a non-module user `mo_use : MO.mk 0 = MO.mk 0`, unchecked (review finding S5: the `.olean` half of the placement rule) | rc 0 on the dependency; rc 1 on the user: `while replaying declaration 'mo_use': (kernel) unknown constant 'MO'` (default and `--fresh`) |
| `ReplayMisplacedPrivPlainDep.olean` (+ parts), `ReplayMisplacedPrivPlainDepUser.olean` | `Init.Prelude` / `ReplayMisplacedPrivPlainDep` | NOT a `module`: the CHECKED `MP \| mk : Nat → MP` (and `mp_self`) is in its `.olean.private` ALONE (`.olean` and `.olean.server` hold `mp_ok`), and the user `mp_use : MP.mk 0 = MP.mk 0`, unchecked (S5: the `.olean.private` half) | rc 0 on the dependency; rc 1 on the user: `while replaying declaration 'mp_use': (kernel) unknown constant 'MP'` (default and `--fresh`) |
| `ReplayStubMv.olean` (+ parts, `.ir`) | `Init.Prelude` | a `module` in `writeModule`'s public-theorem layout over `theorem smv_f : 1 = 1 := ?m` (a metavariable, unchecked) and the CHECKED `theorem smv_u : 1 = 1 := smv_f` (R142, R131's verification S1-conv: Clean's converter cannot read the private value) | rc 1: `while replaying declaration 'smv_f': (kernel) declaration has metavariables 'smv_f'` (default and `--fresh`) (measured 2026-10-24) |
| `ReplayStubFv.olean` (+ parts, `.ir`) | `Init.Prelude` | the same over `theorem sfv_f : 1 = 1 := x` (a free variable) | rc 1: `(kernel) declaration has free variables 'sfv_f'` (default and `--fresh`) |
| `ReplayShadowAx.olean` (+ parts) | `Init.Prelude` | a `module` with the CHECKED `axiom sha_n : 1 = 1` | rc 0 |
| `ReplayShadowStub.olean` (+ parts, `.ir`) | `ReplayShadowAx` | a `module` in the stub layout whose `.olean`/`.olean.server` stub `sha_n`, the import's name and type, and `sh_u`; `.olean.private` holds `theorem sha_n : 1 = 1 := Eq.refl 2` (inserted unchecked over the import's axiom) and the CHECKED `sh_u : 1 = 1 := sha_n` (R142, S1-shadow) | rc 1: `(kernel) constant has already been declared 'sha_n'`; `--fresh` rc 1: `declaration type mismatch, 'sha_n'` |
| `ReplayShadowStubUser.olean` | `ReplayShadowStub` | non-module: the CHECKED `shu_t : 1 = 1 := sh_u` | rc 0 (the default mode trusts the import); `--fresh` rc 1 (`sha_n`, type mismatch) |
| `ReplayShadowThm.olean` | `ReplayShadowAx` | NOT a `module`: `theorem sha_n : 1 = 1 := Eq.refl 2` inserted unchecked over the import's axiom, and the CHECKED `sht_u : 1 = 1 := sha_n` | rc 1: `constant has already been declared 'sha_n'`; `--fresh` rc 1: `declaration type mismatch, 'sha_n'` |
| `ReplayQuotIndThm.olean` | `Init.Prelude` | `theorem Quot.ind` with the kernel quotient's own statement and the unchecked value `True.intro` (R142: no load completes a quotient primitive, so a checker that drops the theorem as a restatement keeps the kernel's value-free `Quot.ind`; a theorem merges only with a theorem) | rc 1: `while replaying declaration 'Quot.ind': (kernel) constant has already been declared 'Quot.ind'`; `--fresh` rc 1: `environment already contains 'Quot.ind' from Init.Prelude` (measured 2026-10-25) |
| `ReplayIsPropStuckBase.olean` | `Init.WF` | COMPILED from `ReplayIsPropStuckBase.lean` by `lean -o`: the tactic-proved `Acc`-trick helpers `run`/`run_eq`/`a`/`b`/`c`/`P`/`Q`/`gate`/`observedProofsFalse` and `opaque witness : Q` | rc 0 (the honest base; Lean's kernel checks it) (measured 2026-10-18) |
| `ReplayIsPropStuck.olean` | `ReplayIsPropStuckBase` | `inductive Owner (h : P) : gate h` (param `h`, field `bit : Bool`), `asProp (h : P) : Sort 0 := Owner h`, `proposition := asProp witness` (a STUCK `Owner witness`, `witness : Q`), `observe : proposition → Bool := fun p => p.1`, `falseProof`/`trueProof := Owner.mk witness {false,true}`, and `isprop_stuck_false : False := observedProofsFalse proposition observe falseProof trueProof rfl rfl`, all admitted by the vulnerable kernel through `addDeclCore` | **Lean accepts; Clean refuses since the `is_prop`-requires-a-sort guard (it admitted it before, a live hole).** rc 0 — `leanchecker v4.30.0-rc2` ACCEPTS the `.olean` (`isprop_stuck_false : False`, `#print axioms = []`); the pinned oracle is itself vulnerable to #14807 (measured 2026-10-18). Under v4.33.1 the `observe` projection can no longer be minted (`is_prop` now `ensure_sort`) |
| `ReplayForgedProjIdx.olean` | `Init.Prelude` | `forged_proj_idx : Nat := .proj Prod (2^64) (Prod.mk Nat Nat 1 1)`: a projection index stored as a heap Nat, which Lean's kernel refuses (`infer_proj`: `!proj_idx(e).is_small()`; v4.33.1 `to_proj_idx`, leanprover/lean4#14632). Before R147 the two-phase decoder read its low limb, so `per-constant-verify` and every `stamp-verified` mode checked `.proj Prod 0 (1, 1) : Nat` and admitted it (release 0.9.0+g33ce84e20, measured 2026-10-20) | rc 1: `(kernel) invalid projection`; `--fresh` rc 1, the same (measured 2026-10-20) |
| `ReplayForgedLevelSubsumption.olean` | `Init.Prelude` | seven level equalities, each true at every assignment, built from raw `Level` constructors and of the shape `def n.{u,v,w} : Sort a → Sort b := fun x => x` unless noted: `fls_join` (t1: `max 1 (imax u v)` vs `max (max 1 v) (imax u v)`), `fls_join_wf` (t2, the WF `reverseRecOn` pair), `fls_imax_reflatten` (t3: `imax (max v u) (w+1)` vs `max u (max v (w+1))`), `fls_decode_max` (t4: `max u v` vs `max (max u v) (imax u v)`), `fls_decode_imax` (t9: `max u (imax v u)` vs `imax v u`); `fls_subst : Sort (max u v) := fls_K.{u,v,imax u v}` over the honest `fls_K.{u,v,w} : Sort (max (max u v) w)` (t5); `fls_infer_pi : Sort (max u (v+1)) := fls_A.{u,v} → fls_B.{u,v}` over the honest `fls_A : Sort (imax u v)`, `fls_B : Sort (max u (v+1))` (t10) | rc 1: `(kernel) declaration type mismatch, 'fls_join_wf'` (`--fresh` the same). Per constant, in dependency order (`reports/level-lean-profile-2026-10-19/PerConstVerdicts.lean`): the three axioms admitted, each of the seven equalities a declaration type mismatch (measured 2026-10-19) |
| `ReplayHonestLevelEquiv.olean` | `Init.Prelude` | CHECKED: the twins (t3b `imax u (w+1)` = `max u (w+1)`; t5b `hle_subst : Sort (max (max u v) (imax u v)) := hle_K.{u,v,imax u v}`; t6 `(max u v)+1` = `max (u+1) (v+1)`; t7 `max 1 (max u v)` = `max (max v 1) u`; t8 `imax u u` = `u`; t10b `hle_infer_pi : Sort (max (imax u v) (max u (v+1))) := hle_A → hle_B`) and their three axioms | rc 0 (`--fresh` rc 0); all nine per constant (measured 2026-10-19) |
| `ReplayLevelSharing.olean` | `Init.Prelude` | `ls_cS.{u,v} : Sort (imax v (u+1))` (a level `mk_imax` rebuilds to `max v (u+1)`), then unchecked `ls_same : Sort (imax v (u+1)) := ls_cS.{u,v}` and `ls_sorted : Sort (max (u+1) v) := ls_cS.{u,v}`: Lean's `instantiate` keeps or rebuilds the stored node according to object sharing, and same-module users share it after `writeModule` | rc 1: `(kernel) declaration type mismatch, 'ls_sorted'` (`--fresh` the same); per constant `ls_cS` and `ls_same` admitted, `ls_sorted` refused (measured 2026-10-19). Clean refuses `ls_same` too, by name (`LevelSharingDependent`): a recorded Clean-refuses-Lean-admits row |
| `ReplayHonestLevelImport.olean` | `Init.Prelude` | CHECKED: `hli_t4.{u,v} : Sort (max (max u v) (imax u v))` and `hli_t9.{u,v} : Sort (max u (imax v u))`, levels a collapsing decoder rewrites | rc 0 (`--fresh` rc 0) (measured 2026-10-19) |
| `ReplayForgedLevelImport.olean` | `ReplayHonestLevelImport` | `fli_t4 : Sort (max u v) := hli_t4.{u,v}`, `fli_t9 : Sort (imax v u) := hli_t9.{u,v}`: t4 and t9 across a module boundary | rc 1: `(kernel) declaration type mismatch, 'fli_t4'` (`--fresh` the same); per constant both refused (measured 2026-10-19) |
| `ReplayHonestLevelImportUse.olean` | `ReplayHonestLevelImport` | CHECKED: `hliu_t4`, `hliu_t9`, the same uses at the stored levels | rc 0 (`--fresh` rc 0) (measured 2026-10-19) |
| `ReplayHonestWfLevels.olean` | `Init` | COMPILED from `ReplayHonestWfLevels.lean` by `lean -o`: a WF-recursive `Sort`-valued eliminator whose `._unary` packs `imax (u+1) (imax (u+1) v)` (the 2026-07 `List.reverseRecOn` shape), and its `rw` equation | rc 0 (`--fresh` rc 0) (measured 2026-10-19) |
| `ReplayForgedLevelReach.olean` | `Init.Prelude` | the honest `flr_S.{u,v,w}` (`structure`, field `Sort (max (max u v) w)`), `flr_D.{u,v,w} : Sort (succ (max (max u v) w)) := Sort (max (max u v) w)` and `flr_Av.{u,v} : Sort (max v (imax u v))`; unchecked `fls_proj : flr_S.{u,v,imax u v} → Sort (max u v) := fun x => x.1` and `fls_delta : flr_D.{u,v,imax u v} → Sort (max u v) := fun x => x`, declared at the level a collapsing substitution builds (Lean builds `max (max u v) (imax u v)`); three blocks minted from a twin Lean admits with the stored sort overwritten: the mutual `flr_MA : Sort (max (max u v) (imax u v))` / `flr_MB : Sort (max u v)`, `flr_Fb : Sort (succ (imax u v))` over a field `flr_Av.{u,v}` (twin `succ (max u v)`), `flr_Z : Sort (max 0 0)` over a `Nat` field (twin `Prop`) | rc 1: `(kernel) mutually inductive types must live in the same universe` while replaying `flr_MA` (`--fresh` the same). Per constant (`reports/level-lean-profile-2026-10-19/PerConstVerdicts.lean`, which re-adds a block once from its stored types): `flr_S`, `flr_D`, `flr_Av` admitted; `fls_proj` and `fls_delta` a declaration type mismatch; `flr_MA` refused for its universes; `flr_Fb` and `flr_Z` refused as `universe level of type_of(arg #1) ... is too big` (measured 2026-10-20) |
| `ReplayHonestLevelReach.olean` | `Init.Prelude` | CHECKED: `hlr_S`, `hlr_D`, `hlr_W` (`node : (Sort (max (max u v) w) → hlr_W) → hlr_W`); `hle_proj` and `hle_delta` at `Sort (max (max u v) (imax u v))`; `hle_iota`, `hlr_W.rec`'s ι-reduct at `w := imax u v`, stated with the rule binder Lean instantiates raw (the only well-typed spelling); `hlr_A0 : Sort (max 0 0)`, `hlr_P0 : Prop \| mk : hlr_A0 → hlr_P0` (its recursor eliminates only into `Prop`, `inductive.cpp:517`) and `hlr_Q0 : Sort (max 0 0) \| mk` (`k = false`, `:557`); the mutual `hlr_MA : Sort (max u v)` / `hlr_MB : Sort (max v u)`; `hlr_Fb : Sort (succ (max u v))` over `hlr_Av : Sort (max v (imax u v))` | rc 0 (`--fresh` rc 0); per constant every declaration and every block admitted (a block's constructors, recursors and other types are re-added with it) (measured 2026-10-20). Imported through the trusted `.olean` path into an `Extended` environment, `hlr_P0.rec` and `hlr_Q0.rec` differ from Clean's semantic-`is_zero` generation and are admitted by the loader's comparison with rc2's structural one (DECISIONS R150) |
| `ReplayHonestLevelProj.olean` | `Init.Tactics` | COMPILED from `ReplayHonestLevelProj.lean` by `lean -o`: `structure RhpS.{a,b,c} where y : Sort (max (max a b) c)` and `theorem rhp_c5 (s : RhpS.{u,v,imax u v}) : RhpS.y s = RhpS.y s := by delta RhpS.y; exact Eq.refl _`, whose value keeps a raw `s.1` at `RhpS.{u,v,imax u v}` | rc 0 (`--fresh` rc 0); per constant every declaration and every block admitted (a block's constructors, recursors and other types are re-added with it) (measured 2026-10-20) |

`ReplayHonestDeltaProp`/`ReplayForgedDeltaPropLargeElim` pin `kernel-result-sort-whnf-elim`
(`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`, P0, 2026-10-16). Lean's kernel finds an
inductive's result level by whnf between binders (`check_inductive_types`); Clean's
elimination analysis read the syntactic head (`fdp_prop`, no `Sort`) and answered "large
elimination allowed", while proof irrelevance, which reduces, made `FDP.t ≡ FDP.f`. Every
re-check lane regenerates a stored recursor and compares, so before the fix the verdicts were
reversed: the regeneration was large, which the forgery matches and Lean's honest `HDP.rec`
does not. The forgery's recursor is exactly that wrong regeneration, so a lane that compares
against a syntactic read admits `forged_dp_false : False`.

`ReplayHonestSortU`/`ReplayForgedSortULargeElim` pin the other half of the same gate: Lean's
kernel exempts a family from the restriction analysis only when its result level is PROVABLY
nonzero (`is_not_zero`), never when it is merely not provably zero. `clean-kernel` already reads
`Level::is_nonzero` there; `clean-ck0` read `!is_zero` until 2026-10-17 and gave `Sort u`
families a large recursor (its own battery: `crates/clean-ck0/tests/sort_u_elim_gate.rs`). The
pair guards the `.olean` lanes against the same misreading.

`ReplayIsPropStuck` (over `ReplayIsPropStuckBase`) carries the #14807 exploit
(`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`, `kernel-exploit-battery-and-intake`). It is
**not** a Clean-rejects-Lean-accepts family. The pinned oracle `leanchecker v4.30.0-rc2` accepts
the `.olean` whose `isprop_stuck_false : False` the kernel admitted (`#print axioms = []`).
Clean admitted it too until the `is_prop`-requires-a-sort guard (item (1) of
`kernel-defensive-invariants-v4331`, `docs/DECISIONS.md` R84 and R85): a release `clean olean
replay --exact --json` at 482b8ab21 (measured 2026-10-18) reported `ok: true`, `admitted: 9`,
`refusals: []`, because `is_prop` (`crates/clean-kernel/src/tc/infer_proj.rs`) answered
`Ok(false)` when the type-of-type was not a `Sort`. With the guard, `is_prop` errors
(`ExpectedSort`) there, as Lean v4.33.1's `ensure_sort` does: the replay lanes and the sharded
worker refuse `IPK.observe` at `ExpectedSort`, and no `stamp-verified` mode stamps it or
`isprop_stuck_false` (measured 2026-10-18, again after the `infer_proj` move on 2026-10-19).
`per-constant-verify` used to refuse the family one layer earlier, at recursor
regeneration (`Invalid recursor IPK.Owner.rec`). That was an over-refusal of honest content:
`IPK.Owner` is kernel-checked by Lean (`doCheck := true`), and the lane's demand walk registered
the family before `IPK.gate`, the definition its type former reduces through, was resident
(decision R147, measured on the honest control `ReplayHonestSortDef`). Since R147 the walk loads
what a module's family types name first. Behind that sat a second over-refusal: the lane
refused `IPK.proposition` (`TypeMismatch`, `P` against `Q`), whose check unfolds the imported
theorems `IPK.b._proof_1` and `IPK.c._proof_1`, which the walk loaded without their values,
and refused the four declarations built on it (measured 2026-10-19). Since R147 the walk loads
an imported theorem that concludes in `Acc` or `WellFounded` with its value, so the lane
verifies `IPK.proposition` and refuses `IPK.observe` at `ExpectedSort`, with
`isprop_stuck_false`: it witnesses the guard, as the replay and `stamp-verified` lanes do.
Intake row 14807 is now `fixture`. The lane tests run a
RELEASE `clean`: a debug build does not finish loading the fixture's Init.WF closure (over
17 min; Init.Core replays in 4.24 s). The first round of this item labelled the family
Clean-rejects-Lean-accepts. That label was never measured and is withdrawn.

The `ReplayMisplaced*`, `ReplayParts*` and `ReplayHonest{ServerParts,Dep,DepUser}` families pin
R113 (`docs/DECISIONS.md`): every re-check lane reads a module the way pinned Lean does, through one
reader (`clean_olean::read_artifact`), and refuses an artifact whose parts tell different stories.
What Lean reads (v4.30.0-rc2 source): an importer — `lean` on a file that imports the artifact, and
`leanchecker --fresh` — reads a non-module artifact through its `.olean`, and a module-system
artifact through its `.olean.private` when the importer is not itself a `module` or imports it
with `import all` (`ImportedModule.mainModule?`; `leanchecker` imports everything that way),
through its `.olean` otherwise; `leanchecker`'s default mode replays the LAST part it found
(`.olean.private`, or `.olean.server` when there is no private part) with no `isModule` check, and
takes the checked module's imports from its `.olean`. Lean's `writeModule` makes every reading
agree: each part states one header, the exported and server levels are subsets of the private one,
and a name two parts hold is one record (`PartSubset.lean`). Clean refuses an artifact that breaks
that: a name a part declares that the part an importer reads does not (`MisplacedDeclaration`; for
a non-module artifact whose companions hold a complete, well-typed set, `leanchecker`'s default
mode accepts what Clean refuses, which is the safe direction), two parts stating one declaration
differently (`PartsDisagree`), or two import lists (`PartsDisagreeOnHeader`). Before R113
`stamp-verified --parallel` stamped `so_use` over a `.olean.server`-only `SO` (its base loaded the
server part, its shard rows did not); `per-constant-verify` and the sequential `stamp-verified`
modes read a module as its `.olean` merged with its private part, the `.olean` winning on a value
and naming the imports, so they verified `sx_use`, `pv_u`, `pd_t`, `pi_t` and `md_use`.

The `ReplayStub*`, `ReplayMisplacedOleanOnlyDep(User)` and `ReplayMisplacedPrivPlainDep(User)`
families pin R131 (`docs/DECISIONS.md`), from the adversarial review of R113's second round. A
value-free stub that a later part completes is what Lean's `writeModule` writes for every public
theorem of a `module` (`Lean.addDecl` exports it as an `axiomInfo` of its type), so the artifact
rule admits it there, and the loader completes the stub from the `.olean.private` through the
kernel's checked upgrade. `ReplayStubRefused` is that layout over a value the kernel refuses:
before R131 the loader kept the stub resident as an axiom and recorded the refusal only as a
skipped constant's reason string, which no lane read, so the sharded worker counted `sr_t` as an
accepted axiom and verified `sr_u` over it, and verify-batch's full re-check passed both (review
finding S1). A non-`module` artifact is read through its `.olean` alone by every importer, and no
Lean writer gives it companions; `ReplayStubPlainDep`/`ReplayStubPlainPrivDep` (a companion that
completes the `.olean`'s stub, S2) and `ReplayStubPlainTgt` (the same as the module checked, S3:
`leanchecker`'s default mode replays the companion, an importer reads the `.olean`) are refused
since R131, which admits the stub exception for a `module` only. `ReplayMisplacedOleanOnlyDep` and
`ReplayMisplacedPrivPlainDep` are the two placement shapes only the rule's `.olean` entry
(`module`) and `.olean.private` entry (non-module) refuse (S5).

`ReplayStubMv`, `ReplayStubFv`, `ReplayShadowStub(User)` and `ReplayShadowThm` pin R142
(`docs/DECISIONS.md`), from the verification of R131: the declaration a module states with a value
in its authoritative part is not what the loader makes resident when the private value does not
convert (`smv_f`, `sfv_f`: Lean's kernel refuses the metavariable or free variable) or when an
import already holds the name as an axiom (`sha_n`), and before R142 those stubs stayed trusted.
Under a re-check lane's policy the loader now refuses any such load by the declaration, whatever
kept the value out. `ReplayQuotIndThm` pins the line between Lean's merge of a theorem restating a
theorem and a theorem restating an axiom, here the kernel's `Quot.ind`, whose value must then be
resident.

`ReplayForgedAllGhost`, `ReplayForgedAllOther`, `ReplayForgedIsRec`, `ReplayForgedMutualEta` and
`ReplayHonestIndFlags` pin hole R112 (`docs/DECISIONS.md`), found by the adversarial review of
the NDJSON front door and confirmed on `.olean`s before the fix (release `clean` at a commit whose
replay code is `origin/main`'s, 2026-10-22). Every re-check lane found an inductive block through
a type's stored `all`, so a type whose `all` names no block containing it was never rebuilt by
the kernel: `clean olean replay`, `verify-batch --full-validation`, `per-constant-verify` and
`stamp-verified --parallel` admitted `forged_all_ghost_false : False` and
`forged_all_other_false : False`; only the sequential `stamp-verified` modes refused them. The
same lanes admitted `forged_isrec_eta`, because the replay compared no flag of the stored
inductive value and the kernel reads `isRec` for eta; the sequential modes stamped the forged
`FIR` block and `forged_hma_eta`, because Clean's admission computed `isRec` per type where
Lean's kernel computes it per block. Coverage is now what a replay generated, never `all`
(`clean_olean::replay_families`), and the stored `isRec`, `isReflexive` and `numNested > 0` must
equal the regenerated ones, which follow Lean's block-level rule
(`clean_kernel` `env/inductive_lean_replay.rs`, `env/inductive_builder.rs`).

`ReplayCrossA`/`ReplayCrossB` pin the cross-module half of the replay order. A run that
stamps BOTH modules (`stamp-verified` in either mode) must refuse `cross_uses_forged`,
because its dependency was not admitted in that same run. `clean olean replay` and
`per-constant-verify` over `ReplayCrossB` ALONE keep Lean's per-module semantics, where imports
are trusted, so they accept it, exactly as `leanchecker ReplayCrossB` does; the stamping lanes
(`stamp-verified`, and the sharded worker, whose verdicts are merged over a corpus) keep the
`.olean` loader's refusal of that import (see below).

`ReplayForged5` goes beyond the audit. On 2026-09-24 the pre-fix binary stamped
`forged5_unsafe` KernelVerified in all three mathverse lanes (`per-constant-verify`,
`stamp-verified --parallel` and the sequential `stamp-verified`), because every Clean checker
allowed a SAFE declaration to use an `unsafe` constant.

Run the generator with `lean --run GenReplayForged.lean <out.olean> <family>`. It exits 0 on
success, 2 on a usage error, and 1 when a checked declaration is rejected. Only the `.lean`
files (the generator, `PartSubset.lean` and the module sources `ReplayIsPropStuckBase`,
`ReplayHonestInd`, `ReplayHonestSortDefBase`, `ReplayHonestSortDef`, `ReplayHonestWfLevels`,
`ReplayHonestLevelProj` and `ReplayHonestDepNestedDeep`), `ORDER` and this file are checked in.
The outputs are build products, minted by
`clean_olean::test_support::compiled_fixture_dir("replay_forged")`, which runs the `run` lines of
`ORDER` and compiles the module sources it names.

The `forgedRec`/`forgedRule`/`forgedCtor`/`forgedQuot`/`redeclare` families write a
`ConstantInfo` into the environment with no kernel check at all, through the environment's own
insert (`Lean.Environment.lakeAdd`, `@[export lake_environment_add]`, named by its private name
because a script cannot spell a numeric name component). `debug.skipKernelTC` is not enough for
them: Lean's kernel generates a recursor and a constructor itself when it admits an inductive,
whatever the source says.

Round 2 of P0_SOUND (2026-09-24) confirmed three classes against the round-1 release binary
(`319c2ccd9`) before fixing them. "Stamped" below means `KernelVerified`; `verify-batch` is
`clean olean verify-batch --full-validation`.
- **Clean's prelude reached the re-check.** `prelude_sorry`, `prelude_arith` and `prelude_ay`
  (`: False`) were stamped by `per-constant-verify`, the sequential and `--single-pass`
  `stamp-verified`, and `--parallel`. `per-constant-verify` stamped `Nat.not_succ_lt_zero : False`
  (the name of a Clean prelude theorem); the sequential lanes stamped `prelude_shadow_use` checked
  against that prelude theorem's type; `per-constant-verify` and `--parallel` stamped
  `ReplayRedeclare`'s `Nat.pred` (Lean: already declared); and `per-constant-verify` stamped
  `forged_quot_false : False` after the stored `quotInfo` overwrote the canonical `Quot.ind`.
  `verify-batch` refused all of these (its base environment holds no Clean prelude). Every
  Lean-profile lane now starts from `Environment::for_lean_replay` (the `.olean` closure and
  Lean's canonical quotient, nothing else) and refuses a declaration whose name its environment
  already holds, except a theorem or axiom restated with the same type and level parameters
  (Lean's `subsumesInfo` in `finalizeImport`).
- **Stored recursors and constructors were trusted.** `per-constant-verify`, `--parallel` and
  `verify-batch` accepted `forged_rec_false : False`, `forged_rule_eq` and
  `forged_ctor_false : False` (`verify-batch` also passed the forged `FRT.rec` and `FRR.rec`);
  the sequential and `--single-pass` lanes stamped `FRR.rec` with its forged rule. Every lane now
  replays each inductive block through the kernel's own admission and compares every stored
  member with the generated one (`clean_kernel` `Environment::lean_replay_inductive_block`,
  `clean_olean::replay_families`, `clean_mathverse` `stamp_family_audit`).
- **Native reducers disagreed with Lean's definitions.** Every lane, `verify-batch` included,
  accepted all five `ReplayForgedStr` equations. The Lean profile now admits only the reducers a
  differential battery checks against δι (`clean_kernel::env::LEAN_PROFILE_DIFFERENTIAL_REDUCERS`,
  `crates/clean-olean/tests/lean_profile_reducer_differential.rs`).
- **A native reducer dropped its over-application argument — in the EXTENDED theory only
  (2026-09-30).** `reduce_native` passed a reducer the whole application spine and re-applied
  nothing, so an `… → α` reducer at a function-valued carrier returned its bare branch and the
  trailing arguments were lost: `@ite (Nat → Nat) True (isTrue ..) (fun n => n) (fun _ => 0)`
  applied to `1` reduced to `fun n => n`, dropping the `1`. The hole was in Clean's own kernel,
  `KernelTheory::Extended` (`with_prelude`, the full Specification, `clean check` over imported
  modules), where `ite`/`dite` have `fold` rows. **No replay lane was exposed:** every lane runs
  `KernelTheory::Lean`, which never admits the `ite`/`dite` reducers (they are not differentially
  checked), so `ite` δ-unfolds there and `ReplayForgedIte` was refused before the fix as after.
  `ReplayForgedIte`/`ReplayHonestIte` are therefore a regression guard plus `leanchecker`
  agreement, not evidence of a replay-lane acceptance. The fix: `reduce_native` hands each reducer
  exactly its head's SYNTACTIC arity (the declared type's leading `Pi` count, never unfolded),
  declines an absent or under-applied head, and re-applies the surplus to the reduced value
  (`clean_kernel` `TypeChecker::native_reducer_spine` / `reapply_native_surplus`); pinned by
  `clean_kernel::tc::def_eq::tests_native_reducer_arity`.

The four rows from `ReplayForgedThmType` to `ReplayHonestUniv` were added with `clean olean
replay` (2026-09-25; `leanchecker` column measured that day with the pinned binary). `ReplayForgedThmType` is the one Lean `add_decl` check the
re-check lanes did not make — their per-declaration check inferred the type's sort and checked
the value, and never required a theorem's type to be a proposition. `ReplayForgedUniv` and
`ReplayForgedDupUniv` are refused by the loader's structural tier before any lane sees them;
`clean olean replay` turns that into a named refusal of the declaration, because a declaration
the loader could not register is one Lean's replay would send to the kernel.

The last seven rows came from the adversarial review of `clean olean replay` (2026-09-26,
`leanchecker` column measured that day with the pinned binary on these exact modules). Each was
admitted by the verb before the fix it pins: `ReplayForgedLamType` by every `verify_batch_full`
lane, because `infer_sort` answers for a term whose type is a function type where Lean's
`ensure_sort` requires a sort; `ReplayForgedBoolDef` because the loader filled the IMPORTED
axiom `bool_ax_b` with the module's definition (the `.olean.private` stub upgrade took any
value-less resident constant, another module's included), after which `forged_bool_false : False`
type-checked; and the two quotient rows because the replay read every restatement of a name its
environment seeds as the module's own declaration. `ReplayForgedThmOverAx` is the control for the
repair of `ReplayForgedBoolDef`: a theorem over an imported axiom is the one pair Lean's import
merges, so the replay must keep accepting it under `--fresh`.

The `.olean` loader's own module-trust rules refuse the WHOLE import for five of these modules
(`ReplayForged`, `ReplayForged3` and `ReplayCrossA` for a declaration that depends on itself,
`ReplayRedeclare` and `ReplayForgedBoolDef` for a name two modules declare), and so for
`ReplayCrossB`, whose import is `ReplayCrossA`. `leanchecker` refuses none of them at load: it
refuses each declaration in its replay (and, under `--fresh`, a duplicate name at the import),
and it trusts `ReplayCrossB`'s import. `clean olean replay` therefore loads with those rules
left to its replay (`OleanImportPolicy::with_replay_refusals`) and names each refusal at
`leanchecker`'s layer. The mathverse sharded worker (`verify::sharded::verify_module`) leaves
them to its replay for the module it replays only
(`clean_olean::load_module_with_deps_replaying_module`): it refuses the forgeries of
`ReplayForged`, `ReplayForged3`, `ReplayCrossA`, `ReplayRedeclare`, `ReplayForgedBoolDef` and
`ReplayForgedIndOverAx` by name, and keeps the loader's refusal of `ReplayCrossB`'s import,
because it never replays an import and its verdicts are merged over a corpus with no
cross-module pass. The other lanes keep the loader's refusal: `verify-batch`, and
`stamp-verified` in every mode (`--parallel` checks every target against one base holding
all of them, where a reference from one target to a name only another declares resolves), which
reports it naming the declarations.

`ReplayHonestIndAx`/`ReplayForgedIndOverAx` came from the adversarial review of that change
(2026-09-28, `leanchecker` column measured that day with the pinned binary). With rule 1 left to
the replay, the loader's carrier-stub discharge (`is_axiom_carrier_stub`, meant for a value-free
axiom the checker's own prelude registers) took the IMPORTED axiom `ind_ax_t` for such a stub, so
the module's `inductive ind_ax_t` replaced it with nothing recorded, and `clean olean replay
ReplayForgedIndOverAx` admitted all four declarations, `forged_ind_false : False` included
(measured without `--fresh`; the default load refuses the module outright). The discharge now
leaves another module's axiom, and the kernel's quotient primitives, alone: the inductive is a
recorded duplicate, and its constructor and recursor are refused with it.

The last seven rows came from the adversarial review of the mathverse lanes' loader layer
(2026-09-29, `leanchecker` column measured that day with the pinned binary). `leanchecker`, a
consumer that is not itself a `module`, reads a `module`-system artifact through its
`.olean.private` and replays its private declarations with the rest; the sharded worker's
replay set was the `.olean`'s names alone, so with the module's own parts loaded under rule 3
left to that replay it verified `ReplayForgedPriv`'s `priv_user : False` (measured on the
reviewed branch head), and `ReplayForgedPrivBad`'s `priv_bad_user : False` over the
never-checked private `priv_bad : False := True.intro` (a hole older than that branch: no loader
rule catches a declaration that is merely ill-typed). The worker now replays every declaration
its parts register, as `clean olean replay` does.

`ReplayForgedOpaqueDef` is the opaque twin of `ReplayForgedBoolDef`: `stamp-verified
--single-pass` roll-elides each verified target's opaque values
(`--closure-elide opaque`, the default), so in a run over `ReplayHonestOpaqueAx`,
`ReplayForgedOpaqueDef` and `ReplayForgedOpaqueUse` the honest `opaque op_b` was resident
value-free and not an axiom, the refusal of a definition over an axiom did not cover it, the
checked stub upgrade replaced it with `true`, and `forged_op_use : False` was stamped (measured
on the reviewed branch head). A value now completes a value-free resident only as a theorem
over an axiom or as a value of the resident's own kind. An opaque the closure loader elides at
registration keeps a placeholder value, so the same definition over an IMPORT's opaque was
already refused there.

`ReplayForgedQuotDef` redefines a name no artifact declares: the kernel seeds Lean's canonical
quotient, so the `.olean` loader's rule 1 (a name another artifact declared) never sees the
redeclaration, and under the default policy the `.olean.private` stub upgrade filled the
kernel's value-free `Quot` with the module's definition, which checks at `Quot`'s own type.
`stamp-verified --parallel` (whose base loads its targets under that policy) stamped `Quot` and
`quot_def_false : False` (measured on the reviewed branch head; by reading, older than it). The
sequential modes refused it (a definition over an axiom), and `per-constant-verify` and the
sharded worker refused it. No load now fills a quotient primitive, the same exclusion the
carrier-stub discharge already made.

Tests that consume the family:
- `crates/clean-olean/src/replay_module/tests.rs`: `clean olean replay`'s engine, module by
  module, with and without `--fresh`.
- `crates/clean-olean/tests/replay_forged_header_lanes.rs`: the three `verify_batch_full`
  lanes on `ReplayForgedThmType` and its control `ReplayHonestUniv`.
- `crates/clean-olean/tests/replay_forged_sort_u.rs`: the loader and the `verify_batch_full`
  lanes on the `Sort u` pair, beside the battery so its arms keep pinning only their file.
- `ReplayIsPropStuck` (#14807): release-only lane tests, because a debug build does not finish
  loading its Init.WF closure: `crates/clean-olean/tests/replay_forged_lanes.rs`
  (`test_verify_batch_full_lanes_projection_needs_a_sort_typed_type`),
  `crates/clean-olean/src/replay_module/tests/is_prop_sort.rs` and
  `crates/clean-mathverse/src/cli/replay_forged_lane_tests/is_prop_sort.rs`. Each names the
  refusing layer; a debug build compiles none of them.
- `crates/clean-olean/tests/replay_forged_lanes.rs`: the `verify_batch_full` lanes (eager,
  streaming and parallel), and `verify-batch --full-validation`'s cross-module run over
  `ReplayCrossA`/`ReplayCrossB`.
- `ReplayHonestSortDef` (R147): `crates/clean-mathverse/src/cli/replay_forged_lane_tests/sort_def.rs`
  (`per-constant-verify` and every `stamp-verified` mode verify it in full).
- The universe-level rows (DECISIONS R150): `crates/clean-olean/src/replay_module/tests/level_equiv.rs`
  (`clean olean replay`; the `ReplayHonestWfLevels` test is release-only, its closure is all of
  `Init`) and `crates/clean-olean/tests/replay_forged_level_equiv.rs` (the `verify_batch_full`
  lanes, and `recheck_closed` / `ImportedConeGate`, which keep Clean's `Extended` level algebra
  and are pinned admitting the seven equalities), and
  `crates/clean-mathverse/src/cli/replay_forged_level_lane_tests.rs` (the mathverse lanes,
  including the import served lazily from a closure shard through `shard_reconstruct`). The
  `ReplayForgedLevelReach` / `ReplayHonestLevelReach` / `ReplayHonestLevelProj` rows reach the
  projection, δ, ι and inductive paths; their kernel-level twins are
  `crates/clean-kernel/src/tc/level_profile_reach_tests.rs`, against pinned Lean's verdicts in
  `reports/level-lean-profile-2026-10-19/ReachVerdicts.txt`.
- `crates/clean-mathverse/src/cli/replay_forged_lane_tests.rs`: `per-constant-verify`,
  `stamp-verified --parallel`, the sequential `stamp-verified`, and the sharded verifier
  (`verify::sharded::verify_module`).
- R113 and R131: `crates/clean-olean/tests/replay_forged_lanes/{misplaced,trailer,stubs}.rs`,
  `crates/clean-olean/src/replay_module/tests/{misplaced,stubs}.rs` and
  `crates/clean-mathverse/src/cli/replay_forged_lane_tests/{misplaced,trailer,parts,stubs}.rs`.
- Hole R112: `crates/clean-olean/tests/replay_forged_lanes/block_cover.rs`,
  `crates/clean-olean/src/replay_module/tests/block_cover.rs` and
  `crates/clean-mathverse/src/cli/replay_forged_lane_tests/block_cover.rs`, child modules of the
  three files above.

To reproduce the `leanchecker` column, run `leanchecker <Module>` with `LEAN_PATH=<dir>:<toolchain>/lib/lean`
and `PATH=<toolchain>/bin:$PATH`. `leanchecker` spawns `lean --print-prefix`, so under aterm also
set `ATERM_NO_REROUTE=1`.
