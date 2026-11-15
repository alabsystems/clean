import Lean

/-!
# `GenReplayForged` — mint replay-order and kernel-theory forgeries with Lean's own serializer

A `lean --run` GENERATOR, not a module source:

    lean --run GenReplayForged.lean <out.olean> <family>

`<family>` is one of `forged`, `forged3`, `forged4`, `forged5`, `crossA`, `crossB`, `honest`,
`honestUnsafe`, `honest4`, `prelude`, `preludeUse`, `forgedRec`, `forgedRule`, `forgedCtor`,
`forgedQuot`, `redeclare`, `forgedStr`, `honestStr`, `forgedThmType`, `forgedUniv`,
`forgedDupUniv`, `honestUniv`, `forgedLamType`, `honestBoolAx`, `forgedBoolDef`,
`forgedQuotRedecl`, `forgedQuotIndAxiom`, `honestPropAx`, `forgedThmOverAx`, `honestIndAx`,
`forgedIndOverAx`, `forgedPriv`, `forgedPrivBad`, `honestPriv`, `honestOpaqueAx`,
`forgedOpaqueDef`, `forgedOpaqueUse`, `forgedQuotDef`, `forgedIte`, `honestIte`,
`honestDeltaProp`, `forgedDeltaPropLargeElim`, `honestSortU`, `forgedSortULargeElim`,
`honestIsPropStuck`, `forgedProjIdx`, `forgedLevelSubsumption`, `honestLevelEquiv`,
`levelSharing`, `honestLevelImport`, `forgedLevelImport`, `honestLevelImportUse`,
`forgedLevelReach`, `honestLevelReach`,
`forgedAllGhost`, `forgedAllOther`, `forgedIsRec`, `forgedMutualEta`,
`honestIndFlags`, `misplacedServer`, `misplacedServerPlain`, `honestServerParts`, `misplacedOlean`,
`partsValDis`, `partsValDep`, `partsValDepUser`, `partsImpE`, `partsImpF`, `partsImpD`, `partsImpT`,
`misplacedDep`, `misplacedDepUser`, `honestDep`, `honestDepUser`, `stubRefused`, `stubHonest`,
`stubRefusedDep`, `stubRefusedDepUser`, `stubPlainDep`, `stubPlainDepUser`, `stubPlainPrivDep`,
`stubPlainPrivDepUser`, `stubPlainHonest`, `stubPlainHonestUser`, `stubPlainTgt`,
`misplacedOleanOnlyDep`, `misplacedOleanOnlyDepUser`, `misplacedPrivPlainDep`,
`misplacedPrivPlainDepUser`, `stubMv`, `stubFv`, `shadowAx`, `shadowStub`, `shadowStubUser`,
`shadowThm`, `forgedQuotIndThm`, `honestDepNested`, `forgedDepNestedRefl`, `forgedPowCap`,
`forgedLevelJoin`, `honestLevelAssoc`, `forgedLevelAssoc`, `forgedMutualLevel`,
`forgedPowCapOuter`, `forgedShlCap`. Each builds an
environment from a
SMALL import (`Init.Prelude`, `Init.System.Platform` for the platform families, the freshly
minted `ReplayCrossA` for `crossB`, found through `LEAN_PATH`), names the main module, adds the
family's declarations through `Environment.addDeclCore`, and writes the result with
`writeModule` (the `parted` families write a `module`'s three parts themselves, and a
`headerImports` family states its own import list).

The `forged*` and `crossA` families pass `doCheck := false` — the same kernel bypass as
`set_option debug.skipKernelTC true` in the audit's `Forged*.lean` sources — so the
`.olean` carries declarations Lean's kernel never admitted. The `honest*` and `crossB`
families pass `doCheck := true`: Lean's kernel checks every one before it is written.

The `forgedRec`/`forgedRule`/`forgedCtor` families add an inductive through the CHECKED
kernel path and then overwrite its kernel-generated recursor or constructor with a forged
`ConstantInfo`, through the environment's own unchecked insert (`lake_environment_add`, the
function the lakefile cache uses). Lean's `Environment.replay` re-derives both and compares
(`checkPostponedRecursors` / `checkPostponedConstructors`), so `leanchecker` refuses them.

Exit status: 0 on success, 2 on a usage error, 1 when a CHECKED declaration is rejected.
-/

open Lean

def cnst (n : Name) (ls : List Level := []) : Expr := .const n ls

/-- `@Eq.{1} Bool a b` -/
def eqBool (a b : Expr) : Expr := mkApp3 (cnst ``Eq [Level.one]) (cnst ``Bool) a b
/-- `@Eq.refl.{1} Bool a` -/
def reflBool (a : Expr) : Expr := mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Bool) a
/-- `@Eq.{1} Nat a b` -/
def eqNat (a b : Expr) : Expr := mkApp3 (cnst ``Eq [Level.one]) (cnst ``Nat) a b

def thm (n : Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := val }

def defn (n : Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := val,
              hints := .regular 0, safety := .safe }

/-- The `ConstantInfo` of a safe, regular definition (for an unchecked insert). -/
def defnInfo (n : Name) (ty val : Expr) : ConstantInfo :=
  .defnInfo { name := n, levelParams := [], type := ty, value := val,
              hints := .regular 0, safety := .safe }

/-- An `unsafe` definition: Lean's kernel checks it in its unsafe context, and
`Lean.Environment.replay` leaves it out of `remaining`. -/
def unsafeDefn (n : Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := val,
              hints := .regular 0, safety := .unsafe }

def one : Expr := mkApp (cnst ``Nat.succ) (cnst ``Nat.zero)

/-- A theorem with explicit universe parameters `ls`. -/
def thmU (n : Name) (ls : List Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := ls, type := ty, value := val }

/-- A safe axiom with no universe parameters. -/
def axm (n : Name) (ty : Expr) : Declaration :=
  .axiomDecl { name := n, levelParams := [], type := ty, isUnsafe := false }

/-- `fun (h : True) => h`: a term of type `True → True`, not a type. -/
def lamTrue : Expr := mkLambda `h .default (cnst ``True) (.bvar 0)

/-- `∀ (α : Sort u) (a : α), a = a`, a proposition at every universe `u`. -/
def reflTy (u : Level) : Expr :=
  mkForall `α .default (.sort u)
    (mkForall `a .default (.bvar 0) (mkApp3 (cnst ``Eq [u]) (.bvar 1) (.bvar 0) (.bvar 0)))

/-- `fun (α : Sort u) (a : α) => @Eq.refl α a`, of type `reflTy u`. -/
def reflVal (u : Level) : Expr :=
  mkLambda `α .default (.sort u)
    (mkLambda `a .default (.bvar 0) (mkApp2 (cnst ``Eq.refl [u]) (.bvar 1) (.bvar 0)))
/-- `ITE := @ite.{1} (Nat → Nat) True (Decidable.isTrue True True.intro)
`(fun n => n) (fun _ => 0)` — a function-valued `ite` whose then-branch depends
on the argument it is later applied to. Fully applied to `k`, Lean reduces it to
`k`; the over-application soundness bug dropped the trailing `k` from
`reduce_native`'s spine and returned the bare then-branch `fun n => n`. -/
def iteNatToNat : Expr :=
  let natTy := cnst ``Nat
  let natToNat := mkForall `n .default natTy natTy
  mkAppN (cnst ``ite [Level.one]) #[
    natToNat, cnst ``True,
    mkApp2 (cnst ``Decidable.isTrue) (cnst ``True) (cnst ``True.intro),
    mkLambda `n .default natTy (.bvar 0),
    mkLambda `x .default natTy (cnst ``Nat.zero)]

/-- `ITE k` — the over-applied `ite`, which must reduce to `k`. -/
def iteApp (k : Expr) : Expr := mkApp iteNatToNat k

/-- `inductive ind : prop | t | f` over `prop`, a definition of `Prop` (`def prop : Type := Prop`):
a family whose result sort is `Prop` only up to whnf. Lean's kernel finds its level by whnf
(`check_inductive_types`), so `ind.rec` eliminates only into `Prop`. -/
def deltaPropDecl (ind prop : Name) : Declaration :=
  .inductDecl [] 0 [{ name := ind, type := cnst prop,
                      ctors := [{ name := .str ind "t", type := cnst ind },
                                { name := .str ind "f", type := cnst ind }] }] false

/-- `@ind.rec.{ls} (fun _ => Bool) true false major`. -/
def deltaToBool (ind : Name) (ls : List Level) (major : Expr) : Expr :=
  mkApp4 (cnst (.str ind "rec") ls) (mkLambda `x .default (cnst ind) (cnst ``Bool))
    (cnst ``Bool.true) (cnst ``Bool.false) major

/-- A proof of `False` from a recursor of the δ-Prop family `ind` that eliminates into `Bool`
(universe arguments `ls`): `ind.t = ind.f` holds by proof irrelevance (`Eq.refl ind.t`), and
`Eq.rec` transports `True.intro : P (toBool ind.t)` to `P (toBool ind.f)`, where
`P b := Bool.rec False True b`, so `P true ≡ True` and `P false ≡ False`. -/
def deltaFalse (ind : Name) (ls : List Level) : Expr :=
  let ty := cnst ind
  let t := cnst (.str ind "t")
  let p := fun (b : Expr) => mkApp4 (cnst ``Bool.rec [Level.one])
    (mkLambda `b .default (cnst ``Bool) (.sort Level.zero)) (cnst ``False) (cnst ``True) b
  let motive := mkLambda `x .default ty
    (mkLambda `h .default (mkApp3 (cnst ``Eq [Level.zero]) ty t (.bvar 0))
      (p (deltaToBool ind ls (.bvar 1))))
  mkAppN (cnst ``Eq.rec [Level.zero, Level.zero])
    #[ty, t, motive, cnst ``True.intro, cnst (.str ind "f"), mkApp2 (cnst ``Eq.refl [Level.zero]) ty t]

/-- `inductive ind.{u} : Sort u | t | f`, whose result level `u` is not provably nonzero: at
`u := 0` it is a two-constructor `Prop`, so Lean's kernel gives `ind.rec` no motive universe
(`elim_only_at_universe_zero`: only `is_not_zero` exempts a family). The elaborator refuses the
`inductive` command without `bootstrap.inductiveCheckResultingUniverse false`; `addDeclCore`
reaches the kernel directly. -/
def sortUDecl (ind : Name) : Declaration :=
  let u := Level.param `u
  .inductDecl [`u] 0 [{ name := ind, type := .sort u,
                        ctors := [{ name := .str ind "t", type := cnst ind [u] },
                                  { name := .str ind "f", type := cnst ind [u] }] }] false

/-- `mutual inductive HMA | a : HMA; inductive HMB | b : HMA → HMB end`. Lean's kernel computes
`isRec` for the WHOLE block (`inductive.cpp` `is_rec`: a binder domain of any constructor of any
type names a type of the block), so the non-recursive `HMA` is stored with `isRec := true`, and
has no structure or unit-like eta. A per-type reading says `false` for `HMA`. -/
def mutualIsRecDecl : Declaration :=
  .inductDecl [] 0 [
    { name := `HMA, type := .sort Level.one, ctors := [{ name := `HMA.a, type := cnst `HMA }] },
    { name := `HMB, type := .sort Level.one,
      ctors := [{ name := `HMB.b, type := mkForall `x .default (cnst `HMA) (cnst `HMB) }] }] false

/-- `structure HBox (α : Type) where f : Nat → α`, a container whose constructor is reflexive. -/
def hboxDecl : Declaration :=
  let boxTy := mkForall `α .default (.sort Level.one) (.sort Level.one)
  let mkTy := mkForall `α .default (.sort Level.one)
    (mkForall `f .default (mkForall `n .default (cnst ``Nat) (.bvar 1))
      (mkApp (cnst `HBox) (.bvar 1)))
  .inductDecl [] 1 [{ name := `HBox, type := boxTy, ctors := [{ name := `HBox.mk, type := mkTy }] }] false

/-- `inductive HNR | mk : HBox HNR → HNR`: nested through `HBox`. Lean's kernel computes
`isReflexive` on the AUXILIARY declaration (`HBox HNR` becomes an auxiliary type whose constructor
takes `Nat → aux`), so `HNR` is stored with `isReflexive := true` although no binder domain of
`HNR.mk` itself is a function type. -/
def hnrDecl : Declaration :=
  let mkTy := mkForall `b .default (mkApp (cnst `HBox) (cnst `HNR)) (cnst `HNR)
  .inductDecl [] 0 [{ name := `HNR, type := .sort Level.one,
                      ctors := [{ name := `HNR.mk, type := mkTy }] }] false

/-- `inductive HWT | leaf | branch : (Nat → HWT) → HWT`, reflexive by its own constructor. -/
def hwtDecl : Declaration :=
  let branchTy := mkForall `f .default (mkForall `n .default (cnst ``Nat) (cnst `HWT)) (cnst `HWT)
  .inductDecl [] 0 [{ name := `HWT, type := .sort Level.one,
                      ctors := [{ name := `HWT.leaf, type := cnst `HWT },
                                { name := `HWT.branch, type := branchTy }] }] false

/-- `@Sigma.{0,0} Nat fam`: a dependent pair whose second component has type `fam fst`. -/
def sigmaNat (fam : Expr) : Expr := mkApp2 (cnst ``Sigma [Level.zero, Level.zero]) (cnst ``Nat) fam

/-- `fun n : Nat => Fin n → ty`, a family whose body is a function type over `ty`. -/
def finTo (ty : Name) : Expr :=
  mkLambda `n .default (cnst ``Nat) (mkForall `i .default (mkApp (cnst ``Fin) (.bvar 0)) (cnst ty))

/-- `inductive ty | mk : field → ty`. -/
def wrapDecl (ty : Name) (field : Expr) : Declaration :=
  .inductDecl [] 0 [{ name := ty, type := .sort Level.one,
                      ctors := [{ name := .str ty "mk",
                                  type := mkForall `s .default field (cnst ty) }] }] false

/-- `inductive SGS | mk : (Σ _ : Nat, Nat → SGS) → SGS`: nested through the DEPENDENT container
`Sigma`, its family argument the lambda `fun _ => Nat → SGS`. Lean's elimination instantiates
`Sigma.mk`'s field `snd : β fst` without a β step (`instantiate_rev`), so the auxiliary
constructor's field is the redex `(fun _ => Nat → SGS) fst`, not a Pi: Lean stores
`isReflexive := false`, and that redex in the minor premises and rules of `SGS.rec`/`SGS.rec_1`.
A checker that β-reduces the auxiliary types reads `Nat → SGS`: reflexive, and different recursors. -/
def sgsDecl : Declaration :=
  wrapDecl `SGS (sigmaNat (mkLambda `x .default (cnst ``Nat)
    (mkForall `n .default (cnst ``Nat) (cnst `SGS))))

/-- `inductive SG | mk : (Σ n : Nat, Fin n → SG) → SG`: the family depends on its argument. -/
def sgDecl : Declaration := wrapDecl `SG (sigmaNat (finTo `SG))

/-- `inductive SGP | mk : (Σ' n : Nat, Fin n → SGP) → SGP`, through `PSigma.{1,1}`. -/
def sgpDecl : Declaration :=
  wrapDecl `SGP (mkApp2 (cnst ``PSigma [Level.one, Level.one]) (cnst ``Nat) (finTo `SGP))

/-- `structure DBox (α : Type) (β : α → Type) where a : α; b : β a`, a user dependent container. -/
def dboxDecl : Declaration :=
  let ty1 := Expr.sort Level.one
  let famTy := fun (α : Expr) => mkForall `x .default α ty1
  let boxTy := mkForall `α .default ty1 (mkForall `β .default (famTy (.bvar 0)) ty1)
  let mkTy := mkForall `α .default ty1 (mkForall `β .default (famTy (.bvar 0))
    (mkForall `a .default (.bvar 1) (mkForall `b .default (mkApp (.bvar 1) (.bvar 0))
      (mkApp2 (cnst `DBox) (.bvar 3) (.bvar 2)))))
  .inductDecl [] 2 [{ name := `DBox, type := boxTy,
                      ctors := [{ name := `DBox.mk, type := mkTy }] }] false

/-- `inductive DB | mk : DBox Nat (fun n => Fin n → DB) → DB`. -/
def dbDecl : Declaration := wrapDecl `DB (mkApp2 (cnst `DBox) (cnst ``Nat) (finTo `DB))

/-- `inductive SJ | leaf | node : (Σ _ : Nat, SJ) → SJ`, a single-level stand-in for the redex
in `Lean.Json`'s map field (not its recursive container, which `ReplayHonestDepNestedDeep` has):
the family `fun _ => SJ` leaves the redex `(fun _ => SJ) fst`, which is not reflexive either way
but stands in the recursors' minor premises and rules. -/
def sjDecl : Declaration :=
  .inductDecl [] 0 [{ name := `SJ, type := .sort Level.one,
                      ctors := [{ name := `SJ.leaf, type := cnst `SJ },
                                { name := `SJ.node, type := mkForall `s .default
                                    (sigmaNat (mkLambda `x .default (cnst ``Nat) (cnst `SJ)))
                                    (cnst `SJ) }] }] false

/-- `@SJ.rec.{1} (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih.succ) (fun _ _ ih => ih) t`: the
depth of `t`, computed through both recursors' rules. -/
def sjDepth (t : Expr) : Expr :=
  let nat := cnst ``Nat
  let sig := sigmaNat (mkLambda `x .default nat (cnst `SJ))
  mkAppN (cnst `SJ.rec [Level.one])
    #[mkLambda `t .default (cnst `SJ) nat, mkLambda `s .default sig nat, cnst ``Nat.zero,
      mkLambda `a .default sig (mkLambda `ih .default nat (mkApp (cnst ``Nat.succ) (.bvar 0))),
      mkLambda `fst .default nat (mkLambda `snd .default (cnst `SJ)
        (mkLambda `ih .default nat (.bvar 0))),
      t]

/-- `SJ.node ⟨0, SJ.leaf⟩`. -/
def sjOne : Expr :=
  mkApp (cnst `SJ.node) (mkAppN (cnst ``Sigma.mk [Level.zero, Level.zero])
    #[cnst ``Nat, mkLambda `x .default (cnst ``Nat) (cnst `SJ), cnst ``Nat.zero, cnst `SJ.leaf])

/-- `fun t : SGS => @SGS.rec.{1} (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih) (fun _ _ _ => 0) t`:
the `Sigma.mk` minor premise takes the field `snd` and its induction hypothesis
`(a : Nat) → motive_1 (snd a)`, which Lean reads through the redex by `whnf`. -/
def sgsElim : Expr :=
  let nat := cnst ``Nat
  let fn := mkForall `n .default nat (cnst `SGS)
  let sig := sigmaNat (mkLambda `x .default nat fn)
  mkLambda `t .default (cnst `SGS) (mkAppN (cnst `SGS.rec [Level.one])
    #[mkLambda `t .default (cnst `SGS) nat, mkLambda `s .default sig nat,
      mkLambda `a .default sig (mkLambda `ih .default nat (.bvar 0)),
      mkLambda `fst .default nat (mkLambda `snd .default fn
        (mkLambda `ih .default (mkForall `n .default nat nat) (cnst ``Nat.zero))),
      .bvar 0])

/-- `deltaFalse` for a universe-polymorphic family: `indLs` instantiates the family, `recLs`
its recursor (motive universe first). Needs the instance to be a proposition (`Eq.{0}`). -/
def twoCtorFalse (ind : Name) (indLs recLs : List Level) : Expr :=
  let ty := cnst ind indLs
  let t := cnst (.str ind "t") indLs
  let toBool := fun (major : Expr) => mkApp4 (cnst (.str ind "rec") recLs)
    (mkLambda `x .default ty (cnst ``Bool)) (cnst ``Bool.true) (cnst ``Bool.false) major
  let p := fun (b : Expr) => mkApp4 (cnst ``Bool.rec [Level.one])
    (mkLambda `b .default (cnst ``Bool) (.sort Level.zero)) (cnst ``False) (cnst ``True) b
  let motive := mkLambda `x .default ty
    (mkLambda `h .default (mkApp3 (cnst ``Eq [Level.zero]) ty t (.bvar 0))
      (p (toBool (.bvar 1))))
  mkAppN (cnst ``Eq.rec [Level.zero, Level.zero])
    #[ty, t, motive, cnst ``True.intro, cnst (.str ind "f") indLs,
      mkApp2 (cnst ``Eq.refl [Level.zero]) ty t]

-- Universe-level families (`kernel-level-normalizer-lean-profile`, DECISIONS R150). Every
-- level below is built with the raw `Level` constructors, so the `.olean` stores it node for
-- node, as Lean's kernel reads it.

def lp (n : Name) : Level := .param n
def lone : Level := .succ .zero
/-- `def n.{ps} : Sort a → Sort b := fun x => x`: admitted iff the kernel finds `a ≡ b`. -/
def sortIdDecl (n : Name) (ps : List Name) (a b : Level) : Declaration :=
  .defnDecl { name := n, levelParams := ps, type := mkForall `x .default (.sort a) (.sort b),
              value := mkLambda `x .default (.sort a) (.bvar 0), hints := .opaque, safety := .safe }
def sortAx (n : Name) (ps : List Name) (l : Level) : Declaration :=
  .axiomDecl { name := n, levelParams := ps, type := .sort l, isUnsafe := false }
/-- `def n.{u,v} : Sort l := k.{u, v, imax u v}` for `k.{u,v,w} : Sort (max (max u v) w)`. -/
def useKDecl (n k : Name) (l : Level) : Declaration :=
  .defnDecl { name := n, levelParams := [`u, `v], type := .sort l,
              value := .const k [lp `u, lp `v, .imax (lp `u) (lp `v)], hints := .opaque,
              safety := .safe }
/-- `def n.{u,v} : Sort l := a.{u,v} → b.{u,v}`: the kernel infers `Sort (mk_imax la lb)`. -/
def arrowDecl (n a b : Name) (l : Level) : Declaration :=
  .defnDecl { name := n, levelParams := [`u, `v], type := .sort l,
              value := mkForall `x .default (.const a [lp `u, lp `v]) (.const b [lp `u, lp `v]),
              hints := .opaque, safety := .safe }
/-- `def n.{u,v} : Sort l := c.{u,v}`. -/
def useDecl (n c : Name) (l : Level) : Declaration :=
  .defnDecl { name := n, levelParams := [`u, `v], type := .sort l,
              value := .const c [lp `u, lp `v], hints := .opaque, safety := .safe }
def uvw : List Name := [`u, `v, `w]

-- Universe levels on the paths other than constant instantiation, level def-eq and the Π
-- sort (DECISIONS R150, 2026-10-20 review round): a projection's constructor type, δ, an ι
-- rule's right-hand side, and the recursor's structural `is_zero`. Pinned Lean's checked
-- verdicts on the same shapes: `reports/level-lean-profile-2026-10-19/ReachVerdicts.lean`.

/-- The stored level `max (max u v) w`. -/
def rchField : Level := .max (.max (lp `u) (lp `v)) (lp `w)
/-- The instantiation `w := imax u v`. -/
def rchInst : List Level := [lp `u, lp `v, .imax (lp `u) (lp `v)]
/-- What a collapsing substitution builds from `rchField` at `rchInst`. -/
def rchCollapsed : Level := .max (lp `u) (lp `v)
/-- What Lean's `instantiate` builds from `rchField` at `rchInst` (`mk_max` keeps both sides). -/
def rchRaw : Level := .max (.max (lp `u) (lp `v)) (.imax (lp `u) (lp `v))
/-- One inductive type of a block. -/
def rchType (n : Name) (type : Expr) (ctors : List Constructor) : InductiveType :=
  { name := n, type := type, ctors := ctors }
/-- `structure s.{u,v,w} where a : Sort (max (max u v) w)`. -/
def rchStruct (s : Name) : Declaration :=
  .inductDecl uvw 0 [rchType s (.sort (.succ rchField))
    [{ name := s ++ `mk, type := mkForall `a .default (.sort rchField) (.const s (uvw.map lp)) }]] false
/-- `def n.{u,v} : s.{u,v,imax u v} → Sort l := fun x => x.1` (a kernel `Proj`). -/
def rchProj (n s : Name) (l : Level) : Declaration :=
  let sI := Expr.const s rchInst
  .defnDecl { name := n, levelParams := [`u, `v], type := mkForall `x .default sI (.sort l),
              value := mkLambda `x .default sI (.proj s 0 (.bvar 0)), hints := .opaque,
              safety := .safe }
/-- `def d.{u,v,w} : Sort (succ (max (max u v) w)) := Sort (max (max u v) w)`. -/
def rchSortDef (d : Name) : Declaration :=
  .defnDecl { name := d, levelParams := uvw, type := .sort (.succ rchField), value := .sort rchField,
              hints := .regular 1, safety := .safe }
/-- `def n.{u,v} : d.{u,v,imax u v} → Sort l := fun x => x` (needs δ on `d`). -/
def rchDelta (n d : Name) (l : Level) : Declaration :=
  let dI := Expr.const d rchInst
  .defnDecl { name := n, levelParams := [`u, `v], type := mkForall `x .default dI (.sort l),
              value := mkLambda `x .default dI (.bvar 0), hints := .opaque, safety := .safe }
/-- `inductive w.{u,v,w} : Sort (succ (max (max u v) w)) | leaf | node : (Sort (max (max u v) w) → w) → w`:
the `node` rule keeps `fun (x : Sort (max (max u v) w)) => w.rec … (g x)` in its right-hand side. -/
def rchTree (w : Name) : Declaration :=
  let wC := Expr.const w (uvw.map lp)
  .inductDecl uvw 0 [rchType w (.sort (.succ rchField)) [
    { name := w ++ `leaf, type := wC },
    { name := w ++ `node, type := mkForall `g .default (mkForall `x .default (.sort rchField) wC) wC }]] false
/-- `def n.{u,v} : ∀ (m : w.{u,v,imax u v} → Type) (lf : m w.leaf)
    (nd : ∀ (g : Sort l → w), (∀ (x : Sort l), m (g x)) → m (w.node g)) (g : Sort l → w),
    @Eq (m (w.node g)) (w.rec m lf nd (w.node g)) (nd g (fun (x : Sort l) => w.rec m lf nd (g x)))
  := fun m lf nd g => Eq.refl _`: the right side is the ι-reduct, so the kernel compares the
rule's instantiated binder with `Sort l`. -/
def rchIota (n w : Name) (l : Level) : Declaration :=
  let wI := Expr.const w rchInst
  let leafI := Expr.const (w ++ `leaf) rchInst
  let nodeI := Expr.const (w ++ `node) rchInst
  let recI := Expr.const (w ++ `rec) (lone :: rchInst)
  let gTy := mkForall `x .default (.sort l) wI
  let mTy := mkForall `t .default wI (.sort lone)
  let lfTy := mkApp (.bvar 0) leafI
  -- under [m, lf, g, x]: m = 3, g = 1; under [m, lf, g, ih]: m = 3, g = 1
  let ihTy := mkForall `x .default (.sort l) (mkApp (.bvar 3) (mkApp (.bvar 1) (.bvar 0)))
  let ndTy := mkForall `g .default gTy
    (mkForall `ih .default ihTy (mkApp (.bvar 3) (mkApp nodeI (.bvar 1))))
  -- under [m, lf, nd, g]: m = 3, lf = 2, nd = 1, g = 0
  let nodeG := mkApp nodeI (.bvar 0)
  let alpha := mkApp (.bvar 3) nodeG
  let lhs := mkAppN recI #[.bvar 3, .bvar 2, .bvar 1, nodeG]
  -- under [m, lf, nd, g, x]: m = 4, lf = 3, nd = 2, g = 1, x = 0
  let ih := mkLambda `x .default (.sort l)
    (mkAppN recI #[.bvar 4, .bvar 3, .bvar 2, mkApp (.bvar 1) (.bvar 0)])
  let rhs := mkAppN (.bvar 1) #[.bvar 0, ih]
  let binders (body : Expr) (mk : Name → BinderInfo → Expr → Expr → Expr) : Expr :=
    mk `m .default mTy (mk `lf .default lfTy (mk `nd .default ndTy (mk `g .default gTy body)))
  .defnDecl { name := n, levelParams := [`u, `v],
              type := binders (mkAppN (cnst ``Eq [lone]) #[alpha, lhs, rhs]) mkForall,
              value := binders (mkAppN (cnst ``Eq.refl [lone]) #[alpha, lhs]) mkLambda,
              hints := .opaque, safety := .safe }

/-- A mutual block of two empty types `a : Sort la`, `b : Sort lb` over `u, v`
(`inductive.cpp:250`: their levels must be `is_equivalent`). -/
def rchMutual (a b : Name) (la lb : Level) : Declaration :=
  .inductDecl [`u, `v] 0 [{ name := a, type := .sort la, ctors := [] },
                          { name := b, type := .sort lb, ctors := [] }] false
/-- `max v (imax u v)`, a level `mk_max`/`mk_imax` keep. Lean's `normalize` keeps both
arguments; Clean's drops `v`, which `imax u v` dominates. -/
def rchAvLvl : Level := .max (lp `v) (.imax (lp `u) (lp `v))
/-- `succ (imax u v)`: above `rchAvLvl` at every assignment. Lean's `is_geq` does not prove it
(it must prove `succ (imax u v) ≥ v`: different bases, different offsets, level.cpp:508-526);
Clean's does (`succ^n x ≥ x` against the normalised `imax u v`). -/
def rchFbLvl : Level := .succ (.imax (lp `u) (lp `v))
/-- `axiom av.{u,v} : Sort (max v (imax u v))`. -/
def rchAv (av : Name) : Declaration :=
  .axiomDecl { name := av, levelParams := [`u, `v], type := .sort rchAvLvl, isUnsafe := false }
/-- `inductive n.{u,v} : Sort l | mk : av.{u,v} → n.{u,v}` (`inductive.cpp:439`: the field's
sort must be `is_geq`-below `l`). -/
def rchFieldBlock (n av : Name) (l : Level) : Declaration :=
  let self := Expr.const n [lp `u, lp `v]
  .inductDecl [`u, `v] 0 [rchType n (.sort l)
    [{ name := n ++ `mk, type := mkForall `x .default (.const av [lp `u, lp `v]) self }]] false
/-- `inductive n : Sort l | mk : Nat → n` (`inductive.cpp:439`: the bound is skipped only for a
structural `0`). -/
def rchNatBlock (n : Name) (l : Level) : Declaration :=
  .inductDecl [] 0 [rchType n (.sort l)
    [{ name := n ++ `mk, type := mkForall `x .default (cnst ``Nat) (cnst n) }]] false

/-- (main module, import, checked?, declarations in `addDecl` order). -/
def family : String → Option (Name × Name × Bool × Array Declaration)
  | "forged" => some (`ReplayForged, `Init.Prelude, false, #[
      -- `False := itself`: Lean's replay reports `(kernel) unknown constant`.
      thm `forged_self (cnst ``False) (cnst `forged_self),
      -- a two-cycle across two declarations.
      thm `forged_cycA (cnst ``False) (cnst `forged_cycB),
      thm `forged_cycB (cnst ``False) (cnst `forged_cycA),
      -- plainly ill-typed control: rejected by every checker already.
      thm `forged_bad (cnst ``False) (cnst ``True.intro)])
  | "forged3" => some (`ReplayForged3, `Init.Prelude, false, #[
      thm `forged3_self (cnst ``False) (cnst `forged3_self),
      thm `forged3_cycA (cnst ``False) (cnst `forged3_cycB),
      thm `forged3_cycB (cnst ``False) (cnst `forged3_cycA)])
  | "forged4" => some (`ReplayForged4, `Init.System.Platform, false, #[
      -- `isOSX`/`isWindows`/`isEmscripten` unfold to applications of `@[extern] opaque`
      -- constants: Lean's kernel cannot decide any of these. One of the first two holds
      -- on whatever host builds Clean, and `isWindows = false` holds on every host Clean
      -- runs on, so a checker that reduces the externs accepts at least one of them.
      thm `forged4_osx (eqBool (cnst ``System.Platform.isOSX) (cnst ``Bool.true))
        (reflBool (cnst ``Bool.true)),
      thm `forged4_not_osx (eqBool (cnst ``System.Platform.isOSX) (cnst ``Bool.false))
        (reflBool (cnst ``Bool.false)),
      thm `forged4_not_windows (eqBool (cnst ``System.Platform.isWindows) (cnst ``Bool.false))
        (reflBool (cnst ``Bool.false)),
      thm `forged4_not_emscripten
        (eqBool (cnst ``System.Platform.isEmscripten) (cnst ``Bool.false))
        (reflBool (cnst ``Bool.false))])
  | "forged5" => some (`ReplayForged5, `Init.Prelude, false, #[
      -- A SAFE theorem whose value uses the `unsafe def unsafeCast`
      -- (`Init/Prelude.lean`): Lean's kernel refuses it (`type_checker.cpp`
      -- `infer_constant`: "invalid declaration, it uses unsafe declaration"),
      -- and `Lean.Environment.replay` never admits an unsafe constant at all.
      thm `forged5_unsafe (cnst ``False)
        (mkApp3 (cnst ``unsafeCast [Level.zero, Level.zero]) (cnst ``True) (cnst ``False)
          (cnst ``True.intro))])
  | "crossA" => some (`ReplayCrossA, `Init.Prelude, false, #[
      -- a forgery another module will import, and an honest neighbour.
      thm `cross_forged (cnst ``False) (cnst `cross_forged),
      thm `cross_honest (cnst ``True) (cnst ``True.intro)])
  | "crossB" => some (`ReplayCrossB, `ReplayCrossA, true, #[
      -- CHECKED by Lean's kernel: `ReplayCrossA` is a trusted import here, so
      -- `leanchecker ReplayCrossB` accepts it; only a replay that also replays
      -- `ReplayCrossA` (`leanchecker --fresh`) refuses `cross_uses_forged`.
      thm `cross_uses_forged (cnst ``False) (cnst `cross_forged),
      thm `cross_uses_honest (cnst ``True) (cnst `cross_honest)])
  | "honest" => some (`ReplayHonest, `Init.Prelude, true, #[
      thm `honest_t (cnst ``True) (cnst ``True.intro),
      -- a module-mate dependency: admitted only AFTER `honest_t`.
      thm `honest_chain (cnst ``True) (cnst `honest_t),
      -- a module-mate definition the next theorem must delta-unfold.
      defn `honest_one (cnst ``Nat) one,
      thm `honest_one_eq (eqNat (cnst `honest_one) one)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Nat) one)])
  | "honestUnsafe" => some (`ReplayHonestUnsafe, `Init.Prelude, true, #[
      -- CHECKED: an honest module with an unsafe definition. `leanchecker`
      -- accepts it (replay skips the unsafe one); a re-check lane must neither
      -- verify nor fail it, and must still verify its safe neighbour.
      unsafeDefn `honest_unsafe_val (cnst ``Nat) (cnst ``Nat.zero),
      thm `honest_safe (cnst ``True) (cnst ``True.intro)])
  | "honest4" => some (`ReplayHonest4, `Init.System.Platform, true, #[
      -- stuck in Lean's kernel, and still reflexive: must keep verifying.
      thm `honest4_osx_refl (eqBool (cnst ``System.Platform.isOSX) (cnst ``System.Platform.isOSX))
        (reflBool (cnst ``System.Platform.isOSX))])
  | "prelude" => some (`ReplayPrelude, `Init.Prelude, false, #[
      -- Clean's import prelude seeds `sorry`, `trustedArith` and `trustedAy`, each
      -- `{α : Sort u} → α`; none is a Lean constant, so for `leanchecker` each reference is an
      -- unknown constant.
      thm `prelude_sorry (cnst ``False) (mkApp (cnst `sorry [Level.zero]) (cnst ``False)),
      thm `prelude_arith (cnst ``False) (mkApp (cnst `trustedArith [Level.zero]) (cnst ``False)),
      thm `prelude_ay (cnst ``False) (mkApp (cnst `trustedAy [Level.zero]) (cnst ``False)),
      -- A module-local declaration whose NAME Clean's prelude also holds (with a proof of a
      -- different statement); `Init.Prelude` declares no such constant, so Lean checks this one.
      thm `Nat.not_succ_lt_zero (cnst ``False) (cnst ``True.intro),
      thm `prelude_honest (cnst ``True) (cnst ``True.intro)])
  | "preludeUse" => some (`ReplayPreludeUse, `Init.Prelude, false, #[
      -- An honest local `Nat.not_succ_lt_zero : True`, and a user that needs Clean's
      -- prelude statement of that name, `∀ n, Nat.lt (n+1) 0 → False`: Lean's kernel sees the
      -- local one and refuses the user.
      thm `Nat.not_succ_lt_zero (cnst ``True) (cnst ``True.intro),
      thm `prelude_shadow_use
        (mkForall `n .default (cnst ``Nat)
          (mkForall `h .default (mkApp2 (cnst ``Nat.lt) (mkApp (cnst ``Nat.succ) (.bvar 0))
            (cnst ``Nat.zero)) (cnst ``False)))
        (cnst `Nat.not_succ_lt_zero)])
  | "forgedThmType" => some (`ReplayForgedThmType, `Init.Prelude, false, #[
      -- A THEOREM whose type is a type, not a proposition. Its value has its type, so a
      -- re-check that infers the type's sort and checks the value against the type admits
      -- it; Lean's `add_theorem` refuses it (`theorem_type_is_not_prop`).
      thm `forged_thm_nat (cnst ``Nat) (cnst ``Nat.zero)])
  | "forgedProjIdx" => some (`ReplayForgedProjIdx, `Init.Prelude, false, #[
      -- `.proj Prod (2^64) (1, 1) : Nat`. Lean's kernel takes a projection index only when it
      -- is a small Nat (v4.30.0-rc2 `infer_proj`: `!proj_idx(e).is_small()` throws; v4.33.1
      -- `to_proj_idx`, leanprover/lean4#14632). The index is a heap Nat in the `.olean`; a
      -- decoder that keeps its low limb reads `.proj Prod 0 (1, 1)`, which checks (R147).
      defn `forged_proj_idx (cnst ``Nat)
        (.proj ``Prod (2 ^ 64)
          (mkApp4 (cnst ``Prod.mk [Level.zero, Level.zero]) (cnst ``Nat) (cnst ``Nat) one one))])
  | "forgedUniv" => some (`ReplayForgedUniv, `Init.Prelude, false, #[
      -- `u` occurs in the type and the value but is not a universe parameter of the
      -- declaration: Lean's kernel refuses the undeclared universe.
      thmU `forged_univ [] (reflTy (.param `u)) (reflVal (.param `u))])
  | "forgedDupUniv" => some (`ReplayForgedDupUniv, `Init.Prelude, false, #[
      -- the universe parameter list names `u` twice: Lean's `check_duplicated_univ_params`.
      thmU `forged_dup_univ [`u, `u] (reflTy (.param `u)) (reflVal (.param `u))])
  | "honestUniv" => some (`ReplayHonestUniv, `Init.Prelude, true, #[
      -- CHECKED: the universe-polymorphic control of the three families above.
      thmU `honest_univ [`u] (reflTy (.param `u)) (reflVal (.param `u))])
  | "forgedLamType" => some (`ReplayForgedLamType, `Init.Prelude, false, #[
      -- An axiom whose "type" is a lambda (of type `True → True`), not a type, and a theorem
      -- stated by it. Lean's `check_constant_val` refuses the axiom (`ensure_sort`: `type
      -- expected`); a checker that asks only for the SORT of the type's type accepts both.
      axm `forged_lam_ax lamTrue,
      thm `forged_lam_thm lamTrue (cnst `forged_lam_ax)])
  | "honestBoolAx" => some (`ReplayHonestBoolAx, `Init.Prelude, true, #[
      -- CHECKED: two jointly consistent axioms, the import of `forgedBoolDef`.
      axm `bool_ax_b (cnst ``Bool),
      axm `bool_ax_hb (eqBool (cnst `bool_ax_b) (cnst ``Bool.false))])
  | "honestPropAx" => some (`ReplayHonestPropAx, `Init.Prelude, true, #[
      -- CHECKED: an honest axiom, the import of `forgedThmOverAx`.
      axm `prop_ax_p (cnst ``True)])
  | "honestIndAx" => some (`ReplayHonestIndAx, `Init.Prelude, true, #[
      -- CHECKED: two jointly consistent axioms (`ind_ax_t := False` models both), the import
      -- of `forgedIndOverAx`.
      axm `ind_ax_t (.sort Level.zero),
      axm `ind_ax_not (mkApp (cnst ``Not) (cnst `ind_ax_t))])
  | "honestOpaqueAx" => some (`ReplayHonestOpaqueAx, `Init.Prelude, true, #[
      -- CHECKED: an opaque and an axiom about it (jointly consistent: `op_b := false`).
      .opaqueDecl { name := `op_b, levelParams := [], type := cnst ``Bool,
                    value := cnst ``Bool.false, isUnsafe := false, all := [`op_b] },
      axm `op_hb (eqBool (cnst `op_b) (cnst ``Bool.false))])
  | "honestDeltaProp" => some (`ReplayHonestDeltaProp, `Init.Prelude, true, #[
      -- CHECKED: `def hdp_prop : Type := Prop` and `inductive HDP : hdp_prop | t | f`, a `Prop`
      -- family only up to whnf, whose kernel-generated `HDP.rec` eliminates only into `Prop`;
      -- `HDP.t = HDP.f` by proof irrelevance; and an elimination into `True`. The elaborator's
      -- `inductive` command cannot build this block (it fails at `HDP.ctorIdx`, v4.30.0-rc2), so
      -- it is added through `addDeclCore`.
      defn `hdp_prop (.sort Level.one) (.sort Level.zero),
      deltaPropDecl `HDP `hdp_prop,
      thm `honest_dp_irrel (mkApp3 (cnst ``Eq [Level.zero]) (cnst `HDP) (cnst `HDP.t) (cnst `HDP.f))
        (mkApp2 (cnst ``Eq.refl [Level.zero]) (cnst `HDP) (cnst `HDP.t)),
      thm `honest_dp_elim (cnst ``True)
        (mkApp4 (cnst `HDP.rec) (mkLambda `x .default (cnst `HDP) (cnst ``True))
          (cnst ``True.intro) (cnst ``True.intro) (cnst `HDP.t))])
  | "honestSortU" => some (`ReplayHonestSortU, `Init.Prelude, true, #[
      -- CHECKED: `inductive HSU.{u} : Sort u | t | f` (kernel-generated `HSU.rec` eliminates
      -- only into `Prop`), `HSU.t.{0} = HSU.f.{0}` by proof irrelevance, and an elimination of
      -- `HSU.{0}` into `True`.
      sortUDecl `HSU,
      thm `honest_su_irrel
        (mkApp3 (cnst ``Eq [Level.zero]) (cnst `HSU [Level.zero]) (cnst `HSU.t [Level.zero])
          (cnst `HSU.f [Level.zero]))
        (mkApp2 (cnst ``Eq.refl [Level.zero]) (cnst `HSU [Level.zero]) (cnst `HSU.t [Level.zero])),
      thm `honest_su_elim (cnst ``True)
        (mkApp4 (cnst `HSU.rec [Level.zero])
          (mkLambda `x .default (cnst `HSU [Level.zero]) (cnst ``True))
          (cnst ``True.intro) (cnst ``True.intro) (cnst `HSU.t [Level.zero]))])
  | "forgedIte" => some (`ReplayForgedIte, `Init.Prelude, false, #[
      -- `@Eq Nat (ITE 1) (ITE 0)`, proved by `rfl` at `ITE 1`. It type-checks
      -- only if `ITE 1 ≡ ITE 0`, which held only in Clean's EXTENDED theory
      -- while `reduce_native` dropped the over-application argument (both sides
      -- fell back to the then-branch `fun n => n`). Lean's kernel, and every
      -- Clean replay lane (`KernelTheory::Lean`, where the `ite` reducer never
      -- fires), reduce them to `1` and `0`: a declaration type mismatch. A
      -- regression guard plus `leanchecker` agreement.
      thm `forged_ite_overapp (eqNat (iteApp one) (iteApp (cnst ``Nat.zero)))
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Nat) (iteApp one))])
  | "honestIte" => some (`ReplayHonestIte, `Init.Prelude, true, #[
      -- CHECKED: the same over-applied `ite`, reduced correctly. `ITE 1 ≡ 1`
      -- (the surplus `1` re-applied to the then-branch, not dropped), so Lean's
      -- kernel admits it and a re-check lane must keep verifying it.
      thm `honest_ite_overapp (eqNat (iteApp one) one)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Nat) one)])
  | "forgedLevelSubsumption" => some (`ReplayForgedLevelSubsumption, `Init.Prelude, false, #[
      -- UNCHECKED: level equalities pinned Lean's kernel refuses (t1-t5, t9, t10 of
      -- `reports/level-normalizer-probe-2026-10-17/`), each true at every assignment.
      -- t1/t2/t3 were admitted by Clean's normaliser (join-subsumption, #1436's `imax`
      -- re-flattening); t4/t9 by its collapsing decoder; t5 by its collapsing level
      -- substitution; t10 by its collapsing `imax` in the Π sort. The axioms are honest.
      sortIdDecl `fls_join uvw (.max lone (.imax (lp `u) (lp `v)))
        (.max (.max lone (lp `v)) (.imax (lp `u) (lp `v))),
      sortIdDecl `fls_join_wf uvw (.max (.succ (lp `u)) (lp `w))
        (.max (.succ (lp `u)) (.max (.max lone (lp `w))
          (.imax (.succ (lp `u)) (.imax (.succ (lp `u)) (lp `w))))),
      sortIdDecl `fls_imax_reflatten uvw (.imax (.max (lp `v) (lp `u)) (.succ (lp `w)))
        (.max (lp `u) (.max (lp `v) (.succ (lp `w)))),
      sortIdDecl `fls_decode_max uvw (.max (lp `u) (lp `v))
        (.max (.max (lp `u) (lp `v)) (.imax (lp `u) (lp `v))),
      sortIdDecl `fls_decode_imax uvw (.max (lp `u) (.imax (lp `v) (lp `u))) (.imax (lp `v) (lp `u)),
      sortAx `fls_K uvw (.max (.max (lp `u) (lp `v)) (lp `w)),
      useKDecl `fls_subst `fls_K (.max (lp `u) (lp `v)),
      sortAx `fls_A [`u, `v] (.imax (lp `u) (lp `v)),
      sortAx `fls_B [`u, `v] (.max (lp `u) (.succ (lp `v))),
      arrowDecl `fls_infer_pi `fls_A `fls_B (.max (lp `u) (.succ (lp `v)))])
  | "honestLevelEquiv" => some (`ReplayHonestLevelEquiv, `Init.Prelude, true, #[
      -- CHECKED: the twins pinned Lean's kernel admits (t3b, t5b, t6, t7, t8, t10b). t5b and
      -- t10b are admitted only with Lean's construction: Clean's collapsing substitution and
      -- `imax` build `max u v` and `max u (v+1)` where the declared levels keep the raw nodes.
      sortIdDecl `hle_imax_nonzero uvw (.imax (lp `u) (.succ (lp `w))) (.max (lp `u) (.succ (lp `w))),
      sortAx `hle_K uvw (.max (.max (lp `u) (lp `v)) (lp `w)),
      useKDecl `hle_subst `hle_K (.max (.max (lp `u) (lp `v)) (.imax (lp `u) (lp `v))),
      sortIdDecl `hle_succ_dist uvw (.succ (.max (lp `u) (lp `v)))
        (.max (.succ (lp `u)) (.succ (lp `v))),
      sortIdDecl `hle_flatten uvw (.max lone (.max (lp `u) (lp `v))) (.max (.max (lp `v) lone) (lp `u)),
      sortIdDecl `hle_imax_self uvw (.imax (lp `u) (lp `u)) (lp `u),
      sortAx `hle_A [`u, `v] (.imax (lp `u) (lp `v)),
      sortAx `hle_B [`u, `v] (.max (lp `u) (.succ (lp `v))),
      arrowDecl `hle_infer_pi `hle_A `hle_B
        (.max (.imax (lp `u) (lp `v)) (.max (lp `u) (.succ (lp `v))))])
  | "levelSharing" => some (`ReplayLevelSharing, `Init.Prelude, false, #[
      -- UNCHECKED: the critic's `Eqp` probe in one module. `ls_cS.{u,v} : Sort (imax v (u+1))`
      -- stores a level `mk_imax` would rebuild (to `max v (u+1)`), so instantiating it by the
      -- identity is kept or rebuilt by Lean's `instantiate` according to object sharing.
      -- Same-module users share `u`/`v` with `ls_cS` after `writeModule`'s max-sharing, so
      -- Lean keeps the node: `ls_same` (`Sort (imax v (u+1))`) is admitted and `ls_sorted`
      -- (`Sort (max (u+1) v)`) refused. Clean cannot see sharing and refuses both by name.
      sortAx `ls_cS [`u, `v] (.imax (lp `v) (.succ (lp `u))),
      useDecl `ls_same `ls_cS (.imax (lp `v) (.succ (lp `u))),
      useDecl `ls_sorted `ls_cS (.max (.succ (lp `u)) (lp `v))])
  | "honestLevelImport" => some (`ReplayHonestLevelImport, `Init.Prelude, true, #[
      -- CHECKED: axioms whose stored levels a collapsing decoder rewrites (t4's and t9's
      -- raw sides), for the cross-module rows below: their users see these levels only
      -- through an import (eager decode, or a mathverse closure shard).
      sortAx `hli_t4 [`u, `v] (.max (.max (lp `u) (lp `v)) (.imax (lp `u) (lp `v))),
      sortAx `hli_t9 [`u, `v] (.max (lp `u) (.imax (lp `v) (lp `u)))])
  | "forgedLevelImport" => some (`ReplayForgedLevelImport, `ReplayHonestLevelImport, false, #[
      -- UNCHECKED: t4 and t9 across a module boundary. Lean infers each use at the stored
      -- level and refuses the declared one; a collapsing decode of the import admits both.
      useDecl `fli_t4 `hli_t4 (.max (lp `u) (lp `v)),
      useDecl `fli_t9 `hli_t9 (.imax (lp `v) (lp `u))])
  | "honestLevelImportUse" => some (`ReplayHonestLevelImportUse, `ReplayHonestLevelImport, true, #[
      -- CHECKED: the same uses at the stored levels, which Lean admits.
      useDecl `hliu_t4 `hli_t4 (.max (.max (lp `u) (lp `v)) (.imax (lp `u) (lp `v))),
      useDecl `hliu_t9 `hli_t9 (.max (lp `u) (.imax (lp `v) (lp `u)))])
  | "honestLevelReach" => some (`ReplayHonestLevelReach, `Init.Prelude, true, #[
      -- CHECKED: the twins at Lean's spelling; the ι-reduct whose rule binder Lean instantiates
      -- raw (`hle_iota`, only the raw spelling is well typed); and two recursors pinned Lean
      -- builds from a STRUCTURAL `is_zero`: `hlr_P0.rec` eliminates only into `Prop` (its field's
      -- sort is `max 0 0`, inductive.cpp:517), `hlr_Q0.rec` has `k = false` (:557).
      rchStruct `hlr_S, rchSortDef `hlr_D, rchTree `hlr_W,
      rchProj `hle_proj `hlr_S rchRaw,
      rchDelta `hle_delta `hlr_D rchRaw,
      rchIota `hle_iota `hlr_W rchRaw,
      .axiomDecl { name := `hlr_A0, levelParams := [], type := .sort (.max .zero .zero),
                   isUnsafe := false },
      .inductDecl [] 0 [rchType `hlr_P0 (.sort .zero)
        [{ name := `hlr_P0.mk, type := mkForall `a .default (cnst `hlr_A0) (cnst `hlr_P0) }]] false,
      .inductDecl [] 0 [rchType `hlr_Q0 (.sort (.max .zero .zero))
        [{ name := `hlr_Q0.mk, type := cnst `hlr_Q0 }]] false,
      -- the honest twins of `ReplayForgedLevelReach`'s blocks: a mutual block whose two levels
      -- Lean's `is_equivalent` equates, and a field bound Lean's `is_geq` proves
      rchMutual `hlr_MA `hlr_MB rchCollapsed (.max (lp `v) (lp `u)),
      rchAv `hlr_Av, rchFieldBlock `hlr_Fb `hlr_Av (.succ (.max (lp `u) (lp `v)))])
  | "honestIndFlags" => some (`ReplayHonestIndFlags, `Init.Prelude, true, #[
      -- CHECKED: blocks whose kernel-generated `isRec`/`isReflexive` a reading of one type's
      -- own constructors, or of the restored (non-auxiliary) constructor types, gets wrong: the
      -- mutual `HMA`/`HMB` (`isRec := true` on the non-recursive `HMA`), `HNR` nested through
      -- `HBox` (`isReflexive := true` from the auxiliary declaration), and `HWT` (reflexive by
      -- its own constructor). A replay that compares the stored flags must accept all of them.
      mutualIsRecDecl, hboxDecl, hnrDecl, hwtDecl,
      defn `honest_hmb_val (cnst `HMB) (mkApp (cnst `HMB.b) (cnst `HMA.a)),
      defn `honest_hwt_val (cnst `HWT)
        (mkApp (cnst `HWT.branch) (mkLambda `n .default (cnst ``Nat) (cnst `HWT.leaf)))])
  | "honestDepNested" => some (`ReplayHonestDepNested, `Init.Core, true, #[
      -- CHECKED: blocks nested through a DEPENDENT container whose family argument is a lambda
      -- (`Sigma`, `PSigma`, the user's `DBox`), so the auxiliary constructors' fields are β-redexes
      -- Lean never reduces. Lean stores `isReflexive := false` on `SGS`/`SG`/`SGP`/`DB` (the field
      -- is not a Pi until β) and the redexes in every recursor; `SJ` is a single-level stand-in for
      -- the redex in `Lean.Json`'s map field (`ReplayHonestDepNestedDeep` has its real shape). A
      -- replay must regenerate exactly that, and every lane must admit every declaration.
      sgsDecl, sgDecl, sgpDecl, dboxDecl, dbDecl, sjDecl,
      defn `honest_sgs_elim (mkForall `t .default (cnst `SGS) (cnst ``Nat)) sgsElim,
      thm `honest_sj_depth (eqNat (sjDepth sjOne) one)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Nat) one)])
  | _ => none

/-- The constant `Lean.Environment.lakeAdd`, `private` to `Lean.Environment`, named by its
private name (a script cannot spell a numeric name component). -/
elab "private_lakeAdd%" : term =>
  return mkConst (mkPrivateNameCore `Lean.Environment `Lean.Environment.lakeAdd)

/-- `Lean.Environment.lakeAdd` (`@[export lake_environment_add]`, the lakefile cache's insert):
put a `ConstantInfo` into the kernel environment and the elaborator's view WITHOUT any kernel
check. -/
def rawAdd : Environment → ConstantInfo → Environment := private_lakeAdd%

def addChecked (env : Environment) (d : Declaration) (checked : Bool) : IO Environment := do
  match env.addDeclCore 0 d none (doCheck := checked) with
  | .ok next => return next
  | .error ex =>
    let msg ← (ex.toMessageData {}).toString
    throw <| IO.userError s!"kernel rejected a {if checked then "checked" else "forged"} declaration: {msg}"

/-- A non-recursive enumeration `ty : Type` with nullary constructors `ctors`. -/
def enumDecl (ty : Name) (ctors : List Name) : Declaration :=
  .inductDecl [] 0 [{ name := ty, type := .sort Level.one,
                      ctors := ctors.map fun c => { name := c, type := cnst ty } }] false

/-- Add `decl` (an inductive) through the CHECKED kernel path, then build the result from `env`
again with every constant the kernel generated inserted UNCHECKED, `forge` applied to each:
one insert per name, so the elaborator's constant map never sees a duplicate. -/
def forgeBlock (env : Environment) (decl : Declaration)
    (forge : ConstantInfo → IO ConstantInfo) (extra : List Name := []) : IO Environment := do
  let checked ← addChecked env decl true
  let mut out := env
  -- `getNames` lists each type, its `.rec` and its constructors; a nested block's auxiliary
  -- recursors (`<first>.rec_<n>`) come in `extra`, and only the kernel's map shows them.
  for n in decl.getNames ++ extra do
    let some ci := checked.find? n <|> checked.toKernelEnv.find? n
      | throw <| IO.userError s!"kernel generated no {n}"
    out := rawAdd out (← forge ci)
  return out

/-- `ty : Prop` with the NEGATIVE constructor `ty.mk : (ty → False) → ty`, which Lean's kernel
refuses (non-positive occurrence), inserted with NO kernel check, its stored `all` set to `all`,
and NO recursor. Every other stored field is what Lean's kernel would generate for the block
`[ty]` (`isRec` and `isReflexive` are `true`: the field `ty → False` names `ty`), so the only
lies are `all` and the block's admission itself. -/
def negPropBlock (env : Environment) (ty : Name) (all : List Name) : Environment :=
  let mk := Name.str ty "mk"
  let field := mkForall `x .default (cnst ty) (cnst ``False)
  let ind : InductiveVal := {
    name := ty, levelParams := [], type := .sort Level.zero, numParams := 0, numIndices := 0,
    all, ctors := [mk], numNested := 0, isRec := true, isUnsafe := false, isReflexive := true }
  let ctor : ConstructorVal := {
    name := mk, levelParams := [], type := mkForall `f .default field (cnst ty), induct := ty,
    cidx := 0, numParams := 0, numFields := 1, isUnsafe := false }
  rawAdd (rawAdd env (.inductInfo ind)) (.ctorInfo ctor)

/-- `(fun x : ty => x.1 x) (ty.mk (fun x : ty => x.1 x)) : False`, well typed over
`negPropBlock` (`x.1 : ty → False` is a `Prop` field of a `Prop` structure). -/
def negPropFalse (ty : Name) : Expr :=
  let selfApp := mkLambda `x .default (cnst ty) (mkApp (.proj ty 0 (.bvar 0)) (.bvar 0))
  mkApp selfApp (mkApp (cnst (.str ty "mk")) selfApp)

def str (s : String) : Expr := .lit (.strVal s)
def nat (n : Nat) : Expr := .lit (.natVal n)
def eqAt (ty a b : Expr) : Expr := mkApp3 (cnst ``Eq [Level.one]) ty a b
def reflAt (ty a : Expr) : Expr := mkApp2 (cnst ``Eq.refl [Level.one]) ty a

/-- A safe axiom with universe parameters `ls`. -/
def axL (n : Name) (ls : List Name) (ty : Expr) : Declaration :=
  .axiomDecl { name := n, levelParams := ls, type := ty, isUnsafe := false }

/-- A safe, regular definition with universe parameters `ls`. -/
def dfL (n : Name) (ls : List Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := ls, type := ty, value := val,
              hints := .regular 0, safety := .safe }

/-- Families whose `.olean` needs more than a list of declarations: the inductive forgeries
(an honest block whose recursor or constructor is then overwritten) and the families whose
declarations name constants only a larger import provides. -/
def special : String → Option (Name × Array Name × (Environment → IO Environment))
  | "forgedRec" => some (`ReplayForgedRec, #[`Init.Prelude], fun env => do
      -- `FRT.rec` stored with NO minor premises: `{motive : FRT → Sort u} → (t : FRT) → motive t`,
      -- so `@FRT.rec (fun _ => False) FRT.a : False`. Lean's replay regenerates the recursor
      -- from the constructors and refuses: `Invalid recursor FRT.rec`.
      let env ← forgeBlock env (enumDecl `FRT [`FRT.a, `FRT.b]) fun
        | .recInfo rv => do
          let u := Level.param rv.levelParams.head!
          let motiveTy := mkForall `t .default (cnst `FRT) (.sort u)
          let forgedTy := mkForall `motive .implicit motiveTy
            (mkForall `t .default (cnst `FRT) (mkApp (.bvar 1) (.bvar 0)))
          let rules := rv.rules.map fun r =>
            { r with rhs := mkLambda `motive .implicit motiveTy (mkApp (.bvar 0) (cnst r.ctor)) }
          return .recInfo { rv with type := forgedTy, numMinors := 0, rules }
        | ci => return ci
      addChecked env (thm `forged_rec_false (cnst ``False)
        (mkApp2 (cnst `FRT.rec [Level.zero])
          (mkLambda `t .default (cnst `FRT) (cnst ``False)) (cnst `FRT.a))) false)
  | "forgedRule" => some (`ReplayForgedRule, #[`Init.Prelude], fun env => do
      -- `FRR.rec`'s rule for `FRR.b` is overwritten with the rule for `FRR.a`, so
      -- `@FRR.rec (fun _ => Bool) true false FRR.b` reduces to `true` instead of `false`.
      let env ← forgeBlock env (enumDecl `FRR [`FRR.a, `FRR.b]) fun
        | .recInfo rv => do
          let some ruleA := rv.rules.head? | throw <| IO.userError "FRR.rec has no rules"
          let rules := rv.rules.map fun r =>
            if r.ctor == `FRR.b then { r with rhs := ruleA.rhs } else r
          return .recInfo { rv with rules }
        | ci => return ci
      let lhs := mkApp4 (cnst `FRR.rec [Level.one])
        (mkLambda `t .default (cnst `FRR) (cnst ``Bool)) (cnst ``Bool.true) (cnst ``Bool.false)
        (cnst `FRR.b)
      addChecked env (thm `forged_rule_eq (eqBool lhs (cnst ``Bool.true))
        (reflBool (cnst ``Bool.true))) false)
  | "forgedLevelReach" => some (`ReplayForgedLevelReach, #[`Init.Prelude], fun env => do
      -- UNCHECKED: a projection and a δ-unfolding at `w := imax u v`, declared at the level a
      -- collapsing substitution builds (`max u v`). Pinned Lean builds `max (max u v) (imax u v)`
      -- (`infer_proj`'s `instantiate_type_lparams`, `unfold_definition`'s
      -- `instantiate_value_lparams`) and refuses both. The structure and the definition are
      -- honest.
      let mut env := env
      for (d, checked) in [(rchStruct `flr_S, true), (rchSortDef `flr_D, true),
                           (rchProj `fls_proj `flr_S rchCollapsed, false),
                           (rchDelta `fls_delta `flr_D rchCollapsed, false), (rchAv `flr_Av, true)] do
        env ← addChecked env d checked
      -- Three inductive blocks pinned Lean's kernel refuses, each minted from a twin it admits
      -- with the inductive's stored sort overwritten, so every stored constructor and recursor
      -- is the one the kernel generates from the stored types (the twins' recursors do not
      -- mention the overwritten level): `flr_MA : Sort (max (max u v) (imax u v))` with
      -- `flr_MB : Sort (max u v)` in one block (not `is_equivalent`); `flr_Fb : Sort
      -- (succ (imax u v))` over a field `flr_Av.{u,v} : Sort (max v (imax u v))` (not `is_geq`;
      -- its twin is `Sort (succ (max u v))`, which eliminates the same way); `flr_Z : Sort
      -- (max 0 0)` over a `Nat` field (not structurally `0`, so the bound is checked, and fails).
      env ← forgeBlock env (rchMutual `flr_MA `flr_MB rchRaw rchRaw) fun
        | .inductInfo iv =>
          return .inductInfo (if iv.name == `flr_MB then { iv with type := .sort rchCollapsed } else iv)
        | ci => return ci
      env ← forgeBlock env (rchFieldBlock `flr_Fb `flr_Av (.succ (.max (lp `u) (lp `v)))) fun
        | .inductInfo iv => return .inductInfo { iv with type := .sort rchFbLvl }
        | ci => return ci
      forgeBlock env (rchNatBlock `flr_Z .zero) fun
        | .inductInfo iv => return .inductInfo { iv with type := .sort (.max .zero .zero) }
        | ci => return ci)
  | "forgedCtor" => some (`ReplayForgedCtor, #[`Init.Prelude], fun env => do
      -- The constructor `FRC.a : FRC` stored with type `False`: `FRC.a` is then a proof of
      -- `False`. Lean's replay rebuilds the inductive from the STORED constructor type, and the
      -- kernel refuses a constructor whose type does not end in the inductive.
      let env ← forgeBlock env (enumDecl `FRC [`FRC.a]) fun
        | .ctorInfo cv => return .ctorInfo { cv with type := cnst ``False }
        | ci => return ci
      addChecked env (thm `forged_ctor_false (cnst ``False) (cnst `FRC.a)) false)
  | "forgedQuot" => some (`ReplayForgedQuot, #[`Init.Prelude], fun env => do
      -- `Init.Prelude` has no quotient; this module stores `Quot.ind` as a
      -- `quotInfo` typed `∀ p : Prop, p`. Lean's replay of a `quotInfo` is the
      -- kernel's own `quotDecl`, which installs the canonical `Quot.ind`, so
      -- `Quot.ind False` is then ill-typed as a proof of `False`.
      let anyProp := mkForall `p .default (.sort Level.zero) (.bvar 0)
      let env := rawAdd env (.quotInfo (mkQuotValEx ``Quot.ind [] anyProp QuotKind.ind))
      addChecked env (thm `forged_quot_false (cnst ``False)
        (mkApp (cnst ``Quot.ind) (cnst ``False))) false)
  | "redeclare" => some (`ReplayRedeclare, #[`Init.Prelude], fun env => do
      -- A module that redeclares `Nat.pred`, which its import `Init.Prelude`
      -- declares: Lean's `addDecl` refuses it as already declared, so the
      -- theorem below is checked against the IMPORTED `Nat.pred`, where
      -- `Nat.pred 0 = 0`.
      let natToNat := mkForall `n .default (cnst ``Nat) (cnst ``Nat)
      let seven := nat 7
      let env := rawAdd env (defnInfo ``Nat.pred natToNat (mkLambda `n .default (cnst ``Nat) seven))
      addChecked env (thm `redecl_pred (eqNat (mkApp (cnst ``Nat.pred) (nat 0)) seven)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Nat) seven)) false)
  | "forgedStr" => some (`ReplayForgedStr, #[`Init.Data.String.TakeDrop, `Init.Data.String.Modify], fun env => do
      -- `String.drop`/`String.take` return a `String.Slice` in 4.30, which remembers the
      -- string it was cut from; `trimLeft` trims ASCII whitespace only; `toLower`/`toUpper`
      -- map ASCII letters only. Each equation is false in Lean.
      let slice := cnst ``String.Slice
      let drop := fun s n => mkApp2 (cnst ``String.drop) (str s) (nat n)
      let take := fun s n => mkApp2 (cnst ``String.take) (str s) (nat n)
      let strTy := cnst ``String
      let mut env := env
      for d in [
        thm `forged_str_drop (eqAt slice (drop "abc" 1) (drop "xbc" 1)) (reflAt slice (drop "abc" 1)),
        thm `forged_str_take (eqAt slice (take "abc" 1) (take "abd" 1)) (reflAt slice (take "abc" 1)),
        thm `forged_str_trim (eqAt strTy (mkApp (cnst ``String.trimLeft) (str "\u3000x")) (str "x"))
          (reflAt strTy (str "x")),
        thm `forged_str_lower (eqAt strTy (mkApp (cnst ``String.toLower) (str "Ä")) (str "ä"))
          (reflAt strTy (str "ä")),
        thm `forged_str_upper (eqAt strTy (mkApp (cnst ``String.toUpper) (str "ß")) (str "SS"))
          (reflAt strTy (str "SS"))] do
        env ← addChecked env d false
      return env)
  | "honestStr" => some (`ReplayHonestStr, #[`Init.Data.String.TakeDrop, `Init.Data.String.Modify], fun env => do
      -- CHECKED by Lean's kernel: the same heads on inputs where Clean's reducers agree.
      let slice := cnst ``String.Slice
      let drop := fun s n => mkApp2 (cnst ``String.drop) (str s) (nat n)
      let strTy := cnst ``String
      let mut env := env
      for d in [
        thm `honest_str_drop_refl (eqAt slice (drop "abc" 1) (drop "abc" 1)) (reflAt slice (drop "abc" 1)),
        thm `honest_str_lower_refl (eqAt strTy (mkApp (cnst ``String.toLower) (str "AB"))
          (mkApp (cnst ``String.toLower) (str "AB"))) (reflAt strTy (mkApp (cnst ``String.toLower) (str "AB")))] do
        env ← addChecked env d true
      return env)
  | "forgedBoolDef" => some (`ReplayForgedBoolDef, #[`ReplayHonestBoolAx], fun env => do
      -- `def bool_ax_b := true` for the IMPORTED axiom `bool_ax_b : Bool` (Lean: already
      -- declared; `--fresh`: the import aborts), and a proof of `False` that goes through only
      -- if `bool_ax_b` unfolds to `true`: `Eq.rec` over `bool_ax_hb : bool_ax_b = false` with
      -- the motive `Bool.rec False True`. A checker that lets a later module fill an imported
      -- axiom's value admits it.
      let env := rawAdd env (defnInfo `bool_ax_b (cnst ``Bool) (cnst ``Bool.true))
      let motive := mkLambda `x .default (cnst ``Bool)
        (mkLambda `h .default (eqBool (cnst ``Bool.true) (.bvar 0))
          (mkApp4 (cnst ``Bool.rec [Level.one]) (mkLambda `y .default (cnst ``Bool) (.sort Level.zero))
            (cnst ``False) (cnst ``True) (.bvar 1)))
      addChecked env (thm `forged_bool_false (cnst ``False)
        (mkAppN (cnst ``Eq.rec [Level.zero, Level.one])
          #[cnst ``Bool, cnst ``Bool.true, motive, cnst ``True.intro, cnst ``Bool.false,
            cnst `bool_ax_hb])) false)
  | "forgedOpaqueDef" => some (`ReplayForgedOpaqueDef, #[`ReplayHonestOpaqueAx], fun env => do
      -- `def op_b := true` over the IMPORTED `opaque op_b : Bool` (Lean: already declared;
      -- `--fresh`: the import aborts), and a proof of `False` that goes through only if `op_b`
      -- unfolds to `true`, as for `forgedBoolDef`. A checker that lets a later module's
      -- definition fill an opaque whose value it dropped (`stamp-verified --single-pass`
      -- roll-elides each verified target's opaque values before the next) admits it.
      let env := rawAdd env (defnInfo `op_b (cnst ``Bool) (cnst ``Bool.true))
      let motive := mkLambda `x .default (cnst ``Bool)
        (mkLambda `h .default (eqBool (cnst ``Bool.true) (.bvar 0))
          (mkApp4 (cnst ``Bool.rec [Level.one]) (mkLambda `y .default (cnst ``Bool) (.sort Level.zero))
            (cnst ``False) (cnst ``True) (.bvar 1)))
      addChecked env (thm `forged_op_false (cnst ``False)
        (mkAppN (cnst ``Eq.rec [Level.zero, Level.one])
          #[cnst ``Bool, cnst ``Bool.true, motive, cnst ``True.intro, cnst ``Bool.false,
            cnst `op_hb])) false)
  | "forgedOpaqueUse" => some (`ReplayForgedOpaqueUse, #[`ReplayHonestOpaqueAx], fun env => do
      -- The same proof of `False` in a THIRD module, built over `ReplayHonestOpaqueAx` alone
      -- and written with `ReplayForgedOpaqueDef` in its import list too (`headerImports`: Lean
      -- cannot import that pair, `environment already contains 'op_b'`). A run over all three
      -- replays it after `ReplayForgedOpaqueDef`, so it goes through exactly when that module's
      -- `def op_b := true` replaced the imported opaque in the run's environment.
      let motive := mkLambda `x .default (cnst ``Bool)
        (mkLambda `h .default (eqBool (cnst ``Bool.true) (.bvar 0))
          (mkApp4 (cnst ``Bool.rec [Level.one]) (mkLambda `y .default (cnst ``Bool) (.sort Level.zero))
            (cnst ``False) (cnst ``True) (.bvar 1)))
      addChecked env (thm `forged_op_use (cnst ``False)
        (mkAppN (cnst ``Eq.rec [Level.zero, Level.one])
          #[cnst ``Bool, cnst ``Bool.true, motive, cnst ``True.intro, cnst ``Bool.false,
            cnst `op_hb])) false)
  | "forgedQuotDef" => some (`ReplayForgedQuotDef, #[`Init.Core], fun env => do
      -- The KERNEL's `Quot` redefined as `fun {α : Sort u} (_ : α → α → Prop) => α` (its own
      -- type, so a checked stub upgrade would take it; Lean: already declared, `--fresh`: the
      -- import aborts), and `False` from `Quot.ind` + `Quot.sound` once `Quot r` unfolds to
      -- `Bool`: every `b : Bool` is then `Quot.mk r true`, so `false = true`.
      let u := Level.param `u
      let rel (a : Expr) := mkForall `a .default a (mkForall `b .default (.bvar 1) (.sort .zero))
      let ty := mkForall `α .implicit (.sort u) (mkForall `r .default (rel (.bvar 0)) (.sort u))
      let val := mkLambda `α .implicit (.sort u) (mkLambda `r .default (rel (.bvar 0)) (.bvar 1))
      let dv : DefinitionVal := { name := ``Quot, levelParams := [`u], type := ty, value := val, hints := .regular 0, safety := .safe }
      let env := rawAdd env (.defnInfo dv)
      let r := mkLambda `x .default (cnst ``Bool) (mkLambda `y .default (cnst ``Bool) (cnst ``True))
      let q := mkApp2 (cnst ``Quot [Level.one]) (cnst ``Bool) r
      let mk (a : Expr) := mkApp3 (cnst ``Quot.mk [Level.one]) (cnst ``Bool) r a
      let eqQ (a b : Expr) := mkApp3 (cnst ``Eq [Level.one]) q a b
      let β := mkLambda `q .default q (eqQ (.bvar 0) (mk (cnst ``Bool.true)))
      let h := mkLambda `a .default (cnst ``Bool) (mkAppN (cnst ``Quot.sound [Level.one])
        #[cnst ``Bool, r, .bvar 0, cnst ``Bool.true, cnst ``True.intro])
      let ind := mkAppN (cnst ``Quot.ind [Level.one]) #[cnst ``Bool, r, β, h]
      let symm := mkAppN (cnst ``Eq.symm [Level.one])
        #[q, cnst ``Bool.true, mk (cnst ``Bool.true), mkApp ind (cnst ``Bool.true)]
      let e := mkAppN (cnst ``Eq.trans [Level.one])
        #[q, cnst ``Bool.false, mk (cnst ``Bool.true), cnst ``Bool.true, mkApp ind (cnst ``Bool.false), symm]
      let motive := mkLambda `x .default q (mkLambda `h .default (eqQ (cnst ``Bool.false) (.bvar 0))
        (mkApp4 (cnst ``Bool.rec [Level.one]) (mkLambda `y .default (cnst ``Bool) (.sort Level.zero))
          (cnst ``True) (cnst ``False) (.bvar 1)))
      addChecked env (thm `quot_def_false (cnst ``False) (mkAppN (cnst ``Eq.rec [Level.zero, Level.one])
        #[q, cnst ``Bool.false, motive, cnst ``True.intro, cnst ``Bool.true, e])) false)
  | "forgedThmOverAx" => some (`ReplayForgedThmOverAx, #[`ReplayHonestPropAx], fun env =>
      -- A THEOREM `prop_ax_p : True := True.intro` over the imported AXIOM of that statement.
      -- Lean: `addDecl` refuses it (its duplicate-theorem skip needs a resident theorem), and
      -- `--fresh` accepts it (the import merges them: the theorem subsumes the axiom).
      return rawAdd env (.thmInfo { name := `prop_ax_p, levelParams := [], type := cnst ``True,
                                    value := cnst ``True.intro, all := [`prop_ax_p] }))
  | "forgedIndOverAx" => some (`ReplayForgedIndOverAx, #[`ReplayHonestIndAx], fun env => do
      -- `inductive ind_ax_t : Prop | mk` over the IMPORTED axiom `ind_ax_t : Prop` (Lean:
      -- already declared; `--fresh`: the import aborts), the block admitted by Lean's kernel
      -- in an environment WITHOUT the import and inserted unchecked, and a proof of `False`
      -- that goes through only if the module's inductive replaces the imported axiom:
      -- `ind_ax_not ind_ax_t.mk`. A checker that lets a later module's inductive displace an
      -- imported axiom admits it.
      let base ← importModules #[{ module := `Init.Prelude }] {} (trustLevel := 0)
      let ctor : Constructor := { name := `ind_ax_t.mk, type := cnst `ind_ax_t }
      let decl : Declaration :=
        .inductDecl [] 0 [{ name := `ind_ax_t, type := .sort Level.zero, ctors := [ctor] }] false
      let checked ← addChecked base decl true
      let mut env := env
      for n in decl.getNames do
        let some ci := checked.find? n | throw <| IO.userError s!"kernel generated no {n}"
        env := rawAdd env ci
      addChecked env (thm `forged_ind_false (cnst ``False)
        (mkApp (cnst `ind_ax_not) (cnst `ind_ax_t.mk))) false)
  | "forgedDeltaPropLargeElim" => some (`ReplayForgedDeltaPropLargeElim, #[`Init.Prelude], fun env => do
      -- The block of `honestDeltaProp` (`def fdp_prop : Type := Prop; inductive FDP : fdp_prop
      -- | t | f`), admitted by Lean's kernel, with `FDP.rec` then overwritten by a LARGE
      -- eliminator: universe parameter `u`, motive `FDP → Sort u`, the same minors and rules.
      -- That is the recursor a checker generates when it reads the syntactic head `fdp_prop`
      -- instead of the result level up to whnf, and with it `False` follows
      -- (`forged_dp_false`, through `FDP.rec.{1}` into `Bool`). Lean's replay regenerates
      -- `FDP.rec` (Prop-only) and refuses the stored one.
      let env ← addChecked env (defn `fdp_prop (.sort Level.one) (.sort Level.zero)) true
      let env ← forgeBlock env (deltaPropDecl `FDP `fdp_prop) fun
        | .recInfo rv => do
          let u := Level.param `u
          let lift : Expr → Expr := fun e => e.replace fun
            | .sort .zero => some (.sort u)
            | _ => none
          return .recInfo { rv with levelParams := [`u], type := lift rv.type,
                                    rules := rv.rules.map fun r => { r with rhs := lift r.rhs } }
        | ci => return ci
      addChecked env (thm `forged_dp_false (cnst ``False) (deltaFalse `FDP [Level.one])) false)
  | "forgedSortULargeElim" => some (`ReplayForgedSortULargeElim, #[`Init.Prelude], fun env => do
      -- The block of `honestSortU` over `FSU`, admitted by Lean's kernel, with `FSU.rec` then
      -- overwritten by a LARGE eliminator (universe parameters `[u_1, u]`, motive
      -- `FSU.{u} → Sort u_1`, the same minors and rules): the recursor a checker generates when
      -- it exempts a level that is merely "not provably zero" (`Sort u`) instead of one that is
      -- provably nonzero. At `u := 0`, `forged_su_false : False` follows through
      -- `FSU.rec.{1, 0}` into `Bool`.
      let env ← forgeBlock env (sortUDecl `FSU) fun
        | .recInfo rv => do
          let v := Level.param `u_1
          let lift : Expr → Expr := fun e => e.replace fun
            | .sort .zero => some (.sort v)
            | _ => none
          return .recInfo { rv with levelParams := `u_1 :: rv.levelParams, type := lift rv.type,
                                    rules := rv.rules.map fun r => { r with rhs := lift r.rhs } }
        | ci => return ci
      addChecked env (thm `forged_su_false (cnst ``False)
        (twoCtorFalse `FSU [Level.zero] [Level.one, Level.zero])) false)
  | "forgedAllGhost" => some (`ReplayForgedAllGhost, #[`Init.Prelude], fun env => do
      -- `FAG : Prop | mk : (FAG → False) → FAG` with stored `all := [FAG_ghost]`, a name no
      -- module declares, and no recursor. A replay that finds a type's block through its
      -- stored `all` never rebuilds `FAG`, so the kernel never sees the negative occurrence,
      -- and `forged_all_ghost_false : False` type-checks against the stored block. Lean's
      -- replay builds the `inductDecl` from `all` and fails.
      let env := negPropBlock env `FAG [`FAG_ghost]
      addChecked env (thm `forged_all_ghost_false (cnst ``False) (negPropFalse `FAG)) false)
  | "forgedAllOther" => some (`ReplayForgedAllOther, #[`Init.Prelude], fun env => do
      -- The same negative `FAO : Prop`, its stored `all := [FAH, FAO]` naming an HONEST
      -- enumeration `FAH` (checked by Lean's kernel, stored `all := [FAH]`) first. A replay that
      -- keys the block on `all.head` replays `FAH`'s own block `[FAH]` and never `FAO`.
      let env ← addChecked env (enumDecl `FAH [`FAH.a]) true
      let env := negPropBlock env `FAO [`FAH, `FAO]
      addChecked env (thm `forged_all_other_false (cnst ``False) (negPropFalse `FAO)) false)
  | "forgedIsRec" => some (`ReplayForgedIsRec, #[`Init.Prelude], fun env => do
      -- `inductive FIR : Type | mk : FIR → FIR`, admitted by Lean's kernel, then its
      -- `inductInfo` overwritten with `isRec := false`. A checker that reads the stored flag
      -- treats `FIR` as a non-recursive structure and gives it eta, so
      -- `forged_isrec_eta : ∀ x : FIR, FIR.mk x.1 = x := fun x => rfl` checks; Lean's replay
      -- regenerates `isRec := true` and refuses it (no eta for a recursive structure).
      let mkTy := mkForall `x .default (cnst `FIR) (cnst `FIR)
      let decl : Declaration := .inductDecl [] 0
        [{ name := `FIR, type := .sort Level.one, ctors := [{ name := `FIR.mk, type := mkTy }] }] false
      let env ← forgeBlock env decl fun
        | .inductInfo iv => return .inductInfo { iv with isRec := false }
        | ci => return ci
      let x := Expr.bvar 0
      let ty := mkForall `x .default (cnst `FIR)
        (mkApp3 (cnst ``Eq [Level.one]) (cnst `FIR) (mkApp (cnst `FIR.mk) (.proj `FIR 0 x)) x)
      let val := mkLambda `x .default (cnst `FIR) (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst `FIR) x)
      addChecked env (thm `forged_isrec_eta ty val) false)
  | "forgedMutualEta" => some (`ReplayForgedMutualEta, #[`Init.Prelude], fun env => do
      -- The honest mutual block `HMA`/`HMB` (checked; Lean stores `isRec := true` on both), and
      -- `forged_hma_eta : ∀ x y : HMA, x = y := fun x y => rfl`, which needs unit-like eta on
      -- `HMA`. Lean's kernel refuses it: `HMA` is not a non-recursive structure, because its
      -- block is recursive. A checker whose regenerated `HMA` reads `isRec` per type admits it.
      let env ← addChecked env mutualIsRecDecl true
      let hma := cnst `HMA
      let ty := mkForall `x .default hma (mkForall `y .default hma
        (mkApp3 (cnst ``Eq [Level.one]) hma (.bvar 1) (.bvar 0)))
      let val := mkLambda `x .default hma (mkLambda `y .default hma
        (mkApp2 (cnst ``Eq.refl [Level.one]) hma (.bvar 1)))
      addChecked env (thm `forged_hma_eta ty val) false)
  | "forgedQuotRedecl" => some (`ReplayForgedQuotRedecl, #[`Init.Core], fun env => do
      -- `axiom Quot.sound`, with its own statement, over `Init.Core`, which declares it: Lean's
      -- `addDecl` refuses it as already declared (`--fresh` merges the two axioms).
      let some ci := env.find? ``Quot.sound | throw <| IO.userError "no Quot.sound"
      return rawAdd env (.axiomInfo { name := ``Quot.sound, levelParams := ci.levelParams,
                                      type := ci.type, isUnsafe := false }))
  | "forgedQuotIndAxiom" => some (`ReplayForgedQuotIndAxiom, #[`Init.Prelude], fun env => do
      -- `Quot.ind` redeclared as an AXIOM with its canonical statement, over `Init.Prelude`,
      -- whose `init_quot` already holds it: `already declared` (`--fresh`: the import aborts).
      let some ci := env.find? ``Quot.ind | throw <| IO.userError "no Quot.ind"
      return rawAdd env (.axiomInfo { name := ``Quot.ind, levelParams := ci.levelParams,
                                      type := ci.type, isUnsafe := false }))
  | "forgedQuotIndThm" => some (`ReplayQuotIndThm, #[`Init.Prelude], fun env => do
      -- R142: `Quot.ind` restated as a THEOREM with its canonical statement and an unchecked
      -- value (`True.intro`), over `Init.Prelude`, whose `init_quot` holds it. Lean's import never
      -- merges a theorem with a quotient primitive, and no load may complete one, so a checker
      -- that drops the theorem as a restatement keeps the kernel's `Quot.ind` in its place.
      let some ci := env.find? ``Quot.ind | throw <| IO.userError "no Quot.ind"
      return rawAdd env (.thmInfo { name := ``Quot.ind, levelParams := ci.levelParams,
                                    type := ci.type, value := cnst ``True.intro,
                                    all := [``Quot.ind] }))
  | "honestIsPropStuck" => some (`ReplayIsPropStuck, #[`ReplayIsPropStuckBase], fun env => do
      -- #14807 (is_prop requires a Sort). The companion `ReplayIsPropStuckBase` holds the
      -- tactic-proved `Acc`-trick helpers (`run`/`run_eq`/`a`/`b`/`c`/`P`/`Q`/`gate`/`witness`/
      -- `observedProofsFalse`), so this family's import closure is only `Init.WF`. The tail is
      -- the stuck carrier: `Owner (h : P) : gate h` (one param `h`, field `bit : Bool`),
      -- `asProp (h : P) : Sort 0 := Owner h`, `proposition := asProp witness` where
      -- `witness : Q` (a STUCK `Owner witness` because `gate witness` never reduces to a
      -- `Sort`), `observe : proposition → Bool := fun p => p.1` (the data-field projection the
      -- pre-#14807 `is_prop` admitted on a stuck carrier), the two `Owner.mk` proofs, and
      -- `isprop_stuck_false : False`. Lean's kernel at v4.30.0-rc2 admits every one of these
      -- (`doCheck := true` for the carrier; the theorem is stored unchecked only to keep the
      -- family's shape uniform with the other `False` producers), and `leanchecker v4.30.0-rc2`
      -- ACCEPTS the written `.olean` (measured 2026-10-18). A release Clean admitted it too
      -- until its `is_prop` guard (README; intake row 14807). Under v4.33.1 the `observe` projection can no longer be minted. Each tail
      -- declaration is added through `addDeclCore`, because the elaborator refuses the stuck
      -- `Owner` carrier that only the vulnerable kernel admits.
      let owner := `IPK.Owner
      let p := cnst `IPK.P
      let bool := cnst ``Bool
      let gate := cnst `IPK.gate
      let abbrevDefn : Name → Expr → Expr → Declaration := fun n ty val =>
        .defnDecl { name := n, levelParams := [], type := ty, value := val,
                    hints := .abbrev, safety := .safe }
      let ownerType := mkForall `h .default p (mkApp gate (.bvar 0))
      let ctorType := mkForall `h .default p <|
        mkForall `bit .default bool (mkApp (cnst owner) (.bvar 1))
      let env ← addChecked env (.inductDecl [] 1 [{
        name := owner, type := ownerType,
        ctors := [{ name := .str owner "mk", type := ctorType }] }] false) true
      let env ← addChecked env (abbrevDefn `IPK.asProp (mkForall `h .default p (.sort Level.zero))
        (mkLambda `h .default p (mkApp (cnst owner) (.bvar 0)))) true
      let witness := cnst `IPK.witness
      let env ← addChecked env
        (abbrevDefn `IPK.proposition (.sort Level.zero) (mkApp (cnst `IPK.asProp) witness)) true
      let prop := cnst `IPK.proposition
      let env ← addChecked env (abbrevDefn `IPK.observe (mkForall `proof .default prop bool)
        (mkLambda `proof .default prop (mkProj owner 0 (.bvar 0)))) true
      let ctor := mkApp (cnst (.str owner "mk")) witness
      let env ← addChecked env (abbrevDefn `IPK.falseProof prop (mkApp ctor (cnst ``Bool.false))) true
      let env ← addChecked env (abbrevDefn `IPK.trueProof prop (mkApp ctor (cnst ``Bool.true))) true
      let fv := mkAppN (cnst `IPK.observedProofsFalse)
        #[prop, cnst `IPK.observe, cnst `IPK.falseProof, cnst `IPK.trueProof,
          reflBool (cnst ``Bool.false), reflBool (cnst ``Bool.true)]
      addChecked env (thm `isprop_stuck_false (cnst ``False) fv) false)
  | "forgedDepNestedRefl" => some (`ReplayForgedDepNestedRefl, #[`Init.Core], fun env => do
      -- The honest `SGS` block (`honestDepNested`), its `inductInfo` then overwritten with
      -- `isReflexive := true`, the value a checker that β-reduces the auxiliary types computes.
      -- Lean's replay installs the regenerated value and compares only constructors and
      -- recursors, so it never reads the stored flag; Clean's replay checks later declarations
      -- against the STORED value, so it compares the flag with the regenerated one (R112).
      let env ← forgeBlock env sgsDecl (extra := [`SGS.rec_1]) fun
        | .inductInfo iv => return .inductInfo { iv with isReflexive := true }
        | ci => return ci
      addChecked env (defn `forged_sgs_elim (mkForall `t .default (cnst `SGS) (cnst ``Nat))
        sgsElim) true)
  | "forgedPowCap" => some (`ReplayForgedPowCap, #[`Init.Prelude], fun env => do
      -- Lean's `reduce_pow` folds `Nat.pow` only up to the exponent `2^24`
      -- (`type_checker.cpp` `ReducePowMaxExp`, v4.30.0-rc2); above it the kernel δ-unfolds
      -- `Nat.pow` and fails with deep recursion, for every base, `0` and `1` included. CHECKED:
      -- `1^(2^24) = 1` (the boundary folds) and `2^10 = 1024`. FORGED: `1^(2^24+1) = 1` and
      -- `0^(2^24+1) = 0`, which pinned Lean refuses.
      let pow := fun (b e : Expr) => mkApp2 (cnst ``Nat.pow) b e
      let natTy := cnst ``Nat
      let eqThm := fun (n : Name) (b e r : Expr) (checked : Bool) (env : Environment) =>
        addChecked env (thm n (eqNat (pow b e) r) (reflAt natTy r)) checked
      let env ← eqThm `pow_one_at_cap (nat 1) (nat 16777216) (nat 1) true env
      let env ← eqThm `pow_small (nat 2) (nat 10) (nat 1024) true env
      let env ← eqThm `pow_one_over_cap (nat 1) (nat 16777217) (nat 1) false env
      eqThm `pow_zero_over_cap (nat 0) (nat 16777217) (nat 0) false env)
  | "forgedLevelJoin" => some (`ReplayForgedLevelJoin, #[`Init.Prelude], fun env => do
      -- Lean compares universe levels with `is_equivalent` (`level.cpp`): structural equality,
      -- or equality of `normalize`d forms, whose `max` keeps every argument but duplicates of one
      -- base. FORGED: `LJB` and `LJD` state a level that is semantically equal to the inferred
      -- one but NOT `is_equivalent` to it (an `imax` argument dominated only by the JOIN of the
      -- others); pinned Lean refuses both with `declaration type mismatch`. CHECKED controls:
      -- `LJA` and `LJC` (the level as inferred). `LJE` is the same class reached through
      -- universe INSTANTIATION (`LJK.{u, imax v u}`: Lean's `mk_max` keeps `max u (imax v u)`).
      let u := Level.param `u
      let v := Level.param `v
      let w := Level.param `w
      let l1 := mkLevelMax (.succ u) (mkLevelMax (.succ v) (mkLevelIMax (.succ v) u))
      let l2 := mkLevelMax (.succ u) (.succ v)
      let ax := fun (n : Name) (ls : List Name) (ty : Expr) =>
        Declaration.axiomDecl { name := n, levelParams := ls, type := ty, isUnsafe := false }
      let df := fun (n : Name) (ls : List Name) (ty val : Expr) =>
        Declaration.defnDecl { name := n, levelParams := ls, type := ty, value := val,
                               hints := .regular 0, safety := .safe }
      let lja := cnst `LJA [u, v]
      let env ← addChecked env (ax `LJA [`u, `v] (.sort l1)) true
      let env ← addChecked env (df `LJC [`u, `v] (.sort l1) lja) true
      let env ← addChecked env (df `LJB [`u, `v] (.sort l2) lja) false
      let ld := mkLevelMax (mkLevelMax v (mkLevelIMax v w)) (.succ w)
      let env ← addChecked env
        (df `LJD [`v, `w] (.sort (.succ (mkLevelMax v (.succ w)))) (.sort ld)) false
      let a := Level.param `a
      let b := Level.param `b
      let env ← addChecked env (ax `LJK [`a, `b] (.sort (mkLevelMax a b))) true
      let ljk := cnst `LJK [u, mkLevelIMax v u]
      let env ← addChecked env (df `LJF [`u, `v] (.sort (mkLevelMax u (mkLevelIMax v u))) ljk) true
      addChecked env (df `LJE [`u, `v] (.sort (mkLevelIMax v u)) ljk) false)
  | "honestLevelAssoc" => some (`ReplayHonestLevelAssoc, #[`Init.Prelude], fun env => do
      -- CHECKED (pinned Lean admits all seven; the 2026-10-24 review's K3). Each states a level
      -- `is_equivalent` to the inferred one that Clean's simplifying `Level::max`/`Level::imax`
      -- built differently before R150: the `.olean` decoder rewrote B1's declared level to
      -- `max a (b+1)` and Pi inference built P1's as `max a (b+1)`, while their partners kept
      -- all three arguments. A level check by Lean's `is_equivalent` on those levels refused B1
      -- and P1 (R141); LB was refused in every theory (the decoder kept `max u (imax u v)` on
      -- one side and built `max u v` on the other). R150's verbatim decoding admits all seven.
      let a := Level.param `a
      let b := Level.param `b
      let env ← addChecked env (axL `X [`a, `b] (.sort (mkLevelIMax a b))) true
      let env ← addChecked env (axL `Y [`a, `b] (.sort (mkLevelMax a (.succ b)))) true
      let env ← addChecked env (dfL `P1 [`a, `b]
        (.sort (mkLevelMax (mkLevelMax (mkLevelIMax a b) a) (.succ b)))
        (mkForall `x .default (cnst `X [a, b]) (cnst `Y [a, b]))) true
      let env ← addChecked env
        (axL `A1 [`a, `b] (.sort (mkLevelMax a (mkLevelMax (.succ b) (mkLevelIMax a b))))) true
      let env ← addChecked env (dfL `B1 [`a, `b]
        (.sort (mkLevelMax (mkLevelMax a (.succ b)) (mkLevelIMax a b))) (cnst `A1 [a, b])) true
      let u := Level.param `u
      let v := Level.param `v
      let env ← addChecked env
        (axL `LA [`u, `v] (.sort (mkLevelMax u (mkLevelMax v (mkLevelIMax u v))))) true
      addChecked env (dfL `LB [`u, `v] (.sort (mkLevelMax (mkLevelMax u v) (mkLevelIMax u v)))
        (cnst `LA [u, v])) true)
  | "forgedLevelAssoc" => some (`ReplayForgedLevelAssoc, #[`Init.Prelude], fun env => do
      -- FORGED (review K4): `LJB2` is `LJB` with `LJA`'s level re-associated, and `LJS2` states
      -- `succ (max u (v+1))` for `succ (imax u (v+1))`; pinned Lean refuses both
      -- (`declaration type mismatch`: its `normalize` does not depend on association and keeps
      -- the `imax` under an offset). Before R150 Clean's decoder built each side as the other.
      let u := Level.param `u
      let v := Level.param `v
      let la2 := mkLevelMax (mkLevelMax (.succ u) (.succ v)) (mkLevelIMax (.succ v) u)
      let env ← addChecked env (axL `LJA2 [`u, `v] (.sort la2)) true
      let env ← addChecked env
        (dfL `LJB2 [`u, `v] (.sort (mkLevelMax (.succ u) (.succ v))) (cnst `LJA2 [u, v])) false
      let env ← addChecked env (axL `LJS1 [`u, `v] (.sort (.succ (mkLevelIMax u (.succ v))))) true
      addChecked env
        (dfL `LJS2 [`u, `v] (.sort (.succ (mkLevelMax u (.succ v)))) (cnst `LJS1 [u, v])) false)
  | "forgedMutualLevel" => some (`ReplayForgedMutualLevel, #[`Init.Prelude], fun env => do
      -- The CHECKED mutual block `MA`/`MB`, both at `Sort (max (u+1) (v+1))`, with MB's stored
      -- `inductInfo` type then overwritten with `Sort (max (u+1) (max (v+1) (imax (v+1) u)))`,
      -- equal at every assignment but not `is_equivalent`: Lean's replay rebuilds the block
      -- from the stored types and refuses it (`mutually inductive types must live in the same
      -- universe`; review K5). Before R150 Clean's admission compared the two by `is_geq` both
      -- ways and admitted it.
      let u := Level.param `u
      let v := Level.param `v
      let ma := mkLevelMax (.succ u) (.succ v)
      let mb := mkLevelMax (.succ u) (mkLevelMax (.succ v) (mkLevelIMax (.succ v) u))
      let decl : Declaration := .inductDecl [`u, `v] 0 [
        { name := `MA, type := .sort ma, ctors := [{ name := `MA.a, type := cnst `MA [u, v] }] },
        { name := `MB, type := .sort ma, ctors := [{ name := `MB.b, type := cnst `MB [u, v] }] }]
        false
      forgeBlock env decl fun
        | .inductInfo iv =>
          return .inductInfo (if iv.name == `MB then { iv with type := .sort mb } else iv)
        | ci => return ci)
  | "forgedPowCapOuter" => some (`ReplayForgedPowCapOuter, #[`Init.Prelude], fun env => do
      -- R140's open half (review K1). FORGED: an outer `Nat.mul`/`add`/`sub`/`pow` over
      -- `1^(2^24+1)` (and `2^(2^24+1)`), whose δ-reduction never inspects that operand. Lean's
      -- `reduce_bin_nat_op`/`reduce_pow` whnf the operand first, which recurses past the cap:
      -- pinned Lean refuses each (`deep recursion detected`). CHECKED: the same at the cap.
      let pow := fun (b e : Expr) => mkApp2 (cnst ``Nat.pow) b e
      let bin := fun (f : Name) (a b : Expr) => mkApp2 (cnst f) a b
      let natTy := cnst ``Nat
      let eqThm := fun (n : Name) (lhs r : Expr) (checked : Bool) (env : Environment) =>
        addChecked env (thm n (eqNat lhs r) (reflAt natTy r)) checked
      let over := pow (nat 1) (nat 16777217)
      let atCap := pow (nat 1) (nat 16777216)
      let env ← eqThm `mul_at_zero (bin ``Nat.mul atCap (nat 0)) (nat 0) true env
      let env ← eqThm `add_at_zero (bin ``Nat.add atCap (nat 0)) atCap true env
      let env ← eqThm `mul_over_zero (bin ``Nat.mul over (nat 0)) (nat 0) false env
      let env ← eqThm `add_over_zero (bin ``Nat.add over (nat 0)) over false env
      let env ← eqThm `sub_over_zero (bin ``Nat.sub over (nat 0)) over false env
      let env ← eqThm `pow_over_exp0 (pow over (nat 0)) (nat 1) false env
      eqThm `mul_over2_zero (bin ``Nat.mul (pow (nat 2) (nat 16777217)) (nat 0)) (nat 0) false env)
  | "forgedShlCap" => some (`ReplayForgedShlCap, #[`Init.Data.Nat.Bitwise.Basic], fun env => do
      -- Review K2. Lean's `reduce_nat` computes `Nat.shiftLeft` with `lean_nat_shiftl`, which
      -- aborts the process ("Nat.shiftl exponent is too big") for a nonzero base and a shift
      -- above `2^32 - 1`. FORGED: `1 <<< 2^32` and `1 <<< 2^64` stated equal to the same shift
      -- spelled `(2^k - 1) + 1`; pinned Lean panics on each (exit 1). CHECKED: a zero base at
      -- `2^32` (Lean returns 0) and the same congruence at shift 2000.
      let shl := fun (a b : Expr) => mkApp2 (cnst ``Nat.shiftLeft) a b
      let add := fun (a b : Expr) => mkApp2 (cnst ``Nat.add) a b
      let natTy := cnst ``Nat
      let cong := fun (n : Name) (k : Nat) (checked : Bool) (env : Environment) =>
        addChecked env (thm n (eqNat (shl (nat 1) (nat k)) (shl (nat 1) (add (nat (k - 1)) (nat 1))))
          (reflAt natTy (shl (nat 1) (nat k)))) checked
      let env ← addChecked env (thm `shl_zero_base (eqNat (shl (nat 0) (nat 4294967296)) (nat 0))
        (reflAt natTy (nat 0))) true
      let env ← cong `shl_cong_small 2000 true env
      let env ← cong `shl_cong 4294967296 false env
      cong `shl_cong64 18446744073709551616 false env)
  | _ => none

/-- CHECKED: `inductive ty : Type | mk : Nat → ty` (Lean's kernel generates `ty.rec`), and
`theorem use : ty.mk Nat.zero = ty.mk Nat.zero := Eq.refl _`, which names `ty` and `ty.mk`. -/
def natBoxAndUse (env : Environment) (ty use : Name) : IO Environment := do
  let mk := Name.str ty "mk"
  let ctor : Constructor := { name := mk, type := mkForall `n .default (cnst ``Nat) (cnst ty) }
  let ind : InductiveType := { name := ty, type := .sort Level.one, ctors := [ctor] }
  let env ← addChecked env (.inductDecl [] 0 [ind] false) true
  let v := mkApp (cnst mk) (cnst ``Nat.zero)
  addChecked env (thm use (mkApp3 (cnst ``Eq [Level.one]) (cnst ty) v v)
    (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ty) v)) true

/-- Families written PART BY PART as a `module`-system artifact, the way `writeModule` splits a
`module`: `.olean` and `.olean.server` hold the public declarations, and `.olean.private` holds
every declaration, the `private` ones (`isPrivateName`) included. A consumer that is not itself a
`module` (`leanchecker`, and every file Clean checks) reads such an artifact through its private
part, so its private declarations are the module's own declarations too, replayed like the rest.
A family's `serverOnly` names are written to `.olean.server` ALONE (`writeModule` never does
that: every name of its `.olean` and `.olean.server` is a name of its `.olean.private`), and a
family that `partedPlain` names is written without the module system (`isModule` false), whose
`.olean` alone `lean` reads. -/
def parted : String → Option (Name × Array Name × (Environment → IO Environment))
  | "forgedPriv" => some (`ReplayForgedPriv, #[`Init.Prelude], fun env => do
      -- A PRIVATE `False := itself`, only in `.olean.private`, and a public theorem that uses it.
      let p := mkPrivateName env `priv_self
      let env ← addChecked env (thm p (cnst ``False) (cnst p)) false
      addChecked env (thm `priv_user (cnst ``False) (cnst p)) false)
  | "forgedPrivBad" => some (`ReplayForgedPrivBad, #[`Init.Prelude], fun env => do
      -- A PRIVATE ill-typed `False := True.intro` (no self-reference), and a public user.
      let p := mkPrivateName env `priv_bad
      let env ← addChecked env (thm p (cnst ``False) (cnst ``True.intro)) false
      addChecked env (thm `priv_bad_user (cnst ``False) (cnst p)) false)
  | "honestPriv" => some (`ReplayHonestPriv, #[`Init.Prelude], fun env => do
      -- CHECKED: a private theorem and a public theorem that uses it.
      let p := mkPrivateName env `priv_ok
      let env ← addChecked env (thm p (cnst ``True) (cnst ``True.intro)) true
      addChecked env (thm `priv_ok_user (cnst ``True) (cnst p)) true)
  | "misplacedServer" => some (`ReplayMisplacedServer, #[`Init.Prelude], fun env =>
      -- CHECKED `SO | mk : Nat → SO` and `so_use`; `serverOnly` keeps `SO`, `SO.mk` and
      -- `SO.rec` out of `.olean` and `.olean.private`, so for `lean` they do not exist.
      natBoxAndUse env `SO `so_use)
  | "misplacedServerPlain" => some (`ReplayMisplacedServerPlain, #[`Init.Prelude], fun env =>
      -- The same, without the module system: `lean` reads the `.olean` alone.
      natBoxAndUse env `SOP `sop_use)
  | "misplacedOlean" => some (`ReplayMisplacedOlean, #[`Init.Prelude], fun env =>
      -- CHECKED `SX | mk : Nat → SX` and `sx_use`; `privateHidden` keeps `SX`, `SX.mk` and
      -- `SX.rec` out of `.olean.private` ONLY, so they are in `.olean` and `.olean.server`.
      natBoxAndUse env `SX `sx_use)
  | "honestServerParts" => some (`ReplayHonestServerParts, #[`Init.Prelude], fun env => do
      -- CHECKED: the same block and use, written as `writeModule` writes a `module` (every part
      -- holds them), and a private theorem over the block.
      let env ← natBoxAndUse env `SH `sh_use
      let p := mkPrivateName env `sh_priv
      let v := mkApp (cnst `SH.mk) (cnst ``Nat.zero)
      addChecked env (thm p (mkApp3 (cnst ``Eq [Level.one]) (cnst `SH) v v)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst `SH) v)) true)
  | _ => none

/-- The names of a `parted` family written to `.olean.server` alone. -/
def serverOnly : String → Name → Bool
  | "misplacedServer" => fun n => n == `SO || n.getPrefix == `SO
  | "misplacedServerPlain" => fun n => n == `SOP || n.getPrefix == `SOP
  | _ => fun _ => false

/-- The names of a `parted` family left out of `.olean.private` ALONE (they stay in `.olean`
and `.olean.server`): `writeModule` never does that either. -/
def privateHidden : String → Name → Bool
  | "misplacedOlean" => fun n => n == `SX || n.getPrefix == `SX
  | _ => fun _ => false

/-- The `parted` families written without the module system. -/
def partedPlain : String → Bool
  | "misplacedServerPlain" => true
  | _ => false

/-- The import list a `special` family's `.olean` header states, when it is not the list the
family was built over. -/
def headerImports : String → Option (Array Name)
  | "forgedOpaqueUse" => some #[`ReplayHonestOpaqueAx, `ReplayForgedOpaqueDef]
  | _ => none

/-- `def n : Nat := v`, CHECKED. -/
def natDef (n : Name) (v : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := cnst ``Nat, value := v,
              hints := .regular 0, safety := .safe }

/-- `n = v := Eq.refl v` over `Nat`, as a theorem. -/
def natEqThm (t n : Name) (v : Expr) : Declaration :=
  thm t (mkApp3 (cnst ``Eq [Level.one]) (cnst ``Nat) (cnst n) v)
    (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ``Nat) v)

/-- `full` with the record of `n` replaced by `def n : Nat := v`. -/
def swapNatDef (full : ModuleData) (n : Name) (v : Expr) : ModuleData := { full with
  constants := full.constants.map fun c => if c.name == n then defnInfo n (cnst ``Nat) v else c }

/-- `full` restricted to the names `p` keeps. -/
def keepNames (full : ModuleData) (p : Name → Bool) : ModuleData := { full with
  constants := full.constants.filter (p ·.name)
  constNames := full.constNames.filter p }

/-- Write a `module`'s three parts, and the `.ir` part an importer of a `module` reads. -/
def writeThreeParts (mod : Name) (out : System.FilePath) (exported server priv : ModuleData) :
    IO Unit := do
  saveModuleDataParts mod #[
    (OLeanLevel.exported.adjustFileName out, exported),
    (OLeanLevel.server.adjustFileName out, server),
    (OLeanLevel.private.adjustFileName out, priv)]
  saveModuleData (out.withExtension "ir") (mod ++ `ir)
    { priv with entries := #[], constants := #[], constNames := #[], extraConstNames := priv.constNames }

/-- A `module` environment over `imps`, named `mod`. -/
def moduleEnv (mod : Name) (imps : Array Name) : IO Environment := do
  let env ← importModules (imps.map fun m => { module := m }) {} (trustLevel := 0) (level := .exported)
  return env.setMainModule mod

/-- A non-`module` environment over `imps`, named `mod`. -/
def plainEnv (mod : Name) (imps : Array Name) : IO Environment := do
  let env ← importModules (imps.map fun m => { module := m }) {} (trustLevel := 0)
  return env.setMainModule mod

/-- `c` as `writeModule` exports a theorem of a `module` (`Lean.addDecl`, `AddDecl.lean`:
`exportedInfo? := some <| .axiomInfo { thm with isUnsafe := false }`): an axiom with the
declaration's name, universe parameters and type (the same type object). -/
def stubInfo (c : ConstantInfo) : ConstantInfo :=
  .axiomInfo { name := c.name, levelParams := c.levelParams, type := c.type, isUnsafe := false }

/-- `full` with each of `ns` replaced by its value-free stub. -/
def withStubs (full : ModuleData) (ns : List Name) : ModuleData := { full with
  constants := full.constants.map fun c => if ns.contains c.name then stubInfo c else c }

/-- `1 = 1` over `Nat`, and `Eq.refl 2`, a proof of `2 = 2` that Lean's kernel refuses for it. -/
def oneEqOne : Expr := eqNat one one
def reflTwo : Expr := reflAt (cnst ``Nat) (mkApp (cnst ``Nat.succ) one)

/-- Write `env`'s own constants as a non-`module` `.olean` with no extension entries: computing
the entries infers each constant's type, which may name a constant the environment does not hold
(`writeModule` panics in `symbolFrequencyExt`). The constants are what `leanchecker` replays. -/
def writeConstantsOnly (env : Environment) (out : System.FilePath) : IO Unit := do
  let constants := env.toKernelEnv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
  saveModuleData out env.mainModule { env.header with
    constNames := constants.map (·.name), constants, entries := #[], extraConstNames := #[] }

/-- A non-`module` user of `dep`: `use : ty.mk 0 = ty.mk 0`, unchecked (`lean`'s `dep` lacks `ty`). -/
def boxUser (mod dep ty use : Name) (out : System.FilePath) : IO Unit := do
  let env ← plainEnv mod #[dep]
  let v := mkApp (cnst (.str ty "mk")) (cnst ``Nat.zero)
  let env ← addChecked env (thm use (mkApp3 (cnst ``Eq [Level.one]) (cnst ty) v v)
    (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst ty) v)) false
  writeConstantsOnly env out

/-- Families whose parts disagree with each other, or whose misplaced family sits in a
DEPENDENCY: each writes its parts itself (`writeModule` writes neither shape). Every checked
declaration is checked by Lean's kernel; a user is stored unchecked only where its dependency, as
`lean` reads it, does not support it. -/
def bespoke (out : System.FilePath) : String → Option (IO Unit)
  | "partsValDis" => some do
      -- `.olean`/`.olean.server` say `pv_X := 1`, `.olean.private` says `pv_X := 0`; the CHECKED
      -- `pv_u : pv_X = 1` (checked against `pv_X := 1`) is in every part.
      let env ← moduleEnv `ReplayPartsValDis #[`Init.Prelude]
      let env ← addChecked env (natDef `pv_X one) true
      let env ← addChecked env (natEqThm `pv_u `pv_X one) true
      let full ← mkModuleData env .private
      writeThreeParts env.mainModule out full full (swapNatDef full `pv_X (cnst ``Nat.zero))
  | "partsValDep" => some do
      -- The dependency form: `pd_X := 1` in `.olean`/`.olean.server`, `pd_X := 0` in the private part.
      let env ← moduleEnv `ReplayPartsValDep #[`Init.Prelude]
      let env ← addChecked env (natDef `pd_X one) true
      let full ← mkModuleData env .private
      writeThreeParts env.mainModule out full full (swapNatDef full `pd_X (cnst ``Nat.zero))
  | "partsValDepUser" => some do
      -- A non-`module` user: `pd_t : pd_X = 1`, unchecked (`lean` reads `pd_X := 0`).
      let env ← plainEnv `ReplayPartsValDepUser #[`ReplayPartsValDep]
      let env ← addChecked env (natEqThm `pd_t `pd_X one) false
      writeModule env out
  | "partsImpE" => some do
      let env ← moduleEnv `ReplayPartsImpE #[`Init.Prelude]
      let env ← addChecked env (natDef `pi_Y (cnst ``Nat.zero)) true
      let full ← mkModuleData env .private
      writeThreeParts env.mainModule out full full full
  | "partsImpF" => some do
      let env ← moduleEnv `ReplayPartsImpF #[`Init.Prelude]
      let env ← addChecked env (natDef `pi_Y one) true
      let full ← mkModuleData env .private
      writeThreeParts env.mainModule out full full full
  | "partsImpD" => some do
      -- `.olean`/`.olean.server` import `ReplayPartsImpF` (`pi_Y := 1`); `.olean.private` imports
      -- `ReplayPartsImpE` (`pi_Y := 0`), the list `lean` follows.
      let env ← moduleEnv `ReplayPartsImpD #[`ReplayPartsImpE]
      let env ← addChecked env (natDef `pi_dz (cnst ``Nat.zero)) true
      let full ← mkModuleData env .private
      let pub : ModuleData := { full with imports := #[{ module := `ReplayPartsImpF }] }
      writeThreeParts env.mainModule out pub pub full
  | "partsImpT" => some do
      -- A non-`module` user: `pi_t : pi_Y = 1`, unchecked (`lean` reaches `ReplayPartsImpE`).
      let env ← plainEnv `ReplayPartsImpT #[`ReplayPartsImpD]
      let env ← addChecked env (natEqThm `pi_t `pi_Y one) false
      writeModule env out
  | "misplacedDep" => some do
      -- A `module` dependency whose CHECKED `MD | mk : Nat → MD` is in `.olean`/`.olean.server`
      -- only; its `.olean.private` holds `md_ok` alone.
      let env ← moduleEnv `ReplayMisplacedDep #[`Init.Prelude]
      let env ← natBoxAndUse env `MD `md_self
      let env ← addChecked env (thm `md_ok (cnst ``True) (cnst ``True.intro)) true
      let full ← mkModuleData env .private
      let inMD (n : Name) := n == `MD || n.getPrefix == `MD || n == `md_self
      writeThreeParts env.mainModule out full full (keepNames full (!inMD ·))
  | "misplacedDepUser" => some do
      -- A non-`module` user: `md_use : MD.mk 0 = MD.mk 0`, unchecked (`lean`'s dependency has no `MD`).
      let env ← plainEnv `ReplayMisplacedDepUser #[`ReplayMisplacedDep]
      let v := mkApp (cnst `MD.mk) (cnst ``Nat.zero)
      let env ← addChecked env (thm `md_use (mkApp3 (cnst ``Eq [Level.one]) (cnst `MD) v v)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst `MD) v)) false
      -- Written without extension entries: computing them infers `md_use`'s type, which names
      -- `MD`, a constant this environment does not hold (`writeModule` panics in
      -- `symbolFrequencyExt`). The module's constants are what `leanchecker` replays.
      let constants := env.toKernelEnv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
      saveModuleData out env.mainModule { env.header with
        constNames := constants.map (·.name), constants, entries := #[], extraConstNames := #[] }
  | "honestDep" => some do
      -- Control: the same dependency with `MD` in every part.
      let env ← moduleEnv `ReplayHonestDep #[`Init.Prelude]
      let env ← natBoxAndUse env `MD `md_self
      let env ← addChecked env (thm `md_ok (cnst ``True) (cnst ``True.intro)) true
      let full ← mkModuleData env .private
      writeThreeParts env.mainModule out full full full
  | "honestDepUser" => some do
      -- Control user, CHECKED.
      let env ← plainEnv `ReplayHonestDepUser #[`ReplayHonestDep]
      let v := mkApp (cnst `MD.mk) (cnst ``Nat.zero)
      let env ← addChecked env (thm `md_use (mkApp3 (cnst ``Eq [Level.one]) (cnst `MD) v v)
        (mkApp2 (cnst ``Eq.refl [Level.one]) (cnst `MD) v)) true
      writeModule env out
  -- R131. Value-free stubs that a later part completes, in `writeModule`'s own layout for a
  -- `module` and in the non-`module` shape no Lean writer produces.
  | "stubRefused" => some do
      -- A `module` in `writeModule`'s public-theorem layout: `.olean` and `.olean.server` hold the
      -- stubs `axiom sr_t : 1 = 1` and `axiom sr_u : 1 = 1`; `.olean.private` holds
      -- `theorem sr_t : 1 = 1 := Eq.refl 2` (unchecked: Lean's kernel refuses the value, a type
      -- mismatch) and the CHECKED `theorem sr_u : 1 = 1 := sr_t`.
      let env ← moduleEnv `ReplayStubRefused #[`Init.Prelude]
      let env ← addChecked env (thm `sr_t oneEqOne reflTwo) false
      let env ← addChecked env (thm `sr_u oneEqOne (cnst `sr_t)) true
      let full ← mkModuleData env .private
      let pub := withStubs full [`sr_t, `sr_u]
      writeThreeParts env.mainModule out pub pub full
  | "stubHonest" => some do
      -- Control: the same layout over the CHECKED `sh_t : 1 = 1 := Eq.refl 1` and `sh_u := sh_t`.
      let env ← moduleEnv `ReplayStubHonest #[`Init.Prelude]
      let env ← addChecked env (thm `sh_t oneEqOne (reflAt (cnst ``Nat) one)) true
      let env ← addChecked env (thm `sh_u oneEqOne (cnst `sh_t)) true
      let full ← mkModuleData env .private
      let pub := withStubs full [`sh_t, `sh_u]
      writeThreeParts env.mainModule out pub pub full
  | "stubRefusedDep" => some do
      -- The dependency form: the stub `srd_t : 1 = 1`, its private value `Eq.refl 2` unchecked.
      let env ← moduleEnv `ReplayStubRefusedDep #[`Init.Prelude]
      let env ← addChecked env (thm `srd_t oneEqOne reflTwo) false
      let full ← mkModuleData env .private
      let pub := withStubs full [`srd_t]
      writeThreeParts env.mainModule out pub pub full
  | "stubRefusedDepUser" => some do
      -- A non-`module` user, CHECKED over the dependency as `lean` reads it: `srd_use := srd_t`.
      let env ← plainEnv `ReplayStubRefusedDepUser #[`ReplayStubRefusedDep]
      let env ← addChecked env (thm `srd_use oneEqOne (cnst `srd_t)) true
      writeModule env out
  | "stubPlainDep" => some do
      -- Not a `module`: `.olean` holds the stub `axiom spd_X : Nat`, `.olean.server` the CHECKED
      -- `def spd_X : Nat := 1`. Every importer reads a non-`module` artifact's `.olean`.
      let env ← plainEnv `ReplayStubPlainDep #[`Init.Prelude]
      let env ← addChecked env (natDef `spd_X one) true
      let full ← mkModuleData env
      saveModuleDataParts env.mainModule #[
        (OLeanLevel.exported.adjustFileName out, withStubs full [`spd_X]),
        (OLeanLevel.server.adjustFileName out, full)]
  | "stubPlainDepUser" => some do
      -- `spd_t : spd_X = 1 := Eq.refl 1`, unchecked (`lean` reads `spd_X` as an axiom).
      let env ← plainEnv `ReplayStubPlainDepUser #[`ReplayStubPlainDep]
      let env ← addChecked env (natEqThm `spd_t `spd_X one) false
      writeModule env out
  | "stubPlainPrivDep" => some do
      -- The same with the definition in a `.olean.private` and no `.olean.server`: a part no
      -- Lean reader opens (`findOLeanParts` looks for it only beside a server part).
      let env ← plainEnv `ReplayStubPlainPrivDep #[`Init.Prelude]
      let env ← addChecked env (natDef `sppd_X one) true
      let full ← mkModuleData env
      saveModuleDataParts env.mainModule #[
        (OLeanLevel.exported.adjustFileName out, withStubs full [`sppd_X]),
        (OLeanLevel.private.adjustFileName out, full)]
  | "stubPlainPrivDepUser" => some do
      let env ← plainEnv `ReplayStubPlainPrivDepUser #[`ReplayStubPlainPrivDep]
      let env ← addChecked env (natEqThm `sppd_t `sppd_X one) false
      writeModule env out
  | "stubPlainHonest" => some do
      -- Control: not a `module`, the CHECKED `def sph_X : Nat := 1` in `.olean` and `.olean.server`.
      let env ← plainEnv `ReplayStubPlainHonest #[`Init.Prelude]
      let env ← addChecked env (natDef `sph_X one) true
      let full ← mkModuleData env
      saveModuleDataParts env.mainModule #[
        (OLeanLevel.exported.adjustFileName out, full),
        (OLeanLevel.server.adjustFileName out, full)]
  | "stubPlainHonestUser" => some do
      let env ← plainEnv `ReplayStubPlainHonestUser #[`ReplayStubPlainHonest]
      let env ← addChecked env (natEqThm `sph_t `sph_X one) true
      writeModule env out
  | "stubPlainTgt" => some do
      -- Not a `module`: `.olean` holds the stub `axiom spt_f : 1 = 1` and the CHECKED
      -- `theorem spt_u : 1 = 1 := spt_f`; `.olean.server` holds `theorem spt_f : 1 = 1 :=
      -- Eq.refl 2` (unchecked: a type mismatch) and the same `spt_u`.
      let env ← plainEnv `ReplayStubPlainTgt #[`Init.Prelude]
      let env ← addChecked env (thm `spt_f oneEqOne reflTwo) false
      let env ← addChecked env (thm `spt_u oneEqOne (cnst `spt_f)) true
      let full ← mkModuleData env
      saveModuleDataParts env.mainModule #[
        (OLeanLevel.exported.adjustFileName out, withStubs full [`spt_f]),
        (OLeanLevel.server.adjustFileName out, full)]
  | "misplacedOleanOnlyDep" => some do
      -- A `module` whose CHECKED `MO | mk : Nat → MO` (and `mo_self`) is in its `.olean` ALONE;
      -- `.olean.server` and `.olean.private` hold `mo_ok` only.
      let env ← moduleEnv `ReplayMisplacedOleanOnlyDep #[`Init.Prelude]
      let env ← natBoxAndUse env `MO `mo_self
      let env ← addChecked env (thm `mo_ok (cnst ``True) (cnst ``True.intro)) true
      let full ← mkModuleData env .private
      let inMO (n : Name) := n == `MO || n.getPrefix == `MO || n == `mo_self
      let rest := keepNames full (!inMO ·)
      writeThreeParts env.mainModule out full rest rest
  | "misplacedOleanOnlyDepUser" => some do
      boxUser `ReplayMisplacedOleanOnlyDepUser `ReplayMisplacedOleanOnlyDep `MO `mo_use out
  | "misplacedPrivPlainDep" => some do
      -- Not a `module`: the CHECKED `MP | mk : Nat → MP` (and `mp_self`) is in its `.olean.private`
      -- ALONE; `.olean` and `.olean.server` hold `mp_ok` only.
      let env ← plainEnv `ReplayMisplacedPrivPlainDep #[`Init.Prelude]
      let env ← natBoxAndUse env `MP `mp_self
      let env ← addChecked env (thm `mp_ok (cnst ``True) (cnst ``True.intro)) true
      let full ← mkModuleData env
      let inMP (n : Name) := n == `MP || n.getPrefix == `MP || n == `mp_self
      let rest := keepNames full (!inMP ·)
      saveModuleDataParts env.mainModule #[
        (OLeanLevel.exported.adjustFileName out, rest),
        (OLeanLevel.server.adjustFileName out, rest),
        (OLeanLevel.private.adjustFileName out, full)]
  | "misplacedPrivPlainDepUser" => some do
      boxUser `ReplayMisplacedPrivPlainDepUser `ReplayMisplacedPrivPlainDep `MP `mp_use out
  -- R142. A declaration the authoritative part states with a value that the loader never makes
  -- resident with it: a private value Clean's converter cannot read, and a stub whose name an
  -- import already holds as an axiom.
  | "stubMv" => some do
      -- `writeModule`'s public-theorem layout over `theorem smv_f : 1 = 1 := ?m` (a metavariable,
      -- unchecked) and the CHECKED `theorem smv_u : 1 = 1 := smv_f`.
      let env ← moduleEnv `ReplayStubMv #[`Init.Prelude]
      let env ← addChecked env (thm `smv_f oneEqOne (.mvar ⟨`m⟩)) false
      let env ← addChecked env (thm `smv_u oneEqOne (cnst `smv_f)) true
      let full ← mkModuleData env .private
      let pub := withStubs full [`smv_f, `smv_u]
      writeThreeParts env.mainModule out pub pub full
  | "stubFv" => some do
      -- The same over `theorem sfv_f : 1 = 1 := x` (a free variable, unchecked).
      let env ← moduleEnv `ReplayStubFv #[`Init.Prelude]
      let env ← addChecked env (thm `sfv_f oneEqOne (.fvar ⟨`x⟩)) false
      let env ← addChecked env (thm `sfv_u oneEqOne (cnst `sfv_f)) true
      let full ← mkModuleData env .private
      let pub := withStubs full [`sfv_f, `sfv_u]
      writeThreeParts env.mainModule out pub pub full
  | "shadowAx" => some do
      -- A `module` with the CHECKED `axiom sha_n : 1 = 1`.
      let env ← moduleEnv `ReplayShadowAx #[`Init.Prelude]
      let env ← addChecked env (axm `sha_n oneEqOne) true
      writeModule env out
  | "shadowStub" => some do
      -- A `module` over `ReplayShadowAx` in the stub layout: `.olean`/`.olean.server` stub
      -- `sha_n` (the import's name and type) and `sh_u`; `.olean.private` holds
      -- `theorem sha_n : 1 = 1 := Eq.refl 2` (inserted unchecked over the import's axiom) and the
      -- CHECKED `theorem sh_u : 1 = 1 := sha_n`.
      let env ← moduleEnv `ReplayShadowStub #[`ReplayShadowAx]
      let env := rawAdd env (.thmInfo { name := `sha_n, levelParams := [], type := oneEqOne,
                                        value := reflTwo, all := [`sha_n] })
      let env ← addChecked env (thm `sh_u oneEqOne (cnst `sha_n)) true
      let constants := env.toKernelEnv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
      let full : ModuleData := { env.header with
        constNames := constants.map (·.name), constants, entries := #[], extraConstNames := #[] }
      let full := { full with isModule := true }
      writeThreeParts env.mainModule out (withStubs full [`sha_n, `sh_u])
        (withStubs full [`sha_n, `sh_u]) full
  | "shadowStubUser" => some do
      -- A non-`module` user, CHECKED over its import as `lean` reads it: `shu_t : 1 = 1 := sh_u`.
      let env ← plainEnv `ReplayShadowStubUser #[`ReplayShadowStub]
      let env ← addChecked env (thm `shu_t oneEqOne (cnst `sh_u)) true
      writeConstantsOnly env out
  | "shadowThm" => some do
      -- Not a `module`: `theorem sha_n : 1 = 1 := Eq.refl 2` inserted unchecked over the import's
      -- axiom, and the CHECKED `theorem sht_u : 1 = 1 := sha_n`.
      let env ← plainEnv `ReplayShadowThm #[`ReplayShadowAx]
      let env := rawAdd env (.thmInfo { name := `sha_n, levelParams := [], type := oneEqOne,
                                        value := reflTwo, all := [`sha_n] })
      let env ← addChecked env (thm `sht_u oneEqOne (cnst `sha_n)) true
      writeConstantsOnly env out
  | _ => none

def generate (out : System.FilePath) (fam : String) : IO UInt32 := do
  -- The toolchain's own stdlib, found from the running binary (never from `PATH`).
  let some sysroot := (← IO.appDir).parent
    | throw <| IO.userError "cannot locate the Lean sysroot from IO.appDir"
  initSearchPath sysroot
  if let some write := bespoke out fam then
    write
    return 0
  if let some (mod, imps, build) := parted fam then
    -- `level := .exported` makes the environment a `module` (`finalizeImport`'s `isModule`).
    let env ← if partedPlain fam then
        importModules (imps.map fun m => { module := m }) {} (trustLevel := 0)
      else
        importModules (imps.map fun m => { module := m }) {} (trustLevel := 0)
          (level := .exported)
    let env ← build (env.setMainModule mod)
    let full ← mkModuleData env .private
    let hidden := serverOnly fam
    let keep (p : Name → Bool) : ModuleData := { full with
      constants := full.constants.filter (p ·.name)
      constNames := full.constNames.filter p }
    saveModuleDataParts env.mainModule #[
      (OLeanLevel.exported.adjustFileName out, keep fun n => !isPrivateName n && !hidden n),
      (OLeanLevel.server.adjustFileName out, keep fun n => !isPrivateName n),
      (OLeanLevel.private.adjustFileName out, keep fun n => !hidden n && !privateHidden fam n)]
    return 0
  if let some (mod, imps, build) := special fam then
    let env ← importModules (imps.map fun m => { module := m }) {} (trustLevel := 0)
    let env ← build (env.setMainModule mod)
    if let some hdr := headerImports fam then
      let data ← mkModuleData env
      saveModuleData out env.mainModule { data with imports := hdr.map fun m => { module := m } }
      return 0
    writeModule env out
    return 0
  let some (mod, imp, checked, decls) := family fam
    | IO.eprintln s!"unknown family `{fam}`"; return 2
  let mut env ← importModules #[{ module := imp }] {} (trustLevel := 0)
  env := env.setMainModule mod
  for d in decls do
    env ← addChecked env d checked
  writeModule env out
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [out, fam] =>
    try
      let code : UInt32 ← generate out fam
      return code
    catch e =>
      IO.eprintln s!"GenReplayForged: {e}"
      return (1 : UInt32)
  | _ =>
    IO.eprintln "usage: lean --run GenReplayForged.lean <out.olean> <family> (see the module docs)"
    return 2
