/-
  Lean 4 kernel-level benchmarks for direct comparison with Clean.
  Measures: Kernel.check (inferType), Kernel.isDefEq, Kernel.whnf
  on expressions matching clean/crates/clean-kernel/benches/kernel_bench.rs

  Run: lake build && .lake/build/bin/lean4_kernel_bench
  Hardware: Apple M4 Max, 128GB (same as Clean benchmarks)
-/
import Lean
open Lean

/-- Number of iterations per benchmark. -/
def numIters : Nat := 100000

/-- Number of warmup iterations (discarded). -/
def warmupIters : Nat := 10000

/-- Run a benchmark with IO-based timing. The function writes its result
    into a ref to prevent DCE. -/
def runBenchCheck (name : String) (iters : Nat) (warmup : Nat)
    (env : Environment) (lctx : LocalContext) (e : Expr) : IO Float := do
  let ref <- IO.mkRef (0 : Nat)
  -- Warmup
  for _ in [:warmup] do
    match Kernel.check env lctx e with
    | .ok r => ref.modify (. + r.hash.toNat)
    | .error _ => ref.modify (. + 1)
  ref.set 0
  -- Measure
  let start <- IO.monoNanosNow
  for _ in [:iters] do
    match Kernel.check env lctx e with
    | .ok r => ref.modify (. + r.hash.toNat)
    | .error _ => ref.modify (. + 1)
  let stop <- IO.monoNanosNow
  let h <- ref.get
  let elapsed := (stop - start).toFloat
  let nsPerOp := elapsed / iters.toFloat
  IO.println s!"{name}: {nsPerOp} ns/op ({iters} iters, hash={h})"
  return nsPerOp

def runBenchWhnf (name : String) (iters : Nat) (warmup : Nat)
    (env : Environment) (lctx : LocalContext) (e : Expr) : IO Float := do
  let ref <- IO.mkRef (0 : Nat)
  for _ in [:warmup] do
    match Kernel.whnf env lctx e with
    | .ok r => ref.modify (. + r.hash.toNat)
    | .error _ => ref.modify (. + 1)
  ref.set 0
  let start <- IO.monoNanosNow
  for _ in [:iters] do
    match Kernel.whnf env lctx e with
    | .ok r => ref.modify (. + r.hash.toNat)
    | .error _ => ref.modify (. + 1)
  let stop <- IO.monoNanosNow
  let h <- ref.get
  let elapsed := (stop - start).toFloat
  let nsPerOp := elapsed / iters.toFloat
  IO.println s!"{name}: {nsPerOp} ns/op ({iters} iters, hash={h})"
  return nsPerOp

def runBenchDefEq (name : String) (iters : Nat) (warmup : Nat)
    (env : Environment) (lctx : LocalContext) (a b : Expr) : IO Float := do
  let ref <- IO.mkRef (0 : Nat)
  for _ in [:warmup] do
    match Kernel.isDefEq env lctx a b with
    | .ok true => ref.modify (. + 1)
    | .ok false => ref.modify (. + 2)
    | .error _ => ref.modify (. + 3)
  ref.set 0
  let start <- IO.monoNanosNow
  for _ in [:iters] do
    match Kernel.isDefEq env lctx a b with
    | .ok true => ref.modify (. + 1)
    | .ok false => ref.modify (. + 2)
    | .error _ => ref.modify (. + 3)
  let stop <- IO.monoNanosNow
  let h <- ref.get
  let elapsed := (stop - start).toFloat
  let nsPerOp := elapsed / iters.toFloat
  IO.println s!"{name}: {nsPerOp} ns/op ({iters} iters, hash={h})"
  return nsPerOp

/-- Build a nested lambda: fun (x0 : Sort 0) => fun (x1 : Sort 1) => ... => x0 -/
def mkNestedLambda (depth : Nat) : Expr := Id.run do
  let mut acc := Expr.bvar (depth - 1)
  for i in [:depth] do
    let sortLevel := Level.ofNat i
    acc := Expr.lam Name.anonymous (mkSort sortLevel) acc .default
  return acc

/-- Build a nested beta redex: (fun x => x) ((fun x => x) (... Prop)) -/
def mkNestedBetaRedex (depth : Nat) : Expr := Id.run do
  let idLam := Expr.lam Name.anonymous (mkSort levelOne) (Expr.bvar 0) .default
  let mut acc := mkSort levelZero
  for _ in [:depth] do
    acc := mkApp idLam acc
  return acc

/-- Build structurally equal nested lambdas for is_def_eq comparison -/
def mkStructuralLambda (depth : Nat) : Expr := Id.run do
  let mut acc := Expr.bvar 0
  for _ in [:depth] do
    acc := Expr.lam Name.anonymous (mkSort levelZero) acc .default
  return acc

unsafe def main : IO Unit := do
  IO.println "=== Lean 4 Kernel Benchmarks ==="
  IO.println s!"Lean version: {Lean.versionString}"
  IO.println s!"Iterations: {numIters}, Warmup: {warmupIters}"
  IO.println ""

  let env <- mkEmptyEnvironment

  -- Add axiom P : Prop
  let pDecl := Declaration.axiomDecl {
    name := Name.mkSimple "P"
    levelParams := []
    type := mkSort levelZero
    isUnsafe := false
  }
  let env <- match env.addDeclCore 0 pDecl none with
    | .ok env => pure env
    | .error _ => throw (IO.Error.userError "addDecl failed for P")

  -- Add definition id_bench : {A : Sort u} -> A -> A
  let u := Name.mkSimple "u"
  let idType := Expr.forallE Name.anonymous (mkSort (mkLevelParam u)) (
    Expr.forallE Name.anonymous (Expr.bvar 0) (Expr.bvar 1) .default
  ) .implicit
  let idValue := Expr.lam Name.anonymous (mkSort (mkLevelParam u)) (
    Expr.lam Name.anonymous (Expr.bvar 0) (Expr.bvar 0) .default
  ) .implicit
  let idDecl := Declaration.defnDecl {
    name := Name.mkSimple "id_bench"
    levelParams := [u]
    type := idType
    value := idValue
    hints := .regular 0
    safety := .safe
  }
  let env <- match env.addDeclCore 0 idDecl none with
    | .ok env => pure env
    | .error _ => throw (IO.Error.userError "addDecl failed for id_bench")

  let lctx : LocalContext := {}

  IO.println "--- infer_type (Kernel.check) ---"

  let prop := mkSort levelZero
  let _ <- runBenchCheck "infer_type/Sort_0 (Prop)" numIters warmupIters env lctx prop

  let type_ := mkSort levelOne
  let _ <- runBenchCheck "infer_type/Sort_1 (Type)" numIters warmupIters env lctx type_

  let simpleLam := Expr.lam Name.anonymous (mkSort levelZero) (Expr.bvar 0) .default
  let _ <- runBenchCheck "infer_type/lambda_simple" numIters warmupIters env lctx simpleLam

  for depth in [2, 4, 8, 16] do
    let nested := mkNestedLambda depth
    let _ <- runBenchCheck s!"infer_type/lambda_nested/{depth}" numIters warmupIters env lctx nested

  let idApp := mkApp2 (mkConst (Name.mkSimple "id_bench") [levelOne]) (mkSort levelZero) (mkConst (Name.mkSimple "P"))
  let _ <- runBenchCheck "infer_type/app_simple (id Prop P)" numIters warmupIters env lctx idApp

  IO.println ""
  IO.println "--- whnf (Kernel.whnf) ---"

  let betaSimple := mkApp (Expr.lam Name.anonymous (mkSort levelOne) (Expr.bvar 0) .default) (mkSort levelZero)
  let _ <- runBenchWhnf "whnf/beta_simple" numIters warmupIters env lctx betaSimple

  for depth in [2, 4, 8, 16, 32] do
    let nested := mkNestedBetaRedex depth
    let _ <- runBenchWhnf s!"whnf/beta_nested/{depth}" numIters warmupIters env lctx nested

  let idConst := mkConst (Name.mkSimple "id_bench") [levelOne]
  let _ <- runBenchWhnf "whnf/delta_unfold (id_bench)" numIters warmupIters env lctx idConst

  IO.println ""
  IO.println "--- is_def_eq (Kernel.isDefEq) ---"

  let _ <- runBenchDefEq "is_def_eq/identical (Prop, Prop)" numIters warmupIters env lctx prop prop
  let _ <- runBenchDefEq "is_def_eq/different_sorts (Prop, Type)" numIters warmupIters env lctx prop type_

  let maxLevel := mkSort (mkLevelMax levelZero levelZero)
  let _ <- runBenchDefEq "is_def_eq/level_normalize" numIters warmupIters env lctx maxLevel prop
  let _ <- runBenchDefEq "is_def_eq/beta_reduce" numIters warmupIters env lctx betaSimple prop

  for depth in [2, 4, 8, 16] do
    let lamA := mkStructuralLambda depth
    let lamB := mkStructuralLambda depth
    let _ <- runBenchDefEq s!"is_def_eq/structural/{depth}" numIters warmupIters env lctx lamA lamB

  IO.println ""
  IO.println "=== Done ==="
