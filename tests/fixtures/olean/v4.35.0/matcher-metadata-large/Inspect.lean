import LargeMatcher
import Lean
open Lean Meta
private def treeJson : Std.DTreeMap.Internal.Impl Nat (fun _ => Unit) → Json
  | .leaf => Json.mkObj [("kind", toJson "leaf")]
  | .inner size key _ left right => Json.mkObj [("kind", toJson "inner"), ("size", toJson size), ("key", toJson key), ("left", treeJson left), ("right", treeJson right)]
private def setJson (value : Std.TreeSet Nat) : Json :=
  Json.mkObj [("values", toJson value.toArray), ("tree", treeJson value.inner.inner.inner)]
private def bucketRows : Std.DHashMap.Internal.AssocList Nat (fun _ => Std.TreeSet Nat) → List Json
  | .nil => []
  | .cons key value tail => Json.mkObj [("key", toJson key), ("nativeHash", toJson (hash key).toNat), ("value", setJson value)] :: bucketRows tail
private def infoJson (label : String) (info : Lean.Meta.MatcherInfo) : Json := Id.run do
  let raw := info.overlaps.map.inner.inner
  let alts := info.altInfos.map fun (a : Lean.Meta.Match.AltParamInfo) => Json.mkObj [("numFields", toJson a.numFields), ("numOverlaps", toJson a.numOverlaps), ("hasUnitThunk", toJson a.hasUnitThunk)]
  let buckets := raw.buckets.map fun bucket => Json.arr (bucketRows bucket).toArray
  let overlaps := info.overlaps.map.toList.map fun (n, ns) => Json.mkObj [("alternative", toJson n), ("overlapping", toJson ns.toArray)]
  return Json.mkObj [("name", toJson label), ("registered", toJson true), ("numParams", toJson info.numParams), ("numDiscrs", toJson info.numDiscrs), ("altInfos", toJson alts), ("altNumParams", toJson info.altNumParams), ("uElimPos", toJson info.uElimPos?), ("discrNames", toJson (info.discrInfos.map fun (d : Lean.Meta.Match.DiscrInfo) => d.hName?.map toString)), ("overlaps", toJson overlaps), ("rawSize", toJson raw.size), ("bucketCount", toJson raw.buckets.size), ("buckets", Json.arr buckets)]
run_meta do
  let env ← getEnv
  for label in ["crossSparse", "crossSparseEq", "disjoint", "ordinary"] do
    let name := Name.str (Name.str (Name.str .anonymous "LargeMatcher") label) "match_1"
    let row := match getMatcherInfoCore? env name with
      | none => Json.mkObj [("name", toJson label), ("registered", toJson false)]
      | some info => infoJson label info
    logInfo m!"{row.compress}"
