import MatcherParity
import Lean
open Lean Meta
run_meta do
  let env ← getEnv
  for label in ["choose.match_1", "chooseEq.match_1", "chooseTwo.match_1", "chooseOverlap.match_1", "ordinary.match_1"] do
    let name := (("MatcherParity." ++ label).splitOn ".").foldl Name.str Name.anonymous
    let row := match getMatcherInfoCore? env name with
    | none => Json.mkObj [("name", toJson label), ("registered", toJson false)]
    | some info =>
      let alts := info.altInfos.map fun (a : Match.AltParamInfo) => Json.mkObj [("numFields", toJson a.numFields), ("numOverlaps", toJson a.numOverlaps), ("hasUnitThunk", toJson a.hasUnitThunk)]
      let overlaps := info.overlaps.map.toList.map fun (entry : Nat × Std.TreeSet Nat) => Json.mkObj [("alternative", toJson entry.1), ("overlapping", toJson entry.2.toArray)]
      Json.mkObj [("name", toJson label), ("registered", toJson true), ("numParams", toJson info.numParams), ("numDiscrs", toJson info.numDiscrs), ("altInfos", toJson alts), ("altNumParams", toJson info.altNumParams), ("uElimPos", toJson info.uElimPos?), ("discrNames", toJson (info.discrInfos.map fun (d : Match.DiscrInfo) => d.hName?.map toString)), ("overlaps", toJson overlaps)]
    logInfo m!"{row.compress}"
