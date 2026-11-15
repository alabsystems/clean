import MatcherParity
import Lean
open Lean Meta
#print MatcherParity.choose
run_meta do
  let env ← getEnv
  for name in [``MatcherParity.choose.match_1, ``MatcherParity.choose, ``MatcherParity.ordinary, ``MatcherParity.chooseEq.match_1, ``MatcherParity.chooseTwo.match_1, ``MatcherParity.ordinary.match_1] do
    match getMatcherInfoCore? env name with
    | none => logInfo m!"{name}: none"
    | some i => logInfo m!"{name}: params={i.numParams} discrs={i.numDiscrs} alts={i.altNumParams} uElim={i.uElimPos?} discrInfos={i.discrInfos.map (fun d => d.hName?)}"
