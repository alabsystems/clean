/-
Carrier-parity P0 oracle generator (designs/2026-07-03-carrier-types-bitvec-parity.md §5 P0.2).

Dumps the ground-truth v4.30 declaration for every K-bucket carrier constant:
kind, level params, `pp.all` type, `pp.all` value (when present), and
inductive/constructor metadata. The output `oracle_decls.txt` is the
transcription target for Phases 1-3 and the expected-value table for the
fidelity tests.

Regenerate with the pinned toolchain (output must be byte-stable for a given
toolchain):

  ~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean \
    tests/fixtures/carrier_v4_30/gen_oracle_decls.lean > \
    tests/fixtures/carrier_v4_30/oracle_decls.txt
-/
import Lean
open Lean Meta Elab Command

def oracleNames : List Name := [
  -- Fin (already faithful — reference row)
  `Fin, `Fin.mk, `Fin.val, `Fin.isLt,
  -- Pow/NatPow substrate (P1 seeds)
  `Pow, `NatPow, `instPowNat, `instNatPowNat, `instHPow, `HPow, `instOfNatNat,
  -- BitVec substrate
  `BitVec, `BitVec.ofFin, `BitVec.toFin, `BitVec.ofNat, `BitVec.ofNatLT,
  `BitVec.toNat, `BitVec.decEq,
  -- UInt8/16/32/64
  `UInt8, `UInt8.ofBitVec, `UInt8.toBitVec, `UInt8.size, `UInt8.ofNat,
  `UInt8.ofNatLT, `UInt8.toNat, `UInt8.decEq, `UInt8.rec,
  `UInt16, `UInt16.ofBitVec, `UInt16.toBitVec, `UInt16.size, `UInt16.ofNat,
  `UInt16.ofNatLT, `UInt16.toNat, `UInt16.decEq,
  `UInt32, `UInt32.ofBitVec, `UInt32.toBitVec, `UInt32.size, `UInt32.ofNat,
  `UInt32.ofNatLT, `UInt32.toNat, `UInt32.decEq, `UInt32.isValidChar,
  `UInt32.lt, `UInt32.le, `UInt32.decLt, `UInt32.decLe,
  `UInt64, `UInt64.ofBitVec, `UInt64.toBitVec, `UInt64.size, `UInt64.ofNat,
  `UInt64.ofNatLT, `UInt64.toNat, `UInt64.decEq,
  -- USize (width-abstract!)
  `USize, `USize.ofBitVec, `USize.toBitVec, `USize.size, `USize.ofNat,
  `USize.ofNatLT, `USize.toNat, `USize.decEq,
  `System.Platform.getNumBits, `System.Platform.numBits,
  -- Char
  `Char, `Char.mk, `Char.val, `Char.valid, `Char.ofNat, `Char.ofNatAux,
  `Char.toNat, `Char.utf8Size, `Char.rec, `Nat.isValidChar,
  `instDecidableEqChar,
  -- ByteArray + UTF-8 validity
  `ByteArray, `ByteArray.mk, `ByteArray.data, `ByteArray.IsValidUTF8,
  `ByteArray.IsValidUTF8.intro, `List.toByteArray, `List.flatMap,
  -- String
  `String, `String.ofByteArray, `String.toByteArray, `String.isValidUTF8,
  `String.utf8EncodeChar, `List.utf8Encode, `String.ofList, `String.mk,
  `String.data, `String.decEq, `String.rec, `instDecidableEqString,
  `Substring.Raw,
  -- Array (ctor-compatible today — reference row)
  `Array, `Array.mk
]

def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

elab "#dumpOracle" : command => do
  let env ← getEnv
  liftTermElabM do
    withOptions (fun o => o.setBool `pp.all true) do
      for n in oracleNames do
        match env.find? n with
        | none => IO.println s!"### {n}\nMISSING\n"
        | some ci => do
          let ty ← Meta.ppExpr ci.type
          let mut out :=
            s!"### {n}\nkind: {kindOf ci}\nlevels: {ci.levelParams}\ntype: {ty}"
          match ci.value? with
          | some v => do
            let pv ← Meta.ppExpr v
            out := out ++ s!"\nvalue: {pv}"
          | none => pure ()
          match ci with
          | .inductInfo iv =>
            out := out ++
              s!"\nnumParams: {iv.numParams}\nnumIndices: {iv.numIndices}\nctors: {iv.ctors}"
          | .ctorInfo cv =>
            out := out ++
              s!"\ninduct: {cv.induct}\ncidx: {cv.cidx}\nnumParams: {cv.numParams}\nnumFields: {cv.numFields}"
          | .recInfo rv =>
            out := out ++
              s!"\nnumParams: {rv.numParams}\nnumIndices: {rv.numIndices}\nnumMotives: {rv.numMotives}\nnumMinors: {rv.numMinors}\nk: {rv.k}"
          | _ => pure ()
          -- Structure projection info (proj-spelled vs rec-spelled matters):
          if let some pi := env.getProjectionFnInfo? n then
            out := out ++
              s!"\nprojection: ctor={pi.ctorName} numParams={pi.numParams} i={pi.i}"
          IO.println (out ++ "\n")

#dumpOracle
