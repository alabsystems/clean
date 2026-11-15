/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Replay a lean4export NDJSON 3.1 export through Lean's own kernel, READ BY
lean4export's own parser (`Export.parseStream`, lean4export `Export/Parse.lean`,
Lean FRO).

    lean --run Upstream.lean <export.ndjson> [--permit <axiom>]...

Run by `scripts/lean_export_replay.sh --reader upstream`, which compiles the
pinned lean4export checkout's `Export/Parse.lean` with the same toolchain and
puts it on LEAN_PATH; do not run it with a bare `lean` (under aterm that is
Clean).

WHY. `Replay.lean` beside this file parses the format with Clean's reading of
`format_ndjson.md`, written in Lean. This file parses it with the exporter's
own reader, so neither the parsing nor the kernel that decides is Clean's: the
constants upstream's parser builds go to `Lean.Environment.replay` (the engine
of `leanchecker`) from `mkEmptyEnvironment`.

The checks around upstream's parser are this file's, and are those of
`Replay.lean`: the export's `meta.lean` must be the Lean running (exit 2
otherwise), an `unsafe` or `partial` constant is refused (Lean's replay would
skip it, and a skipped declaration is no evidence), every parsed constant must
be in the replayed environment, and every axiom must be permitted.

Exit 0: accepted; the last line of stdout is one JSON object. Exit 1: refused,
with the reason on stderr. Exit 2: usage, or an export this file does not
judge.
-/
import Export.Parse
import Lean
open Lean

namespace UpstreamExportReplay

/-- The header: format 3.1, and the Lean that is running. -/
def checkMeta (j : Json) : Except String (String × String) := do
  let m ← j.getObjVal? "meta"
  let format ← (← (← m.getObjVal? "format").getObjVal? "version").getStr?
  let lean ← m.getObjVal? "lean"
  let version ← (← lean.getObjVal? "version").getStr?
  let githash ← (← lean.getObjVal? "githash").getStr?
  if !format.startsWith "3.1." then throw s!"format version {format} is not 3.1"
  if version != Lean.versionString then
    throw s!"the export states Lean {version}; this replay runs Lean {Lean.versionString}"
  if githash != Lean.githash then
    throw s!"the export states githash {githash}; this replay runs {Lean.githash}"
  pure (version, githash)

end UpstreamExportReplay

open UpstreamExportReplay in
def main (args : List String) : IO UInt32 := do
  let rec permits : List String → Except String (List String)
    | [] => pure []
    | "--permit" :: a :: rest => do pure (a :: (← permits rest))
    | other :: _ => throw s!"unexpected argument {other}"
  let (path, permitted) ← match args with
    | path :: rest => match permits rest with
      | .ok ps => pure (path, ps)
      | .error e => do
        IO.eprintln s!"lean_export_replay: {e}"
        return (2 : UInt32)
    | [] => do
      IO.eprintln "usage: lean --run Upstream.lean <export.ndjson> [--permit <axiom>]..."
      return (2 : UInt32)
  let first ← (← IO.FS.Handle.mk path .read).getLine
  let (version, githash) ← match Json.parse first >>= checkMeta with
    | .ok v => pure v
    | .error e => do
      IO.eprintln s!"lean_export_replay: not judged: {e}"
      return (2 : UInt32)
  -- Upstream's parser reads the whole file, the meta line included.
  let exported ← try
      Export.parseStream (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk path .read))
    catch e => do
      IO.eprintln s!"lean_export_replay: REJECTED (upstream reader): {e}"
      return (1 : UInt32)
  for (n, ci) in exported.constMap.toList do
    if ci.isUnsafe || ci.isPartial then
      IO.eprintln s!"lean_export_replay: REJECTED: {n} is unsafe or partial: Lean's replay would skip it"
      return (1 : UInt32)
  let env ← mkEmptyEnvironment
  let replayed ← try
      env.replay exported.constMap
    catch e => do
      IO.eprintln s!"lean_export_replay: REJECTED (kernel): {e}"
      return (1 : UInt32)
  let mut missing := #[]
  for (n, _) in exported.constMap.toList do
    if (replayed.toKernelEnv.find? n).isNone then missing := missing.push n
  if !missing.isEmpty then
    IO.eprintln s!"lean_export_replay: REJECTED: declared and not in the replayed environment: {missing}"
    return (1 : UInt32)
  let mut declared : Array String := #[]
  for (n, ci) in exported.constMap.toList do
    if let .axiomInfo _ := ci then declared := declared.push n.toString
  let axioms := declared.qsort (· < ·)
  let unpermitted := axioms.filter fun a => !permitted.contains a
  if !unpermitted.isEmpty then
    IO.eprintln s!"lean_export_replay: REJECTED: axioms outside the permitted set: {unpermitted}"
    return (1 : UInt32)
  IO.println (Json.mkObj [
    ("verdict", "accepted"), ("kernel", "Lean.Environment.replay"),
    ("reader", "lean4export Export.parseStream"),
    ("lean_version", version), ("lean_githash", githash),
    ("declarations", exported.constMap.size), ("order", exported.constOrder.size),
    ("axioms", toJson axioms), ("permitted", toJson permitted)]).compress
  return (0 : UInt32)
