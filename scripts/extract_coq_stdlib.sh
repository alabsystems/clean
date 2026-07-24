#!/bin/bash
# Extract Coq stdlib definitions for Mathverse Library import
# Copyright 2026 Andrew Yates Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
OUT="${1:-/tmp/coq_stdlib_extract.txt}"

echo "Extracting Coq stdlib definitions to $OUT..."

cat <<'COQEOF' | coqtop -q 2>"$OUT.err" | grep -v "^Rocq" | grep -v "^$" | grep -v "^Skipping" | grep -v "^Welcome" > "$OUT"
From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Init.Logic.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Init.Specif.
From Stdlib Require Import Init.Peano.
From Stdlib Require Import Init.Wf.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import ZArith.Zorder.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import NArith.BinNat.
From Stdlib Require Import QArith.QArith_base.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Classes.RelationClasses.

(* == Init.Datatypes == *)
Print nat. Print bool. Print unit. Print list. Print option.
Print prod. Print sum. Print comparison. Print sumbool. Print sumor.
Print Empty_set. Print identity.

(* == Init.Logic == *)
Print True. Print False. Print and. Print or. Print ex. Print eq.
Print not. Print iff. Print ex2. Print all.
Print eq_ind. Print eq_sym. Print eq_trans. Print f_equal.

(* == Init.Specif == *)
Print sig. Print sigT. Print sigT2. Print sig2.
Print exist. Print existT.
Print proj1_sig. Print proj2_sig.

(* == Peano arithmetic == *)
Print Nat.add. Print Nat.mul. Print Nat.sub. Print Nat.pred.
Print Nat.eqb. Print Nat.leb. Print Nat.ltb. Print Nat.even.
Print Nat.odd. Print Nat.max. Print Nat.min. Print Nat.pow.
Print Nat.div. Print Nat.modulo. Print Nat.log2.
Print Nat.succ. Print Nat.double.
Print Nat.le. Print Nat.lt.

(* == Bool == *)
Print negb. Print andb. Print orb. Print xorb. Print implb.
Print Bool.eqb. Print Bool.ifb.

(* == ZArith == *)
Print Z. Print positive.
Print Z.add. Print Z.mul. Print Z.opp. Print Z.sub. Print Z.abs.
Print Z.compare. Print Z.le. Print Z.lt. Print Z.ge. Print Z.gt.
Print Z.max. Print Z.min. Print Z.div. Print Z.modulo.
Print Z.of_nat. Print Z.to_nat. Print Z.abs_nat.
Print Z.even. Print Z.odd.
Print Pos.succ. Print Pos.add. Print Pos.mul.

(* == NArith == *)
Print N. Print N.add. Print N.mul. Print N.sub.
Print N.compare. Print N.of_nat.

(* == QArith == *)
Print Q. Print Qplus. Print Qmult. Print Qminus. Print Qinv.
Print Qle. Print Qlt. Print Qeq.

(* == Lists == *)
Print List.map. Print List.app. Print List.rev. Print List.length.
Print List.nth. Print List.filter. Print List.fold_left.
Print List.fold_right. Print List.flat_map.
Print List.In. Print List.NoDup.
Print List.Forall. Print List.Exists.
Print List.hd. Print List.tl.

(* == Strings == *)
Print string. Print ascii.
Print String.append. Print String.length.

(* == Relations == *)
Print relation. Print reflexive. Print symmetric. Print transitive.
Print equivalence. Print order.

(* == Classical axioms (if available) == *)
Print Coq.Init.Logic.eq_refl.

(* == Well-founded == *)
Print well_founded. Print Acc.
COQEOF

LINES=$(wc -l < "$OUT")
echo "Extracted $LINES lines to $OUT"
