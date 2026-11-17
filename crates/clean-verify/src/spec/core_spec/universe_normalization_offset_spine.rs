// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public-add_offset-shaped mathematical iteration and the actual Max-tail graph.
//! Path-Succ budgets constrain created intermediates; full public normalization,
//! its mutual recursion, source admission/execution and Trust remain open.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const OFFSET: &[(&str, &str)] = &[
    (
        r"def level_add_offset (n : Nat) (a : Level) : Level :=
 @Nat.rec (fun (_ : Nat) => Level) a (fun (_ : Nat) (r : Level) => Level.succ r) n",
        "Actual public add_offset-shaped mathematical iterator: exactly n successor constructions, no count saturation or smart normalization.",
    ),
    (
        r"def level_succ_path (a : Level) : Nat :=
 @Level.rec (fun (_ : Level) => Nat) Nat.zero
 (fun (_ : Level) (h : Nat) => Nat.succ h)
 (fun (_ : Level) (_ : Level) (hx : Nat) (hy : Nat) => natMax hx hy)
 (fun (_ : Level) (_ : Level) (hx : Nat) (hy : Nat) => natMax hx hy)
 (fun (_ : Name) => Nat.zero) a",
        "Maximum number of Succ nodes along a root-to-leaf path, including spines separated by Max/IMax; not semantic evaluation or a proved admission policy.",
    ),
    (
        r"def level_offset_le_succ_path (a : Level) : Le (level_offset_nat a) (level_succ_path a) :=
 @Level.rec (fun (x : Level) => Le (level_offset_nat x) (level_succ_path x))
 (@Le.refl Nat.zero)
 (fun (x : Level) (ih : Le (level_offset_nat x) (level_succ_path x)) => le_succ_succ (level_offset_nat x) (level_succ_path x) ih)
 (fun (x : Level) (y : Level) (_ : Le (level_offset_nat x) (level_succ_path x)) (_ : Le (level_offset_nat y) (level_succ_path y)) => le_zero_n (natMax (level_succ_path x) (level_succ_path y)))
 (fun (x : Level) (y : Level) (_ : Le (level_offset_nat x) (level_succ_path x)) (_ : Le (level_offset_nat y) (level_succ_path y)) => le_zero_n (natMax (level_succ_path x) (level_succ_path y)))
 (fun (_ : Name) => @Le.refl Nat.zero) a",
        "The actual leading successor count is bounded by the path-wide count.",
    ),
    (
        r"def level_succ_path_implies_offsets (a : Level) : forall (cap : Nat), Le (level_succ_path a) cap -> LevelOffsetsBounded cap a :=
 @Level.rec (fun (x : Level) => forall (cap : Nat), Le (level_succ_path x) cap -> LevelOffsetsBounded cap x)
 (fun (cap : Nat) (h : Le Nat.zero cap) => h)
 (fun (x : Level) (ih : forall (cap : Nat), Le (level_succ_path x) cap -> LevelOffsetsBounded cap x) => fun (cap : Nat) (h : Le (Nat.succ (level_succ_path x)) cap) =>
  uoffset_and_intro (Le (Nat.succ (level_offset_nat x)) cap) (LevelOffsetsBounded cap x)
   (le_trans (Nat.succ (level_offset_nat x)) (Nat.succ (level_succ_path x)) cap
    (le_succ_succ (level_offset_nat x) (level_succ_path x) (level_offset_le_succ_path x)) h)
   (ih cap (le_trans (level_succ_path x) (Nat.succ (level_succ_path x)) cap
    (@Le.step (level_succ_path x) (level_succ_path x) (@Le.refl (level_succ_path x))) h)))
 (fun (x : Level) (y : Level) (ihx : forall (cap : Nat), Le (level_succ_path x) cap -> LevelOffsetsBounded cap x) (ihy : forall (cap : Nat), Le (level_succ_path y) cap -> LevelOffsetsBounded cap y) =>
 fun (cap : Nat) (h : Le (natMax (level_succ_path x) (level_succ_path y)) cap) =>
 uoffset_and_intro (LevelOffsetsBounded cap x) (LevelOffsetsBounded cap y)
 (ihx cap (le_trans (level_succ_path x) (natMax (level_succ_path x) (level_succ_path y)) cap
  (le_natMax_left (level_succ_path x) (level_succ_path y)) h))
 (ihy cap (le_trans (level_succ_path y) (natMax (level_succ_path x) (level_succ_path y)) cap
  (ugeq_natMax_right (level_succ_path x) (level_succ_path y)) h)))
 (fun (x : Level) (y : Level) (ihx : forall (cap : Nat), Le (level_succ_path x) cap -> LevelOffsetsBounded cap x) (ihy : forall (cap : Nat), Le (level_succ_path y) cap -> LevelOffsetsBounded cap y) =>
 fun (cap : Nat) (h : Le (natMax (level_succ_path x) (level_succ_path y)) cap) =>
 uoffset_and_intro (LevelOffsetsBounded cap x) (LevelOffsetsBounded cap y)
 (ihx cap (le_trans (level_succ_path x) (natMax (level_succ_path x) (level_succ_path y)) cap
  (le_natMax_left (level_succ_path x) (level_succ_path y)) h))
 (ihy cap (le_trans (level_succ_path y) (natMax (level_succ_path x) (level_succ_path y)) cap
  (ugeq_natMax_right (level_succ_path x) (level_succ_path y)) h)))
 (fun (_ : Name) (cap : Nat) (h : Le Nat.zero cap) => h) a",
        "Actual Level induction derives the existing EVERY-subterm comparator invariant from one stronger path budget. No normalizer-preservation or admission assumption.",
    ),
    (
        r"def level_add_offset_eval (n : Nat) (a : Level) (rho : Name -> Nat) :
 @Eq Nat (evalL rho (level_add_offset n a)) (Nat.add (evalL rho a) n) :=
 @Nat.rec (fun (k : Nat) => @Eq Nat (evalL rho (level_add_offset k a)) (Nat.add (evalL rho a) k))
 (@Eq.refl Nat (evalL rho a))
 (fun (k : Nat) (ih : @Eq Nat (evalL rho (level_add_offset k a)) (Nat.add (evalL rho a) k)) =>
  Eq.cong Nat Nat Nat.succ (evalL rho (level_add_offset k a)) (Nat.add (evalL rho a) k) ih) n",
        "Denotation of the actual successor iterator is addition by n.",
    ),
    (
        r"def level_add_offset_path (n : Nat) (a : Level)  :
 @Eq Nat (level_succ_path (level_add_offset n a)) (Nat.add (level_succ_path a) n) :=
 @Nat.rec (fun (k : Nat) => @Eq Nat (level_succ_path (level_add_offset k a)) (Nat.add (level_succ_path a) k))
 (@Eq.refl Nat (level_succ_path a))
 (fun (k : Nat) (ih : @Eq Nat (level_succ_path (level_add_offset k a)) (Nat.add (level_succ_path a) k)) =>
  Eq.cong Nat Nat Nat.succ (level_succ_path (level_add_offset k a)) (Nat.add (level_succ_path a) k) ih) n",
        "The created iterator result's path budget adds n exactly.",
    ),
    (
        r"def level_add_offset_count (n : Nat) (a : Level)  :
 @Eq Nat (level_offset_nat (level_add_offset n a)) (Nat.add (level_offset_nat a) n) :=
 @Nat.rec (fun (k : Nat) => @Eq Nat (level_offset_nat (level_add_offset k a)) (Nat.add (level_offset_nat a) k))
 (@Eq.refl Nat (level_offset_nat a))
 (fun (k : Nat) (ih : @Eq Nat (level_offset_nat (level_add_offset k a)) (Nat.add (level_offset_nat a) k)) =>
  Eq.cong Nat Nat Nat.succ (level_offset_nat (level_add_offset k a)) (Nat.add (level_offset_nat a) k) ih) n",
        "Exact leading count of the created result adds n, rather than saturating its structural value.",
    ),
    (
        r"def level_strip_offset_path (a : Level) :
 @Eq Nat (level_succ_path a) (Nat.add (level_succ_path (level_offset_base a)) (level_offset_nat a)) :=
 @Level.rec
 (fun (x : Level) => @Eq Nat (level_succ_path x) (Nat.add (level_succ_path (level_offset_base x)) (level_offset_nat x)))
 (@Eq.refl Nat Nat.zero)
 (fun (x : Level) (ih : @Eq Nat (level_succ_path x) (Nat.add (level_succ_path (level_offset_base x)) (level_offset_nat x))) =>
  Eq.cong Nat Nat Nat.succ (level_succ_path x) (Nat.add (level_succ_path (level_offset_base x)) (level_offset_nat x)) ih)
 (fun (x : Level) (y : Level)
 (_ : @Eq Nat (level_succ_path x) (Nat.add (level_succ_path (level_offset_base x)) (level_offset_nat x)))
 (_ : @Eq Nat (level_succ_path y) (Nat.add (level_succ_path (level_offset_base y)) (level_offset_nat y))) =>
 @Eq.refl Nat (natMax (level_succ_path x) (level_succ_path y)))
 (fun (x : Level) (y : Level)
 (_ : @Eq Nat (level_succ_path x) (Nat.add (level_succ_path (level_offset_base x)) (level_offset_nat x)))
 (_ : @Eq Nat (level_succ_path y) (Nat.add (level_succ_path (level_offset_base y)) (level_offset_nat y))) =>
 @Eq.refl Nat (natMax (level_succ_path x) (level_succ_path y)))
 (fun (_ : Name) => @Eq.refl Nat Nat.zero) a",
        "Path budget decomposes into the structural stripped base and exact outer count; required to justify later redistribution sums.",
    ),
    (
        r"def level_add_offset_offsets (cap : Nat) (n : Nat) (a : Level)
 (h : Le (Nat.add (level_succ_path a) n) cap) :
 LevelOffsetsBounded cap (level_add_offset n a) :=
 level_succ_path_implies_offsets (level_add_offset n a) cap
 (Eq.substType Nat (fun (k : Nat) => Le k cap)
  (Nat.add (level_succ_path a) n) (level_succ_path (level_add_offset n a))
  (Eq.symm Nat (level_succ_path (level_add_offset n a)) (Nat.add (level_succ_path a) n) (level_add_offset_path n a)) h)",
        "The actual sum budget establishes all created-result comparator bounds; two separate <=cap bounds are not substituted.",
    ),
    (
        r"def offset_natMax_add_right (a : Nat) (b : Nat) (n : Nat) :
 @Eq Nat (natMax (Nat.add a n) (Nat.add b n)) (Nat.add (natMax a b) n) :=
 @Nat.rec (fun (k : Nat) => @Eq Nat (natMax (Nat.add a k) (Nat.add b k)) (Nat.add (natMax a b) k))
 (@Eq.refl Nat (natMax a b))
 (fun (k : Nat) (ih : @Eq Nat (natMax (Nat.add a k) (Nat.add b k)) (Nat.add (natMax a b) k)) =>
  Eq.cong Nat Nat Nat.succ (natMax (Nat.add a k) (Nat.add b k)) (Nat.add (natMax a b) k) ih) n",
        "Derived maximum/addition distribution by actual Nat induction, with no arithmetic oracle.",
    ),
];

const MAX_LIST: &[(&str, &str)] = &[
    (
        r"def offset_natMax_assoc (a : Nat) (b : Nat) (c : Nat) :
 @Eq Nat (natMax (natMax a b) c) (natMax a (natMax b c)) :=
 le_antisymm (natMax (natMax a b) c) (natMax a (natMax b c))
 (ugeq_natMax_upper (natMax a b) c (natMax a (natMax b c))
  (ugeq_natMax_upper a b (natMax a (natMax b c))
   (le_natMax_left a (natMax b c))
   (le_trans b (natMax b c) (natMax a (natMax b c)) (le_natMax_left b c) (ugeq_natMax_right a (natMax b c))))
  (le_trans c (natMax b c) (natMax a (natMax b c)) (ugeq_natMax_right b c) (ugeq_natMax_right a (natMax b c))))
 (ugeq_natMax_upper a (natMax b c) (natMax (natMax a b) c)
  (le_trans a (natMax a b) (natMax (natMax a b) c) (le_natMax_left a b) (le_natMax_left (natMax a b) c))
  (ugeq_natMax_upper b c (natMax (natMax a b) c)
   (le_trans b (natMax a b) (natMax (natMax a b) c) (ugeq_natMax_right a b) (le_natMax_left (natMax a b) c))
   (ugeq_natMax_right (natMax a b) c)))",
        "Maximum association derives from checked order antisymmetry and both upper-bound introductions; no permutation or normalization oracle.",
    ),
    (
        r"def level_max_list_fold (f : Level -> Nat) (xs : ListType Level) : Nat :=
 @ListType.rec Level (fun (_ : ListType Level) => Nat) Nat.zero
 (fun (x : Level) (_ : ListType Level) (tail : Nat) => natMax (f x) tail) xs",
        "Semantic/path maximum over a Level list; zero is only the mathematical empty fold, not an extra raw Level node.",
    ),
    (
        r"def level_raw_max_from (a : Level) (xs : ListType Level) : Level :=
 @ListType.rec Level (fun (_ : ListType Level) => Level -> Level)
 (fun (head : Level) => head)
 (fun (x : Level) (_ : ListType Level) (tail : Level -> Level) => fun (head : Level) => Level.max head (tail x)) xs a",
        "Actual nonempty right-associated raw fold: head plus tail, singleton exactly the head. No smart constructor or inserted Max(_,Zero).",
    ),
    (
        r"def level_raw_max_args (xs : ListType Level) : Level :=
 @ListType.rec Level (fun (_ : ListType Level) => Level) Level.zero
 (fun (x : Level) (rest : ListType Level) (_ : Level) => level_raw_max_from x rest) xs",
        "Combined normalize_max empty guard plus raw right-fold. Empty maps to Zero; equivalence to the private unchecked fold is claimed only for nonempty inputs.",
    ),
    (
        r"def level_max_restore (n : Nat) (xs : ListType Level) : Level :=
 level_raw_max_args (mapLL (fun (a : Level) => level_add_offset n a) xs)",
        "Actual normalize_max tail: apply the outer offset to every retained argument then use its empty guard/raw right-fold. n=0 is the same identity branch.",
    ),
    (
        r"def level_raw_max_singleton (a : Level) :
 @Eq Level (level_raw_max_args (@ListType.cons Level a (@ListType.nil Level))) a := @Eq.refl Level a",
        "Singleton preserves the exact structural Level, not merely its denotation.",
    ),
    (
        r"def level_max_restore_empty (n : Nat) :
 @Eq Level (level_max_restore n (@ListType.nil Level)) Level.zero := @Eq.refl Level Level.zero",
        "Actual empty-tail guard returns Zero even for positive offsets; never silently identified with adding the offset to Zero.",
    ),
    (
        r"def level_max_restore_singleton (n : Nat) (a : Level) :
 @Eq Level (level_max_restore n (@ListType.cons Level a (@ListType.nil Level))) (level_add_offset n a) :=
 @Eq.refl Level (level_add_offset n a)",
        "Actual positive-offset singleton graph has no extra raw Max node.",
    ),
    (
        r"def level_raw_max_from_eval (rho : Name -> Nat) (xs : ListType Level) : forall (a : Level), @Eq Nat (evalL rho (level_raw_max_from a xs)) (natMax (evalL rho a) (level_max_list_fold (evalL rho) xs)) :=
 @ListType.rec Level (fun (ys : ListType Level) => forall (a : Level), @Eq Nat (evalL rho (level_raw_max_from a ys)) (natMax (evalL rho a) (level_max_list_fold (evalL rho) ys)))
 (fun (a : Level) =>
  Eq.symm Nat (natMax (evalL rho a) Nat.zero) (evalL rho a) (ugeq_natMax_absorb_left (evalL rho a) Nat.zero (le_zero_n (evalL rho a))))
 (fun (x : Level) (rest : ListType Level) (ih : forall (a : Level), @Eq Nat (evalL rho (level_raw_max_from a rest)) (natMax (evalL rho a) (level_max_list_fold (evalL rho) rest))) =>
  fun (a : Level) => Eq.cong Nat Nat (fun (k : Nat) => natMax (evalL rho a) k)
   (evalL rho (level_raw_max_from x rest)) (natMax (evalL rho x) (level_max_list_fold (evalL rho) rest)) (ih x)) xs",
        "Actual nonempty raw fold's denotation is the mathematical maximum of its real inputs.",
    ),
    (
        r"def level_raw_max_args_eval (rho : Name -> Nat) (xs : ListType Level) :
 @Eq Nat (evalL rho (level_raw_max_args xs)) (level_max_list_fold (evalL rho) xs) :=
 @ListType.rec Level
 (fun (ys : ListType Level) => @Eq Nat (evalL rho (level_raw_max_args ys)) (level_max_list_fold (evalL rho) ys))
 (@Eq.refl Nat Nat.zero)
 (fun (x : Level) (rest : ListType Level)
 (_ : @Eq Nat (evalL rho (level_raw_max_args rest)) (level_max_list_fold (evalL rho) rest)) =>
  level_raw_max_from_eval rho rest x) xs",
        "Combined empty guard/nonempty raw fold has the expected denotation for all lists.",
    ),
    (
        r"def level_raw_max_from_path  (xs : ListType Level) : forall (a : Level), @Eq Nat (level_succ_path (level_raw_max_from a xs)) (natMax (level_succ_path a) (level_max_list_fold (level_succ_path) xs)) :=
 @ListType.rec Level (fun (ys : ListType Level) => forall (a : Level), @Eq Nat (level_succ_path (level_raw_max_from a ys)) (natMax (level_succ_path a) (level_max_list_fold (level_succ_path) ys)))
 (fun (a : Level) =>
  Eq.symm Nat (natMax (level_succ_path a) Nat.zero) (level_succ_path a) (ugeq_natMax_absorb_left (level_succ_path a) Nat.zero (le_zero_n (level_succ_path a))))
 (fun (x : Level) (rest : ListType Level) (ih : forall (a : Level), @Eq Nat (level_succ_path (level_raw_max_from a rest)) (natMax (level_succ_path a) (level_max_list_fold (level_succ_path) rest))) =>
  fun (a : Level) => Eq.cong Nat Nat (fun (k : Nat) => natMax (level_succ_path a) k)
   (level_succ_path (level_raw_max_from x rest)) (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) rest)) (ih x)) xs",
        "Actual nonempty raw fold's path count is the mathematical maximum of its real inputs.",
    ),
    (
        r"def level_raw_max_args_path  (xs : ListType Level) :
 @Eq Nat (level_succ_path (level_raw_max_args xs)) (level_max_list_fold (level_succ_path) xs) :=
 @ListType.rec Level
 (fun (ys : ListType Level) => @Eq Nat (level_succ_path (level_raw_max_args ys)) (level_max_list_fold (level_succ_path) ys))
 (@Eq.refl Nat Nat.zero)
 (fun (x : Level) (rest : ListType Level)
 (_ : @Eq Nat (level_succ_path (level_raw_max_args rest)) (level_max_list_fold (level_succ_path) rest)) =>
  level_raw_max_from_path rest x) xs",
        "Combined empty guard/nonempty raw fold has the expected path count for all lists.",
    ),
    (
        r"def level_flatten_max_into (a : Level) (rest : ListType Level) : ListType Level :=
 @Level.rec (fun (_ : Level) => ListType Level -> ListType Level)
 (fun (tail : ListType Level) => @ListType.cons Level Level.zero tail)
 (fun (x : Level) (_ : ListType Level -> ListType Level) => fun (tail : ListType Level) => @ListType.cons Level (Level.succ x) tail)
 (fun (_ : Level) (_ : Level) (left : ListType Level -> ListType Level) (right : ListType Level -> ListType Level) =>
  fun (tail : ListType Level) => left (right tail))
 (fun (x : Level) (y : Level) (_ : ListType Level -> ListType Level) (_ : ListType Level -> ListType Level) =>
  fun (tail : ListType Level) => @ListType.cons Level (Level.imax x y) tail)
 (fun (n : Name) => fun (tail : ListType Level) => @ListType.cons Level (Level.param n) tail) a rest",
        "Source-shaped max-only flattening with a trailing accumulator: preserves left-to-right order and never enters Succ or IMax payloads.",
    ),
    (
        r"def level_flatten_max (a : Level) : ListType Level :=
 level_flatten_max_into a (@ListType.nil Level)",
        "Actual first/second flattening result, initialized with the empty output suffix.",
    ),
    (
        r"def level_list_nonempty (xs : ListType Level) : Bool :=
 @ListType.rec Level (fun (_ : ListType Level) => Bool) Bool.false
 (fun (_ : Level) (_ : ListType Level) (_ : Bool) => Bool.true) xs",
        "Computational nonempty discriminator, not an assumed invariant.",
    ),
    (
        r"def level_flatten_into_nonempty (a : Level) : forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into a rest)) Bool.true :=
 @Level.rec (fun (x : Level) => forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into x rest)) Bool.true)
 (fun (_ : ListType Level) => @Eq.refl Bool Bool.true)
 (fun (x : Level) (_ : forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into x rest)) Bool.true) => fun (_ : ListType Level) => @Eq.refl Bool Bool.true)
 (fun (x : Level) (y : Level) (ihx : forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into x rest)) Bool.true) (_ : forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into y rest)) Bool.true) =>
  fun (rest : ListType Level) => ihx (level_flatten_max_into y rest))
 (fun (x : Level) (y : Level) (_ : forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into x rest)) Bool.true) (_ : forall (rest : ListType Level), @Eq Bool (level_list_nonempty (level_flatten_max_into y rest)) Bool.true) =>
  fun (_ : ListType Level) => @Eq.refl Bool Bool.true)
 (fun (_ : Name) => fun (_ : ListType Level) => @Eq.refl Bool Bool.true) a",
        "Actual flattening always produces at least one argument, including Zero and nested raw Max trees.",
    ),
    (
        r"def level_flatten_into_eval (rho : Name -> Nat) (a : Level) : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into a rest)) (natMax (evalL rho a) (level_max_list_fold (evalL rho) rest)) :=
 @Level.rec (fun (x : Level) => forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into x rest)) (natMax (evalL rho x) (level_max_list_fold (evalL rho) rest)))
 (fun (rest : ListType Level) => @Eq.refl Nat (natMax (evalL rho Level.zero) (level_max_list_fold (evalL rho) rest)))
 (fun (x : Level) (_ : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into x rest)) (natMax (evalL rho x) (level_max_list_fold (evalL rho) rest))) => fun (rest : ListType Level) => @Eq.refl Nat (natMax (evalL rho (Level.succ x)) (level_max_list_fold (evalL rho) rest)))
 (fun (x : Level) (y : Level) (ihx : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into x rest)) (natMax (evalL rho x) (level_max_list_fold (evalL rho) rest))) (ihy : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into y rest)) (natMax (evalL rho y) (level_max_list_fold (evalL rho) rest))) => fun (rest : ListType Level) =>
 Eq.trans Nat (level_max_list_fold (evalL rho) (level_flatten_max_into x (level_flatten_max_into y rest)))
 (natMax (evalL rho x) (level_max_list_fold (evalL rho) (level_flatten_max_into y rest)))
 (natMax (natMax (evalL rho x) (evalL rho y)) (level_max_list_fold (evalL rho) rest))
 (ihx (level_flatten_max_into y rest))
 (Eq.trans Nat (natMax (evalL rho x) (level_max_list_fold (evalL rho) (level_flatten_max_into y rest)))
  (natMax (evalL rho x) (natMax (evalL rho y) (level_max_list_fold (evalL rho) rest)))
  (natMax (natMax (evalL rho x) (evalL rho y)) (level_max_list_fold (evalL rho) rest))
  (Eq.cong Nat Nat (fun (k : Nat) => natMax (evalL rho x) k)
   (level_max_list_fold (evalL rho) (level_flatten_max_into y rest))
   (natMax (evalL rho y) (level_max_list_fold (evalL rho) rest)) (ihy rest))
  (Eq.symm Nat (natMax (natMax (evalL rho x) (evalL rho y)) (level_max_list_fold (evalL rho) rest))
   (natMax (evalL rho x) (natMax (evalL rho y) (level_max_list_fold (evalL rho) rest)))
   (offset_natMax_assoc (evalL rho x) (evalL rho y) (level_max_list_fold (evalL rho) rest)))))
 (fun (x : Level) (y : Level) (_ : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into x rest)) (natMax (evalL rho x) (level_max_list_fold (evalL rho) rest))) (_ : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (evalL rho) (level_flatten_max_into y rest)) (natMax (evalL rho y) (level_max_list_fold (evalL rho) rest))) => fun (rest : ListType Level) => @Eq.refl Nat (natMax (evalL rho (Level.imax x y)) (level_max_list_fold (evalL rho) rest)))
 (fun (n : Name) => fun (rest : ListType Level) => @Eq.refl Nat (natMax (evalL rho (Level.param n)) (level_max_list_fold (evalL rho) rest))) a",
        "Actual max-only flattening preserves join denotation, including its accumulator suffix.",
    ),
    (
        r"def level_flatten_raw_eval (rho : Name -> Nat) (a : Level) :
 @Eq Nat (evalL rho (level_raw_max_args (level_flatten_max a))) (evalL rho a) :=
 Eq.trans Nat (evalL rho (level_raw_max_args (level_flatten_max a)))
 (level_max_list_fold (evalL rho) (level_flatten_max a)) (evalL rho a)
 (level_raw_max_args_eval rho (level_flatten_max a))
 (Eq.trans Nat (level_max_list_fold (evalL rho) (level_flatten_max a))
  (natMax (evalL rho a) Nat.zero) (evalL rho a)
  (level_flatten_into_eval rho a (@ListType.nil Level))
  (ugeq_natMax_absorb_left (evalL rho a) Nat.zero (le_zero_n (evalL rho a))))",
        "Flatten followed by the actual raw fold preserves denotation for every raw Level, with no smart normalization premise.",
    ),
    (
        r"def level_flatten_into_path  (a : Level) : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into a rest)) (natMax (level_succ_path a) (level_max_list_fold (level_succ_path) rest)) :=
 @Level.rec (fun (x : Level) => forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into x rest)) (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) rest)))
 (fun (rest : ListType Level) => @Eq.refl Nat (natMax (level_succ_path Level.zero) (level_max_list_fold (level_succ_path) rest)))
 (fun (x : Level) (_ : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into x rest)) (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) rest))) => fun (rest : ListType Level) => @Eq.refl Nat (natMax (level_succ_path (Level.succ x)) (level_max_list_fold (level_succ_path) rest)))
 (fun (x : Level) (y : Level) (ihx : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into x rest)) (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) rest))) (ihy : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into y rest)) (natMax (level_succ_path y) (level_max_list_fold (level_succ_path) rest))) => fun (rest : ListType Level) =>
 Eq.trans Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into x (level_flatten_max_into y rest)))
 (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) (level_flatten_max_into y rest)))
 (natMax (natMax (level_succ_path x) (level_succ_path y)) (level_max_list_fold (level_succ_path) rest))
 (ihx (level_flatten_max_into y rest))
 (Eq.trans Nat (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) (level_flatten_max_into y rest)))
  (natMax (level_succ_path x) (natMax (level_succ_path y) (level_max_list_fold (level_succ_path) rest)))
  (natMax (natMax (level_succ_path x) (level_succ_path y)) (level_max_list_fold (level_succ_path) rest))
  (Eq.cong Nat Nat (fun (k : Nat) => natMax (level_succ_path x) k)
   (level_max_list_fold (level_succ_path) (level_flatten_max_into y rest))
   (natMax (level_succ_path y) (level_max_list_fold (level_succ_path) rest)) (ihy rest))
  (Eq.symm Nat (natMax (natMax (level_succ_path x) (level_succ_path y)) (level_max_list_fold (level_succ_path) rest))
   (natMax (level_succ_path x) (natMax (level_succ_path y) (level_max_list_fold (level_succ_path) rest)))
   (offset_natMax_assoc (level_succ_path x) (level_succ_path y) (level_max_list_fold (level_succ_path) rest)))))
 (fun (x : Level) (y : Level) (_ : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into x rest)) (natMax (level_succ_path x) (level_max_list_fold (level_succ_path) rest))) (_ : forall (rest : ListType Level), @Eq Nat (level_max_list_fold (level_succ_path) (level_flatten_max_into y rest)) (natMax (level_succ_path y) (level_max_list_fold (level_succ_path) rest))) => fun (rest : ListType Level) => @Eq.refl Nat (natMax (level_succ_path (Level.imax x y)) (level_max_list_fold (level_succ_path) rest)))
 (fun (n : Name) => fun (rest : ListType Level) => @Eq.refl Nat (natMax (level_succ_path (Level.param n)) (level_max_list_fold (level_succ_path) rest))) a",
        "Actual max-only flattening preserves path maxima, including its accumulator suffix.",
    ),
    (
        r"def level_flatten_raw_path  (a : Level) :
 @Eq Nat (level_succ_path (level_raw_max_args (level_flatten_max a))) (level_succ_path a) :=
 Eq.trans Nat (level_succ_path (level_raw_max_args (level_flatten_max a)))
 (level_max_list_fold (level_succ_path) (level_flatten_max a)) (level_succ_path a)
 (level_raw_max_args_path (level_flatten_max a))
 (Eq.trans Nat (level_max_list_fold (level_succ_path) (level_flatten_max a))
  (natMax (level_succ_path a) Nat.zero) (level_succ_path a)
  (level_flatten_into_path a (@ListType.nil Level))
  (ugeq_natMax_absorb_left (level_succ_path a) Nat.zero (le_zero_n (level_succ_path a))))",
        "Flatten followed by the actual raw fold preserves path count for every raw Level, with no smart normalization premise.",
    ),
];

const RESTORE: &[(&str, &str)] = &[
    (
        r"def level_add_zero_map (xs : ListType Level) :
 @Eq (ListType Level) (mapLL (fun (a : Level) => level_add_offset Nat.zero a) xs) xs :=
 @ListType.rec Level
 (fun (ys : ListType Level) => @Eq (ListType Level) (mapLL (fun (a : Level) => level_add_offset Nat.zero a) ys) ys)
 (@Eq.refl (ListType Level) (@ListType.nil Level))
 (fun (x : Level) (rest : ListType Level)
 (ih : @Eq (ListType Level) (mapLL (fun (a : Level) => level_add_offset Nat.zero a) rest) rest) =>
  Eq.cong (ListType Level) (ListType Level) (fun (ys : ListType Level) => @ListType.cons Level x ys)
   (mapLL (fun (a : Level) => level_add_offset Nat.zero a) rest) rest ih) xs",
        "Zero offset mapping is the actual identity, proved structurally rather than assumed from the source's skipped loop.",
    ),
    (
        r"def level_max_restore_zero (xs : ListType Level) :
 @Eq Level (level_max_restore Nat.zero xs) (level_raw_max_args xs) :=
 Eq.cong (ListType Level) Level (fun (ys : ListType Level) => level_raw_max_args ys)
 (mapLL (fun (a : Level) => level_add_offset Nat.zero a) xs) xs (level_add_zero_map xs)",
        "The simplified mathematical tail has exactly the source zero-offset skip branch's output, without claiming the same allocation trace.",
    ),
    (
        r"def level_raw_max_from_restore_eval (n : Nat) (rho : Name -> Nat) (xs : ListType Level) : forall (a : Level), @Eq Nat (evalL rho (level_raw_max_from (level_add_offset n a) (mapLL (fun (u : Level) => level_add_offset n u) xs))) (Nat.add (evalL rho (level_raw_max_from a xs)) n) :=
 @ListType.rec Level (fun (ys : ListType Level) => forall (a : Level), @Eq Nat (evalL rho (level_raw_max_from (level_add_offset n a) (mapLL (fun (u : Level) => level_add_offset n u) ys))) (Nat.add (evalL rho (level_raw_max_from a ys)) n))
 (fun (a : Level) => level_add_offset_eval n a rho)
 (fun (x : Level) (rest : ListType Level) (ih : forall (a : Level), @Eq Nat (evalL rho (level_raw_max_from (level_add_offset n a) (mapLL (fun (u : Level) => level_add_offset n u) rest))) (Nat.add (evalL rho (level_raw_max_from a rest)) n)) =>
  fun (a : Level) =>
   Eq.trans Nat
    (natMax (evalL rho (level_add_offset n a)) (evalL rho (level_raw_max_from (level_add_offset n x) (mapLL (fun (u : Level) => level_add_offset n u) rest))))
    (natMax (Nat.add (evalL rho a) n) (Nat.add (evalL rho (level_raw_max_from x rest)) n))
    (Nat.add (natMax (evalL rho a) (evalL rho (level_raw_max_from x rest))) n)
    (universe_bridge_congr2 Nat Nat Nat (fun (p : Nat) (q : Nat) => natMax p q)
     (evalL rho (level_add_offset n a)) (Nat.add (evalL rho a) n)
     (evalL rho (level_raw_max_from (level_add_offset n x) (mapLL (fun (u : Level) => level_add_offset n u) rest)))
     (Nat.add (evalL rho (level_raw_max_from x rest)) n)
     (level_add_offset_eval n a rho) (ih x))
    (offset_natMax_add_right (evalL rho a) (evalL rho (level_raw_max_from x rest)) n)) xs",
        "Actual nonempty raw-fold induction distributes the offset in denotation, using the derived max/add law.",
    ),
    (
        r"def level_max_restore_eval (n : Nat) (rho : Name -> Nat) (xs : ListType Level) : @Eq Bool (level_list_nonempty xs) Bool.true -> @Eq Nat (evalL rho (level_max_restore n xs)) (Nat.add (evalL rho (level_raw_max_args xs)) n) :=
 @ListType.rec Level (fun (ys : ListType Level) => @Eq Bool (level_list_nonempty ys) Bool.true -> @Eq Nat (evalL rho (level_max_restore n ys)) (Nat.add (evalL rho (level_raw_max_args ys)) n))
 (fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq Nat Nat.zero (Nat.add Nat.zero n)) h)
 (fun (x : Level) (rest : ListType Level) (_ : @Eq Bool (level_list_nonempty rest) Bool.true -> @Eq Nat (evalL rho (level_max_restore n rest)) (Nat.add (evalL rho (level_raw_max_args rest)) n)) =>
  fun (_ : @Eq Bool Bool.true Bool.true) => level_raw_max_from_restore_eval n rho rest x) xs",
        "The actual complete restore/empty-guard/raw-fold tail obeys offset distribution in denotation only under its proved nonempty input condition.",
    ),
    (
        r"def level_flatten_restore_eval (n : Nat) (rho : Name -> Nat) (a : Level) :
 @Eq Nat (evalL rho (level_max_restore n (level_flatten_max a))) (Nat.add (evalL rho a) n) :=
 Eq.trans Nat (evalL rho (level_max_restore n (level_flatten_max a)))
 (Nat.add (evalL rho (level_raw_max_args (level_flatten_max a))) n) (Nat.add (evalL rho a) n)
 (level_max_restore_eval n rho (level_flatten_max a) (level_flatten_into_nonempty a (@ListType.nil Level)))
 (Eq.cong Nat Nat (fun (k : Nat) => Nat.add k n) (evalL rho (level_raw_max_args (level_flatten_max a))) (evalL rho a)
  (level_flatten_raw_eval rho a))",
        "Actual flattening discharges nonemptiness and composes with the actual offset tail's denotation theorem.",
    ),
    (
        r"def level_raw_max_from_restore_path (n : Nat)  (xs : ListType Level) : forall (a : Level), @Eq Nat (level_succ_path (level_raw_max_from (level_add_offset n a) (mapLL (fun (u : Level) => level_add_offset n u) xs))) (Nat.add (level_succ_path (level_raw_max_from a xs)) n) :=
 @ListType.rec Level (fun (ys : ListType Level) => forall (a : Level), @Eq Nat (level_succ_path (level_raw_max_from (level_add_offset n a) (mapLL (fun (u : Level) => level_add_offset n u) ys))) (Nat.add (level_succ_path (level_raw_max_from a ys)) n))
 (fun (a : Level) => level_add_offset_path n a )
 (fun (x : Level) (rest : ListType Level) (ih : forall (a : Level), @Eq Nat (level_succ_path (level_raw_max_from (level_add_offset n a) (mapLL (fun (u : Level) => level_add_offset n u) rest))) (Nat.add (level_succ_path (level_raw_max_from a rest)) n)) =>
  fun (a : Level) =>
   Eq.trans Nat
    (natMax (level_succ_path (level_add_offset n a)) (level_succ_path (level_raw_max_from (level_add_offset n x) (mapLL (fun (u : Level) => level_add_offset n u) rest))))
    (natMax (Nat.add (level_succ_path a) n) (Nat.add (level_succ_path (level_raw_max_from x rest)) n))
    (Nat.add (natMax (level_succ_path a) (level_succ_path (level_raw_max_from x rest))) n)
    (universe_bridge_congr2 Nat Nat Nat (fun (p : Nat) (q : Nat) => natMax p q)
     (level_succ_path (level_add_offset n a)) (Nat.add (level_succ_path a) n)
     (level_succ_path (level_raw_max_from (level_add_offset n x) (mapLL (fun (u : Level) => level_add_offset n u) rest)))
     (Nat.add (level_succ_path (level_raw_max_from x rest)) n)
     (level_add_offset_path n a ) (ih x))
    (offset_natMax_add_right (level_succ_path a) (level_succ_path (level_raw_max_from x rest)) n)) xs",
        "Actual nonempty raw-fold induction distributes the offset in path count, using the derived max/add law.",
    ),
    (
        r"def level_max_restore_path (n : Nat)  (xs : ListType Level) : @Eq Bool (level_list_nonempty xs) Bool.true -> @Eq Nat (level_succ_path (level_max_restore n xs)) (Nat.add (level_succ_path (level_raw_max_args xs)) n) :=
 @ListType.rec Level (fun (ys : ListType Level) => @Eq Bool (level_list_nonempty ys) Bool.true -> @Eq Nat (level_succ_path (level_max_restore n ys)) (Nat.add (level_succ_path (level_raw_max_args ys)) n))
 (fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq Nat Nat.zero (Nat.add Nat.zero n)) h)
 (fun (x : Level) (rest : ListType Level) (_ : @Eq Bool (level_list_nonempty rest) Bool.true -> @Eq Nat (level_succ_path (level_max_restore n rest)) (Nat.add (level_succ_path (level_raw_max_args rest)) n)) =>
  fun (_ : @Eq Bool Bool.true Bool.true) => level_raw_max_from_restore_path n rest x) xs",
        "The actual complete restore/empty-guard/raw-fold tail obeys offset distribution in path count only under its proved nonempty input condition.",
    ),
    (
        r"def level_flatten_restore_path (n : Nat)  (a : Level) :
 @Eq Nat (level_succ_path (level_max_restore n (level_flatten_max a))) (Nat.add (level_succ_path a) n) :=
 Eq.trans Nat (level_succ_path (level_max_restore n (level_flatten_max a)))
 (Nat.add (level_succ_path (level_raw_max_args (level_flatten_max a))) n) (Nat.add (level_succ_path a) n)
 (level_max_restore_path n (level_flatten_max a) (level_flatten_into_nonempty a (@ListType.nil Level)))
 (Eq.cong Nat Nat (fun (k : Nat) => Nat.add k n) (level_succ_path (level_raw_max_args (level_flatten_max a))) (level_succ_path a)
  (level_flatten_raw_path a))",
        "Actual flattening discharges nonemptiness and composes with the actual offset tail's created-result budget theorem.",
    ),
    (
        r"def level_max_restore_sem (n : Nat) (xs : ListType Level)
 (hne : @Eq Bool (level_list_nonempty xs) Bool.true) :
 levelEqSem (level_max_restore n xs) (level_add_offset n (level_raw_max_args xs)) :=
 fun (rho : Name -> Nat) =>
 Eq.trans Nat (evalL rho (level_max_restore n xs)) (Nat.add (evalL rho (level_raw_max_args xs)) n)
 (evalL rho (level_add_offset n (level_raw_max_args xs)))
 (level_max_restore_eval n rho xs hne)
 (Eq.symm Nat (evalL rho (level_add_offset n (level_raw_max_args xs))) (Nat.add (evalL rho (level_raw_max_args xs)) n)
  (level_add_offset_eval n (level_raw_max_args xs) rho))",
        "Real nonempty normalization-tail output is semantically equal to adding the offset outside the raw join; not a theorem about the entire normalization pipeline.",
    ),
    (
        r"def level_flatten_restore_sem (n : Nat) (a : Level) :
 levelEqSem (level_max_restore n (level_flatten_max a)) (level_add_offset n a) :=
 fun (rho : Name -> Nat) =>
 Eq.trans Nat (evalL rho (level_max_restore n (level_flatten_max a))) (Nat.add (evalL rho a) n)
 (evalL rho (level_add_offset n a))
 (level_flatten_restore_eval n rho a)
 (Eq.symm Nat (evalL rho (level_add_offset n a)) (Nat.add (evalL rho a) n) (level_add_offset_eval n a rho))",
        "Unconditional denotation of the source-shaped max-only flatten/offset/raw-fold composition, with actual nonemptiness derived.",
    ),
    (
        r"def LevelListPathBudget (cap : Nat) (n : Nat) (xs : ListType Level) : Prop :=
 @ListType.rec Level (fun (_ : ListType Level) => Prop) (Le Nat.zero cap)
 (fun (x : Level) (_ : ListType Level) (inside : Prop) =>
  UOffsetAnd (Le (Nat.add (level_succ_path x) n) cap) inside) xs",
        "Input-only list budget: each original member's path count PLUS the to-be-added offset is within cap. No bound on a created output is assumed.",
    ),
    (
        r"def level_mapped_path_budget (cap : Nat) (n : Nat) (xs : ListType Level) : LevelListPathBudget cap n xs ->
 Le (level_max_list_fold level_succ_path (mapLL (fun (u : Level) => level_add_offset n u) xs)) cap :=
 @ListType.rec Level (fun (ys : ListType Level) => LevelListPathBudget cap n ys ->
 Le (level_max_list_fold level_succ_path (mapLL (fun (u : Level) => level_add_offset n u) ys)) cap)
 (fun (h : Le Nat.zero cap) => h)
 (fun (x : Level) (rest : ListType Level) (ih : LevelListPathBudget cap n rest ->
 Le (level_max_list_fold level_succ_path (mapLL (fun (u : Level) => level_add_offset n u) rest)) cap) =>
  fun (h : LevelListPathBudget cap n (@ListType.cons Level x rest)) =>
  ugeq_natMax_upper (level_succ_path (level_add_offset n x))
   (level_max_list_fold level_succ_path (mapLL (fun (u : Level) => level_add_offset n u) rest)) cap
   (Eq.substType Nat (fun (k : Nat) => Le k cap) (Nat.add (level_succ_path x) n) (level_succ_path (level_add_offset n x))
    (Eq.symm Nat (level_succ_path (level_add_offset n x)) (Nat.add (level_succ_path x) n) (level_add_offset_path n x))
    (uoffset_and_left (Le (Nat.add (level_succ_path x) n) cap) (LevelListPathBudget cap n rest) h))
   (ih (uoffset_and_right (Le (Nat.add (level_succ_path x) n) cap) (LevelListPathBudget cap n rest) h))) xs",
        "Actual map/fold induction proves the maximum budget of all created members from the input sum budgets.",
    ),
    (
        r"def level_max_restore_offsets (cap : Nat) (n : Nat) (xs : ListType Level)
 (h : LevelListPathBudget cap n xs) : LevelOffsetsBounded cap (level_max_restore n xs) :=
 level_succ_path_implies_offsets (level_max_restore n xs) cap
 (Eq.substType Nat (fun (k : Nat) => Le k cap)
  (level_max_list_fold level_succ_path (mapLL (fun (u : Level) => level_add_offset n u) xs))
  (level_succ_path (level_max_restore n xs))
  (Eq.symm Nat (level_succ_path (level_max_restore n xs))
   (level_max_list_fold level_succ_path (mapLL (fun (u : Level) => level_add_offset n u) xs))
   (level_raw_max_args_path (mapLL (fun (u : Level) => level_add_offset n u) xs)))
  (level_mapped_path_budget cap n xs h))",
        "Actual input-only member budgets imply every-subterm comparator bounds on the created restore-tail output, including its empty guard.",
    ),
    (
        r"def level_flatten_restore_offsets (cap : Nat) (n : Nat) (a : Level)
 (h : Le (Nat.add (level_succ_path a) n) cap) :
 LevelOffsetsBounded cap (level_max_restore n (level_flatten_max a)) :=
 level_succ_path_implies_offsets (level_max_restore n (level_flatten_max a)) cap
 (Eq.substType Nat (fun (k : Nat) => Le k cap)
  (Nat.add (level_succ_path a) n) (level_succ_path (level_max_restore n (level_flatten_max a)))
  (Eq.symm Nat (level_succ_path (level_max_restore n (level_flatten_max a))) (Nat.add (level_succ_path a) n)
   (level_flatten_restore_path n a)) h)",
        "Original path-plus-offset budget, not separate spine bounds, establishes the actual flattened/restored output invariant.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def offset_spine_input : Level := level_add_offset (Nat.succ Nat.zero) ugeq_join_left",
        "Source-shaped input succ(Max(succ u,v)): all individual spines have length one, but a root-to-leaf path has two successors.",
    ),
    (
        r"def offset_spine_output : Level := level_max_restore (Nat.succ Nat.zero) (level_flatten_max ugeq_join_left)",
        "Actual flatten/restore/right-fold output, not an assumed result of the unmodeled full normalizer.",
    ),
    (
        r"def offset_spine_output_exact :
 @Eq Level offset_spine_output (Level.max (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_v)) :=
 @Eq.refl Level (Level.max (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_v))",
        "Positive outer-offset caller computes the exact distributed structure, including the newly length-two spine.",
    ),
    (
        r"def offset_spine_semantic : levelEqSem offset_spine_output offset_spine_input :=
 level_flatten_restore_sem (Nat.succ Nat.zero) ugeq_join_left",
        "Actual universal tail theorem is consumed by the nonzero created-output caller.",
    ),
    (
        r"def offset_spine_weak_input : LevelOffsetsBounded (Nat.succ Nat.zero) offset_spine_input :=
 uoffset_and_intro (Le (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (LevelOffsetsBounded (Nat.succ Nat.zero) ugeq_join_left)
 (@Le.refl (Nat.succ Nat.zero)) ugeq_cap_join_left_bound",
        "The old every-separate-spine invariant is genuinely inhabited for the problematic original input.",
    ),
    (
        r"def offset_spine_weak_output_false (h : LevelOffsetsBounded (Nat.succ Nat.zero) offset_spine_output) : Empty :=
 ugeq_cap_boundary_bound_false
 (level_offsets_bound_max_left (Nat.succ Nat.zero) (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_v) h)",
        "Actual restored output violates the old cap-one invariant; offset redistribution cannot silently inherit original separate-spine bounds.",
    ),
    (
        r"def offset_spine_weak_preservation_false
 (preserves : forall (n : Nat) (a : Level), LevelOffsetsBounded (Nat.succ Nat.zero) (level_add_offset n a) ->
  LevelOffsetsBounded (Nat.succ Nat.zero) (level_max_restore n (level_flatten_max a))) : Empty :=
 offset_spine_weak_output_false (preserves (Nat.succ Nat.zero) ugeq_join_left offset_spine_weak_input)",
        "Constructively refutes the proposed unrestricted preservation of the old invariant by this actual source-shaped tail.",
    ),
    (
        r"def offset_spine_input_path : @Eq Nat (level_succ_path offset_spine_input) (Nat.succ (Nat.succ Nat.zero)) :=
 @Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))",
        "Path budget records the otherwise hidden sum at the original input.",
    ),
    (
        r"def offset_spine_output_path : @Eq Nat (level_succ_path offset_spine_output) (Nat.succ (Nat.succ Nat.zero)) :=
 level_flatten_restore_path (Nat.succ Nat.zero) ugeq_join_left",
        "Actual output budget follows the proved tail path equation, not a per-output bound premise.",
    ),
    (
        r"def offset_spine_safe_output : LevelOffsetsBounded (Nat.succ (Nat.succ Nat.zero)) offset_spine_output :=
 level_flatten_restore_offsets (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) ugeq_join_left (@Le.refl (Nat.succ (Nat.succ Nat.zero)))",
        "Original path-plus-offset sum at cap two derives every created-output comparator bound.",
    ),
    (
        r"def offset_spine_member_budget :
 LevelListPathBudget (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) (level_flatten_max ugeq_join_left) :=
 uoffset_and_intro (Le (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)))
  (LevelListPathBudget (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) (@ListType.cons Level ugeq_test_v (@ListType.nil Level)))
  (@Le.refl (Nat.succ (Nat.succ Nat.zero)))
  (uoffset_and_intro (Le (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero))) (Le Nat.zero (Nat.succ (Nat.succ Nat.zero)))
   (@Le.step (Nat.succ Nat.zero) (Nat.succ Nat.zero) (@Le.refl (Nat.succ Nat.zero))) (le_zero_n (Nat.succ (Nat.succ Nat.zero))))",
        "Actual pre-restoration members also inhabit the input-only sum-budget interface.",
    ),
    (
        r"def offset_spine_safe_from_members : LevelOffsetsBounded (Nat.succ (Nat.succ Nat.zero)) offset_spine_output :=
 level_max_restore_offsets (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) (level_flatten_max ugeq_join_left) offset_spine_member_budget",
        "Member-budget theorem has a concrete created-output caller, not only a schematic signature.",
    ),
    (
        r"def offset_spine_comparison :
 @Eq Bool (level_geq_cap_core (Nat.succ (Nat.succ Nat.zero)) offset_spine_output (Level.succ (Level.succ ugeq_test_u))) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Existing actual capped comparator is invoked on the newly constructed distributed output.",
    ),
    (
        r"def offset_spine_capped_caller : levelLeqSem (Level.succ (Level.succ ugeq_test_u)) offset_spine_output :=
 level_geq_cap_core_sound (Nat.succ (Nat.succ Nat.zero)) offset_spine_output (Level.succ (Level.succ ugeq_test_u))
 offset_spine_safe_output ugeq_cap_two_bound offset_spine_comparison",
        "Derived intermediate bound is consumed by the existing capped-comparator soundness theorem.",
    ),
    (
        r"def offset_spine_sort_caller (R : RedEnv) :
 DefEqIn R (KExpr.sort offset_spine_output) (KExpr.sort offset_spine_input) :=
 @DefEqIn.levels R (KExpr.sort offset_spine_output) (KExpr.sort offset_spine_input)
 (KExprUniverseEq.sort offset_spine_output offset_spine_input offset_spine_semantic)",
        "Actual semantic conversion caller connects offset redistribution to universe-aware Sort equality without assuming whole-normalizer correctness.",
    ),
    (
        r"def offset_spine_flatten_order :
 @Eq (ListType Level) (level_flatten_max (Level.max (Level.max ugeq_test_u ugeq_test_v) ugeq_test_w))
 (@ListType.cons Level ugeq_test_u (@ListType.cons Level ugeq_test_v (@ListType.cons Level ugeq_test_w (@ListType.nil Level)))) :=
 @Eq.refl (ListType Level) (@ListType.cons Level ugeq_test_u (@ListType.cons Level ugeq_test_v (@ListType.cons Level ugeq_test_w (@ListType.nil Level))))",
        "Nested raw Max flattening preserves exact left-to-right order.",
    ),
    (
        r"def offset_spine_flatten_barriers :
 @Eq (ListType Level) (level_flatten_max (Level.max (Level.succ (Level.max ugeq_test_u ugeq_test_v)) (Level.imax ugeq_test_u ugeq_test_v)))
 (@ListType.cons Level (Level.succ (Level.max ugeq_test_u ugeq_test_v))
  (@ListType.cons Level (Level.imax ugeq_test_u ugeq_test_v) (@ListType.nil Level))) :=
 @Eq.refl (ListType Level) (@ListType.cons Level (Level.succ (Level.max ugeq_test_u ugeq_test_v))
  (@ListType.cons Level (Level.imax ugeq_test_u ugeq_test_v) (@ListType.nil Level)))",
        "Source-shaped flattening does not recurse through Succ(Max) or IMax, so it cannot invent earlier distribution.",
    ),
    (
        r"def offset_spine_empty_sem_false
 (h : levelEqSem (level_max_restore (Nat.succ Nat.zero) (@ListType.nil Level))
  (level_add_offset (Nat.succ Nat.zero) (level_raw_max_args (@ListType.nil Level)))) : Empty :=
 nat_zero_ne_succ Nat.zero Empty (h (fun (_ : Name) => Nat.zero))",
        "Empty-tail offset distribution is genuinely false: actual tail Zero versus successor Zero.",
    ),
    (
        r"def offset_spine_empty_path_false
 (h : @Eq Nat (level_succ_path (level_max_restore (Nat.succ Nat.zero) (@ListType.nil Level)))
  (Nat.add (level_succ_path (level_raw_max_args (@ListType.nil Level))) (Nat.succ Nat.zero))) : Empty :=
 nat_zero_ne_succ Nat.zero Empty h",
        "The analogous unqualified budget equation is also false on the actual empty branch.",
    ),
    (
        r"def offset_spine_unqualified_distribution_false
 (h : forall (n : Nat) (xs : ListType Level),
  levelEqSem (level_max_restore n xs) (level_add_offset n (level_raw_max_args xs))) : Empty :=
 offset_spine_empty_sem_false (h (Nat.succ Nat.zero) (@ListType.nil Level))",
        "Constructively refutes deleting the nonempty premise from the whole tail's denotation theorem.",
    ),
];

impl Specification {
    /// Late after the existing raw/capped universe stages; reuses le_antisymm
    /// and DefEqIn for an actual Sort-conversion caller.
    pub(super) fn add_universe_normalization_offset_spine(&mut self) -> Result<(), SpecError> {
        for (source, description) in OFFSET.iter().chain(MAX_LIST).chain(RESTORE).chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn offset_spine_tail_and_created_bounds_are_kernel_checked() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        let mut count = 0;
        for (source, _) in super::OFFSET
            .iter()
            .chain(super::MAX_LIST)
            .chain(super::RESTORE)
            .chain(super::CONTROLS)
        {
            let name = source.split_whitespace().nth(1).expect("declaration name");
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked offset-spine declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
            count += 1;
        }
        assert_eq!(count, 64);
        for source in [
            "def offset_spine_forged_weak_bound : LevelOffsetsBounded (Nat.succ Nat.zero) offset_spine_output := offset_spine_weak_input",
            "def offset_spine_forged_empty_distribution : levelEqSem (level_max_restore (Nat.succ Nat.zero) (@ListType.nil Level)) (level_add_offset (Nat.succ Nat.zero) (level_raw_max_args (@ListType.nil Level))) := fun (_rho : Name -> Nat) => @Eq.refl Nat Nat.zero",
            "def offset_spine_forged_flatten_through_succ : @Eq (ListType Level) (level_flatten_max (Level.succ (Level.max ugeq_test_u ugeq_test_v))) (@ListType.cons Level (Level.succ ugeq_test_u) (@ListType.cons Level (Level.succ ugeq_test_v) (@ListType.nil Level))) := @Eq.refl (ListType Level) (@ListType.cons Level (Level.succ ugeq_test_u) (@ListType.cons Level (Level.succ ugeq_test_v) (@ListType.nil Level)))",
        ] {
            crate::test_utils::parse_check(source).expect("negative offset control parses");
            assert!(spec.add_recursive_def(source, "Reject an unproved bound, empty distribution or incorrect flatten traversal.").is_err());
        }
    }
}
