-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained cardinality/PB-to-CNF soundness kernels for SAT-COMP work.
-- Uses small Church encodings to avoid import fragility.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_pair_clause_forbids_both
    (p : Prop) (q : Prop) :
    AyDisj (Not p) (Not q) -> p -> q -> False := by
  intro pair_clause
  intro hp
  intro hq
  exact pair_clause False
    (fun not_p => not_p hp)
    (fun not_q => not_q hq)

def AyAtLeastOne3 (a : Prop) (b : Prop) (c : Prop) :=
  AyDisj a (AyDisj b c)

def AyPairwiseAtMostOne3Cnf (a : Prop) (b : Prop) (c : Prop) :=
  AyConj
    (AyDisj (Not a) (Not b))
    (AyConj
      (AyDisj (Not a) (Not c))
      (AyDisj (Not b) (Not c)))

def AyAtMostOne3 (a : Prop) (b : Prop) (c : Prop) :=
  AyConj
    (a -> b -> False)
    (AyConj
      (a -> c -> False)
      (b -> c -> False))

def AyExactlyOne3 (a : Prop) (b : Prop) (c : Prop) :=
  AyConj (AyAtLeastOne3 a b c) (AyAtMostOne3 a b c)

def AyExactlyOne3Cnf (a : Prop) (b : Prop) (c : Prop) :=
  AyConj (AyAtLeastOne3 a b c) (AyPairwiseAtMostOne3Cnf a b c)

theorem ay_pairwise_amo3_sound
    (a : Prop) (b : Prop) (c : Prop) :
    AyPairwiseAtMostOne3Cnf a b c -> AyAtMostOne3 a b c := by
  intro pairwise
  intro result
  intro build
  exact pairwise result
    (fun ab_clause tail =>
      tail result
        (fun ac_clause bc_clause =>
          build
            (ay_pair_clause_forbids_both a b ab_clause)
            (ay_conj_intro
              (a -> c -> False)
              (b -> c -> False)
              (ay_pair_clause_forbids_both a c ac_clause)
              (ay_pair_clause_forbids_both b c bc_clause))))

theorem ay_exactly_one3_decompose_forward
    (a : Prop) (b : Prop) (c : Prop) :
    AyExactlyOne3 a b c ->
    AyConj (AyAtLeastOne3 a b c) (AyAtMostOne3 a b c) := by
  intro exactly_one
  exact exactly_one

theorem ay_exactly_one3_decompose_backward
    (a : Prop) (b : Prop) (c : Prop) :
    AyConj (AyAtLeastOne3 a b c) (AyAtMostOne3 a b c) ->
    AyExactlyOne3 a b c := by
  intro decomposed
  exact decomposed

theorem ay_exactly_one3_decompose_equisat
    (a : Prop) (b : Prop) (c : Prop) :
    AyEquisat
      (AyExactlyOne3 a b c)
      (AyConj (AyAtLeastOne3 a b c) (AyAtMostOne3 a b c)) := by
  exact ay_conj_intro
    (AyExactlyOne3 a b c ->
      AyConj (AyAtLeastOne3 a b c) (AyAtMostOne3 a b c))
    (AyConj (AyAtLeastOne3 a b c) (AyAtMostOne3 a b c) ->
      AyExactlyOne3 a b c)
    (ay_exactly_one3_decompose_forward a b c)
    (ay_exactly_one3_decompose_backward a b c)

theorem ay_exactly_one3_pairwise_cnf_sound
    (a : Prop) (b : Prop) (c : Prop) :
    AyExactlyOne3Cnf a b c -> AyExactlyOne3 a b c := by
  intro cnf
  intro result
  intro build
  exact cnf result
    (fun at_least_one pairwise_amo =>
      build at_least_one
        (ay_pairwise_amo3_sound a b c pairwise_amo))
