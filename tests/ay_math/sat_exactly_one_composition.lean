-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained exactly-one composition kernels for SAT-COMP math work.
-- Church encodings keep the package independent of staged imports.

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

def AyTwoExactlyOneTriples
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :=
  AyConj
    (AyExactlyOne3 a1 b1 c1)
    (AyExactlyOne3 a2 b2 c2)

def AyTwoExactlyOneTriplesCnf
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :=
  AyConj
    (AyExactlyOne3Cnf a1 b1 c1)
    (AyExactlyOne3Cnf a2 b2 c2)

def AyTwoPairwiseAmoTriplesCnf
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :=
  AyConj
    (AyPairwiseAtMostOne3Cnf a1 b1 c1)
    (AyPairwiseAtMostOne3Cnf a2 b2 c2)

def AyTwoAtMostOneTriples
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :=
  AyConj
    (AyAtMostOne3 a1 b1 c1)
    (AyAtMostOne3 a2 b2 c2)

theorem ay_two_exactly_one_conj_compose
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :
    AyExactlyOne3 a1 b1 c1 ->
    AyExactlyOne3 a2 b2 c2 ->
    AyTwoExactlyOneTriples a1 b1 c1 a2 b2 c2 :=
  fun first second result build => build first second

theorem ay_two_exactly_one_cnf_sound
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :
    AyTwoExactlyOneTriplesCnf a1 b1 c1 a2 b2 c2 ->
    AyTwoExactlyOneTriples a1 b1 c1 a2 b2 c2 := by
  intro cnf
  intro result
  intro build
  exact cnf result
    (fun first_cnf second_cnf =>
      build
        (ay_exactly_one3_pairwise_cnf_sound a1 b1 c1 first_cnf)
        (ay_exactly_one3_pairwise_cnf_sound a2 b2 c2 second_cnf))

theorem ay_two_pairwise_amo3_sound
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :
    AyTwoPairwiseAmoTriplesCnf a1 b1 c1 a2 b2 c2 ->
    AyTwoAtMostOneTriples a1 b1 c1 a2 b2 c2 := by
  intro pairwise
  intro result
  intro build
  exact pairwise result
    (fun first_pairwise second_pairwise =>
      build
        (ay_pairwise_amo3_sound a1 b1 c1 first_pairwise)
        (ay_pairwise_amo3_sound a2 b2 c2 second_pairwise))

theorem ay_two_exactly_one_cnf_sound_via_amo_composition
    (a1 : Prop) (b1 : Prop) (c1 : Prop)
    (a2 : Prop) (b2 : Prop) (c2 : Prop) :
    AyConj
      (AyConj
        (AyAtLeastOne3 a1 b1 c1)
        (AyAtLeastOne3 a2 b2 c2))
      (AyTwoPairwiseAmoTriplesCnf a1 b1 c1 a2 b2 c2) ->
    AyTwoExactlyOneTriples a1 b1 c1 a2 b2 c2 := by
  intro encoded
  intro result
  intro build
  exact encoded result
    (fun at_least_pair amo_pair =>
      at_least_pair result
        (fun at_least_first at_least_second =>
          amo_pair result
            (fun amo_first amo_second =>
              build
                (ay_conj_intro
                  (AyAtLeastOne3 a1 b1 c1)
                  (AyAtMostOne3 a1 b1 c1)
                  at_least_first
                  (ay_pairwise_amo3_sound a1 b1 c1 amo_first))
                (ay_conj_intro
                  (AyAtLeastOne3 a2 b2 c2)
                  (AyAtMostOne3 a2 b2 c2)
                  at_least_second
                  (ay_pairwise_amo3_sound a2 b2 c2 amo_second)))))
