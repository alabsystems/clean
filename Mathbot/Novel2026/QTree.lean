-- QTree: a 5-constructor recursive structure invented 2026-05-26
-- for this session. Has not been published anywhere prior to this
-- file's creation timestamp.

set_option autoImplicit false

namespace Novel2026

inductive QTree where
  | seed     : QTree
  | branch   : QTree → QTree → QTree
  | echo     : QTree → QTree
  | clip     : QTree → QTree
  | crown    : QTree → QTree → QTree → QTree

namespace QTree

def size : QTree → Nat
  | seed         => 1
  | branch a b   => 1 + size a + size b
  | echo x       => 1 + size x
  | clip x       => 1 + size x
  | crown a b c  => 1 + size a + size b + size c

def echoes : QTree → Nat
  | seed         => 0
  | branch a b   => echoes a + echoes b
  | echo x       => 1 + echoes x
  | clip x       => echoes x
  | crown a b c  => echoes a + echoes b + echoes c

def clips : QTree → Nat
  | seed         => 0
  | branch a b   => clips a + clips b
  | echo x       => clips x
  | clip x       => 1 + clips x
  | crown a b c  => clips a + clips b + clips c

-- Theorem T-NOVEL-1: echo count is bounded by size minus one.
theorem echoes_lt_size : ∀ q : QTree, echoes q < size q := by
  intro q
  induction q with
  | seed => decide
  | branch a b iha ihb => simp [echoes, size]; omega
  | echo x ih => simp [echoes, size]; omega
  | clip x ih => simp [echoes, size]; omega
  | crown a b c iha ihb ihc => simp [echoes, size]; omega

-- Theorem T-NOVEL-2: total of echoes and clips is bounded by size minus one.
theorem echoes_plus_clips_lt_size : ∀ q : QTree, echoes q + clips q < size q := by
  intro q
  induction q with
  | seed => decide
  | branch a b iha ihb => simp [echoes, clips, size]; omega
  | echo x ih => simp [echoes, clips, size]; omega
  | clip x ih => simp [echoes, clips, size]; omega
  | crown a b c iha ihb ihc => simp [echoes, clips, size]; omega

-- Theorem T-NOVEL-3: if the QTree universe is restricted to seed and
-- branch only, then every tree has zero echoes and clips. The hypothesis
-- as stated is *globally* about the type — and since `echo seed : QTree`
-- exists, the hypothesis is vacuous, hence the theorem holds by ex falso.
theorem branch_only_has_no_echoes_or_clips :
    ∀ q : QTree, (∀ r : QTree, r = seed ∨ (∃ a b, r = branch a b)) →
      echoes q = 0 ∧ clips q = 0 := by
  intro q h
  exfalso
  rcases h (echo seed) with heq | ⟨a, b, heq⟩
  · cases heq
  · cases heq

end QTree
end Novel2026
