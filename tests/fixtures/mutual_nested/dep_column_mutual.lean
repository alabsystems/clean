-- Brick B4, class (88), on the pass-2 path of a `mutual` theorem block
-- (trust-ir `Proofs/TemplateProps.lean` `substTy_total` / `substTys_total`):
-- `| .node ts, h => …` with `h : ok (.node ts) = true`.
inductive T where
  | leaf : Nat → T
  | node : List T → T

mutual
def ok (k : Nat) : T → Bool
  | .leaf _ => true
  | .node ts => oks k ts
def oks (k : Nat) : List T → Bool
  | [] => true
  | t :: ts => ok k t && oks k ts
end

mutual
def sz (k : Nat) : T → Nat
  | .leaf _ => 0
  | .node ts => szs k ts
def szs (k : Nat) : List T → Nat
  | [] => 0
  | t :: ts => sz k t + szs k ts
end

mutual
theorem sz_zero (k : Nat) : ∀ t : T, ok k t = true → sz k t = 0
  | .leaf _, _ => by simp [sz]
  | .node ts, h => by
    simp only [ok] at h
    simp only [sz]
    exact szs_zero k ts h
theorem szs_zero (k : Nat) : ∀ ts : List T, oks k ts = true → szs k ts = 0
  | [], _ => by simp [szs]
  | t :: ts, h => by
    simp only [oks, Bool.and_eq_true] at h
    simp only [szs]
    rw [sz_zero k t h.1, szs_zero k ts h.2]
end
