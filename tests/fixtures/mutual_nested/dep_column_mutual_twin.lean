-- B4 twin over the mutual block: `h` in the `node` arm is about `.node ts`,
-- so it does not prove `szs ts = 1`.
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
theorem sz_one (k : Nat) : ∀ t : T, ok k t = true → sz k t = 1
  | .leaf _, _ => by simp [sz]
  | .node ts, h => by
    simp only [ok] at h
    simp only [sz]
    exact szs_one k ts h
theorem szs_one (k : Nat) : ∀ ts : List T, oks k ts = true → szs k ts = 1
  | [], _ => by simp [szs]
  | t :: ts, h => by
    simp only [oks, Bool.and_eq_true] at h
    simp only [szs]
    rw [sz_one k t h.1, szs_one k ts h.2]
end
