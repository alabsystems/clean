import VF5Ovf

namespace VF5
open SemR

variable {m : Module}

def EnvRel (m : Module) (ρ : Nat → Int) : List (Nat × SV) → List (Nat × Val) → Prop
  | [], [] => True
  | (x, s) :: ss, (y, v) :: vs => x = y ∧ valRel m ρ s v ∧ EnvRel m ρ ss vs
  | _, _ => False

def ValsRel (m : Module) (ρ : Nat → Int) : List SV → List Val → Prop
  | [], [] => True
  | s :: ss, v :: vs => valRel m ρ s v ∧ ValsRel m ρ ss vs
  | _, _ => False

def EnvScoped (n : Nat) (env : List (Nat × SV)) : Prop := ∀ p ∈ env, p.2.Scoped n

structure Rel (m : Module) (ρ : Nat → Int) (s : SSt) (k : Core) : Prop where
  blk : k.block = s.blk
  pc : k.pc = s.pc
  env : EnvRel m ρ s.env k.env
  sat : Sat s.cs ρ
  scE : EnvScoped s.nv s.env
  scC : CsScoped s.nv s.cs
  target : F1Target m

theorem EnvScoped.mono {n n' : Nat} {e : List (Nat × SV)} (h : EnvScoped n e) (hn : n ≤ n') :
    EnvScoped n' e := fun p hp => (h p hp).mono hn

theorem envRel_congr {ρ ρ' : Nat → Int} {n : Nat} :
    ∀ {se : List (Nat × SV)} {ce : List (Nat × Val)}, EnvScoped n se → Agree ρ ρ' n →
      EnvRel m ρ se ce → EnvRel m ρ' se ce
  | [], [], _, _, _ => trivial
  | (x, s) :: ss, (y, v) :: vs, hs, h, ⟨h1, h2, h3⟩ =>
    ⟨h1, valRel_congr (hs (x, s) (List.Mem.head _)) h h2,
      envRel_congr (fun p hp => hs p (List.Mem.tail _ hp)) h h3⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h

theorem valsRel_congr {ρ ρ' : Nat → Int} {n : Nat} :
    ∀ {ss : List SV} {vs : List Val}, (∀ s ∈ ss, s.Scoped n) → Agree ρ ρ' n →
      ValsRel m ρ ss vs → ValsRel m ρ' ss vs
  | [], [], _, _, _ => trivial
  | s :: ss, v :: vs, hs, h, ⟨h1, h2⟩ =>
    ⟨valRel_congr (hs s (List.Mem.head _)) h h1,
      valsRel_congr (fun p hp => hs p (List.Mem.tail _ hp)) h h2⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h

theorem lookup_rel {ρ : Nat → Int} :
    ∀ {se : List (Nat × SV)} {ce : List (Nat × Val)} {x : Nat} {s : SV}, EnvRel m ρ se ce →
      slook se x = some s → ∃ v, lookupEnv ce x = some v ∧ valRel m ρ s v
  | [], [], _, _, _, h => nomatch h
  | (y, s') :: ss, (z, v) :: vs, x, s, ⟨h1, h2, h3⟩, h => by
    subst h1
    simp only [slook] at h
    simp only [lookupEnv]
    split at h
    · next hy => simp only [Option.some.injEq] at h; subst h; simp [hy]; exact h2
    · next hy => simp only [hy]; exact lookup_rel h3 h
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h

theorem envOK_of_rel {ρ : Nat → Int} :
    ∀ {se : List (Nat × SV)} {ce : List (Nat × Val)}, EnvRel m ρ se ce → EnvOK m ce
  | [], [], _ => fun _ h => nomatch h
  | (y, s') :: ss, (z, v) :: vs, ⟨_, h2, h3⟩ => by
    intro p hp
    cases hp with
    | head => exact valRel_ok h2
    | tail _ hp => exact envOK_of_rel h3 p hp
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem getV_rel {ρ : Nat → Int} {s : SSt} {k : Core} {x : Nat} {sv : SV} (h : Rel m ρ s k)
    (hx : slook s.env x = some sv) : ∃ v, getV k x = .ok v ∧ valRel m ρ sv v := by
  obtain ⟨v, hv, hr⟩ := lookup_rel h.env hx
  exact ⟨v, by simp [getV, hv], hr⟩

theorem getVs_rel {ρ : Nat → Int} {s : SSt} {k : Core} (h : Rel m ρ s k) :
    ∀ {xs : List Nat} {svs : List SV}, slooks s.env xs = some svs →
      ∃ vs, getVs k xs = .ok vs ∧ ValsRel m ρ svs vs
  | [], svs, hx => by
    simp only [slooks, Option.some.injEq] at hx; subst hx; exact ⟨[], rfl, trivial⟩
  | x :: xs, svs, hx => by
    simp only [slooks] at hx
    split at hx
    · next s1 ss h1 h2 =>
      simp only [Option.some.injEq] at hx; subst hx
      obtain ⟨v, hv, hr⟩ := getV_rel h h1
      obtain ⟨vs, hvs, hrs⟩ := getVs_rel h h2
      exact ⟨v :: vs, by simp [getVs, hv, hvs, bind, R.bind, pure], hr, hrs⟩
    · exact nomatch hx

theorem envRel_append {ρ : Nat → Int} :
    ∀ {a : List (Nat × SV)} {b : List (Nat × Val)} {c : List (Nat × SV)} {d : List (Nat × Val)},
      EnvRel m ρ a b → EnvRel m ρ c d → EnvRel m ρ (a ++ c) (b ++ d)
  | [], [], _, _, _, h => h
  | (x, s) :: ss, (y, v) :: vs, _, _, ⟨h1, h2, h3⟩, h => ⟨h1, h2, envRel_append h3 h⟩
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h

theorem envRel_reverse {ρ : Nat → Int} :
    ∀ {a : List (Nat × SV)} {b : List (Nat × Val)}, EnvRel m ρ a b → EnvRel m ρ a.reverse b.reverse
  | [], [], h => h
  | (x, s) :: ss, (y, v) :: vs, ⟨h1, h2, h3⟩ => by
    simp only [List.reverse_cons]
    exact envRel_append (envRel_reverse h3) ⟨h1, h2, trivial⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem envRel_zip {ρ : Nat → Int} :
    ∀ (rs : List Nat) {ss : List SV} {vs : List Val}, ValsRel m ρ ss vs →
      EnvRel m ρ (rs.zip ss) (rs.zip vs)
  | [], _, _, _ => by simp [EnvRel]
  | _ :: _, [], [], _ => by simp [EnvRel]
  | r :: rs, s :: ss, v :: vs, ⟨h1, h2⟩ => ⟨rfl, h1, envRel_zip rs h2⟩
  | _ :: _, [], _ :: _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h

theorem valsRel_length {ρ : Nat → Int} :
    ∀ {ss : List SV} {vs : List Val}, ValsRel m ρ ss vs → ss.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [valsRel_length h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem valsRel_of_zip {ρ : Nat → Int} :
    ∀ {ss : List SV} {vs : List Val}, ss.length = vs.length →
      (∀ p ∈ ss.zip vs, valRel m ρ p.1 p.2) → ValsRel m ρ ss vs
  | [], [], _, _ => trivial
  | s :: ss, v :: vs, hl, h =>
    ⟨h (s, v) (List.Mem.head _),
      valsRel_of_zip (by simpa using hl) (fun p hp => h p (List.Mem.tail _ hp))⟩
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl

theorem envScoped_zip {n : Nat} (rs : List Nat) {ss : List SV} (h : ∀ s ∈ ss, s.Scoped n) :
    EnvScoped n (rs.zip ss).reverse := by
  intro p hp
  rw [List.mem_reverse] at hp
  exact h p.2 (List.of_mem_zip hp).2

theorem envScoped_append {n : Nat} {a b : List (Nat × SV)} (ha : EnvScoped n a) (hb : EnvScoped n b) :
    EnvScoped n (a ++ b) := by
  intro p hp; rcases List.mem_append.mp hp with h | h; exact ha p h; exact hb p h

@[simp] theorem R_bind_ok {α β : Type} (a : α) (f : α → R β) : (R.ok a >>= f) = f a := rfl
@[simp] theorem R_bind_stop {α β : Type} (o : Out) (f : α → R β) : ((R.stop o : R α) >>= f) = .stop o := rfl
@[simp] theorem R_pure {α : Type} (a : α) : (pure a : R α) = .ok a := rfl

/-- The general continuation lemma: the branch the concrete values take is in
    the list, so its continuation's obligations are among the node's. -/
theorem contBrs_cover {cont : SSt → List (List Cons)} {s : SSt} {node : Node} {bs : List Br}
    {br : Br} {vs : List Val} {ρ : Nat → Int} {k : Core}
    (hob : ∀ p ∈ contBrs cont s node bs, Unsat p) (hbr : br ∈ bs) (hcov : BrCovers m ρ s.nv br vs)
    (hrel : Rel m ρ s k) :
    ∃ k', bindResults (next k) node vs = .ok k' ∧
      k' = { next k with env := (node.results.zip vs).reverse ++ k.env } ∧
      ∃ s' ρ', Rel m ρ' s' k' ∧ ∀ p ∈ cont s', Unsat p := by
  obtain ⟨ρ', hag, hsat, hnv, hsc, hlen, hvals, hvsc⟩ := hcov
  have htf : br.cs.any trivFalse = false := by
    cases h : br.cs.any trivFalse with
    | false => rfl
    | true =>
      rw [List.any_eq_true] at h
      obtain ⟨c, hc, hcf⟩ := h
      exact absurd (hsat c hc) (trivFalse_sound hcf)
  have hob' : ∀ p ∈ (if node.results.length == br.vals.length then
      cont { s with pc := s.pc + 1, env := (node.results.zip br.vals).reverse ++ s.env,
                    cs := s.cs ++ br.cs, nv := max s.nv br.nv }
      else FAIL), Unsat p := by
    intro p hp; apply hob; simp only [contBrs, List.mem_flatMap]; exact ⟨br, hbr, by simp only [htf]; exact hp⟩
  split at hob'
  · next hl =>
    have hl' : node.results.length = vs.length := by simpa [hlen] using hl
    refine ⟨_, by simp [bindResults, hl', next], rfl, _, ρ', ⟨?_, ?_, ?_, ?_, ?_, ?_, hrel.target⟩, hob'⟩
    · simp [next, hrel.blk]
    · simp [next, hrel.pc]
    · exact envRel_append (envRel_reverse (envRel_zip _ (valsRel_of_zip hlen hvals)))
        (envRel_congr hrel.scE hag hrel.env)
    · exact Sat.append (Sat.congr hrel.scC hag hrel.sat) hsat
    · exact envScoped_append (envScoped_zip _ (fun s hs => (hvsc s hs).mono (Nat.le_max_right _ _)))
        (hrel.scE.mono (Nat.le_max_left _ _))
    · exact CsScoped.append (hrel.scC.mono (Nat.le_max_left _ _)) (hsc.mono (Nat.le_max_right _ _))
  · exact fail_refutes hob'

end VF5
