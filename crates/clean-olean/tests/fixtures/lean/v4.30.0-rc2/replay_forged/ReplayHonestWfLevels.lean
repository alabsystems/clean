/-! `ReplayHonestWfLevels`: a WF-recursive `Sort`-valued eliminator whose function-typed
arguments VARY in the recursive call, so the WF compilation packs `⟨l, nil, step⟩` into a
`PSigma` (`revRecOn._unary`) whose universe mentions `imax (u+1) (imax (u+1) v)` — the
shape of the 2026-07 `List.reverseRecOn._unary` / `.eq_1` pair. Pinned Lean's kernel admits it. -/
universe u v

def revRecOn {α : Type u} {motive : List α → Sort v} (l : List α) (nil : motive [])
    (step : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l :=
  match l with
  | [] => nil
  | a :: l' => (List.dropLast_concat_getLast (List.cons_ne_nil a l')) ▸
    step _ _ (revRecOn (a :: l').dropLast (id nil) (fun l a h => id (step l a h)))
  termination_by l.length

theorem revRecOn_nil {α : Type u} {motive : List α → Sort v} (nil : motive [])
    (step : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    revRecOn [] nil step = nil := by
  rw [revRecOn]
