/-
TrustSem.lean — RM1's relational core (Trust `docs/plans/2026-10-15-proven-core.md`
§2.2 and RM1), stated over the translator's own free monad `SOut`.

`MiniRust` is the shared canonical import of Trust's `scripts/trust_core/specr/SpecrPrelude.lean` followed by
its generated `generated/MiniRustSlice.lean`, byte for byte (the copies beside this
file; Trust's `regen.py check` compares them), inside a `noncomputable section`
(Lean's code generator does not take `SOut.rec`; the kernel does). So `SOut` here is
the type the generated MiniRust code returns, `SOut.runOracle` is the prelude's
oracle interpretation, and the MiniRust instance at the end is the generated
`MRf.Machine.step`.

* `SOut` has two choice nodes, both indexed by `Nat`: `pick` (demonic) and `predict`
  (angelic). An index past the candidates, or a candidate that fails its predicate,
  is `reject`: that resolution is not a behaviour (MiniRust's "no behaviour").
* A program is a state machine whose step is an `SOut` tree ending in
  `ok (events, inl next)` or `ok (events, inr result)`; `bad` says which results
  are UB.
* `Beh P` holds finite behaviours (`fin τ o`) and divergent ones (`div σ`: an
  infinite run, `σ k` its trace after `k` steps, finite or not).
* `run (δ, π) n P` is the executable interpretation: `n` steps, each resolved by
  the oracles exactly as `SOut.runOracle` resolves it (`stepT_runOracle`).

The four statements the plan names, as proved here:

  core_wf       no state's step is a dead end (every resolution rejected)
                → Beh P ≠ ∅   (divergence included; no finite-branching premise is
                needed, because `MustUB` and `Dead` are inductive over every branch)
  run_sound     run (δ,π) n P = fin τ o → ¬ bad o → fin τ o ∈ Beh P
  run_ub        bad o → (fin τ o ∈ Beh P ↔ ∃ δ admissible. (∀ π. ∃ n. run (δ,π) n P
                is UB or rejected) ∧ ∃ π n. run (δ,π) n P = fin τ o)
  run_adequate  fin τ o ∈ Beh P → ∃ δ π n. run (δ,π) n P = fin τ o, and
                div σ ∈ Beh P → ∀ k. ∃ δ π. run (δ,π) k P = cut (σ k)  (every prefix)

plus the committed counter-example (the naive `run_sound` fails for two casts) and
controls showing each departure from the plan's wording is needed.

Pure Lean 4 `Init` plus the slice; no `sorry`, no `native_decide`, no `partial
def`, no axiom of its own. Checked by Clean's kernel through the reference entry
(`crates/clean-olean/tests/rm1_trust_sem.rs`), closure ⊆ Ax0.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.
-/
import MiniRust

noncomputable section

namespace TrustSem

open Classical

/-! ## Oracles

An oracle answers the choice at a node from the choices taken on the way there,
oldest first, as `SOut.runOracle` queries it. Below a choice `c` the oracle is
`o.after c`. `δ` resolves `pick` and `π` resolves `predict`; both see every earlier
choice of either kind. -/

abbrev Oracle := List Nat → Nat

def Oracle.after (o : Oracle) (c : Nat) : Oracle := fun h => o (c :: h)

/-- The oracle that answers `c` at the root and `o` below it. -/
def Oracle.cons (c : Nat) (o : Oracle) : Oracle := fun h =>
  match h with
  | [] => c
  | _ :: t => o t

/-- The oracle after the history `h`. -/
def Oracle.afterL (o : Oracle) (h : List Nat) : Oracle := fun h' => o (h ++ h')

theorem Oracle.cons_after (c x : Nat) (o : Oracle) : (Oracle.cons c o).after x = o := rfl

theorem Oracle.cons_root (c : Nat) (o : Oracle) : Oracle.cons c o [] = c := rfl

theorem Oracle.afterL_nil (o : Oracle) : o.afterL [] = o := rfl

theorem Oracle.afterL_after (o : Oracle) (h : List Nat) (c : Nat) :
    (o.afterL h).after c = o.afterL (h ++ [c]) := by
  funext h'
  show o (h ++ c :: h') = o ((h ++ [c]) ++ h')
  rw [List.append_assoc]; rfl

theorem Oracle.afterL_root (o : Oracle) (h : List Nat) : o.afterL h [] = o h := by
  show o (h ++ []) = o h
  rw [List.append_nil]

/-! ## Programs, outcomes, behaviours -/

/-- A program: an initial state and a step whose leaves are `ok (events, inl next)`
or `ok (events, inr result)`; `bad r` says the result `r` is UB. -/
structure Prog (E S R : Type) where
  init : S
  step : S → SOut (List E × (S ⊕ R))
  bad : R → Bool

/-- How a finite run ends: a result, or one of the prelude's other leaves. -/
inductive Outcome (R : Type) where
  | done (r : R)
  | panic (msg : String)
  | fuel
  | refused (what : String)
  | nobehavior

def Outcome.isBad {R : Type} (bad : R → Bool) : Outcome R → Bool
  | .done r => bad r
  | _ => false

/-- A behaviour: finite (`fin τ o`) or divergent (`div σ`, the trace after each
step of an infinite run). -/
inductive Behaviour (E R : Type) where
  | fin (τ : List E) (o : Outcome R)
  | div (σ : Nat → List E)

/-! ## The relational semantics -/

section Sem
variable {E S R : Type} (P : Prog E S R)

/-- Every resolution of `t` is rejected (continuing through the states it reaches). -/
inductive Dead : SOut (List E × (S ⊕ R)) → Prop
  | reject : Dead .reject
  | step {τ : List E} {s : S} : Dead (P.step s) → Dead (.ok (τ, .inl s))
  | pick {k : Nat → SOut (List E × (S ⊕ R))} : (∀ i, Dead (k i)) → Dead (.pick k)
  | predict {k : Nat → SOut (List E × (S ⊕ R))} : (∀ i, Dead (k i)) → Dead (.predict k)

/-- `t` must reach UB: some resolution of the demonic choices sends every resolution
of the angelic ones that is not rejected to UB. -/
inductive MustUB : SOut (List E × (S ⊕ R)) → Prop
  | bad {τ : List E} {r : R} : P.bad r = true → MustUB (.ok (τ, .inr r))
  | step {τ : List E} {s : S} : MustUB (P.step s) → MustUB (.ok (τ, .inl s))
  | pick {k : Nat → SOut (List E × (S ⊕ R))} (i : Nat) : MustUB (k i) → MustUB (.pick k)
  | predict {k : Nat → SOut (List E × (S ⊕ R))} (i : Nat) : MustUB (k i) →
      (∀ j, ¬ Dead P (k j) → MustUB (k j)) → MustUB (.predict k)

/-- `(τ, o)` is a finite behaviour of `t`. Demonic choice contributes every branch.
An angelic prediction contributes every branch's non-UB behaviours, and its UB ones
only when the prediction must reach UB. -/
inductive BehT : SOut (List E × (S ⊕ R)) → List E → Outcome R → Prop
  | done {τ : List E} {r : R} : BehT (.ok (τ, .inr r)) τ (.done r)
  | step {τ : List E} {s : S} {τ' : List E} {o : Outcome R} :
      BehT (P.step s) τ' o → BehT (.ok (τ, .inl s)) (τ ++ τ') o
  | panic (m : String) : BehT (.panic m) [] (.panic m)
  | fuel : BehT .fuel [] .fuel
  | refused (w : String) : BehT (.refused w) [] (.refused w)
  | nobehavior : BehT .nobehavior [] .nobehavior
  | pick {k : Nat → SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R} (i : Nat) :
      BehT (k i) τ o → BehT (.pick k) τ o
  | predictOk {k : Nat → SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R} (i : Nat) :
      BehT (k i) τ o → o.isBad P.bad = false → BehT (.predict k) τ o
  | predictUB {k : Nat → SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R} (i : Nat) :
      BehT (k i) τ o → o.isBad P.bad = true → MustUB P (.predict k) → BehT (.predict k) τ o

/-- One step of `t` can end at the state `s` after the events `τ`. -/
inductive Reach : SOut (List E × (S ⊕ R)) → List E → S → Prop
  | here {τ : List E} {s : S} : Reach (.ok (τ, .inl s)) τ s
  | pick {k : Nat → SOut (List E × (S ⊕ R))} {τ : List E} {s : S} (i : Nat) :
      Reach (k i) τ s → Reach (.pick k) τ s
  | predict {k : Nat → SOut (List E × (S ⊕ R))} {τ : List E} {s : S} (i : Nat) :
      Reach (k i) τ s → Reach (.predict k) τ s

/-- An infinite run whose trace after `k` steps is `σ k`. -/
def Diverges (σ : Nat → List E) : Prop :=
  ∃ st : Nat → S, st 0 = P.init ∧ σ 0 = [] ∧
    ∀ k, ∃ τ, Reach (P.step (st k)) τ (st (k + 1)) ∧ σ (k + 1) = σ k ++ τ

/-- The behaviours of a program. -/
def Beh : Behaviour E R → Prop
  | .fin τ o => BehT P (P.step P.init) τ o
  | .div σ => Diverges P σ

end Sem

/-! ## The executable interpretation -/

/-- What `n` steps under an oracle give: a finite end, a cut (fuel spent) after the
events so far, or a rejected resolution. -/
inductive RunRes (E R : Type) where
  | fin (τ : List E) (o : Outcome R)
  | cut (τ : List E)
  | rejected

def RunRes.prepend {E R : Type} (τ : List E) : RunRes E R → RunRes E R
  | .fin τ' o => .fin (τ ++ τ') o
  | .cut τ' => .cut (τ ++ τ')
  | .rejected => .rejected

section Run
variable {E S R : Type}

/-- One step: resolve the choices of `t` by `(δ, π)`, then continue with `cont`. -/
def stepT (cont : S → Oracle → Oracle → RunRes E R) :
    SOut (List E × (S ⊕ R)) → Oracle → Oracle → RunRes E R
  | .ok (τ, .inl s), δ, π => (cont s δ π).prepend τ
  | .ok (τ, .inr r), _, _ => .fin τ (.done r)
  | .panic m, _, _ => .fin [] (.panic m)
  | .fuel, _, _ => .fin [] .fuel
  | .refused w, _, _ => .fin [] (.refused w)
  | .nobehavior, _, _ => .fin [] .nobehavior
  | .reject, _, _ => .rejected
  | .pick k, δ, π => stepT cont (k (δ [])) (δ.after (δ [])) (π.after (δ []))
  | .predict k, δ, π => stepT cont (k (π [])) (δ.after (π [])) (π.after (π []))

/-- `n` steps from the tree `t`. -/
def runC (P : Prog E S R) : Nat → SOut (List E × (S ⊕ R)) → Oracle → Oracle → RunRes E R
  | 0, _, _, _ => .cut []
  | n + 1, t, δ, π => stepT (fun s => runC P n (P.step s)) t δ π

/-- The executable: `n` steps of `P` under the oracle `(δ, π)`. -/
def run (δ π : Oracle) (n : Nat) (P : Prog E S R) : RunRes E R :=
  runC P n (P.step P.init) δ π

/-- The oracles left after resolving the choices of `t`. -/
def resid {X : Type} : SOut X → Oracle → Oracle → Oracle × Oracle
  | .pick k, δ, π => resid (k (δ [])) (δ.after (δ [])) (π.after (δ []))
  | .predict k, δ, π => resid (k (π [])) (δ.after (π [])) (π.after (π []))
  | _, δ, π => (δ, π)

/-- How `stepT` ends on a resolved leaf. -/
def finish (cont : S → Oracle → Oracle → RunRes E R) :
    SOut (List E × (S ⊕ R)) → Oracle × Oracle → RunRes E R
  | .ok (τ, .inl s), (δ, π) => (cont s δ π).prepend τ
  | .ok (τ, .inr r), _ => .fin τ (.done r)
  | .panic m, _ => .fin [] (.panic m)
  | .fuel, _ => .fin [] .fuel
  | .refused w, _ => .fin [] (.refused w)
  | .nobehavior, _ => .fin [] .nobehavior
  | .reject, _ => .rejected
  | .pick _, _ => .rejected
  | .predict _, _ => .rejected

theorem runOracle_pick {X : Type} (δ π : Oracle) (k : Nat → SOut X) :
    SOut.runOracle δ π (.pick k) = SOut.runOracle (δ.after (δ [])) (π.after (δ [])) (k (δ [])) :=
  rfl

theorem runOracle_predict {X : Type} (δ π : Oracle) (k : Nat → SOut X) :
    SOut.runOracle δ π (.predict k) = SOut.runOracle (δ.after (π [])) (π.after (π [])) (k (π [])) :=
  rfl

/-- **The run is the prelude's interpretation.** Each step of `run` ends exactly on
the leaf `SOut.runOracle δ π` resolves the step's tree to. -/
theorem stepT_runOracle (cont : S → Oracle → Oracle → RunRes E R) (t : SOut (List E × (S ⊕ R))) :
    ∀ δ π : Oracle, stepT cont t δ π = finish cont (SOut.runOracle δ π t) (resid t δ π) := by
  induction t with
  | ok a => intro δ π; obtain ⟨τ, x⟩ := a; cases x <;> rfl
  | panic m => intro δ π; rfl
  | fuel => intro δ π; rfl
  | refused w => intro δ π; rfl
  | nobehavior => intro δ π; rfl
  | reject => intro δ π; rfl
  | pick k ih =>
    intro δ π
    rw [runOracle_pick]
    exact ih _ _ _
  | predict k ih =>
    intro δ π
    rw [runOracle_predict]
    exact ih _ _ _

theorem runC_zero (P : Prog E S R) (t : SOut (List E × (S ⊕ R))) (δ π : Oracle) :
    runC P 0 t δ π = .cut [] := rfl

theorem runC_inl (P : Prog E S R) (n : Nat) (τ : List E) (s : S) (δ π : Oracle) :
    runC P (n + 1) (.ok (τ, .inl s)) δ π = (runC P n (P.step s) δ π).prepend τ := rfl

theorem runC_inr (P : Prog E S R) (n : Nat) (τ : List E) (r : R) (δ π : Oracle) :
    runC P (n + 1) (.ok (τ, .inr r)) δ π = .fin τ (.done r) := rfl

theorem runC_pick (P : Prog E S R) (n : Nat) (k : Nat → SOut (List E × (S ⊕ R))) (δ π : Oracle) :
    runC P (n + 1) (.pick k) δ π = runC P (n + 1) (k (δ [])) (δ.after (δ [])) (π.after (δ [])) :=
  rfl

theorem runC_predict (P : Prog E S R) (n : Nat) (k : Nat → SOut (List E × (S ⊕ R))) (δ π : Oracle) :
    runC P (n + 1) (.predict k) δ π = runC P (n + 1) (k (π [])) (δ.after (π [])) (π.after (π [])) :=
  rfl

theorem prepend_eq_fin {τ0 τ : List E} {o : Outcome R} {r : RunRes E R} :
    r.prepend τ0 = .fin τ o → ∃ τ', r = .fin τ' o ∧ τ = τ0 ++ τ' := by
  cases r with
  | fin τ' o' =>
    intro h
    simp only [RunRes.prepend, RunRes.fin.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨τ', rfl, rfl⟩
  | cut τ' => intro h; cases h
  | rejected => intro h; cases h

end Run

/-! ## Facts about the relations -/

section Facts
variable {E S R : Type} (P : Prog E S R)

theorem mustUB_not_dead {t : SOut (List E × (S ⊕ R))} (h : MustUB P t) : ¬ Dead P t := by
  induction h with
  | bad _ => intro hd; cases hd
  | step _ ih => intro hd; cases hd with | step hd => exact ih hd
  | pick i _ ih => intro hd; cases hd with | pick hd => exact ih (hd i)
  | predict i _ _ ih _ => intro hd; cases hd with | predict hd => exact ih (hd i)

theorem behT_not_dead {t : SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R}
    (h : BehT P t τ o) : ¬ Dead P t := by
  induction h with
  | done => intro hd; cases hd
  | step _ ih => intro hd; cases hd with | step hd => exact ih hd
  | panic m => intro hd; cases hd
  | fuel => intro hd; cases hd
  | refused w => intro hd; cases hd
  | nobehavior => intro hd; cases hd
  | pick i _ ih => intro hd; cases hd with | pick hd => exact ih (hd i)
  | predictOk i _ _ ih => intro hd; cases hd with | predict hd => exact ih (hd i)
  | predictUB i _ _ _ ih => intro hd; cases hd with | predict hd => exact ih (hd i)

theorem behT_bad_mustUB {t : SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R}
    (h : BehT P t τ o) : o.isBad P.bad = true → MustUB P t := by
  induction h with
  | done => intro hb; exact .bad hb
  | step _ ih => intro hb; exact .step (ih hb)
  | panic m => intro hb; cases hb
  | fuel => intro hb; cases hb
  | refused w => intro hb; cases hb
  | nobehavior => intro hb; cases hb
  | pick i _ ih => intro hb; exact .pick i (ih hb)
  | predictOk i _ hnb _ => intro hb; rw [hnb] at hb; cases hb
  | predictUB i _ _ hm _ => intro _; exact hm

theorem mustUB_behT {t : SOut (List E × (S ⊕ R))} (h : MustUB P t) :
    ∃ τ o, o.isBad P.bad = true ∧ BehT P t τ o := by
  induction h with
  | @bad τ r hb => exact ⟨τ, .done r, hb, .done⟩
  | step _ ih =>
    obtain ⟨τ, o, hb, h⟩ := ih
    exact ⟨_, o, hb, .step h⟩
  | pick i _ ih =>
    obtain ⟨τ, o, hb, h⟩ := ih
    exact ⟨τ, o, hb, .pick i h⟩
  | predict i hi hall ih _ =>
    obtain ⟨τ, o, hb, h⟩ := ih
    exact ⟨τ, o, hb, .predictUB i h hb (.predict i hi hall)⟩

end Facts

/-! ## run_sound and run_adequate -/

section Sound
variable {E S R : Type} (P : Prog E S R)

theorem runC_sound (n : Nat) :
    ∀ (t : SOut (List E × (S ⊕ R))) (δ π : Oracle) (τ : List E) (o : Outcome R),
      runC P n t δ π = .fin τ o → o.isBad P.bad = false → BehT P t τ o := by
  induction n with
  | zero => intro t δ π τ o h; cases h
  | succ n ihn =>
    intro t
    induction t with
    | ok a =>
      intro δ π τ o h hb
      obtain ⟨τ0, x⟩ := a
      cases x with
      | inl s =>
        rw [runC_inl] at h
        obtain ⟨τ', h', rfl⟩ := prepend_eq_fin h
        exact .step (ihn _ _ _ _ _ h' hb)
      | inr r =>
        rw [runC_inr] at h
        simp only [RunRes.fin.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .done
    | panic m =>
      intro δ π τ o h _
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .panic m
    | fuel =>
      intro δ π τ o h _
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .fuel
    | refused w =>
      intro δ π τ o h _
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .refused w
    | nobehavior =>
      intro δ π τ o h _
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .nobehavior
    | reject => intro δ π τ o h _; cases h
    | pick k ih =>
      intro δ π τ o h hb
      rw [runC_pick] at h
      exact .pick _ (ih _ _ _ _ _ h hb)
    | predict k ih =>
      intro δ π τ o h hb
      rw [runC_predict] at h
      exact .predictOk _ (ih _ _ _ _ _ h hb) hb

/-- **run_sound.** A run that ends, and not in UB, is a behaviour. -/
theorem run_sound (δ π : Oracle) (n : Nat) (τ : List E) (o : Outcome R) :
    run δ π n P = .fin τ o → o.isBad P.bad = false → Beh P (.fin τ o) :=
  runC_sound P n _ δ π τ o

/-- Every finite behaviour of a tree is the run of some oracle and fuel. -/
theorem behT_run {t : SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R}
    (h : BehT P t τ o) : ∃ δ π : Oracle, ∃ n, runC P n t δ π = .fin τ o := by
  induction h with
  | done => exact ⟨fun _ => 0, fun _ => 0, 1, rfl⟩
  | step _ ih =>
    obtain ⟨δ, π, n, h⟩ := ih
    exact ⟨δ, π, n + 1, by rw [runC_inl, h]; rfl⟩
  | panic m => exact ⟨fun _ => 0, fun _ => 0, 1, rfl⟩
  | fuel => exact ⟨fun _ => 0, fun _ => 0, 1, rfl⟩
  | refused w => exact ⟨fun _ => 0, fun _ => 0, 1, rfl⟩
  | nobehavior => exact ⟨fun _ => 0, fun _ => 0, 1, rfl⟩
  | pick i _ ih =>
    obtain ⟨δ, π, n, h⟩ := ih
    cases n with
    | zero => cases h
    | succ n => exact ⟨Oracle.cons i δ, Oracle.cons 0 π, n + 1, by rw [runC_pick]; exact h⟩
  | predictOk i _ _ ih =>
    obtain ⟨δ, π, n, h⟩ := ih
    cases n with
    | zero => cases h
    | succ n => exact ⟨Oracle.cons 0 δ, Oracle.cons i π, n + 1, by rw [runC_predict]; exact h⟩
  | predictUB i _ _ _ ih =>
    obtain ⟨δ, π, n, h⟩ := ih
    cases n with
    | zero => cases h
    | succ n => exact ⟨Oracle.cons 0 δ, Oracle.cons i π, n + 1, by rw [runC_predict]; exact h⟩

/-- A one-step path to `s` is what some oracle resolves the step to. -/
theorem reach_oracles {t : SOut (List E × (S ⊕ R))} {τ : List E} {s : S} (h : Reach t τ s) :
    ∀ δ' π' : Oracle, ∃ δ π : Oracle, ∀ cont : S → Oracle → Oracle → RunRes E R,
      stepT cont t δ π = (cont s δ' π').prepend τ := by
  induction h with
  | here => intro δ' π'; exact ⟨δ', π', fun _ => rfl⟩
  | pick i _ ih =>
    intro δ' π'
    obtain ⟨δ, π, h⟩ := ih δ' π'
    exact ⟨Oracle.cons i δ, Oracle.cons 0 π, fun cont => h cont⟩
  | predict i _ ih =>
    intro δ' π'
    obtain ⟨δ, π, h⟩ := ih δ' π'
    exact ⟨Oracle.cons 0 δ, Oracle.cons i π, fun cont => h cont⟩

theorem diverges_runs {σ : Nat → List E} {st : Nat → S}
    (hstep : ∀ k, ∃ τ, Reach (P.step (st k)) τ (st (k + 1)) ∧ σ (k + 1) = σ k ++ τ) :
    ∀ m j, ∃ δ π : Oracle, ∃ τ, runC P m (P.step (st j)) δ π = .cut τ ∧ σ (j + m) = σ j ++ τ := by
  intro m
  induction m with
  | zero => intro j; exact ⟨fun _ => 0, fun _ => 0, [], rfl, by simp⟩
  | succ m ih =>
    intro j
    obtain ⟨τj, hr, hσ⟩ := hstep j
    obtain ⟨δ', π', τ', hrun, hσ'⟩ := ih (j + 1)
    obtain ⟨δ, π, hp⟩ := reach_oracles hr δ' π'
    refine ⟨δ, π, τj ++ τ', ?_, ?_⟩
    · show stepT (fun s => runC P m (P.step s)) (P.step (st j)) δ π = _
      rw [hp, hrun]; rfl
    · rw [show j + (m + 1) = j + 1 + m by omega, hσ', hσ, List.append_assoc]

/-- **run_adequate.** Every finite behaviour is the run of some oracle and fuel, and
every prefix of a divergent behaviour is the cut of some oracle's run. -/
theorem run_adequate :
    (∀ τ o, Beh P (.fin τ o) → ∃ δ π : Oracle, ∃ n, run δ π n P = .fin τ o) ∧
    (∀ σ, Beh P (.div σ) → ∀ k, ∃ δ π : Oracle, run δ π k P = .cut (σ k)) := by
  refine ⟨fun τ o h => behT_run P h, ?_⟩
  intro σ ⟨st, h0, hσ0, hstep⟩ k
  obtain ⟨δ, π, τ, hrun, hσ⟩ := diverges_runs P hstep k 0
  refine ⟨δ, π, ?_⟩
  rw [Nat.zero_add, hσ0, List.nil_append] at hσ
  unfold run
  rw [← h0, hrun, hσ]

end Sound

/-! ## core_wf -/

section Wf
variable {E S R : Type} (P : Prog E S R)

/-- The state `s` has a finite behaviour. -/
def Good (s : S) : Prop := ∃ τ o, BehT P (P.step s) τ o

/-- A tree that is not dead, all of whose one-step successors have a finite
behaviour, has a non-UB behaviour or must reach UB. No finite branching is needed:
`MustUB` and `Dead` are inductive over every branch. -/
theorem live_split (t : SOut (List E × (S ⊕ R))) :
    ¬ Dead P t → (∀ τ s', Reach t τ s' → Good P s') →
      (∃ τ o, o.isBad P.bad = false ∧ BehT P t τ o) ∨ MustUB P t := by
  induction t with
  | ok a =>
    intro _ hg
    obtain ⟨τ, x⟩ := a
    cases x with
    | inl s =>
      obtain ⟨τ', o, h⟩ := hg τ s .here
      cases hb : o.isBad P.bad with
      | false => exact .inl ⟨_, o, hb, .step h⟩
      | true => exact .inr (.step (behT_bad_mustUB P h hb))
    | inr r =>
      cases hb : P.bad r with
      | false => exact .inl ⟨τ, .done r, hb, .done⟩
      | true => exact .inr (.bad hb)
  | panic m => intro _ _; exact .inl ⟨[], .panic m, rfl, .panic m⟩
  | fuel => intro _ _; exact .inl ⟨[], .fuel, rfl, .fuel⟩
  | refused w => intro _ _; exact .inl ⟨[], .refused w, rfl, .refused w⟩
  | nobehavior => intro _ _; exact .inl ⟨[], .nobehavior, rfl, .nobehavior⟩
  | reject => intro hd _; exact absurd .reject hd
  | pick k ih =>
    intro hd hg
    have : ∃ i, ¬ Dead P (k i) :=
      Classical.byContradiction fun hno =>
        hd (.pick fun i => Classical.byContradiction fun hi => hno ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := this
    rcases ih i hi (fun τ s' hr => hg τ s' (.pick i hr)) with ⟨τ, o, hb, h⟩ | hm
    · exact .inl ⟨τ, o, hb, .pick i h⟩
    · exact .inr (.pick i hm)
  | predict k ih =>
    intro hd hg
    by_cases hex : ∃ i, ∃ τ o, o.isBad P.bad = false ∧ BehT P (k i) τ o
    · obtain ⟨i, τ, o, hb, h⟩ := hex
      exact .inl ⟨τ, o, hb, .predictOk i h hb⟩
    · have hall : ∀ j, ¬ Dead P (k j) → MustUB P (k j) := fun j hj =>
        (ih j hj (fun τ s' hr => hg τ s' (.predict j hr))).resolve_left
          (fun ⟨τ, o, hb, h⟩ => hex ⟨j, τ, o, hb, h⟩)
      have : ∃ i, ¬ Dead P (k i) :=
        Classical.byContradiction fun hno =>
          hd (.predict fun i => Classical.byContradiction fun hi => hno ⟨i, hi⟩)
      obtain ⟨i, hi⟩ := this
      exact .inr (.predict i (hall i hi) hall)

/-- A state with no finite behaviour, whose step is not dead, steps to another one. -/
theorem not_good_next (hwf : ∀ s, ¬ Dead P (P.step s)) {s : S} (h : ¬ Good P s) :
    ∃ p : List E × S, Reach (P.step s) p.1 p.2 ∧ ¬ Good P p.2 :=
  Classical.byContradiction fun hno => by
    have hg : ∀ τ s', Reach (P.step s) τ s' → Good P s' := fun τ s' hr =>
      Classical.byContradiction fun hs => hno ⟨(τ, s'), hr, hs⟩
    rcases live_split P (P.step s) (hwf s) hg with ⟨τ, o, _, hb⟩ | hm
    · exact h ⟨τ, o, hb⟩
    · obtain ⟨τ, o, _, hb⟩ := mustUB_behT P hm
      exact h ⟨τ, o, hb⟩

/-- The next state of the divergent run, and the events on the way. -/
def chain (hwf : ∀ s, ¬ Dead P (P.step s)) (x : {s : S // ¬ Good P s}) :
    List E × {s : S // ¬ Good P s} :=
  ((Classical.choose (not_good_next P hwf x.2)).1,
   ⟨(Classical.choose (not_good_next P hwf x.2)).2,
    (Classical.choose_spec (not_good_next P hwf x.2)).2⟩)

theorem chain_reach (hwf : ∀ s, ¬ Dead P (P.step s)) (x : {s : S // ¬ Good P s}) :
    Reach (P.step x.1) (chain P hwf x).1 (chain P hwf x).2.1 :=
  (Classical.choose_spec (not_good_next P hwf x.2)).1

def chainSt (hwf : ∀ s, ¬ Dead P (P.step s)) (x0 : {s : S // ¬ Good P s}) :
    Nat → {s : S // ¬ Good P s}
  | 0 => x0
  | k + 1 => (chain P hwf (chainSt hwf x0 k)).2

def chainTr (hwf : ∀ s, ¬ Dead P (P.step s)) (x0 : {s : S // ¬ Good P s}) : Nat → List E
  | 0 => []
  | k + 1 => chainTr hwf x0 k ++ (chain P hwf (chainSt P hwf x0 k)).1

/-- **core_wf.** Every node of `SOut` is final (a result or one of the prelude's
other leaves) or chooses; when no state's step is a dead end (every resolution
rejected), the program has a behaviour: a finite one, or else an infinite run. -/
theorem core_wf (hwf : ∀ s, ¬ Dead P (P.step s)) : ∃ b, Beh P b := by
  by_cases hg : Good P P.init
  · obtain ⟨τ, o, h⟩ := hg
    exact ⟨.fin τ o, h⟩
  · let x0 : {s : S // ¬ Good P s} := ⟨P.init, hg⟩
    refine ⟨.div (chainTr P hwf x0), fun k => (chainSt P hwf x0 k).1, rfl, rfl, fun k => ?_⟩
    exact ⟨_, chain_reach P hwf (chainSt P hwf x0 k), rfl⟩

end Wf

/-! ## run_ub -/

section Ub
variable {E S R : Type} (P : Prog E S R)

/-- A demonic oracle is admissible on a run when it never moves from a node that has
a resolution which is not rejected into a branch that has none: MiniRust's `pick`
chooses among the candidates that pass its predicate, so a demonic choice of a
rejected one is not a resolution at all. (An angelic oracle may predict a rejected
candidate: that run is rejected.) `admC P n t δ π` says this along the first `n`
steps of the run of `t` under `(δ, π)`. -/
def admT (cont : S → Oracle → Oracle → Prop) :
    SOut (List E × (S ⊕ R)) → Oracle → Oracle → Prop
  | .ok (_, .inl s), δ, π => cont s δ π
  | .pick k, δ, π => (¬ Dead P (.pick k) → ¬ Dead P (k (δ []))) ∧
      admT cont (k (δ [])) (δ.after (δ [])) (π.after (δ []))
  | .predict k, δ, π => admT cont (k (π [])) (δ.after (π [])) (π.after (π []))
  | _, _, _ => True

def admC : Nat → SOut (List E × (S ⊕ R)) → Oracle → Oracle → Prop
  | 0, _, _, _ => True
  | n + 1, t, δ, π => admT P (fun s => admC n (P.step s)) t δ π

/-- `δ` is admissible for `P`: on every run, under every angelic oracle. -/
def Admissible (δ : Oracle) : Prop := ∀ π n, admC P n (P.step P.init) δ π

theorem admC_inl (n : Nat) (τ : List E) (s : S) (δ π : Oracle) :
    admC P (n + 1) (.ok (τ, .inl s)) δ π = admC P n (P.step s) δ π := rfl

theorem admC_pick (n : Nat) (k : Nat → SOut (List E × (S ⊕ R))) (δ π : Oracle) :
    admC P (n + 1) (.pick k) δ π = ((¬ Dead P (.pick k) → ¬ Dead P (k (δ []))) ∧
      admC P (n + 1) (k (δ [])) (δ.after (δ [])) (π.after (δ []))) := rfl

theorem admC_predict (n : Nat) (k : Nat → SOut (List E × (S ⊕ R))) (δ π : Oracle) :
    admC P (n + 1) (.predict k) δ π = admC P (n + 1) (k (π [])) (δ.after (π [])) (π.after (π [])) :=
  rfl

end Ub

/-- The run ended in UB, or was rejected. -/
def RunRes.badOrRejected {E R : Type} (bad : R → Bool) : RunRes E R → Bool
  | .fin _ o => o.isBad bad
  | .cut _ => false
  | .rejected => true

theorem RunRes.badOrRejected_prepend {E R : Type} (bad : R → Bool) (τ : List E) (r : RunRes E R) :
    (r.prepend τ).badOrRejected bad = r.badOrRejected bad := by
  cases r <;> rfl

section Ub2
variable {E S R : Type} (P : Prog E S R)

theorem dead_rejects {t : SOut (List E × (S ⊕ R))} (h : Dead P t) :
    ∀ δ π : Oracle, ∃ n, runC P n t δ π = .rejected := by
  induction h with
  | reject => intro δ π; exact ⟨1, rfl⟩
  | step _ ih =>
    intro δ π
    obtain ⟨n, hn⟩ := ih δ π
    exact ⟨n + 1, by rw [runC_inl, hn]; rfl⟩
  | @pick k _ ih =>
    intro δ π
    obtain ⟨n, hn⟩ := ih (δ []) (δ.after (δ [])) (π.after (δ []))
    cases n with
    | zero => cases hn
    | succ n => exact ⟨n + 1, by rw [runC_pick]; exact hn⟩
  | @predict k _ ih =>
    intro δ π
    obtain ⟨n, hn⟩ := ih (π []) (δ.after (π [])) (π.after (π []))
    cases n with
    | zero => cases hn
    | succ n => exact ⟨n + 1, by rw [runC_predict]; exact hn⟩

theorem dead_adm {t : SOut (List E × (S ⊕ R))} (h : Dead P t) :
    ∀ n (δ π : Oracle), admC P n t δ π := by
  induction h with
  | reject => intro n δ π; cases n <;> trivial
  | step _ ih =>
    intro n δ π
    cases n with
    | zero => trivial
    | succ n => rw [admC_inl]; exact ih n δ π
  | @pick k hk ih =>
    intro n δ π
    cases n with
    | zero => trivial
    | succ n =>
      rw [admC_pick]
      exact ⟨fun hnd => absurd (Dead.pick hk) hnd, ih _ _ _ _⟩
  | @predict k _ ih =>
    intro n δ π
    cases n with
    | zero => trivial
    | succ n => rw [admC_predict]; exact ih _ _ _ _

/-- A tree that must reach UB has an admissible demonic oracle under which every
angelic oracle ends in UB or is rejected. -/
theorem forcing {t : SOut (List E × (S ⊕ R))} (h : MustUB P t) :
    ∃ δ : Oracle, (∀ π n, admC P n t δ π) ∧
      ∀ π, ∃ n, (runC P n t δ π).badOrRejected P.bad = true := by
  induction h with
  | @bad τ r hb =>
    refine ⟨fun _ => 0, fun π n => ?_, fun π => ⟨1, hb⟩⟩
    cases n <;> trivial
  | @step τ s _ ih =>
    obtain ⟨δ, hadm, hbor⟩ := ih
    refine ⟨δ, fun π n => ?_, fun π => ?_⟩
    · cases n with
      | zero => trivial
      | succ n => rw [admC_inl]; exact hadm π n
    · obtain ⟨n, hn⟩ := hbor π
      exact ⟨n + 1, by rw [runC_inl, RunRes.badOrRejected_prepend]; exact hn⟩
  | @pick k i hi ih =>
    obtain ⟨δ, hadm, hbor⟩ := ih
    refine ⟨Oracle.cons i δ, fun π n => ?_, fun π => ?_⟩
    · cases n with
      | zero => trivial
      | succ n =>
        rw [admC_pick]
        exact ⟨fun _ => mustUB_not_dead P hi, hadm _ _⟩
    · obtain ⟨n, hn⟩ := hbor (π.after i)
      cases n with
      | zero => cases hn
      | succ n => exact ⟨n + 1, by rw [runC_pick]; exact hn⟩
  | @predict k i _ _ _ ihall =>
    let ch : Nat → Oracle := fun c =>
      if hc : ¬ Dead P (k c) then Classical.choose (ihall c hc) else fun _ => 0
    let δ' : Oracle := fun hist =>
      match hist with
      | [] => 0
      | c :: t => ch c t
    have hδ : ∀ c, δ'.after c = ch c := fun _ => rfl
    have hch : ∀ c (hc : ¬ Dead P (k c)), ch c = Classical.choose (ihall c hc) :=
      fun c hc => dif_pos hc
    refine ⟨δ', fun π n => ?_, fun π => ?_⟩
    · cases n with
      | zero => trivial
      | succ n =>
        rw [admC_predict, hδ]
        by_cases hc : Dead P (k (π []))
        · exact dead_adm P hc _ _ _
        · rw [hch _ hc]; exact (Classical.choose_spec (ihall _ hc)).1 _ _
    · by_cases hc : Dead P (k (π []))
      · obtain ⟨n, hn⟩ := dead_rejects P hc (δ'.after (π [])) (π.after (π []))
        cases n with
        | zero => cases hn
        | succ n => exact ⟨n + 1, by rw [runC_predict, hn]; rfl⟩
      · obtain ⟨n, hn⟩ := (Classical.choose_spec (ihall _ hc)).2 (π.after (π []))
        cases n with
        | zero => cases hn
        | succ n => exact ⟨n + 1, by rw [runC_predict, hδ, hch _ hc]; exact hn⟩

/-- A UB behaviour has an admissible demonic oracle forcing UB that also reaches it. -/
theorem ub_strategy {t : SOut (List E × (S ⊕ R))} {τ : List E} {o : Outcome R}
    (h : BehT P t τ o) : o.isBad P.bad = true →
      ∃ δ : Oracle, (∀ π n, admC P n t δ π) ∧
        (∀ π, ∃ n, (runC P n t δ π).badOrRejected P.bad = true) ∧
        ∃ π n, runC P n t δ π = .fin τ o := by
  induction h with
  | @done τ r =>
    intro hb
    refine ⟨fun _ => 0, fun π n => ?_, fun π => ⟨1, hb⟩, fun _ => 0, 1, rfl⟩
    cases n <;> trivial
  | @step τ s τ' o _ ih =>
    intro hb
    obtain ⟨δ, hadm, hbor, π, n, hr⟩ := ih hb
    refine ⟨δ, fun π n => ?_, fun π => ?_, π, n + 1, by rw [runC_inl, hr]; rfl⟩
    · cases n with
      | zero => trivial
      | succ n => rw [admC_inl]; exact hadm π n
    · obtain ⟨n, hn⟩ := hbor π
      exact ⟨n + 1, by rw [runC_inl, RunRes.badOrRejected_prepend]; exact hn⟩
  | panic m => intro hb; cases hb
  | fuel => intro hb; cases hb
  | refused w => intro hb; cases hb
  | nobehavior => intro hb; cases hb
  | @pick k τ o i hk ih =>
    intro hb
    obtain ⟨δ, hadm, hbor, π, n, hr⟩ := ih hb
    refine ⟨Oracle.cons i δ, fun π n => ?_, fun π => ?_, Oracle.cons 0 π, n, ?_⟩
    · cases n with
      | zero => trivial
      | succ n =>
        rw [admC_pick]
        exact ⟨fun _ => behT_not_dead P hk, hadm _ _⟩
    · obtain ⟨n, hn⟩ := hbor (π.after i)
      cases n with
      | zero => cases hn
      | succ n => exact ⟨n + 1, by rw [runC_pick]; exact hn⟩
    · cases n with
      | zero => cases hr
      | succ n => rw [runC_pick]; exact hr
  | predictOk i _ hnb _ => intro hb; rw [hnb] at hb; cases hb
  | @predictUB k τ o i hk _ hm ih =>
    intro hb
    obtain ⟨δi, hadmi, hbori, πi, ni, hri⟩ := ih hb
    have hall : ∀ j, ¬ Dead P (k j) → MustUB P (k j) := by
      cases hm with
      | predict _ _ hall => exact hall
    have hf : ∀ j, ¬ Dead P (k j) → ∃ δ : Oracle, (∀ π n, admC P n (k j) δ π) ∧
        ∀ π, ∃ n, (runC P n (k j) δ π).badOrRejected P.bad = true :=
      fun j hj => forcing P (hall j hj)
    let ch : Nat → Oracle := fun c =>
      if c = i then δi else if hc : ¬ Dead P (k c) then Classical.choose (hf c hc) else fun _ => 0
    let δ' : Oracle := fun hist =>
      match hist with
      | [] => 0
      | c :: t => ch c t
    have hδ : ∀ c, δ'.after c = ch c := fun _ => rfl
    have hchi : ch i = δi := if_pos rfl
    have hch : ∀ c, c ≠ i → ∀ (hc : ¬ Dead P (k c)), ch c = Classical.choose (hf c hc) :=
      fun c hci hc => by
        show (if c = i then δi else if hc : ¬ Dead P (k c) then Classical.choose (hf c hc)
          else fun _ => 0) = _
        rw [if_neg hci, dif_pos hc]
    refine ⟨δ', fun π n => ?_, fun π => ?_, Oracle.cons i πi, ni, ?_⟩
    · cases n with
      | zero => trivial
      | succ n =>
        rw [admC_predict, hδ]
        by_cases hci : π [] = i
        · rw [hci, hchi]; exact hadmi _ _
        · by_cases hc : Dead P (k (π []))
          · exact dead_adm P hc _ _ _
          · rw [hch _ hci hc]; exact (Classical.choose_spec (hf _ hc)).1 _ _
    · by_cases hci : π [] = i
      · obtain ⟨n, hn⟩ := hbori (π.after (π []))
        cases n with
        | zero => cases hn
        | succ n =>
          refine ⟨n + 1, ?_⟩
          rw [runC_predict, hδ]
          rw [hci, hchi] at *
          exact hn
      · by_cases hc : Dead P (k (π []))
        · obtain ⟨n, hn⟩ := dead_rejects P hc (δ'.after (π [])) (π.after (π []))
          cases n with
          | zero => cases hn
          | succ n => exact ⟨n + 1, by rw [runC_predict, hn]; rfl⟩
        · obtain ⟨n, hn⟩ := (Classical.choose_spec (hf _ hc)).2 (π.after (π []))
          cases n with
          | zero => cases hn
          | succ n => exact ⟨n + 1, by rw [runC_predict, hδ, hch _ hci hc]; exact hn⟩
    · cases ni with
      | zero => cases hri
      | succ n =>
        rw [runC_predict]
        show runC P (n + 1) (k i) (δ'.after i) πi = _
        rw [hδ, hchi]; exact hri

/-! ### The converse, by an escaping angelic oracle

If an admissible `δ` makes every angelic oracle end in UB or be rejected, the tree
must reach UB. Otherwise an angelic oracle can always predict a branch that is
neither dead nor must reach UB, and its run never ends in UB and is never
rejected. That oracle is a function of the history, built from where the history
leads (`AtPre`). -/

/-- From `t`, the choice history `h` (oldest first) leads to the node `u`. -/
inductive AtPre : SOut (List E × (S ⊕ R)) → List Nat → SOut (List E × (S ⊕ R)) → Prop
  | refl {t : SOut (List E × (S ⊕ R))} : AtPre t [] t
  | step {τ : List E} {s : S} {h : List Nat} {u : SOut (List E × (S ⊕ R))} :
      AtPre (P.step s) h u → AtPre (.ok (τ, .inl s)) h u
  | pick {k : Nat → SOut (List E × (S ⊕ R))} {c : Nat} {h : List Nat} {u : SOut (List E × (S ⊕ R))} :
      AtPre (k c) h u → AtPre (.pick k) (c :: h) u
  | predict {k : Nat → SOut (List E × (S ⊕ R))} {c : Nat} {h : List Nat} {u : SOut (List E × (S ⊕ R))} :
      AtPre (k c) h u → AtPre (.predict k) (c :: h) u

theorem AtPre.trans {t u v : SOut (List E × (S ⊕ R))} {h h' : List Nat}
    (h1 : AtPre P t h u) (h2 : AtPre P u h' v) : AtPre P t (h ++ h') v := by
  induction h1 with
  | refl => exact h2
  | step _ ih => exact .step (ih h2)
  | pick _ ih => exact .pick (ih h2)
  | predict _ ih => exact .predict (ih h2)

def IsChoice {X : Type} : SOut X → Prop
  | .pick _ => True
  | .predict _ => True
  | _ => False

/-- A history leads to at most one choice node. -/
theorem AtPre.choice_unique {t u : SOut (List E × (S ⊕ R))} {h : List Nat} (h1 : AtPre P t h u) :
    ∀ {u'}, AtPre P t h u' → IsChoice u → IsChoice u' → u = u' := by
  induction h1 with
  | refl =>
    intro u' h2 hc hc'
    cases h2 with
    | refl => rfl
    | step _ => exact hc.elim
  | step _ ih =>
    intro u' h2 hc hc'
    cases h2 with
    | refl => exact hc'.elim
    | step h2 => exact ih h2 hc hc'
  | pick _ ih =>
    intro u' h2 hc hc'
    cases h2 with
    | pick h2 => exact ih h2 hc hc'
  | predict _ ih =>
    intro u' h2 hc hc'
    cases h2 with
    | predict h2 => exact ih h2 hc hc'

/-- Neither dead nor must reach UB. -/
def Esc (u : SOut (List E × (S ⊕ R))) : Prop := ¬ Dead P u ∧ ¬ MustUB P u

theorem esc_predict {k : Nat → SOut (List E × (S ⊕ R))} (h : Esc P (.predict k)) :
    ∃ i, Esc P (k i) :=
  Classical.byContradiction fun hno => by
    have hall : ∀ j, ¬ Dead P (k j) → MustUB P (k j) := fun j hj =>
      Classical.byContradiction fun hm => hno ⟨j, hj, hm⟩
    have : ∃ i, ¬ Dead P (k i) :=
      Classical.byContradiction fun hd =>
        h.1 (.predict fun i => Classical.byContradiction fun hi => hd ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := this
    exact h.2 (.predict i (hall i hi) hall)

/-- The escaping angelic oracle of `t`. -/
def escPi (t : SOut (List E × (S ⊕ R))) : Oracle := fun h =>
  if hh : ∃ i, ∃ k, AtPre P t h (.predict k) ∧ Esc P (k i) then Classical.choose hh else 0

theorem escPi_spec {t : SOut (List E × (S ⊕ R))} {h : List Nat} {k : Nat → SOut (List E × (S ⊕ R))}
    (hat : AtPre P t h (.predict k)) (he : Esc P (.predict k)) : Esc P (k (escPi P t h)) := by
  obtain ⟨i, hi⟩ := esc_predict P he
  have hh : ∃ i, ∃ k, AtPre P t h (.predict k) ∧ Esc P (k i) := ⟨i, k, hat, hi⟩
  have e : escPi P t h = Classical.choose hh := dif_pos hh
  obtain ⟨k', hat', he'⟩ := Classical.choose_spec hh
  have : SOut.predict k' = SOut.predict k := AtPre.choice_unique P hat' hat trivial trivial
  cases this
  rw [e]; exact he'

theorem escape (t : SOut (List E × (S ⊕ R))) (δ : Oracle) (n : Nat) :
    ∀ (u : SOut (List E × (S ⊕ R))) (h : List Nat), AtPre P t h u → Esc P u →
      admC P n u (δ.afterL h) ((escPi P t).afterL h) →
      (runC P n u (δ.afterL h) ((escPi P t).afterL h)).badOrRejected P.bad = false := by
  induction n with
  | zero => intro u h _ _ _; rfl
  | succ n ihn =>
    intro u
    induction u with
    | ok a =>
      intro h hat he hadm
      obtain ⟨τ, x⟩ := a
      cases x with
      | inl s =>
        rw [runC_inl, RunRes.badOrRejected_prepend]
        rw [admC_inl] at hadm
        have hat' : AtPre P t h (P.step s) := by
          have := AtPre.trans P hat (AtPre.step (τ := τ) AtPre.refl)
          rwa [List.append_nil] at this
        exact ihn _ h hat' ⟨fun hd => he.1 (.step hd), fun hm => he.2 (.step hm)⟩ hadm
      | inr r =>
        rw [runC_inr]
        show P.bad r = false
        cases hb : P.bad r with
        | false => rfl
        | true => exact absurd (MustUB.bad hb) he.2
    | panic m => intro _ _ _ _; rfl
    | fuel => intro _ _ _ _; rfl
    | refused w => intro _ _ _ _; rfl
    | nobehavior => intro _ _ _ _; rfl
    | reject => intro _ _ he _; exact absurd .reject he.1
    | pick k ih =>
      intro h hat he hadm
      rw [admC_pick] at hadm
      rw [runC_pick]
      have hc : δ.afterL h [] = δ h := Oracle.afterL_root δ h
      rw [Oracle.afterL_after, Oracle.afterL_after] at hadm ⊢
      rw [hc] at hadm ⊢
      have hesc : Esc P (k (δ h)) :=
        ⟨hadm.1 he.1, fun hm => he.2 (.pick _ hm)⟩
      exact ih (δ h) (h ++ [δ h]) (AtPre.trans P hat (.pick .refl)) hesc hadm.2
    | predict k ih =>
      intro h hat he hadm
      rw [admC_predict] at hadm
      rw [runC_predict]
      have hc : (escPi P t).afterL h [] = escPi P t h := Oracle.afterL_root _ h
      rw [Oracle.afterL_after, Oracle.afterL_after] at hadm ⊢
      rw [hc] at hadm ⊢
      exact ih _ (h ++ [escPi P t h]) (AtPre.trans P hat (.predict .refl))
        (escPi_spec P hat he) hadm

theorem mustUB_of_strategy (t : SOut (List E × (S ⊕ R))) (δ : Oracle)
    (hadm : ∀ π n, admC P n t δ π)
    (hbor : ∀ π, ∃ n, (runC P n t δ π).badOrRejected P.bad = true)
    (hnd : ¬ Dead P t) : MustUB P t :=
  Classical.byContradiction fun hm => by
    obtain ⟨n, hn⟩ := hbor (escPi P t)
    have := escape P t δ n t [] .refl ⟨hnd, hm⟩ (hadm _ n)
    rw [Oracle.afterL_nil, Oracle.afterL_nil] at this
    rw [this] at hn
    cases hn

theorem behT_of_strategy {o : Outcome R} (hb : o.isBad P.bad = true) (n : Nat) :
    ∀ (t : SOut (List E × (S ⊕ R))) (δ π : Oracle) (τ : List E),
      (∀ π' m, admC P m t δ π') →
      (∀ π', ∃ m, (runC P m t δ π').badOrRejected P.bad = true) →
      runC P n t δ π = .fin τ o → BehT P t τ o := by
  induction n with
  | zero => intro t δ π τ _ _ h; cases h
  | succ n ihn =>
    intro t
    induction t with
    | ok a =>
      intro δ π τ hadm hbor h
      obtain ⟨τ0, x⟩ := a
      cases x with
      | inl s =>
        rw [runC_inl] at h
        obtain ⟨τ', h', rfl⟩ := prepend_eq_fin h
        refine .step (ihn _ δ π τ' (fun π' m => ?_) (fun π' => ?_) h')
        · have := hadm π' (m + 1); rwa [admC_inl] at this
        · obtain ⟨m, hm⟩ := hbor π'
          cases m with
          | zero => cases hm
          | succ m => rw [runC_inl, RunRes.badOrRejected_prepend] at hm; exact ⟨m, hm⟩
      | inr r =>
        rw [runC_inr] at h
        simp only [RunRes.fin.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .done
    | panic m =>
      intro δ π τ _ _ h
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hb
    | fuel =>
      intro δ π τ _ _ h
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hb
    | refused w =>
      intro δ π τ _ _ h
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hb
    | nobehavior =>
      intro δ π τ _ _ h
      simp only [runC, stepT, RunRes.fin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hb
    | reject => intro δ π τ _ _ h; cases h
    | pick k ih =>
      intro δ π τ hadm hbor h
      rw [runC_pick] at h
      refine .pick _ (ih _ _ _ τ (fun π' m => ?_) (fun π' => ?_) h)
      · cases m with
        | zero => trivial
        | succ m =>
          have := hadm (Oracle.cons 0 π') (m + 1)
          rw [admC_pick] at this
          exact this.2
      · obtain ⟨m, hm⟩ := hbor (Oracle.cons 0 π')
        cases m with
        | zero => cases hm
        | succ m => rw [runC_pick] at hm; exact ⟨m + 1, hm⟩
    | predict k ih =>
      intro δ π τ hadm hbor h
      rw [runC_predict] at h
      have hk := ih _ _ _ τ (fun π' m => ?_) (fun π' => ?_) h
      · refine .predictUB _ hk hb (mustUB_of_strategy P _ δ hadm hbor ?_)
        intro hd
        cases hd with
        | predict hd => exact behT_not_dead P hk (hd _)
      · cases m with
        | zero => trivial
        | succ m =>
          have := hadm (Oracle.cons (π []) π') (m + 1)
          rw [admC_predict] at this
          exact this
      · obtain ⟨m, hm⟩ := hbor (Oracle.cons (π []) π')
        cases m with
        | zero => cases hm
        | succ m => rw [runC_predict] at hm; exact ⟨m + 1, hm⟩

/-- **run_ub.** For a UB outcome `o`: `(τ, o)` is a behaviour exactly when some
admissible demonic oracle makes every angelic oracle's run end in UB or be rejected
(each after finitely many steps of its own), and some angelic oracle's run ends in
`o` after `τ`. -/
theorem run_ub (τ : List E) (o : Outcome R) (hb : o.isBad P.bad = true) :
    Beh P (.fin τ o) ↔
      ∃ δ : Oracle, Admissible P δ ∧
        (∀ π, ∃ n, (run δ π n P).badOrRejected P.bad = true) ∧
        ∃ π n, run δ π n P = .fin τ o := by
  constructor
  · intro h
    obtain ⟨δ, hadm, hbor, π, n, hr⟩ := ub_strategy P h hb
    exact ⟨δ, hadm, hbor, π, n, hr⟩
  · intro ⟨δ, hadm, hbor, π, n, hr⟩
    exact behT_of_strategy P hb n _ δ π τ hadm hbor hr

end Ub2

/-! ## Programs: the MiniRust slice, the counter-example and the controls -/

/-- MiniRust's UB termination. -/
def isUb : MR_TerminationInfo → Bool
  | .Ub _ => true
  | _ => false

section Programs
variable {E S R : Type} (P : Prog E S R)

/-- A step with no demonic choice. -/
inductive NoPick : SOut (List E × (S ⊕ R)) → Prop
  | ok (a : List E × (S ⊕ R)) : NoPick (.ok a)
  | panic (m : String) : NoPick (.panic m)
  | fuel : NoPick .fuel
  | refused (w : String) : NoPick (.refused w)
  | nobehavior : NoPick .nobehavior
  | reject : NoPick .reject
  | predict {k : Nat → SOut (List E × (S ⊕ R))} : (∀ i, NoPick (k i)) → NoPick (.predict k)

/-- Every demonic oracle is admissible for a program with no demonic choice. -/
theorem admissible_of_noPick (hp : ∀ s, NoPick (P.step s)) (δ : Oracle) : Admissible P δ := by
  have key : ∀ n (t : SOut (List E × (S ⊕ R))), NoPick t → ∀ δ π, admC P n t δ π := by
    intro n
    induction n with
    | zero => intro t _ δ π; trivial
    | succ n ihn =>
      intro t ht
      induction ht with
      | ok a =>
        intro δ π
        obtain ⟨τ, x⟩ := a
        cases x with
        | inl s => rw [admC_inl]; exact ihn _ (hp s) δ π
        | inr r => trivial
      | panic m => intro δ π; trivial
      | fuel => intro δ π; trivial
      | refused w => intro δ π; trivial
      | nobehavior => intro δ π; trivial
      | reject => intro δ π; trivial
      | predict _ ih => intro δ π; rw [admC_predict]; exact ih _ _ _
  exact fun π n => key n _ (hp _) δ π

end Programs

/-! ### The generated MiniRust slice as a program

The state is the machine (`none` before `MRf.Machine.new` built it); a step is the
generated `MRf.Machine.step` at call-depth fuel `fuel`, as K8's driver runs it; a
result is MiniRust's `TerminationInfo`, and `Ub` is the bad one. The four theorems
hold for it as for every program; `core_wf` needs its live-step premise, which the
generated slice does not yet discharge (RM1's remaining work). -/

def miniRustStep (fuel : Nat) (prog : MR_Program) :
    Option MR_Machine → SOut (List Unit × (Option MR_Machine ⊕ MR_TerminationInfo))
  | none => SOut.bind (MRf.Machine.new fuel prog () () ()) fun r =>
      match r with
      | SRes.ok m => SOut.ok ([], .inl (some m))
      | SRes.err t => SOut.ok ([], .inr t)
  | some m => SOut.bind (MRf.Machine.step fuel m) fun p =>
      match p with
      | (SRes.ok _, m2) => SOut.ok ([], .inl (some m2))
      | (SRes.err t, _) => SOut.ok ([], .inr t)

def miniRust (fuel : Nat) (prog : MR_Program) : Prog Unit (Option MR_Machine) MR_TerminationInfo :=
  ⟨none, miniRustStep fuel prog, isUb⟩

theorem miniRust_run_sound (fuel : Nat) (prog : MR_Program) (δ π : Oracle) (n : Nat)
    (τ : List Unit) (o : Outcome MR_TerminationInfo) :
    run δ π n (miniRust fuel prog) = .fin τ o → o.isBad isUb = false →
      Beh (miniRust fuel prog) (.fin τ o) :=
  run_sound _ δ π n τ o

theorem miniRust_run_ub (fuel : Nat) (prog : MR_Program) (τ : List Unit) (m : String) :
    Beh (miniRust fuel prog) (.fin τ (.done (.Ub m))) ↔
      ∃ δ : Oracle, Admissible (miniRust fuel prog) δ ∧
        (∀ π, ∃ n, (run δ π n (miniRust fuel prog)).badOrRejected isUb = true) ∧
        ∃ π n, run δ π n (miniRust fuel prog) = .fin τ (.done (.Ub m)) :=
  run_ub _ τ _ rfl

theorem miniRust_run_adequate (fuel : Nat) (prog : MR_Program) :
    (∀ τ o, Beh (miniRust fuel prog) (.fin τ o) →
      ∃ δ π : Oracle, ∃ n, run δ π n (miniRust fuel prog) = .fin τ o) ∧
    (∀ σ, Beh (miniRust fuel prog) (.div σ) →
      ∀ k, ∃ δ π : Oracle, run δ π k (miniRust fuel prog) = .cut (σ k)) :=
  run_adequate (miniRust fuel prog)

theorem miniRust_core_wf (fuel : Nat) (prog : MR_Program)
    (hwf : ∀ s, ¬ Dead (miniRust fuel prog) (miniRustStep fuel prog s)) :
    ∃ b, Beh (miniRust fuel prog) b :=
  core_wf _ hwf

-- tests::abort::abort, K8's record 0 (generated/conformance.lean.gz), verbatim.
def k8p_0 : MR_Program := (MR_Program.mk [((MR_FnName.mk (0 : Nat)), (MR_Function.mk [((MR_LocalName.mk (0 : Nat)), (MR_Type.Tuple ([] : List (Int × MR_Type)) (MR_TupleHeadLayout.mk (0 : Int) (1 : Int) (none : Option Int)) (none : Option MR_Type)))] ([] : List MR_LocalName) (MR_LocalName.mk (0 : Nat)) MR_CallingConvention.C [((MR_BbName.mk (0 : Nat)), (MR_BasicBlock.mk ([] : List MR_Statement) (MR_Terminator.Intrinsic MR_IntrinsicOp.Abort ([] : List MR_ValueExpr) (MR_PlaceExpr.Deref (MR_ValueExpr.Constant (MR_Constant.PointerWithoutProvenance (1 : Int)) (MR_Type.Ptr (MR_PtrType.Raw MR_PointerMetaKind.None))) (MR_Type.Tuple ([] : List (Int × MR_Type)) (MR_TupleHeadLayout.mk (0 : Int) (1 : Int) (none : Option Int)) (none : Option MR_Type))) (none : Option MR_BbName)) MR_BbKind.Regular))] (MR_BbName.mk (0 : Nat))))] (MR_FnName.mk (0 : Nat)) ([] : List (MR_GlobalName × MR_Global)) ([] : List (MR_TraitName × List MR_TraitMethodName)) ([] : List (MR_VTableName × MR_VTable)))

/-- The oracle the abort run uses: the first demonic choice (an allocation's
address) takes candidate 1000, every later one candidate 0; every prediction 0. (The all-zero oracle's run is rejected: its allocation candidate fails
the allocator's predicate.) -/
def abortδ : Oracle := fun h => if h.length = 0 then 1000 else 0

/-- The relational semantics runs the generated code: K8's first minitest ends in
`Abort` after two steps (build the machine, step it) under `abortδ`, and that run
is a behaviour. -/
def abortRunClaim (t : MR_TerminationInfo) : Prop :=
  run abortδ (fun _ => 0) 2 (miniRust 2000 k8p_0) = .fin [] (.done t)

theorem miniRust_abort_run : abortRunClaim .Abort :=
  rfl

theorem miniRust_zero_rejected : run (fun _ => 0) (fun _ => 0) 2 (miniRust 2000 k8p_0) = .rejected :=
  rfl

theorem miniRust_abort : Beh (miniRust 2000 k8p_0) (.fin [] (.done .Abort)) :=
  run_sound _ _ _ 2 [] _ miniRust_abort_run rfl

/-! ### The committed counter-example: naive `run_sound` fails for two casts

Two allocations are live, ids 0 and 1. The program casts an address inside
allocation 0 to a pointer, then one inside allocation 1, and writes through both.
Each integer-to-pointer cast predicts its provenance (LD-3's per-cast angelic
prediction; an index past the two allocations is rejected), and a write through a
pointer whose predicted provenance is not the allocation its address lies in is
UB. -/

def ubAt (m : String) : SOut (List Unit × (Unit ⊕ MR_TerminationInfo)) := .ok ([], .inr (.Ub m))

def stopAt : SOut (List Unit × (Unit ⊕ MR_TerminationInfo)) := .ok ([], .inr .MachineStop)

def twoCast : Prog Unit Unit MR_TerminationInfo where
  init := ()
  step := fun _ => .predict fun p₀ =>
    match p₀ with
    | 0 => .predict fun p₁ =>
      match p₁ with
      | 0 => ubAt "write through ptr1: provenance mismatch"
      | 1 => stopAt
      | _ => .reject
    | 1 => .predict fun p₁ =>
      match p₁ with
      | 0 => ubAt "write through ptr0: provenance mismatch"
      | 1 => ubAt "write through ptr0: provenance mismatch"
      | _ => .reject
    | _ => .reject
  bad := isUb

/-- The naive statement: every run that ends, UB runs included, is a behaviour. -/
def NaiveRunSound {E S R : Type} (P : Prog E S R) : Prop :=
  ∀ (δ π : Oracle) (n : Nat) (τ : List E) (o : Outcome R), run δ π n P = .fin τ o → Beh P (.fin τ o)

/-- What the all-zero oracle's one-step run of `twoCast` returns. -/
def zeroRunClaim (m : String) : Prop :=
  run (fun _ => 0) (fun _ => 0) 1 twoCast = .fin [] (.done (.Ub m))

/-- The all-zero oracle predicts allocation 0 for both casts; the second write is UB. -/
theorem twoCast_zero_run : zeroRunClaim "write through ptr1: provenance mismatch" :=
  rfl

/-- ... but that UB run is not a behaviour: the prediction (0, 1) avoids UB. -/
theorem twoCast_ub_not_beh (τ : List Unit) (m : String) : ¬ Beh twoCast (.fin τ (.done (.Ub m))) := by
  intro h
  have hm : MustUB twoCast (twoCast.step ()) := behT_bad_mustUB twoCast h rfl
  cases hm with
  | predict i _ hall =>
    have h0 := hall 0 (by
      intro hd
      cases hd with
      | predict hd =>
        have := hd 1
        cases this)
    cases h0 with
    | predict i' _ hall' =>
      have h1 := hall' 1 (by intro hd; cases hd)
      cases h1 with
      | bad hb => cases hb

/-- Its UB-free run is a behaviour. -/
theorem twoCast_done : Beh twoCast (.fin [] (.done .MachineStop)) :=
  run_sound twoCast (fun _ => 0) (Oracle.cons 0 (Oracle.cons 1 fun _ => 0)) 1 [] _ rfl rfl

theorem naive_run_sound_fails : ¬ NaiveRunSound twoCast := fun h =>
  twoCast_ub_not_beh [] _ (h _ _ 1 [] _ twoCast_zero_run)

/-! ### Control: when every prediction fails, the UB run is a behaviour (by `run_ub`) -/

def twoCastBad : Prog Unit Unit MR_TerminationInfo where
  init := ()
  step := fun _ => .predict fun p₀ =>
    match p₀ with
    | 0 => .predict fun p₁ =>
      match p₁ with
      | 0 => ubAt "write outside every allocation"
      | 1 => ubAt "write outside every allocation"
      | _ => .reject
    | 1 => .predict fun p₁ =>
      match p₁ with
      | 0 => ubAt "write outside every allocation"
      | 1 => ubAt "write outside every allocation"
      | _ => .reject
    | _ => .reject
  bad := isUb

theorem twoCastBad_noPick (s : Unit) : NoPick (twoCastBad.step s) := by
  refine .predict fun p => ?_
  match p with
  | 0 => exact .predict fun q => match q with | 0 => .ok _ | 1 => .ok _ | _ + 2 => .reject
  | 1 => exact .predict fun q => match q with | 0 => .ok _ | 1 => .ok _ | _ + 2 => .reject
  | _ + 2 => exact .reject

theorem twoCastBad_forced (π : Oracle) :
    ∃ n, (run (fun _ => 0) π n twoCastBad).badOrRejected isUb = true := by
  refine ⟨1, ?_⟩
  show RunRes.badOrRejected isUb (runC twoCastBad 1 (twoCastBad.step ()) (fun _ => 0) π) = true
  show RunRes.badOrRejected isUb (runC twoCastBad (0 + 1) (.predict _) (fun _ => 0) π) = true
  rw [runC_predict]
  generalize π.after (π []) = π'
  match π [] with
  | 0 =>
    show RunRes.badOrRejected isUb (runC twoCastBad (0 + 1) (.predict _) _ π') = true
    rw [runC_predict]
    match π' [] with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  | 1 =>
    show RunRes.badOrRejected isUb (runC twoCastBad (0 + 1) (.predict _) _ π') = true
    rw [runC_predict]
    match π' [] with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  | _ + 2 => rfl

theorem twoCastBad_ub : Beh twoCastBad (.fin [] (.done (.Ub "write outside every allocation"))) :=
  (run_ub twoCastBad [] _ rfl).mpr
    ⟨fun _ => 0, admissible_of_noPick twoCastBad twoCastBad_noPick _, twoCastBad_forced,
      fun _ => 0, 1, rfl⟩

/-! ### Controls for the departures from the plan's wording

1. `run_ub` does not ask the UB trace to be common to every prediction: two
   predictions that reach UB after different events make that version false. -/

def twoTrace : Prog Unit Unit MR_TerminationInfo where
  init := ()
  step := fun _ => .predict fun p =>
    match p with
    | 0 => .ok ([()], .inr (.Ub "a"))
    | 1 => .ok ([(), ()], .inr (.Ub "b"))
    | _ => .reject
  bad := isUb

/-- The plan's wording of `run_ub`'s right side: one trace for every prediction
(rejected predictions excepted). -/
def CommonTraceUB {E S R : Type} (P : Prog E S R) (τ : List E) (o : Outcome R) : Prop :=
  ∃ δ : Oracle, Admissible P δ ∧ ∀ π, ∃ n, run δ π n P = .fin τ o ∨ run δ π n P = .rejected

theorem twoTrace_ub : Beh twoTrace (.fin [()] (.done (.Ub "a"))) := by
  refine BehT.predictUB 0 .done rfl (.predict 0 (.bad rfl) fun j hj => ?_)
  match j, hj with
  | 0, _ => exact .bad rfl
  | 1, _ => exact .bad rfl
  | _ + 2, hj => exact absurd .reject hj

theorem twoTrace_not_common : ¬ CommonTraceUB twoTrace [()] (.done (.Ub "a")) := by
  intro ⟨δ, _, h⟩
  obtain ⟨n, hn⟩ := h (fun _ => 1)
  cases n with
  | zero => rcases hn with hn | hn <;> cases hn
  | succ n =>
    have e : run δ (fun _ => 1) (n + 1) twoTrace = .fin [(), ()] (.done (.Ub "b")) := rfl
    rw [e] at hn
    rcases hn with hn | hn
    · simp at hn
    · cases hn

theorem run_ub_common_trace_fails :
    ¬ ∀ (τ : List Unit) (o : Outcome MR_TerminationInfo), o.isBad isUb = true →
      (Beh twoTrace (.fin τ o) ↔ CommonTraceUB twoTrace τ o) :=
  fun h => twoTrace_not_common ((h _ _ rfl).mp twoTrace_ub)

/-! 2. `Beh` holds divergence. A program that only loops has no finite behaviour, so
   without divergence its behaviour set is empty and `core_wf` false. -/

def loopP : Prog Unit Unit MR_TerminationInfo := ⟨(), fun _ => .ok ([], .inl ()), isUb⟩

theorem loopP_diverges : Beh loopP (.div fun _ => []) :=
  ⟨fun _ => (), rfl, rfl, fun _ => ⟨[], .here, rfl⟩⟩

theorem loopP_no_fin (τ : List Unit) (o : Outcome MR_TerminationInfo) : ¬ Beh loopP (.fin τ o) := by
  have key : ∀ t τ o, BehT loopP t τ o → t = .ok ([], .inl ()) → False := by
    intro t τ o h
    induction h with
    | done => intro e; cases e
    | step _ ih => intro _; exact ih rfl
    | panic m => intro e; cases e
    | fuel => intro e; cases e
    | refused w => intro e; cases e
    | nobehavior => intro e; cases e
    | pick _ _ _ => intro e; cases e
    | predictOk _ _ _ _ => intro e; cases e
    | predictUB _ _ _ _ _ => intro e; cases e
  exact fun h => key _ τ o h rfl

/-! 3. An angelic prediction may avoid UB by diverging (the review's example): the
   prediction 0 loops, the prediction 1 is UB; the loop is a behaviour, the UB is
   not. -/

def divOrUB : Prog Unit Unit MR_TerminationInfo where
  init := ()
  step := fun _ => .predict fun p =>
    match p with
    | 0 => .ok ([], .inl ())
    | 1 => ubAt "the other prediction"
    | _ => .reject
  bad := isUb

theorem divOrUB_diverges : Beh divOrUB (.div fun _ => []) :=
  ⟨fun _ => (), rfl, rfl, fun _ => ⟨[], .predict 0 .here, rfl⟩⟩

theorem divOrUB_no_ub (τ : List Unit) (m : String) : ¬ Beh divOrUB (.fin τ (.done (.Ub m))) := by
  have live : ¬ Dead divOrUB (.ok ([], .inl ())) := by
    intro hd
    cases hd with
    | step hd =>
      cases hd with
      | predict hd =>
        have := hd 1
        cases this
  have key : ∀ t, MustUB divOrUB t → t = divOrUB.step () ∨ t = .ok ([], .inl ()) → False := by
    intro t h
    induction h with
    | bad _ => intro e; rcases e with e | e <;> cases e
    | @step τ s _ ih => intro _; exact ih (.inl rfl)
    | pick _ _ _ => intro e; rcases e with e | e <;> cases e
    | predict i _ _ _ ihall =>
      intro e
      rcases e with e | e
      · cases e
        exact ihall 0 live (.inr rfl)
      · cases e
  intro h
  exact key _ (behT_bad_mustUB divOrUB h rfl) (.inl rfl)

/-! 4. `core_wf` needs its premise: a program whose step rejects every resolution
   has no behaviour at all. -/

def deadP : Prog Unit Unit MR_TerminationInfo := ⟨(), fun _ => .reject, isUb⟩

theorem deadP_no_beh : ¬ ∃ b, Beh deadP b := by
  intro ⟨b, h⟩
  cases b with
  | fin τ o => cases h
  | div σ =>
    obtain ⟨st, _, _, hstep⟩ := h
    obtain ⟨τ, hr, _⟩ := hstep 0
    cases hr

/-- The unconditional `core_wf`, false (the reference-entry test offers `core_wf`'s
proof for it and requires a refusal). -/
def CoreWfUnconditional : Prop := ∀ P : Prog Unit Unit MR_TerminationInfo, ∃ b, Beh P b

theorem core_wf_unconditional_fails : ¬ CoreWfUnconditional := fun h => deadP_no_beh (h deadP)

end TrustSem
