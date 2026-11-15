/-
  VF5Sound — `vc_sound_F1`: a refuted verification condition makes the
  function `Valid_R` over SemR.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import VF5Frame

set_option linter.unusedVariables false

namespace VF5
open SemR

variable {m : Module}

/-- The invariant: a frame state the symbolic executor covers. -/
def Inv (m : Module) (A : Nat → List Cons) (fn : Func) (sig : FuncTy) (k : Core) : Prop :=
  k.fn = fn ∧ k.sig = sig ∧ ∃ n s ρ, Rel m ρ s k ∧ ∀ p ∈ sx m A fn sig n s, Unsat p

theorem inv_step {m : Module} {A : Nat → List Cons} {fn : Func} {sig : FuncTy} {k : Core}
    (h : Inv m A fn sig k) :
    ¬ LBad m A k ∧ EnvOK m k.env ∧ ∀ k', LStep m A k k' → Inv m A fn sig k' := by
  obtain ⟨hfn, hsig, n, s, ρ, hrel, hob⟩ := h
  cases n with
  | zero => exact fail_refutes hob
  | succ n =>
  simp only [sx, sxC] at hob
  have hnth : nth? k.block.body k.pc = nth? s.blk.body s.pc := by rw [hrel.blk, hrel.pc]
  split at hob
  · exact fail_refutes hob
  · next node hnode =>
  rw [← hnth] at hnode
  refine ⟨?_, envOK_of_rel hrel.env, ?_⟩
  · intro hbad
    cases hbad with
    | missing h => rw [hnode] at h; exact nomatch h
    | exec node' o h hloc he hb =>
      rw [hnode] at h; cases h
      exact (step_local hrel hob hfn hloc).1 o he hb
    | outside node' h hloc hc hr =>
      rw [hnode] at h; cases h
      exact step_outside hrel hob hloc hc hr
    | callArgs node' callee args o h hi hg =>
      rw [hnode] at h; cases h
      obtain ⟨vs, _, _, hg', _⟩ := (step_call hrel hob hi).vals
      rw [hg] at hg'; exact nomatch hg'
    | callFn node' callee args vs h hi hg hf =>
      rw [hnode] at h; cases h
      obtain ⟨vs', f, csig, _, hf', _⟩ := (step_call hrel hob hi).vals
      rw [hf] at hf'; exact nomatch hf'
    | callEnter node' callee args vs f csig h hi hg hf he =>
      rw [hnode] at h; cases h
      obtain ⟨vs', f', csig', hg', hf', he', _⟩ := (step_call hrel hob hi).vals
      rw [hg] at hg'; cases hg'; rw [hf] at hf'; cases hf'
      rw [he] at he'; exact nomatch he'
    | callPre node' callee args vs f csig h hi hg hf hp =>
      rw [hnode] at h; cases h
      obtain ⟨vs', f', csig', hg', hf', _, hp', _⟩ := (step_call hrel hob hi).vals
      rw [hg] at hg'; cases hg'
      exact hp hp'
    | retArgs node' xs o h hi hg =>
      rw [hnode] at h; cases h
      obtain ⟨vs, hg', _⟩ := step_ret hrel hob hsig hi
      rw [hg] at hg'; exact nomatch hg'
    | retSig node' xs vs o h hi hg hc =>
      rw [hnode] at h; cases h
      obtain ⟨vs', hg', hc'⟩ := step_ret hrel hob hsig hi
      rw [hg] at hg'; cases hg'
      rw [hc] at hc'; exact nomatch hc'
  · intro k' hstep
    cases hstep with
    | exec node' h hloc he =>
      rw [hnode] at h; cases h
      obtain ⟨s', ρ', hrel', hob'⟩ := (step_local hrel hob hfn hloc).2 k' he
      have hc := execNode_local_ctx hloc he
      simp only [ctxOf, Prod.mk.injEq] at hc
      exact ⟨hc.1.trans hfn, hc.2.1.trans hsig, n, s', ρ', hrel', hob'⟩
    | call node' callee args vs f csig rs h hi hg hf hrs hb =>
      rw [hnode] at h; cases h
      obtain ⟨s', ρ', hrel', hob'⟩ := (step_call hrel hob hi).next vs f csig rs k' hg hf hrs hb
      have hc := (bindResults_ctx hb).trans (next_ctx k)
      simp only [ctxOf, Prod.mk.injEq] at hc
      exact ⟨hc.1.trans hfn, hc.2.1.trans hsig, n, s', ρ', hrel', hob'⟩

theorem inv_star {m : Module} {A : Nat → List Cons} {fn : Func} {sig : FuncTy} {k k' : Core}
    (hs : LStar m A k k') (h : Inv m A fn sig k) : ¬ LBad m A k' ∧ EnvOK m k'.env := by
  induction hs with
  | refl k => exact ⟨(inv_step h).1, (inv_step h).2.1⟩
  | step k1 k2 k3 h12 _ ih => exact ih ((inv_step h).2.2 k2 h12)

/-! ## Entry -/

/-- The argument assignment reads the parameters as variables `i, i+1, …`. -/
def ArgsAt (ρ : Nat → Int) (i : Nat) (args : List Val) : Prop :=
  ∀ j v, nth? args j = some v → ρ (i + j) = valInt v

theorem entryVals_cover : ∀ (ts : List Ty) (i : Nat) (args : List Val) (ρ : Nat → Int)
    (R : List (List Cons × List SV)), entryVals m ts i = some R → ArgsOK m ts args → ArgsAt ρ i args →
    ∃ x ∈ R, Sat x.1 ρ ∧ ValsRel m ρ x.2 args ∧ CsScoped (i + ts.length) x.1 ∧
      ∀ s ∈ x.2, s.Scoped (i + ts.length)
  | [], i, args, ρ, R, hR, hok, hat => by
    cases args with
    | cons _ _ => exact nomatch hok
    | nil =>
      simp only [entryVals, Option.some.injEq] at hR; subst hR
      exact ⟨_, List.Mem.head _, sat_nil ρ, trivial, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | t :: ts, i, args, ρ, R, hR, hok, hat => by
    cases args with
    | nil => exact nomatch hok
    | cons v rest =>
    obtain ⟨h1, h2, h3⟩ := hok
    have hat' : ArgsAt ρ (i + 1) rest := by
      intro j v' hj
      have := hat (j + 1) v' (by simpa [nth?] using hj)
      rw [← this]; congr 1; omega
    have hv : ρ i = valInt v := by have := hat 0 v (by simp [nth?]); simpa using this
    cases t with
    | int t =>
      simp only [entryVals] at hR
      split at hR
      · split at hR
        · exact nomatch hR
        · next R' hR' =>
          simp only [Option.some.injEq] at hR; subst hR
          obtain ⟨a, rfl, ha⟩ := argsOK_int h1 h2
          obtain ⟨⟨c', svs'⟩, hx', hsat, hvs, hsc, hss⟩ := entryVals_cover ts (i + 1) rest ρ R' hR' h3 hat'
          simp only at hsat hvs hsc hss
          have hia : ρ i = a := by simpa [valInt] using hv
          refine ⟨_, List.mem_map.mpr ⟨(c', svs'), hx', rfl⟩, ?_, ⟨⟨a, rfl, ha, by simp [hia]⟩, hvs⟩, ?_, ?_⟩
          · refine Sat.append (fun c hc => ?_) hsat
            simp only [rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl <;> rw [sat_le0] <;> simp [hia, Mw] <;> omega
          · refine CsScoped.append (fun c hc => ?_) (by simpa [Nat.add_assoc, Nat.add_comm 1] using hsc)
            simp only [rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl
            · exact scoped_le0 (scoped_smul _ (scoped_v (by simp)))
            · exact scoped_le0 (scoped_addC _ (scoped_v (by simp)))
          · intro s hs
            simp only [List.mem_cons] at hs
            rcases hs with rfl | hs
            · exact scoped_v (by simp)
            · simpa [Nat.add_assoc, Nat.add_comm 1] using hss s hs
      · exact nomatch hR
    | bool =>
      simp only [entryVals] at hR
      split at hR
      · exact nomatch hR
      · next R' hR' =>
        simp only [Option.some.injEq] at hR; subst hR
        obtain ⟨b, rfl⟩ := argsOK_bool h1 h2
        obtain ⟨⟨c', svs'⟩, hx', hsat, hvs, hsc, hss⟩ := entryVals_cover ts (i + 1) rest ρ R' hR' h3 hat'
        simp only at hsat hvs hsc hss
        have hsc' : CsScoped (i + (ts.length + 1)) c' := by simpa [Nat.add_assoc, Nat.add_comm 1] using hsc
        have hvi : (Aff.v i).Scoped (i + (ts.length + 1)) := scoped_v (by omega)
        cases b
        · refine ⟨(le0 (Aff.v i) :: c', .bool false :: svs'), ?_, ?_, ⟨rfl, hvs⟩, ?_, ?_⟩
          · simp only [List.mem_flatMap]; exact ⟨(c', svs'), hx', by simp⟩
          · exact sat_cons.mpr ⟨by rw [sat_le0]; simp [hv, valInt], hsat⟩
          · intro c hc; cases hc with
            | head => exact scoped_le0 hvi
            | tail _ hc => simpa using hsc' c hc
          · intro s hs; simp only [List.mem_cons] at hs
            rcases hs with rfl | hs
            · trivial
            · simpa [Nat.add_assoc, Nat.add_comm 1] using hss s hs
        · refine ⟨(le0 ((Aff.c 1).sub (Aff.v i)) :: le0 ((Aff.v i).addC (-1)) :: c', .bool true :: svs'),
            ?_, ?_, ⟨rfl, hvs⟩, ?_, ?_⟩
          · simp only [List.mem_flatMap]; exact ⟨(c', svs'), hx', by simp⟩
          · exact sat_cons.mpr ⟨by rw [sat_le0]; simp [hv, valInt],
              sat_cons.mpr ⟨by rw [sat_le0]; simp [hv, valInt], hsat⟩⟩
          · intro c hc; cases hc with
            | head => exact scoped_le0 (scoped_sub (scoped_c _ _) hvi)
            | tail _ hc => cases hc with
              | head => exact scoped_le0 (scoped_addC _ hvi)
              | tail _ hc => simpa using hsc' c hc
          · intro s hs; simp only [List.mem_cons] at hs
            rcases hs with rfl | hs
            · trivial
            · simpa [Nat.add_assoc, Nat.add_comm 1] using hss s hs
    | enum id =>
      simp only [entryVals] at hR
      split at hR
      · next es R' hes hR' =>
        simp only [Option.some.injEq] at hR; subst hR
        obtain ⟨lanes, rfl, hok⟩ := argsOK_enum h1 h2
        obtain ⟨es', hes', hmem⟩ := enumVals_mem hok
        rw [hes] at hes'; cases hes'
        obtain ⟨⟨c', svs'⟩, hx', hsat, hvs, hsc, hss⟩ := entryVals_cover ts (i + 1) rest ρ R' hR' h3 hat'
        simp only at hsat hvs hsc hss
        refine ⟨(c', .enm id lanes :: svs'), ?_, hsat, ⟨⟨rfl, hok⟩, hvs⟩, ?_, ?_⟩
        · simp only [List.mem_flatMap, List.mem_map]; exact ⟨(c', svs'), hx', _, hmem, rfl⟩
        · simpa [Nat.add_assoc, Nat.add_comm 1] using hsc
        · intro s hs; simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · trivial
          · simpa [Nat.add_assoc, Nat.add_comm 1] using hss s hs
      · exact nomatch hR
    | _ => simp [entryVals] at hR

theorem argsAt_argρ (args : List Val) : ArgsAt (argρ args) 0 args := by
  intro j v h; simp [argρ, h]

theorem argsOK_checkSig :
    ∀ {ts : List Ty} {vs : List Val}, ArgsOK m ts vs → checkSig 64 vs ts = .ok ()
  | [], [], _ => rfl
  | t :: ts, v :: vs, ⟨h1, h2, h3⟩ => by
    have hp : rejectPoison v "signature boundary" = .ok () := by
      cases v <;> simp [ValOK] at h2 <;> rfl
    simp [checkSig, hp, h1, valOK_expectTy h2 h1, argsOK_checkSig h3]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem fnOf_find {m : Module} {fid : Nat} {f : Func} {sig : FuncTy} (h : fnOf m fid = some (f, sig)) :
    m.functions.find? (fun g => g.id == fid) = some f ∧ nth? m.funcTys f.ty = some sig := by
  simp only [fnOf] at h
  split at h
  · exact nomatch h
  · next f' hf =>
    split at h
    · exact nomatch h
    · next sig' hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hf, hs⟩

/-- **`vc_sound_F1`**: when every obligation of `vc m A fid` is refuted, the
    function is `Valid_R`: from any well-typed in-range entry meeting `A fid`,
    in any outer context, no frame state it reaches goes wrong (callees read
    through `A`). -/
theorem vc_sound_F1 (m : Module) (A : Nat → List Cons) (fid : Nat)
    (h : ∀ p ∈ vc m A fid, Unsat p) : Valid_R m A fid := by
  simp only [vc, vcC] at h
  split at h
  · exact fail_refutes h
  · next ht =>
  have htarget : F1Target m := by simpa [F1Target] using ht
  refine ⟨htarget, ?_⟩
  split at h
  · exact fail_refutes h
  · next htexec =>
  have hexec : m.executableTarget = true := by simpa using htexec
  refine ⟨hexec, ?_⟩
  split at h
  · exact fail_refutes h
  · next f sig hfs =>
  split at h
  · exact fail_refutes h
  · next hvb =>
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hvb
  split at h
  · exact fail_refutes h
  · next b hb =>
  split at h
  · exact fail_refutes h
  · next hpre =>
  split at h
  · exact fail_refutes h
  · next es hes =>
  refine ⟨f, sig, hfs, fun args depth hargs hpreA => ?_⟩
  obtain ⟨⟨c, svs⟩, hx, hsat, hvs, hsc, hss⟩ :=
    entryVals_cover sig.params 0 args (argρ args) es hes hargs (argsAt_argρ args)
  simp only [Nat.zero_add] at hsc hss
  have hob : ∀ p ∈ (match sbindParams [] b.params svs with
      | none => FAIL
      | some env => sx m A f sig (budget f)
          { blk := b, pc := 0, env := env, cs := c ++ A fid, nv := sig.params.length }), Unsat p :=
    fun p hp => h p (List.mem_flatMap.mpr ⟨(c, svs), hx, hp⟩)
  split at hob
  · exact fail_refutes hob
  · next env henv =>
  obtain ⟨ce, hce, hrel⟩ := sbindParams_rel (se := []) (ce := []) trivial hvs henv
  obtain ⟨hfind, hnth⟩ := fnOf_find hfs
  refine ⟨{ fn := f, sig := sig, block := b, pc := 0, env := ce, depth := depth, stack := [],
            openFrames := [], nextFrame := 0, mem := Mem.empty }, ?_, ?_⟩
  · simp [start, hfind, hnth, hvb.2, hvb.1, argsOK_checkSig hargs, hb, hce, htarget, hexec]
  · intro cx k hstar
    refine inv_star hstar ⟨rfl, rfl, budget f, _, argρ args, ⟨rfl, rfl, hrel, ?_, ?_, ?_, htarget⟩, hob⟩
    · exact Sat.append hsat hpreA
    · exact sbindParams_scoped (fun p (h : p ∈ ([] : List (Nat × SV))) => nomatch h) hss henv
    · refine CsScoped.append hsc (fun c' hc' => ?_)
      simp at hpre
      exact hpre c' hc'

end VF5
