import VF5Step

set_option linter.unusedVariables false

namespace VF5
open SemR

variable {m : Module}

theorem argsOK_int {t : IntTy} {v : Val} (h1 : v.ty.beq (.int t) = true) (h2 : ValOK m v) :
    ∃ a, v = .int t a ∧ a < modulus t.bits := by
  cases v <;> simp [Val.ty, Ty.beq, ValOK] at h1 h2
  next t' a => exact ⟨a, by rw [code_inj h1], by rw [← code_inj h1]; exact h2⟩

theorem argsOK_bool {v : Val} (h1 : v.ty.beq .bool = true) (h2 : ValOK m v) : ∃ b, v = .bool b := by
  cases v <;> simp [ValOK] at h2
  · simp [Val.ty, Ty.beq] at h1
  · exact ⟨_, rfl⟩
  · simp [Val.ty, Ty.beq] at h1

theorem argsOK_enum {id : Nat} {v : Val} (h1 : v.ty.beq (.enum id) = true) (h2 : ValOK m v) :
    ∃ lanes, v = .enum id lanes ∧ EnumOK m id lanes := by
  cases v <;> simp [ValOK] at h2 <;> simp [Val.ty, Ty.beq] at h1
  next id' lanes => subst h1; exact ⟨lanes, rfl, h2⟩

theorem enumVals_mem {id : Nat} {lanes : List Val} (h : EnumOK m id lanes) :
    ∃ es, enumVals m id = some es ∧ SV.enm id lanes ∈ es := by
  obtain ⟨d, hd, hf, disc, hdm, rfl⟩ := h
  exact ⟨d.discs.map fun disc => .enm id [.int d.tag (resid d.tag.bits disc)],
    by simp [enumVals, hd, hf], List.mem_map.mpr ⟨disc, hdm, rfl⟩⟩

theorem freshVals_cover : ∀ (ts : List Ty) (nv : Nat) (rs : List Val) (ρ : Nat → Int)
    (R : List (List Cons × List SV × Nat)), freshVals m ts nv = some R → ArgsOK m ts rs →
    ∃ x ∈ R, BrCovers m ρ nv ⟨x.1, x.2.1, x.2.2⟩ rs
  | [], nv, rs, ρ, R, hR, hok => by
    cases rs with
    | cons _ _ => exact nomatch hok
    | nil =>
      simp only [freshVals, Option.some.injEq] at hR; subst hR
      exact ⟨_, List.Mem.head _, ρ, Agree.refl _ _, sat_nil ρ, Nat.le_refl _, (fun _ h => nomatch h),
        rfl, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | t :: ts, nv, rs, ρ, R, hR, hok => by
    cases rs with
    | nil => exact nomatch hok
    | cons v rs =>
    obtain ⟨h1, h2, h3⟩ := hok
    cases t with
    | int t =>
      simp only [freshVals] at hR
      split at hR
      · exact nomatch hR
      · next R' hR' =>
        simp only [Option.some.injEq] at hR; subst hR
        obtain ⟨a, rfl, ha⟩ := argsOK_int h1 h2
        obtain ⟨⟨c', svs', n'⟩, hx', ρ2, hag, hsat, hnv, hsc, hlen, hvals, hvsc⟩ :=
          freshVals_cover ts (nv + 1) rs (upd ρ nv a) R' hR' h3
        simp only at hnv hsc hvsc hlen hvals hsat
        refine ⟨_, List.mem_map.mpr ⟨(c', svs', n'), hx', rfl⟩, ρ2, ?_, ?_, by simp only; omega, ?_, by simp [hlen], ?_, ?_⟩
        · exact (agree_upd ρ nv a).trans (hag.mono (Nat.le_succ _))
        · obtain ⟨ρ', _, hs1, hsc1, _, _⟩ := fresh_covers (m := m) ρ nv t a ha
          refine Sat.append (fun c hc => ?_) hsat
          have hc1 := hsc1 c hc
          have : c.sat (upd ρ nv a) := by
            simp only [rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl <;> rw [sat_le0] <;> simp [upd, Mw] <;> omega
          exact (sat_congr hc1 hag).mp this
        · exact CsScoped.append (fun c hc => Nat.le_trans ((fresh_covers (m := m) ρ nv t a ha).choose_spec.2.2.1 c hc)
            (by omega)) hsc
        · intro p hp
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨a, rfl, ha, by simp; rw [← hag nv (by omega)]; simp⟩
          · exact hvals p hp
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact scoped_v (show nv < n' by omega)
          · exact hvsc s hs
    | bool =>
      simp only [freshVals] at hR
      split at hR
      · exact nomatch hR
      · next R' hR' =>
        simp only [Option.some.injEq] at hR; subst hR
        obtain ⟨b, rfl⟩ := argsOK_bool h1 h2
        obtain ⟨⟨c', svs', n'⟩, hx', ρ2, hag, hsat, hnv, hsc, hlen, hvals, hvsc⟩ :=
          freshVals_cover ts nv rs ρ R' hR' h3
        simp only at hnv hsc hvsc hlen hvals hsat
        refine ⟨(c', .bool b :: svs', n'), ?_, ρ2, hag, hsat, hnv, hsc, by simp [hlen], ?_, ?_⟩
        · simp only [List.mem_flatMap]
          refine ⟨(c', svs', n'), hx', ?_⟩
          cases b <;> simp
        · intro p hp
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · rfl
          · exact hvals p hp
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · trivial
          · exact hvsc s hs
    | enum id =>
      simp only [freshVals] at hR
      split at hR
      · next es R' hes hR' =>
        simp only [Option.some.injEq] at hR; subst hR
        obtain ⟨lanes, rfl, hok⟩ := argsOK_enum h1 h2
        obtain ⟨es', hes', hmem⟩ := enumVals_mem hok
        rw [hes] at hes'; cases hes'
        obtain ⟨⟨c', svs', n'⟩, hx', ρ2, hag, hsat, hnv, hsc, hlen, hvals, hvsc⟩ :=
          freshVals_cover ts nv rs ρ R' hR' h3
        simp only at hnv hsc hvsc hlen hvals hsat
        refine ⟨(c', .enm id lanes :: svs', n'), ?_, ρ2, hag, hsat, hnv, hsc, by simp [hlen], ?_, ?_⟩
        · simp only [List.mem_flatMap, List.mem_map]
          exact ⟨(c', svs', n'), hx', _, hmem, rfl⟩
        · intro p hp
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨rfl, hok⟩
          · exact hvals p hp
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · trivial
          · exact hvsc s hs
      · exact nomatch hR
    | _ => simp [freshVals] at hR

theorem svsAre_checkSig {ρ : Nat → Int} : ∀ {svs : List SV} {vs : List Val} {ts : List Ty},
    svsAre svs ts = true → ValsRel m ρ svs vs → checkSig 64 vs ts = .ok ()
  | [], [], [], _, _ => rfl
  | s :: ss, v :: vs, t :: ts, h, ⟨h1, h2⟩ => by
    simp only [svsAre, Bool.and_eq_true] at h
    have hp : rejectPoison v "signature boundary" = .ok () := by
      cases s with
      | int _ _ => obtain ⟨a, rfl, _⟩ := h1; rfl
      | bool _ => cases h1; rfl
      | enm _ _ => obtain ⟨rfl, _⟩ := h1; rfl
    have ht : v.ty.beq t = true := by rw [valRel_ty h1]; exact h.1
    simp [checkSig, hp, ht, svIs_expectTy h1 h.1, svsAre_checkSig h.2 h2]
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | [], [], _ :: _, h, _ => by simp [svsAre] at h
  | _ :: _, _ :: _, [], h, _ => by simp [svsAre] at h

theorem valsRel_argsOK {ρ : Nat → Int} : ∀ {svs : List SV} {vs : List Val} {ts : List Ty},
    svsAre svs ts = true → ValsRel m ρ svs vs → ArgsOK m ts vs
  | [], [], [], _, _ => trivial
  | s :: ss, v :: vs, t :: ts, h, ⟨h1, h2⟩ => by
    simp only [svsAre, Bool.and_eq_true] at h
    exact ⟨by rw [valRel_ty h1]; exact h.1, valRel_ok h1, valsRel_argsOK h.2 h2⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | [], [], _ :: _, h, _ => by simp [svsAre] at h
  | _ :: _, _ :: _, [], h, _ => by simp [svsAre] at h

theorem argρ_cons (v : Val) (vs : List Val) (i : Nat) : argρ (v :: vs) (i + 1) = argρ vs i := by
  simp [argρ, nth?]

theorem argρ_zero (v : Val) (vs : List Val) : argρ (v :: vs) 0 = valInt v := by
  simp [argρ, nth?]

theorem argρ_nil (i : Nat) : argρ [] i = 0 := by simp [argρ, nth?]

theorem dot_zero_fn : ∀ (co : List Int), ChkLIA.dot co (fun _ => 0) = 0
  | [] => rfl
  | a :: as => by simp [ChkLIA.dot, dot_zero_fn as]

theorem eval_substCo {ρ : Nat → Int} : ∀ (co : List Int) {svs : List SV} {vs : List Val},
    ValsRel m ρ svs vs → (substCo co (svs.map SV.aff)).eval ρ = ChkLIA.dot co (argρ vs)
  | [], _, _, _ => by simp [substCo, ChkLIA.dot]
  | a :: as, [], [], _ => by
    have : argρ [] = fun _ => 0 := funext argρ_nil
    simp [substCo, this, dot_zero_fn, ChkLIA.dot]
  | a :: as, s :: ss, v :: vs, ⟨h1, h2⟩ => by
    simp only [List.map_cons, substCo, eval_add, eval_smul, valRel_aff h1, ChkLIA.dot,
      eval_substCo as h2, argρ_zero]
    congr 1
  | _ :: _, [], _ :: _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h

theorem negSubst_sat {ρ : Nat → Int} {c : Cons} {svs : List SV} {vs : List Val}
    (h : ValsRel m ρ svs vs) (hn : ¬ c.sat (argρ vs)) : (negSubst c (svs.map SV.aff)).sat ρ := by
  simp only [negSubst, sat_le0, eval_sub, eval_c, eval_substCo c.coeffs h]
  simp only [ChkLIA.Cons.sat] at hn
  omega

theorem substCo_scoped {n : Nat} : ∀ (co : List Int) (es : List Aff), (∀ e ∈ es, e.Scoped n) →
    (substCo co es).Scoped n
  | [], _, _ => by simp [substCo]; exact scoped_c _ _
  | _ :: _, [], _ => by simp [substCo]; exact scoped_c _ _
  | a :: as, e :: es, h => by
    simp only [substCo]
    exact scoped_add (scoped_smul _ (h e (List.Mem.head _)))
      (substCo_scoped as es (fun e' he => h e' (List.Mem.tail _ he)))

/-- What the calculus guarantees at a call node. -/
structure CallOK (m : Module) (A : Nat → List Cons) (cont : SSt → List (List Cons))
    (k : Core) (node : Node) (callee : Nat) (args : List Nat) : Prop where
  vals : ∃ vs f csig, getVs k args = .ok vs ∧ fnOf m callee = some (f, csig) ∧
    entersOk m f csig vs node = true ∧ PreHolds (A callee) vs ∧ ArgsOK m csig.params vs
  next : ∀ vs f csig rs k', getVs k args = .ok vs → fnOf m callee = some (f, csig) →
    RetsOK m csig.returns rs → bindResults (next k) node rs = .ok k' →
    ∃ s' ρ', Rel m ρ' s' k' ∧ ∀ p ∈ cont s', Unsat p

theorem step_call {m : Module} {A : Nat → List Cons} {fn : Func} {sig : FuncTy}
    {cont : SSt → List (List Cons)} {s : SSt} {node : Node} {k : Core} {ρ : Nat → Int}
    (hrel : Rel m ρ s k) (hob : ∀ p ∈ snode m A fn sig cont s node, Unsat p)
    {callee : Nat} {args : List Nat} (hinst : node.inst = .call callee args) :
    CallOK m A cont k node callee args := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slooks s.env args with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some svs =>
  cases hf : fnOf m callee with
  | none => simp only [hl, hf] at hob; exact fail_refutes hob
  | some fs =>
  obtain ⟨f, csig⟩ := fs
  simp only [hl, hf] at hob
  obtain ⟨vs, hg, hvs⟩ := getVs_rel hrel hl
  split at hob
  · next hok =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨hcall, hres⟩ := hok
    split at hob
    · exact fail_refutes hob
    · next R hR =>
      simp only [callOk, Bool.and_eq_true, Bool.not_eq_true'] at hcall
      obtain ⟨⟨⟨hva, hsv⟩, hne⟩, hentry⟩ := hcall
      constructor
      · refine ⟨vs, f, csig, hg, hf, ?_, ?_, valsRel_argsOK hsv hvs⟩
        · simp only [entersOk, hrel.target, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
          refine ⟨⟨⟨⟨hva, by simp [svsAre_checkSig hsv hvs, isOkR]⟩, hne⟩, ?_⟩, hres⟩
          split at hentry
          · exact nomatch hentry
          · next b hb =>
            simp only [hb]
            obtain ⟨env, he⟩ := Option.isSome_iff_exists.mp hentry
            obtain ⟨ce, hce, _⟩ := sbindParams_rel (se := []) (ce := []) trivial hvs he
            simp [hce, isOkR]
        · intro c hc
          refine Classical.byContradiction fun hn => ?_
          exact hob _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
            ⟨ρ, Sat.append hrel.sat (sat_one (negSubst_sat hvs hn))⟩
      · intro vs' f' csig' rs k' hg' hf' hrs hb
        rw [hg] at hg'; cases hg'
        rw [hf] at hf'; cases hf'
        obtain ⟨x, hx, hcov⟩ := freshVals_cover csig.returns s.nv rs ρ R hR hrs
        obtain ⟨k'', hk'', _, h'⟩ := contBrs_cover (fun p hp => hob p (List.mem_append_right _ hp))
          (List.mem_map.mpr ⟨x, hx, rfl⟩) hcov hrel
        rw [hb] at hk''; cases hk''
        exact h'
  · exact fail_refutes hob

/-- What the calculus guarantees at a return node. -/
theorem step_ret {m : Module} {A : Nat → List Cons} {fn : Func} {sig : FuncTy}
    {cont : SSt → List (List Cons)} {s : SSt} {node : Node} {k : Core} {ρ : Nat → Int}
    (hrel : Rel m ρ s k) (hob : ∀ p ∈ snode m A fn sig cont s node, Unsat p) (hsig : k.sig = sig)
    {xs : List Nat} (hinst : node.inst = .ret xs) :
    ∃ vs, getVs k xs = .ok vs ∧ checkSig m.pointerBits vs k.sig.returns = .ok () := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slooks s.env xs with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some svs =>
    simp only [hl] at hob
    obtain ⟨vs, hg, hvs⟩ := getVs_rel hrel hl
    split at hob
    · next hty => exact ⟨vs, hg, by rw [hsig, hrel.target]; exact svsAre_checkSig hty hvs⟩
    · exact fail_refutes hob

end VF5
