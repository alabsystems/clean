import VF5Env

set_option linter.unusedVariables false

namespace VF5
open SemR

/-- What a local node's symbolic reading guarantees of SemR's `execNode`. -/
def StepOK (m : Module) (cont : SSt → List (List Cons)) (k : Core) (node : Node) : Prop :=
  (∀ o, execNode m k node = .done o → ¬ Bad o) ∧
  (∀ k', execNode m k node = .cont k' → ∃ s' ρ', Rel m ρ' s' k' ∧ ∀ p ∈ cont s', Unsat p)

theorem stepOK_of_ok {m : Module} {cont : SSt → List (List Cons)} {k k1 : Core} {node : Node}
    (he : execNode m k node = .cont k1) (h : ∃ s' ρ', Rel m ρ' s' k1 ∧ ∀ p ∈ cont s', Unsat p) :
    StepOK m cont k node := by
  refine ⟨?_, ?_⟩
  · intro o ho; rw [he] at ho; exact nomatch ho
  · intro k' hk; rw [he] at hk; cases hk; exact h

@[simp] theorem expectTy_bool (b : Bool) : expectTy 64 (.bool b) .bool = .ok () := rfl
@[simp] theorem expectTy_int (t : IntTy) (a : Nat) (ha : a < modulus t.bits) :
    expectTy 64 (.int t a) (.int t) = .ok () := by
  simp [expectTy, Val.ty, Ty.beq, ha]
@[simp] theorem rejectPoison_int (t : IntTy) (a : Nat) (w : String) : rejectPoison (.int t a) w = .ok () := rfl
@[simp] theorem rejectPoison_bool (b : Bool) (w : String) : rejectPoison (.bool b) w = .ok () := rfl

theorem ofR_ok (k : Core) : ofR (.ok k) = .cont k := rfl

theorem valOK_expectTy {v : Val} {ty : Ty} (hv : ValOK m v)
    (ht : v.ty.beq ty = true) : expectTy 64 v ty = .ok () := by
  cases v <;> cases ty <;> simp_all [expectTy, ValOK, Val.ty, Ty.beq]

theorem svIs_expectTy {ρ : Nat → Int} {s : SV} {v : Val} {ty : Ty} (hr : valRel m ρ s v)
    (h : svIs s ty = true) : expectTy 64 v ty = .ok () :=
  valOK_expectTy (valRel_ok hr) (by rw [valRel_ty hr]; exact h)

theorem code_inj : ∀ {a b : IntTy}, a.code = b.code → a = b := by
  intro a b h; cases a <;> cases b <;> simp_all [IntTy.code]

theorem enumOKb_sound {m : Module} {id : Nat} {ls : List Val} (h : enumOKb m id ls = true) :
    EnumOK m id ls := by
  simp only [enumOKb] at h
  split at h
  · next d t a hd =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨⟨hf, ht⟩, disc, hdm, ha⟩ := h
    refine ⟨d, hd, hf, disc, hdm, ?_⟩
    rw [code_inj ht, ha]
  · exact nomatch h

theorem int_beq {ta tb : IntTy} {ty : Ty} (ha : svIs (.int ta ea) ty = true)
    (hb : svIs (.int tb eb) ty = true) : ta = tb ∧ ty = .int ta := by
  cases ty <;> simp [svIs, SV.ty, Ty.beq] at ha hb
  next t => exact ⟨code_inj (ha.trans hb.symm), by rw [code_inj ha]⟩

theorem bool_beq {ty : Ty} (h : svIs (.bool a) ty = true) : ty = .bool := by
  cases ty <;> simp [svIs, SV.ty, Ty.beq] at h; rfl

/-- `one v`'s continuation: a node that binds one known value. -/
theorem one_cover {cont : SSt → List (List Cons)} {s : SSt} {node : Node} {sv : SV} {v : Val}
    {ρ : Nat → Int} {k : Core} (hob : ∀ p ∈ contBrs cont s node [⟨[], [sv], s.nv⟩], Unsat p)
    (hv : valRel m ρ sv v) (hs : sv.Scoped s.nv) (hrel : Rel m ρ s k) :
    ∃ k', bindResults (next k) node [v] = .ok k' ∧ ∃ s' ρ', Rel m ρ' s' k' ∧ ∀ p ∈ cont s', Unsat p := by
  obtain ⟨k', h1, _, h3⟩ := contBrs_cover (vs := [v]) hob (List.Mem.head _)
    ⟨ρ, Agree.refl ρ s.nv, sat_nil ρ, Nat.le_refl _, (fun _ h => nomatch h), rfl,
      (fun p hp => by
        simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.mem_nil_iff,
          or_false] at hp
        subst hp; exact hv),
      (fun s' hs' => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'; subst hs'; exact hs)⟩
    hrel
  exact ⟨k', h1, h3⟩

theorem slook_mem : ∀ {env : List (Nat × SV)} {x : Nat} {v : SV}, slook env x = some v →
    ∃ p ∈ env, p.2 = v
  | [], _, _, h => nomatch h
  | (y, w) :: rest, x, v, h => by
    simp only [slook] at h
    split at h
    · simp only [Option.some.injEq] at h; exact ⟨(y, w), List.Mem.head _, h⟩
    · obtain ⟨p, hp, he⟩ := slook_mem h; exact ⟨p, List.Mem.tail _ hp, he⟩

theorem slook_scoped {s : SSt} {x : Nat} {v : SV} (hs : EnvScoped s.nv s.env)
    (h : slook s.env x = some v) : v.Scoped s.nv := by
  obtain ⟨p, hp, rfl⟩ := slook_mem h; exact hs p hp

theorem sbindParams_rel {ρ : Nat → Int} :
    ∀ {se : List (Nat × SV)} {ce : List (Nat × Val)} {ps : List (Nat × Ty)} {svs : List SV}
      {vs : List Val} {se' : List (Nat × SV)}, EnvRel m ρ se ce → ValsRel m ρ svs vs →
      sbindParams se ps svs = some se' → ∃ ce', bindParams 64 ce ps vs = .ok ce' ∧ EnvRel m ρ se' ce'
  | se, ce, [], [], [], se', h, _, hb => by
    simp only [sbindParams, Option.some.injEq] at hb; subst hb; exact ⟨ce, rfl, h⟩
  | se, ce, (x, t) :: ps, sv :: svs, v :: vs, se', h, ⟨h1, h2⟩, hb => by
    simp only [sbindParams] at hb
    split at hb
    · next ht =>
      obtain ⟨ce', h3, h4⟩ := sbindParams_rel (se := (x, sv) :: se) (ce := (x, v) :: ce)
        ⟨rfl, h1, h⟩ h2 hb
      exact ⟨ce', by simp [bindParams, svIs_expectTy h1 ht, h3], h4⟩
    · exact nomatch hb
  | _, _, [], _ :: _, _, _, _, _, hb => by simp [sbindParams] at hb
  | _, _, _ :: _, [], _, _, _, _, hb => by simp [sbindParams] at hb
  | _, _, [], [], _ :: _, _, _, h, _ => nomatch h
  | _, _, _ :: _, _ :: _, [], _, _, h, _ => nomatch h

theorem sbindParams_scoped {n : Nat} :
    ∀ {se : List (Nat × SV)} {ps : List (Nat × Ty)} {svs : List SV} {se' : List (Nat × SV)},
      EnvScoped n se → (∀ s ∈ svs, s.Scoped n) → sbindParams se ps svs = some se' → EnvScoped n se'
  | se, [], [], se', h, _, hb => by
    simp only [sbindParams, Option.some.injEq] at hb; subst hb; exact h
  | se, (x, t) :: ps, sv :: svs, se', h, hs, hb => by
    simp only [sbindParams] at hb
    split at hb
    · refine sbindParams_scoped (se := (x, sv) :: se) ?_ (fun s hs' => hs s (List.Mem.tail _ hs')) hb
      intro p hp
      cases hp with
      | head => exact hs sv (List.Mem.head _)
      | tail _ hp => exact h p hp
    · exact nomatch hb
  | _, [], _ :: _, _, _, _, hb => by simp [sbindParams] at hb
  | _, _ :: _, [], _, _, _, hb => by simp [sbindParams] at hb

theorem slooks_scoped {s : SSt} (hs : EnvScoped s.nv s.env) :
    ∀ {xs : List Nat} {svs : List SV}, slooks s.env xs = some svs → ∀ v ∈ svs, v.Scoped s.nv
  | [], svs, h => by simp only [slooks, Option.some.injEq] at h; subst h; intro v hv; exact nomatch hv
  | x :: xs, svs, h => by
    simp only [slooks] at h
    split at h
    · next a as h1 h2 =>
      simp only [Option.some.injEq] at h; subst h
      intro v hv
      cases hv with
      | head => exact slook_scoped hs h1
      | tail _ hv => exact slooks_scoped hs h2 v hv
    · exact nomatch h

theorem scoped_pairs {n : Nat} {l : List (List Cons × Bool)}
    (h : ∀ p ∈ l, CsScoped n p.1) : ∀ p ∈ l, CsScoped n p.1 := h

theorem cmpCases_scoped (op : ICmpOp) {w n : Nat} {ea eb : Aff} (ha : ea.Scoped n)
    (hb : eb.Scoped n) : ∀ p ∈ cmpCases op w ea eb, CsScoped n p.1 := by
  have two : ∀ (x y : Aff), x.Scoped n → y.Scoped n →
      (∀ p ∈ ([([leAn x 1 y], true), ([leA y x], false)] : List (List Cons × Bool)), CsScoped n p.1) ∧
      (∀ p ∈ ([([leA x y], true), ([leAn y 1 x], false)] : List (List Cons × Bool)), CsScoped n p.1) := by
    intro x y hx hy
    constructor <;> intro p hp <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp <;>
      rcases hp with rfl | rfl
    · exact scoped_one (scoped_leAn _ hx hy)
    · exact scoped_one (scoped_leA hy hx)
    · exact scoped_one (scoped_leA hx hy)
    · exact scoped_one (scoped_leAn _ hy hx)
  have sgn : ∀ (f : Aff → Aff → List (List Cons × Bool)),
      (∀ x y, x.Scoped n → y.Scoped n → ∀ p ∈ f x y, CsScoped n p.1) →
      ∀ p ∈ ((biasSplit w ea).flatMap fun (c1, x) =>
        (biasSplit w eb).flatMap fun (c2, y) =>
          (f x y).map fun (c3, r) => (c1 ++ c2 ++ c3, r)), CsScoped n p.1 := by
    intro f hf p hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨⟨c1, x⟩, h1, ⟨c2, y⟩, h2, ⟨c3, r⟩, h3, rfl⟩ := hp
    have s1 := biasSplit_scoped ha _ h1
    have s2 := biasSplit_scoped hb _ h2
    exact CsScoped.append (CsScoped.append s1.1 s2.1) (hf x y s1.2 s2.2 _ h3)
  cases op
  case eq | ne =>
    intro p hp; simp only [cmpCases, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact scoped_leA ha hb
      · exact scoped_leA hb ha
    · exact scoped_one (scoped_leAn _ ha hb)
    · exact scoped_one (scoped_leAn _ hb ha)
  case ult => exact (two ea eb ha hb).1
  case ule => exact (two ea eb ha hb).2
  case ugt => exact (two eb ea hb ha).1
  case uge => exact (two eb ea hb ha).2
  case slt => exact sgn _ (fun x y hx hy => (two x y hx hy).1)
  case sle => exact sgn _ (fun x y hx hy => (two x y hx hy).2)
  case sgt => exact sgn _ (fun x y hx hy => (two y x hy hx).1)
  case sge => exact sgn _ (fun x y hx hy => (two y x hy hx).2)

/-- Entering a block: `jumpS` covers `jump`. -/
theorem jump_cover {cont : SSt → List (List Cons)} {fn : Func} {s : SSt} {k : Core} {ρ : Nat → Int}
    {target : Nat} {svs : List SV} {vs : List Val} (hrel : Rel m ρ s k) (hfn : k.fn = fn)
    (hvs : ValsRel m ρ svs vs) (hsc : ∀ v ∈ svs, v.Scoped s.nv)
    (hob : ∀ p ∈ jumpS cont fn s target svs, Unsat p) :
    ∃ k', jump 64 k target vs = .ok k' ∧ ∃ s' ρ', Rel m ρ' s' k' ∧ ∀ p ∈ cont s', Unsat p := by
  simp only [jumpS] at hob
  split at hob
  · exact fail_refutes hob
  · next b hb =>
    split at hob
    · exact fail_refutes hob
    · next env henv =>
      obtain ⟨ce', h1, h2⟩ := sbindParams_rel hrel.env hvs henv
      refine ⟨{ k with block := b, pc := 0, env := ce' }, by simp [jump, hfn, hb, h1],
        { s with blk := b, pc := 0, env := env }, ρ, ⟨rfl, rfl, h2, hrel.sat,
        sbindParams_scoped hrel.scE hsc henv, hrel.scC, hrel.target⟩, hob⟩

theorem modulus_mono {a b : Nat} (h : a ≤ b) : modulus a ≤ modulus b :=
  Nat.pow_le_pow_right (by decide) h

theorem resid_lt (w : Nat) : ∀ d : Int, resid w d < modulus w
  | .ofNat n => Nat.mod_lt _ (modulus_pos w)
  | .negSucc n => Nat.mod_lt _ (modulus_pos w)

theorem resid_ofNat (w n : Nat) : resid w (n : Int) = n % modulus w := rfl

/-- The residue of a negative `-x` (`0 < x < 2^w`) is `2^w - x`. -/
theorem resid_neg {w x : Nat} (h0 : 0 < x) (h1 : x < modulus w) :
    resid w (-(x : Int)) = modulus w - x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have : (-((y + 1 : Nat) : Int)) = Int.negSucc y := by simp [Int.negSucc_eq]
  rw [this]
  simp only [resid, negR]
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

theorem brcov_bool {m : Module} {ρ : Nat → Int} {nv : Nat} {b : Bool} :
    BrCovers m ρ nv ⟨[], [.bool b], nv⟩ [.bool b] :=
  ⟨ρ, Agree.refl ρ nv, sat_nil ρ, Nat.le_refl _, (fun _ h => nomatch h), rfl,
    (fun p hp => by simp at hp; subst hp; rfl), (fun s hs => by simp at hs; subst hs; trivial)⟩

theorem evalCast_int (op : CastOp) (t : IntTy) (dst : Ty) (a : Nat) (ha : a < modulus t.bits) :
    evalCast 64 op (.int t) dst (.int t a) = castCore 64 op (.int t) dst (.int t a) := by
  simp [evalCast, expectTy, Val.ty, Ty.beq, rejectPoison, ha]

theorem castCases_cover {m : Module} {op : CastOp} {t : IntTy} {dst : Ty} {e : Aff} {nv : Nat}
    {cs : List Cons} {bs : List Br} {ρ : Nat → Int} {a : Nat} (hc : castCases op t dst e nv cs = some bs)
    (he : e.eval ρ = (a : Int)) (ha : a < modulus t.bits) (hs : e.Scoped nv)
    (hsat : Sat cs ρ) (hcs : CsScoped nv cs) :
    ∃ br ∈ bs, ∃ r, evalCast 64 op (.int t) dst (.int t a) = .ok r ∧ BrCovers m ρ nv br [r] := by
  rw [evalCast_int _ _ _ _ ha]
  have hm := modulus_pos t.bits
  cases op <;> cases dst <;> simp only [castCases, reduceCtorEq, Option.some.injEq] at hc <;>
    simp only [castCore, resizeOf, bitcastSame, bitcastInt]
  -- trunc
  case trunc.int t' | zext.int t' =>
    split at hc
    · simp only [Option.some.injEq] at hc
      subst hc
      split
      · next hle =>
        have hlt : a < modulus t'.bits := Nat.lt_of_lt_of_le ha (modulus_mono hle)
        exact ⟨_, List.Mem.head _, _, rfl, by
          simpa [mod_of_lt hlt] using brcov_same (m := m) (t := t') (sat_nil ρ) (fun _ h => nomatch h)
            (show e.eval ρ = ((a % modulus t'.bits : Nat) : Int) by rw [mod_of_lt hlt]; exact he)
            (Nat.mod_lt _ (modulus_pos _)) hs⟩
      · next hle =>
        exact ⟨_, List.Mem.head _, _, rfl, bitsBr_covers hsat hcs he ha hs
          (fun ρ' n xs hr => take_ok hr (by omega)) (Nat.mod_lt _ (modulus_pos _))⟩
    · exact nomatch hc
  case trunc.bool =>
    subst hc
    cases hb : (a % 2 == 1)
    · exact ⟨_, mem2 (Or.inl rfl), .bool false, by simp [hb], brcov_bool⟩
    · exact ⟨_, mem2 (Or.inr rfl), .bool true, by simp [hb], brcov_bool⟩
  case bitcast.int t' =>
    split at hc
    · next hb =>
      simp only [Option.some.injEq] at hc
      subst hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      have hlt : a < modulus t'.bits := by rw [← hb.1]; exact ha
      split
      · next heq =>
        have : t = t' := code_inj (by simpa [Ty.beq] using heq)
        subst this
        exact ⟨_, List.Mem.head _, _, rfl, brcov_same (sat_nil ρ) (fun _ h => nomatch h) he ha hs⟩
      · simp only [hb.1, beq_self_eq_true, if_true]
        exact ⟨_, List.Mem.head _, _, rfl, by
          simpa [mod_of_lt hlt] using brcov_same (m := m) (t := t') (sat_nil ρ) (fun _ h => nomatch h)
            (show e.eval ρ = ((a % modulus t'.bits : Nat) : Int) by rw [mod_of_lt hlt]; exact he)
            (Nat.mod_lt _ (modulus_pos _)) hs⟩
    · exact nomatch hc
  case sext.int t' =>
    split at hc
    · simp only [Option.some.injEq] at hc
      subst hc
      split
      · next hle =>
        have hM : modulus t.bits ≤ modulus t'.bits := modulus_mono hle
        have hh := modulus_two_half (bits_pos t)
        by_cases hn : isNeg t.bits a = true
        · have hge : half t.bits ≤ a := by simpa [isNeg] using hn
          have hres : resid t'.bits (readInt true t.bits a) = modulus t'.bits - (modulus t.bits - a) := by
            have : readInt true t.bits a = -(((modulus t.bits - a : Nat)) : Int) := by
              simp only [readInt, hn, Bool.true_and, if_true]; omega
            rw [this, resid_neg (by omega) (by omega)]
          refine ⟨_, mem2 (Or.inr rfl), _, rfl, ?_⟩
          rw [hres]
          exact brcov_same (sat_one (by rw [sat_le0]; simp [Hw, he]; omega))
            (scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) hs)))
            (by simp [Mw, he]; omega) (by omega) (scoped_addC _ hs)
        · have hlt : a < half t.bits := by simp [isNeg] at hn; omega
          have hres : resid t'.bits (readInt true t.bits a) = a := by
            have : readInt true t.bits a = (a : Int) := by simp [readInt, hn]
            rw [this, resid_ofNat, mod_of_lt (by omega)]
          refine ⟨_, mem2 (Or.inl rfl), _, rfl, ?_⟩
          rw [hres]
          exact brcov_same (sat_one (by rw [sat_le0]; simp [Hw, he]; omega))
            (scoped_one (scoped_le0 (scoped_addC _ hs))) he (by omega) hs
      · exact ⟨_, List.Mem.head _, _, rfl, by
          simpa using brcov_fresh (m := m) (ρ := ρ) (nv := nv) (pre := []) (t := t') (sat_nil ρ)
            (fun _ h => nomatch h) (resid_lt t'.bits _)⟩
    · exact nomatch hc
  all_goals exact nomatch hc

/-- The first case constant equal to `a`, with its edge. -/
def firstMatch : List (Nat × Nat × List Nat) → Nat → Option (Nat × List Nat)
  | [], _ => none
  | (ci, tg, as) :: rest, a => if ci == a then some (tg, as) else firstMatch rest a

theorem constVal_int_ty {m : Module} {n : Nat} {t t' : IntTy} {c : Const} {ci : Nat}
    (h : constVal m n (.int t) c = .ok (.int t' ci)) : t' = t := by
  cases n with
  | zero => simp [constVal, unsupR] at h
  | succ n =>
    cases c with
    | int p => simp [constVal] at h; exact h.1.symm
    | bool b => simp [constVal, unsupR] at h
    | aggregate es => simp [constVal, unsupR] at h
    | uninit => simp [constVal, unsupR] at h

theorem caseConsts_switch {m : Module} {t : IntTy} {a : Nat} :
    ∀ {cases : List (Const × Nat × List Nat)} {cs : List (Nat × Nat × List Nat)},
      caseConsts m t cases = some cs → switchTarget m (.int t a) cases = .ok (firstMatch cs a)
  | [], cs, h => by simp only [caseConsts, Option.some.injEq] at h; subst h; rfl
  | (c, tg, as) :: rest, cs, h => by
    simp only [caseConsts] at h
    split at h
    · next ci rs hc hr =>
      simp only [Option.some.injEq] at h; subst h
      have ht := constVal_int_ty hc
      subst ht
      simp only [switchTarget, Val.ty, hc, R_bind_ok, firstMatch, valEqScalar, beq_self_eq_true,
        Bool.true_and, caseConsts_switch hr]
      split <;> rfl
    · exact nomatch h

theorem firstMatch_mem : ∀ {cs : List (Nat × Nat × List Nat)} {a tg : Nat} {as : List Nat},
    firstMatch cs a = some (tg, as) → ∃ ci, (ci, tg, as) ∈ cs ∧ ci = a
  | [], _, _, _, h => nomatch h
  | (ci, tg', as') :: rest, a, tg, as, h => by
    simp only [firstMatch] at h
    split at h
    · next he =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ci, List.Mem.head _, by simpa using he⟩
    · obtain ⟨c, hm, hc⟩ := firstMatch_mem h
      exact ⟨c, List.Mem.tail _ hm, hc⟩

/-- An edge the symbolic executor takes is an edge SemR takes. -/
theorem edge_cover {m : Module} {cont : SSt → List (List Cons)} {fn : Func} {s : SSt} {k : Core}
    {ρ : Nat → Int} {tg : Nat} {as : List Nat} (hrel : Rel m ρ s k) (hfn : k.fn = fn)
    (hob : ∀ p ∈ (match slooks s.env as with
      | some vs => jumpS cont fn s tg vs
      | none => FAIL), Unsat p) :
    ∃ k', (getVs k as >>= fun vs => jump 64 k tg vs) = .ok k' ∧
      ∃ s' ρ', Rel m ρ' s' k' ∧ ∀ p ∈ cont s', Unsat p := by
  split at hob
  · next vs hvs =>
    obtain ⟨cvs, hg, hr⟩ := getVs_rel hrel hvs
    obtain ⟨k', hk', h'⟩ := jump_cover hrel hfn hr (slooks_scoped hrel.scE hvs) hob
    exact ⟨k', by rw [hg]; exact hk', h'⟩
  · exact fail_refutes hob

section
variable {m : Module} {A : Nat → List Cons} {fn : Func} {sig : FuncTy}
  {cont : SSt → List (List Cons)} {s : SSt} {node : Node} {k : Core} {ρ : Nat → Int}
  (hrel : Rel m ρ s k) (hob : ∀ p ∈ snode m A fn sig cont s node, Unsat p)
include hrel hob

theorem step_binop {op : BinOp} {ty : Ty} {l r : Nat} (hinst : node.inst = .binop op ty l r) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env l with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some svl =>
  cases hr : slook s.env r with
  | none => cases svl <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | some svr =>
  obtain ⟨vl, hgl, hvl⟩ := getV_rel hrel hl
  obtain ⟨vr, hgr, hvr⟩ := getV_rel hrel hr
  cases svl with
  | enm _ _ => cases svr <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | bool x =>
    cases svr with
    | int _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | enm _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | bool y =>
      cases hvl; cases hvr
      simp only [hl, hr] at hob
      split at hob
      · next hty =>
        simp only [Bool.and_eq_true] at hty
        have hb := bool_beq hty.1
        split at hob
        · next c hc =>
          obtain ⟨k', hk', h'⟩ := one_cover hob (v := .bool c) (show valRel m ρ (.bool c) (.bool c) from rfl) trivial hrel
          refine stepOK_of_ok ?_ h'
          subst hb
          simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgl, hgr, evalBinop, isBoolTy, expectBool, liftOp, hc, hk', ofR]
        · exact fail_refutes hob
      · exact fail_refutes hob
  | int ta ea =>
    cases svr with
    | bool _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | enm _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | int tb eb =>
      obtain ⟨a, rfl, ha', hae⟩ := hvl
      obtain ⟨b, rfl, hb', hbe⟩ := hvr
      simp only [hl, hr] at hob
      split at hob
      · next hty =>
        simp only [Bool.and_eq_true] at hty
        obtain ⟨rfl, hty0⟩ := int_beq hty.1.1 hty.1.2
        split at hob
        · exact fail_refutes hob
        · next ubs bs hbc =>
          have hsa : ea.Scoped s.nv := slook_scoped hrel.scE hl
          have hsb : eb.Scoped s.nv := slook_scoped hrel.scE hr
          have hcov := binCases_sound (m := m) hbc hae hbe ha' hb' hsa hsb hrel.sat hrel.scC
          cases hib : intBin op ta.bits a b with
          | ok c =>
            obtain ⟨br, hbr, hbcov⟩ := hcov.1 c hib
            obtain ⟨k', hk', _, h'⟩ := contBrs_cover (fun p hp => hob p (List.mem_append_right _ hp))
              hbr hbcov hrel
            refine stepOK_of_ok ?_ h'
            subst hty0
            simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgl, hgr, evalBinop, isBoolTy, expectInt, ha', hb', hib, liftOp, hk', ofR]
          | ub msg =>
            obtain ⟨u, hu, hsu⟩ := hcov.2.1 msg hib
            exact absurd (Sat.append hrel.sat hsu)
              (fun hs => hob (s.cs ++ u) (List.mem_append_left _ (List.mem_map.mpr ⟨u, hu, rfl⟩)) ⟨ρ, hs⟩)
          | tyErr msg => exact absurd hib (hcov.2.2.1 msg)
          | unsup f => exact absurd hib (hcov.2.2.2 f)
      · exact fail_refutes hob

theorem step_unop {op : UnOp} {ty : Ty} {x : Nat} (hinst : node.inst = .unop op ty x) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env x with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some sv =>
  obtain ⟨v, hg, hv⟩ := getV_rel hrel hl
  cases sv with
  | bool _ => simp only [hl] at hob; exact fail_refutes hob
  | enm _ _ => simp only [hl] at hob; exact fail_refutes hob
  | int ta ea =>
    obtain ⟨a, rfl, ha', hae⟩ := hv
    simp only [hl] at hob
    split at hob
    · next hty =>
      simp only [Bool.and_eq_true] at hty
      obtain ⟨_, hty0⟩ := int_beq hty.1 hty.1
      split at hob
      · exact fail_refutes hob
      · next bs hbc =>
        obtain ⟨br, hbr, hbcov⟩ := unCases_cover hae hae ha' ha' (slook_scoped hrel.scE hl)
          (slook_scoped hrel.scE hl) hbc
        obtain ⟨k', hk', _, h'⟩ := contBrs_cover hob hbr hbcov hrel
        refine stepOK_of_ok ?_ h'
        subst hty0
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, evalUnop, expectInt, ha', hk', ofR]
    · exact fail_refutes hob

theorem step_overflow {op : OvfOp} {ty : Ty} {l r : Nat} (hinst : node.inst = .overflow op ty l r) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env l with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some svl =>
  cases hr : slook s.env r with
  | none => cases svl <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | some svr =>
  obtain ⟨vl, hgl, hvl⟩ := getV_rel hrel hl
  obtain ⟨vr, hgr, hvr⟩ := getV_rel hrel hr
  cases svl with
  | enm _ _ => cases svr <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | bool x => cases svr <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | int ta ea =>
    cases svr with
    | bool _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | enm _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | int tb eb =>
      obtain ⟨a, rfl, ha', hae⟩ := hvl
      obtain ⟨b, rfl, hb', hbe⟩ := hvr
      simp only [hl, hr] at hob
      split at hob
      · next hty =>
        simp only [Bool.and_eq_true] at hty
        obtain ⟨rfl, hty0⟩ := int_beq hty.1.1 hty.1.2
        obtain ⟨br, hbr, hbcov⟩ := ovfCases_cover hae hbe ha' hb' (slook_scoped hrel.scE hl)
          (slook_scoped hrel.scE hr) op
        obtain ⟨k', hk', _, h'⟩ := contBrs_cover hob hbr hbcov hrel
        refine stepOK_of_ok ?_ h'
        subst hty0
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgl, hgr, evalOverflow, expectInt, ha', hb', hk', ofR]
      · exact fail_refutes hob

theorem step_icmp {op : ICmpOp} {ty : Ty} {l r : Nat} (hinst : node.inst = .icmp op ty l r) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env l with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some svl =>
  cases hr : slook s.env r with
  | none => cases svl <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | some svr =>
  obtain ⟨vl, hgl, hvl⟩ := getV_rel hrel hl
  obtain ⟨vr, hgr, hvr⟩ := getV_rel hrel hr
  cases svl with
  | enm _ _ => cases svr <;> simp only [hl, hr] at hob <;> exact fail_refutes hob
  | bool x =>
    cases svr with
    | int _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | enm _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | bool y =>
      cases hvl; cases hvr
      simp only [hl, hr] at hob
      split at hob
      · next hty =>
        simp only [Bool.and_eq_true] at hty
        have hb := bool_beq hty.1
        obtain ⟨k', hk', h'⟩ := one_cover hob (v := .bool (icmpR op 1 (b2n x) (b2n y)))
          (show valRel m ρ (.bool _) (.bool _) from rfl) trivial hrel
        refine stepOK_of_ok ?_ h'
        subst hb
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgl, hgr, evalIcmp, isBoolTy, expectBool, hk', ofR]
      · exact fail_refutes hob
  | int ta ea =>
    cases svr with
    | bool _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | enm _ _ => simp only [hl, hr] at hob; exact fail_refutes hob
    | int tb eb =>
      obtain ⟨a, rfl, ha', hae⟩ := hvl
      obtain ⟨b, rfl, hb', hbe⟩ := hvr
      simp only [hl, hr] at hob
      split at hob
      · next hty =>
        simp only [Bool.and_eq_true] at hty
        obtain ⟨rfl, hty0⟩ := int_beq hty.1.1 hty.1.2
        obtain ⟨⟨c, rb⟩, hm, hsat, hrb⟩ := cmpCases_cover op (bits_pos ta) hae hbe ha' hb'
        have hsc : CsScoped s.nv c := cmpCases_scoped op (slook_scoped hrel.scE hl)
          (slook_scoped hrel.scE hr) _ hm
        obtain ⟨k', hk', _, h'⟩ := contBrs_cover (vs := [.bool rb]) hob
          (br := ⟨c, [.bool rb], s.nv⟩)
          (List.mem_map.mpr ⟨(c, rb), pruneCases_mem (p := (c, rb)) hm hrel.sat hsat, rfl⟩)
          ⟨ρ, Agree.refl ρ s.nv, hsat, Nat.le_refl _, hsc, rfl,
            (fun p hp => by simp at hp; subst hp; rfl), (fun s' hs' => by simp at hs'; subst hs'; trivial)⟩
          hrel
        refine stepOK_of_ok ?_ h'
        subst hty0
        simp only at hrb
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgl, hgr, evalIcmp, isBoolTy, expectInt, ha', hb', ← hrb, hk', ofR]
      · exact fail_refutes hob

theorem step_const {ty : Ty} {c : Const} (hinst : node.inst = .const ty c) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  split at hob
  · next t p =>
    split at hob
    · obtain ⟨k', hk', h'⟩ := one_cover hob (v := .int t (p % modulus t.bits))
        ⟨_, rfl, Nat.mod_lt _ (modulus_pos _), by simp⟩ (scoped_c _ _) hrel
      refine stepOK_of_ok ?_ h'
      simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, constVal, hk', ofR]
    · exact fail_refutes hob
  · next b =>
    obtain ⟨k', hk', h'⟩ := one_cover hob (v := .bool b) (show valRel m ρ (.bool b) (.bool b) from rfl)
      trivial hrel
    refine stepOK_of_ok ?_ h'
    simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, constVal, hk', ofR]
  · next id c' =>
    split at hob
    · next id' ls hcv =>
      split at hob
      · next hok =>
        obtain ⟨k', hk', h'⟩ := one_cover hob (v := .enum id' ls)
          (show valRel m ρ (.enm id' ls) (.enum id' ls) from ⟨rfl, enumOKb_sound hok⟩) trivial hrel
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hcv, hk', ofR]
      · exact fail_refutes hob
    · exact fail_refutes hob
  · exact fail_refutes hob

theorem step_copy {ty : Ty} {x : Nat} (hinst : node.inst = .copy ty x) : StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env x with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some sv =>
    obtain ⟨v, hg, hv⟩ := getV_rel hrel hl
    simp only [hl] at hob
    split at hob
    · next hty =>
      obtain ⟨k', hk', h'⟩ := one_cover hob hv (slook_scoped hrel.scE hl) hrel
      refine stepOK_of_ok ?_ h'
      simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, svIs_expectTy hv hty, hk', ofR]
    · exact fail_refutes hob

theorem step_select {ty : Ty} {c t e : Nat} (hinst : node.inst = .select ty c t e) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hc : slook s.env c with
  | none => simp only [hc] at hob; exact fail_refutes hob
  | some svc =>
  cases ht : slook s.env t with
  | none => cases svc <;> simp only [hc, ht] at hob <;> exact fail_refutes hob
  | some svt =>
  cases he : slook s.env e with
  | none => cases svc <;> simp only [hc, ht, he] at hob <;> exact fail_refutes hob
  | some sve =>
  cases svc with
  | int _ _ => simp only [hc, ht, he] at hob; exact fail_refutes hob
  | enm _ _ => simp only [hc, ht, he] at hob; exact fail_refutes hob
  | bool b =>
    obtain ⟨vc, hgc, hvc⟩ := getV_rel hrel hc
    obtain ⟨vt, hgt, hvt⟩ := getV_rel hrel ht
    obtain ⟨ve, hge, hve⟩ := getV_rel hrel he
    cases hvc
    simp only [hc, ht, he] at hob
    split at hob
    · next hty =>
      simp only [Bool.and_eq_true] at hty
      cases b
      · obtain ⟨k', hk', h'⟩ := one_cover hob hve (slook_scoped hrel.scE he) hrel
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgc, hgt, hge, svIs_expectTy hvt hty.1, svIs_expectTy hve hty.2, hk', ofR]
      · obtain ⟨k', hk', h'⟩ := one_cover hob hvt (slook_scoped hrel.scE ht) hrel
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgc, hgt, hge, svIs_expectTy hvt hty.1, svIs_expectTy hve hty.2, hk', ofR]
    · exact fail_refutes hob

theorem step_assert {c : Nat} {kind : AssertKind} (hinst : node.inst = .assert c kind) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hc : slook s.env c with
  | none => simp only [hc] at hob; exact fail_refutes hob
  | some sv =>
  cases sv with
  | int _ _ => simp only [hc] at hob; exact fail_refutes hob
  | enm _ _ => simp only [hc] at hob; exact fail_refutes hob
  | bool b =>
    obtain ⟨v, hg, hv⟩ := getV_rel hrel hc
    cases hv
    cases b
    · simp only [hc] at hob
      exact absurd ⟨ρ, hrel.sat⟩ (hob s.cs (List.Mem.head _))
    · simp only [hc] at hob
      refine stepOK_of_ok (k1 := next k) (by simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, ofR])
        ⟨{ s with pc := s.pc + 1 }, ρ, ⟨by simp [next, hrel.blk], by simp [next, hrel.pc],
          hrel.env, hrel.sat, hrel.scE, hrel.scC, hrel.target⟩, hob⟩

theorem step_unreachable (hinst : node.inst = .unreachable) : StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  exact absurd ⟨ρ, hrel.sat⟩ (hob s.cs (List.Mem.head _))

theorem step_br {target : Nat} {args : List Nat} (hfn : k.fn = fn)
    (hinst : node.inst = .br target args) : StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slooks s.env args with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some svs =>
    simp only [hl] at hob
    obtain ⟨vs, hg, hvs⟩ := getVs_rel hrel hl
    obtain ⟨k', hk', h'⟩ := jump_cover hrel hfn hvs (slooks_scoped hrel.scE hl) hob
    refine stepOK_of_ok ?_ h'
    simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hk', ofR]

theorem step_condBr {c tT eT : Nat} {tA eA : List Nat} (hfn : k.fn = fn)
    (hinst : node.inst = .condBr c tT tA eT eA) : StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hc : slook s.env c with
  | none => simp only [hc] at hob; exact fail_refutes hob
  | some sv =>
  cases sv with
  | int _ _ => simp only [hc] at hob; exact fail_refutes hob
  | enm _ _ => simp only [hc] at hob; exact fail_refutes hob
  | bool b =>
    obtain ⟨v, hg, hv⟩ := getV_rel hrel hc
    cases hv
    cases b
    · simp only [hc] at hob
      cases hl : slooks s.env eA with
      | none => simp only [hl] at hob; exact fail_refutes hob
      | some svs =>
        simp only [hl] at hob
        obtain ⟨vs, hgs, hvs⟩ := getVs_rel hrel hl
        obtain ⟨k', hk', h'⟩ := jump_cover hrel hfn hvs (slooks_scoped hrel.scE hl) hob
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hgs, hk', ofR]
    · simp only [hc] at hob
      cases hl : slooks s.env tA with
      | none => simp only [hl] at hob; exact fail_refutes hob
      | some svs =>
        simp only [hl] at hob
        obtain ⟨vs, hgs, hvs⟩ := getVs_rel hrel hl
        obtain ⟨k', hk', h'⟩ := jump_cover hrel hfn hvs (slooks_scoped hrel.scE hl) hob
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hgs, hk', ofR]

theorem step_extract {ty : Ty} {agg field : Nat} (hinst : node.inst = .extractField ty agg field) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env agg with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some sv =>
  cases sv with
  | int _ _ => simp only [hl] at hob; exact fail_refutes hob
  | bool _ => simp only [hl] at hob; exact fail_refutes hob
  | enm id ls =>
    obtain ⟨v, hg, hv⟩ := getV_rel hrel hl
    obtain ⟨rfl, _⟩ := hv
    simp only [hl] at hob
    split at hob
    · next t a he =>
      split at hob
      · next hok =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨k', hk', h'⟩ := one_cover hob (v := .int t a)
          (show valRel m ρ (.int t (Aff.c (a : Int))) (.int t a) from ⟨a, rfl, hok.2, by simp⟩)
          (scoped_c _ _) hrel
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, he, hk', ofR]
      · exact fail_refutes hob
    · next b he =>
      obtain ⟨k', hk', h'⟩ := one_cover hob (v := .bool b)
        (show valRel m ρ (.bool b) (.bool b) from rfl) trivial hrel
      refine stepOK_of_ok ?_ h'
      simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, he, hk', ofR]
    · exact fail_refutes hob

theorem step_cast {op : CastOp} {src dst : Ty} {x : Nat} (hinst : node.inst = .cast op src dst x) :
    StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env x with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some sv =>
  obtain ⟨v, hg, hv⟩ := getV_rel hrel hl
  cases sv with
  | enm _ _ => simp only [hl] at hob; exact fail_refutes hob
  | bool b =>
    cases hv
    simp only [hl] at hob
    split at hob
    · next hty =>
      have hsrc := bool_beq hty
      subst hsrc
      split at hob
      · next t a he =>
        split at hob
        · next hok =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨k', hk', h'⟩ := one_cover hob (v := .int t a)
            (show valRel m ρ (.int t (Aff.c (a : Int))) (.int t a) from ⟨a, rfl, hok.2, by simp⟩)
            (scoped_c _ _) hrel
          refine stepOK_of_ok ?_ h'
          simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, he, hk', ofR]
        · exact fail_refutes hob
      · next b' he =>
        obtain ⟨k', hk', h'⟩ := one_cover hob (v := .bool b')
          (show valRel m ρ (.bool b') (.bool b') from rfl) trivial hrel
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, he, hk', ofR]
      · exact fail_refutes hob
    · exact fail_refutes hob
  | int t e =>
    obtain ⟨a, rfl, ha', hae⟩ := hv
    simp only [hl] at hob
    split at hob
    · next hty =>
      simp only [Bool.and_eq_true] at hty
      obtain ⟨_, hsrc⟩ := int_beq hty.1 hty.1
      subst hsrc
      split at hob
      · next bs hbs =>
        obtain ⟨br, hbr, r, hr, hcov⟩ := castCases_cover (m := m) hbs hae ha' (slook_scoped hrel.scE hl)
          hrel.sat hrel.scC
        obtain ⟨k', hk', _, h'⟩ := contBrs_cover hob hbr hcov hrel
        refine stepOK_of_ok ?_ h'
        simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hr, hk', ofR]
      · exact fail_refutes hob
    · exact fail_refutes hob

theorem step_switch {x dflt : Nat} {dArgs : List Nat} {cases : List (Const × Nat × List Nat)}
    (hfn : k.fn = fn) (hinst : node.inst = .switch x dflt dArgs cases) : StepOK m cont k node := by
  simp only [snode, snodeC, stdCalc, hinst] at hob
  cases hl : slook s.env x with
  | none => simp only [hl] at hob; exact fail_refutes hob
  | some sv =>
  obtain ⟨v, hg, hv⟩ := getV_rel hrel hl
  -- A known scrutinee: the target is SemR's own `switchTarget`.
  have known : ∀ (w : Val), v = w → (w.ty = v.ty) → (∀ o, rejectPoison w "switch" ≠ .stop o) →
      (∀ p ∈ (match switchTarget m w cases with
        | .ok (some (tg, as)) =>
          match slooks s.env as with
          | some vs => jumpS cont fn s tg vs
          | none => FAIL
        | .ok none =>
          match slooks s.env dArgs with
          | some vs => jumpS cont fn s dflt vs
          | none => FAIL
        | .stop _ => FAIL), Unsat p) →
      (match w with | .int _ _ | .bool _ => True | _ => False) →
      StepOK m cont k node := by
    intro w hw _ _ hob' hsc
    subst hw
    cases hst : switchTarget m v cases with
    | stop o => rw [hst] at hob'; exact fail_refutes hob'
    | ok r =>
      rw [hst] at hob'
      cases r with
      | some p =>
        obtain ⟨tg, as⟩ := p
        obtain ⟨k', hk', h'⟩ := edge_cover hrel hfn hob'
        refine stepOK_of_ok ?_ h'
        cases v <;> simp at hsc <;>
          simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hst, ofR] <;> rw [hk']
      | none =>
        obtain ⟨k', hk', h'⟩ := edge_cover hrel hfn hob'
        refine stepOK_of_ok ?_ h'
        cases v <;> simp at hsc <;>
          simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hst, ofR] <;> rw [hk']
  cases sv with
  | enm _ _ => simp only [hl] at hob; exact fail_refutes hob
  | bool b =>
    cases hv
    simp only [hl] at hob
    exact known (.bool b) rfl rfl (fun _ h => nomatch h) hob trivial
  | int t e =>
    obtain ⟨a, rfl, ha', hae⟩ := hv
    simp only [hl] at hob
    split at hob
    · next hk =>
      split at hob
      · next hk0 =>
        have hek : e.k = (a : Int) := by rw [← eval_isConst e ρ hk]; exact hae
        have : e.k.toNat = a := by rw [hek]; simp
        rw [this] at hob
        exact known (.int t a) rfl rfl (fun _ h => nomatch h) hob trivial
      · exact fail_refutes hob
    · split at hob
      · next cs dvs hcs hdvs =>
        have hst := caseConsts_switch (a := a) hcs
        cases hfm : firstMatch cs a with
        | some p =>
          obtain ⟨tg, as⟩ := p
          obtain ⟨ci, hmem, hci⟩ := firstMatch_mem hfm
          subst hci
          have hrel' : Rel m ρ { s with cs := s.cs ++ [leA e (Aff.c ci), leA (Aff.c ci) e] } k :=
            ⟨hrel.blk, hrel.pc, hrel.env,
              Sat.append hrel.sat (by
                intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                rcases hc with rfl | rfl <;> rw [sat_leA] <;> simp [hae]),
              hrel.scE,
              CsScoped.append hrel.scC (by
                intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                have hse := slook_scoped hrel.scE hl
                rcases hc with rfl | rfl
                · exact scoped_leA hse (scoped_c _ _)
                · exact scoped_leA (scoped_c _ _) hse), hrel.target⟩
          have hob' := fun p hp => hob p (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hmem, hp⟩))
          obtain ⟨k', hk', h'⟩ := edge_cover hrel' hfn hob'
          refine stepOK_of_ok ?_ h'
          simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hst, hfm, ofR]
          rw [hk']
        | none =>
          have hob' : ∀ p ∈ (match slooks s.env dArgs with
              | some vs => jumpS cont fn s dflt vs
              | none => FAIL), Unsat p := by
            rw [hdvs]; exact fun p hp => hob p (List.mem_append_right _ hp)
          obtain ⟨k', hk', h'⟩ := edge_cover hrel hfn hob'
          refine stepOK_of_ok ?_ h'
          simp [execNode, hrel.target, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hg, hst, hfm, ofR]
          rw [hk']
      · exact fail_refutes hob

/-- Every local node the calculus reads is covered; the rest emit `FAIL`. -/
theorem step_local (hfn : k.fn = fn) (hloc : isLocal node.inst = true) : StepOK m cont k node := by
  cases hinst : node.inst with
  | binop op ty l r => exact step_binop hrel hob hinst
  | unop op ty x => exact step_unop hrel hob hinst
  | overflow op ty l r => exact step_overflow hrel hob hinst
  | icmp op ty l r => exact step_icmp hrel hob hinst
  | const ty c => exact step_const hrel hob hinst
  | copy ty x => exact step_copy hrel hob hinst
  | select ty c t e => exact step_select hrel hob hinst
  | assert c kind => exact step_assert hrel hob hinst
  | unreachable => exact step_unreachable hrel hob hinst
  | br t a => exact step_br hrel hob hfn hinst
  | condBr c tT tA eT eA => exact step_condBr hrel hob hfn hinst
  | extractField ty a f => exact step_extract hrel hob hinst
  | cast op src dst x => exact step_cast hrel hob hinst
  | switch x d da cs => exact step_switch hrel hob hfn hinst
  | insertField _ _ _ _ => simp only [snode, snodeC, stdCalc, hinst] at hob; exact fail_refutes hob
  | nullPtr => simp only [snode, snodeC, stdCalc, hinst] at hob; exact fail_refutes hob
  | _ => simp [isLocal, hinst] at hloc

/-- A node outside the frame-local fragment that is neither a call nor a
    return emits `FAIL`. -/
theorem step_outside (hloc : isLocal node.inst = false)
    (hc : ∀ callee args, node.inst ≠ .call callee args) (hr : ∀ xs, node.inst ≠ .ret xs) : False := by
  cases hinst : node.inst <;> simp [isLocal, hinst] at hloc
  all_goals first
    | exact absurd hinst (hc _ _)
    | exact absurd hinst (hr _)
    | (simp only [snode, snodeC, stdCalc, hinst] at hob; exact fail_refutes hob)

end

end VF5
