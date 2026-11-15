/-
  VF5Compose — `compose_F1`: per-function `Valid_R` under the callees'
  contracts gives closed-program safety on SemR's whole machine, callees run
  for real on its call stack.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import VF5Sound

set_option linter.unusedVariables false

namespace VF5
open SemR

variable {m : Module}

/-- A frame reached frame-locally from a valid entry of some function. -/
def FrameOK (m : Module) (A : Nat → List Cons) (k : Core) : Prop :=
  ∃ fid f sig args d k0, fnOf m fid = some (f, sig) ∧ ArgsOK m sig.params args ∧
    PreHolds (A fid) args ∧ start m fid args d = .ok k0 ∧ LStar m A (withCtx k0 k) k

/-- The suspended caller as the frame state it was at its call. -/
def callerCore (c : Caller) (rest : List Caller) : Core :=
  { fn := c.fn, sig := c.sig, block := c.block, pc := c.pc, env := c.env, depth := c.depth,
    stack := rest, openFrames := [], nextFrame := 0, mem := Mem.empty }

/-- Every suspended caller is a good frame at a call whose callee has the
    signature the frame above runs under. -/
def StackOK (m : Module) (A : Nat → List Cons) : FuncTy → List Caller → Prop
  | _, [] => True
  | csig, c :: rest =>
    FrameOK m A (callerCore c rest) ∧ nth? c.block.body c.pc = some c.node ∧
      (∃ callee args vs f, c.node.inst = .call callee args ∧
        getVs (callerCore c rest) args = .ok vs ∧ fnOf m callee = some (f, csig)) ∧
      StackOK m A c.sig rest

def Good (m : Module) (A : Nat → List Cons) (k : Core) : Prop :=
  FrameOK m A k ∧ k.openFrames = [] ∧ k.nextFrame = 0 ∧ k.cells = [] ∧ k.nextCell = 0 ∧ k.mem = Mem.empty ∧
    StackOK m A k.sig k.stack

theorem fnOf_mem {m : Module} {fid : Nat} {f : Func} {sig : FuncTy} (h : fnOf m fid = some (f, sig)) :
    f ∈ m.functions ∧ f.id = fid := by
  obtain ⟨hf, _⟩ := fnOf_find h
  exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem frameOK_sound {m : Module} {A : Nat → List Cons}
    (hall : ∀ g ∈ m.functions, Valid_R m A g.id) {k : Core} (h : FrameOK m A k) :
    ¬ LBad m A k ∧ EnvOK m k.env := by
  obtain ⟨fid, f, sig, args, d, k0, hf, hargs, hpre, hs, hstar⟩ := h
  obtain ⟨hmem, hid⟩ := fnOf_mem hf
  obtain ⟨_, _, f', sig', hf', hv⟩ := hall f hmem
  rw [hid, hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  obtain ⟨k0', hs', hsafe⟩ := hv args d hargs (by rw [hid]; exact hpre)
  rw [hid, hs] at hs'; cases hs'
  exact hsafe k k hstar

theorem lstar_snoc {m : Module} {A : Nat → List Cons} {a b c : Core} (h : LStar m A a b)
    (h' : LStep m A b c) : LStar m A a c := by
  induction h with
  | refl k => exact .step _ _ _ h' (.refl _)
  | step k1 k2 k3 h12 _ ih => exact .step _ _ _ h12 (ih h')

theorem withCtx_eq {k0 k k' : Core} (h : ctxOf k' = ctxOf k) : withCtx k0 k' = withCtx k0 k := by
  simp only [ctxOf, Prod.mk.injEq] at h
  simp only [withCtx, h]

theorem lookup_mem : ∀ {env : List (Nat × Val)} {x : Nat} {v : Val}, lookupEnv env x = some v →
    ∃ p ∈ env, p.2 = v
  | [], _, _, h => nomatch h
  | (y, w) :: rest, x, v, h => by
    simp only [lookupEnv] at h
    split at h
    · simp only [Option.some.injEq] at h; exact ⟨(y, w), List.Mem.head _, h⟩
    · obtain ⟨p, hp, he⟩ := lookup_mem h; exact ⟨p, List.Mem.tail _ hp, he⟩

theorem getVs_ok {k : Core} (henv : EnvOK m k.env) :
    ∀ {xs : List Nat} {vs : List Val}, getVs k xs = .ok vs → ∀ v ∈ vs, ValOK m v
  | [], vs, h => by simp only [getVs] at h; cases h; intro v hv; exact nomatch hv
  | x :: xs, vs, h => by
    simp only [getVs] at h
    obtain ⟨v, hv, h⟩ := R_bind_eq_ok h
    obtain ⟨vs', hvs, h⟩ := R_bind_eq_ok h
    cases h
    intro w hw
    cases hw with
    | head =>
      simp only [getV] at hv
      split at hv
      · next v' hl => cases hv; obtain ⟨p, hp, rfl⟩ := lookup_mem hl; exact henv p hp
      · exact nomatch hv
    | tail _ hw => exact getVs_ok henv hvs w hw

theorem checkSig_argsOK : ∀ {vs : List Val} {ts : List Ty}, checkSig m.pointerBits vs ts = .ok () →
    (∀ v ∈ vs, ValOK m v) → ArgsOK m ts vs
  | [], [], _, _ => trivial
  | v :: vs, t :: ts, h, hv => by
    simp only [checkSig] at h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    split at h
    · next ht =>
      obtain ⟨_, _, h⟩ := R_bind_eq_ok h
      exact ⟨ht, hv v (List.Mem.head _), checkSig_argsOK h (fun w hw => hv w (List.Mem.tail _ hw))⟩
    · exact nomatch h
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

theorem checkSig_length : ∀ {vs : List Val} {ts : List Ty}, checkSig m.pointerBits vs ts = .ok () →
    vs.length = ts.length
  | [], [], _ => rfl
  | v :: vs, t :: ts, h => by
    simp only [checkSig] at h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    split at h
    · obtain ⟨_, _, h⟩ := R_bind_eq_ok h
      simp [checkSig_length h]
    · exact nomatch h
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem good_step {m : Module} {A : Nat → List Cons} (hall : ∀ g ∈ m.functions, Valid_R m A g.id)
    {k : Core} (hg : Good m A k) :
    (∀ o, stepCore m k = .done o → ¬ Bad o) ∧ (∀ k', stepCore m k = .cont k' → Good m A k') := by
  obtain ⟨hfr, hof, hnf, hcells, hnc, hmem, hst⟩ := hg
  obtain ⟨hnb, henv⟩ := frameOK_sound hall hfr
  cases hnode : nth? k.block.body k.pc with
  | none => exact absurd (LBad.missing k hnode) hnb
  | some node =>
  have hsc : stepCore m k = execNode m k node := by simp [stepCore, hnode]
  rw [hsc]
  cases hloc : isLocal node.inst
  · -- not local: a call, a return, or outside
    cases hinst : node.inst
    case call callee args =>
      cases hgv : getVs k args with
      | stop o => exact absurd (LBad.callArgs k node callee args o hnode hinst hgv) hnb
      | ok vs =>
      cases hfn : fnOf m callee with
      | none => exact absurd (LBad.callFn k node callee args vs hnode hinst hgv hfn) hnb
      | some fs =>
      obtain ⟨f, sig⟩ := fs
      obtain ⟨hfind, hnth⟩ := fnOf_find hfn
      cases hent : entersOk m f sig vs node
      · exact absurd (LBad.callEnter k node callee args vs f sig hnode hinst hgv hfn hent) hnb
      · have hpre : PreHolds (A callee) vs := Classical.byContradiction fun hn =>
          hnb (LBad.callPre k node callee args vs f sig hnode hinst hgv hfn hn)
        simp only [entersOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hent
        obtain ⟨⟨⟨⟨hva, hcs⟩, hne⟩, hentry⟩, hres⟩ := hent
        cases hcs' : checkSig m.pointerBits vs sig.params with
        | stop o => simp [hcs', isOkR] at hcs
        | ok u =>
        cases hb : findBlock f.blocks f.entry with
        | none => simp [hb] at hentry
        | some b =>
        cases hbp : bindParams m.pointerBits [] b.params vs with
        | stop o => simp [hb, hbp, isOkR] at hentry
        | ok env =>
        have hargs : ArgsOK m sig.params vs := checkSig_argsOK hcs' (getVs_ok henv hgv)
        cases hd : k.depth == 0
        · -- the call enters its callee
          have hk' : execNode m k node = .cont
              { k with fn := f, sig := sig, block := b, pc := 0, env := env, depth := k.depth - 1,
                       stack := { fn := k.fn, sig := k.sig, block := k.block, pc := k.pc, env := k.env,
                                  depth := k.depth, node := node } :: k.stack } := by
            simp [execNode, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgv, hd, hfind, hnth, hva, hcs', hne, hb, hbp, ofR]
          rw [hk']
          refine ⟨(fun o ho => nomatch ho), (fun k' hk => ?_)⟩
          cases hk
          refine ⟨⟨callee, f, sig, vs, k.depth - 1,
              { fn := f, sig := sig, block := b, pc := 0, env := env, depth := k.depth - 1, stack := [],
                openFrames := [], nextFrame := 0, mem := Mem.empty }, hfn, hargs, hpre, ?_, ?_⟩,
              hof, hnf, hcells, hnc, hmem, ?_⟩
          · have hexec := (hall f (fnOf_mem hfn).1).2.1
            simp [start, hfind, hnth, hne, hva, hcs', hb, hbp, hexec]
          · simp only [withCtx, hof, hnf, hcells, hnc, hmem]; exact .refl _
          · have hkc : callerCore (Caller.mk k.fn k.sig k.block k.pc k.env k.depth node) k.stack = k := by
              cases k; simp_all [callerCore]
            refine ⟨?_, hnode, ⟨callee, args, vs, f, hinst, ?_, hfn⟩, hst⟩
            · rw [hkc]; exact hfr
            · rw [hkc]; exact hgv
        · have hk' : execNode m k node = .done .outOfFuel := by
            simp [execNode, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgv, hd, ofR]
          rw [hk']
          exact ⟨(fun o ho => by cases ho; simp [Bad]), (fun k' hk => nomatch hk)⟩
    case ret xs =>
      cases hgv : getVs k xs with
      | stop o => exact absurd (LBad.retArgs k node xs o hnode hinst hgv) hnb
      | ok vs =>
      cases hcs : checkSig m.pointerBits vs k.sig.returns with
      | stop o => exact absurd (LBad.retSig k node xs vs o hnode hinst hgv hcs) hnb
      | ok u =>
      cases hstk : k.stack with
      | nil =>
        have hk' : execNode m k node = .done (.ret vs) := by
          simp [execNode, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgv, hcs, hstk, ofR]
        rw [hk']
        exact ⟨(fun o ho => by cases ho; simp [Bad]), (fun k' hk => nomatch hk)⟩
      | cons c rest =>
        rw [hstk] at hst
        obtain ⟨hcfr, hcnode, ⟨callee, args, vs0, f, hci, hcg, hcf⟩, hrest⟩ := hst
        obtain ⟨hcnb, hcenv⟩ := frameOK_sound hall hcfr
        have hrets : RetsOK m k.sig.returns vs := checkSig_argsOK hcs (getVs_ok henv hgv)
        -- the caller's call node binds as many results as the callee returns
        have hent : entersOk m f k.sig vs0 c.node = true := by
          cases he : entersOk m f k.sig vs0 c.node
          · exact absurd (LBad.callEnter (callerCore c rest) c.node callee args vs0 f k.sig hcnode hci hcg hcf he) hcnb
          · rfl
        simp only [entersOk, Bool.and_eq_true, beq_iff_eq] at hent
        have hlen : c.node.results.length = vs.length := by rw [hent.2, checkSig_length hcs]
        have hkr : Core.mk c.fn c.sig c.block (c.pc + 1) c.env c.depth rest k.openFrames k.nextFrame
            k.cells k.nextCell k.mem = next (callerCore c rest) := by
          simp [next, callerCore, hof, hnf, hcells, hnc, hmem]
        obtain ⟨k'', hb''⟩ : ∃ k'', bindResults (next (callerCore c rest)) c.node vs = .ok k'' :=
          ⟨{ next (callerCore c rest) with env := (c.node.results.zip vs).reverse ++ (next (callerCore c rest)).env },
            by simp [bindResults, hlen]⟩
        have hk' : execNode m k node = .cont k'' := by
          simp only [execNode, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst, hgv, hcs, hstk, R_bind_ok]
          rw [hkr, hb'']; rfl
        rw [hk']
        refine ⟨(fun o ho => nomatch ho), (fun k' hk => ?_)⟩
        cases hk
        have hstep : LStep m A (callerCore c rest) k'' :=
          .call _ _ c.node callee args vs0 f k.sig vs hcnode hci hcg hcf hrets hb''
        have hctx := (bindResults_ctx hb'').trans (next_ctx _)
        obtain ⟨fid, f0, sig0, args0, d0, k0, h1, h2, h3, h4, h5⟩ := hcfr
        refine ⟨⟨fid, f0, sig0, args0, d0, k0, h1, h2, h3, h4, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [withCtx_eq hctx]; exact lstar_snoc h5 hstep
        · simp only [ctxOf, Prod.mk.injEq] at hctx; rw [hctx.2.2.2.2.1]; rfl
        · simp only [ctxOf, Prod.mk.injEq] at hctx; rw [hctx.2.2.2.2.2.1]; rfl
        · simp only [ctxOf, Prod.mk.injEq] at hctx; rw [hctx.2.2.2.2.2.2.1]; rfl
        · simp only [ctxOf, Prod.mk.injEq] at hctx; rw [hctx.2.2.2.2.2.2.2.1]; rfl
        · simp only [ctxOf, Prod.mk.injEq] at hctx; rw [hctx.2.2.2.2.2.2.2.2]; rfl
        · simp only [ctxOf, Prod.mk.injEq] at hctx
          rw [hctx.2.1, hctx.2.2.2.1]; exact hrest
    all_goals first
      | (simp [isLocal, hinst] at hloc; done)
      | exact absurd (LBad.outside k node hnode hloc
          (fun _ _ h => by rw [hinst] at h; exact nomatch h) (fun _ h => by rw [hinst] at h; exact nomatch h)) hnb
  · -- local
    refine ⟨(fun o ho hbad => hnb (LBad.exec k node o hnode hloc ho hbad)), (fun k' hk => ?_)⟩
    have hstep : LStep m A k k' := .exec k k' node hnode hloc hk
    have hctx := execNode_local_ctx hloc hk
    obtain ⟨fid, f0, sig0, args0, d0, k0, h1, h2, h3, h4, h5⟩ := hfr
    simp only [ctxOf, Prod.mk.injEq] at hctx
    refine ⟨⟨fid, f0, sig0, args0, d0, k0, h1, h2, h3, h4, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [withCtx_eq (k := k) (by simp [ctxOf, hctx])]; exact lstar_snoc h5 hstep
    · rw [hctx.2.2.2.2.1]; exact hof
    · rw [hctx.2.2.2.2.2.1]; exact hnf
    · rw [hctx.2.2.2.2.2.2.1]; exact hcells
    · rw [hctx.2.2.2.2.2.2.2.1]; exact hnc
    · rw [hctx.2.2.2.2.2.2.2.2]; exact hmem
    · rw [hctx.2.1, hctx.2.2.2.1]; exact hst

theorem good_run {m : Module} {A : Nat → List Cons} (hall : ∀ g ∈ m.functions, Valid_R m A g.id) :
    ∀ (fuel : Nat) (k : Core), Good m A k → ¬ Bad (run m fuel k)
  | 0, k, _ => by simp [run, Bad]
  | fuel + 1, k, hg => by
    obtain ⟨h1, h2⟩ := good_step hall hg
    simp only [run]
    split
    · next o ho => exact h1 o ho
    · next k' hk' => exact good_run hall fuel k' (h2 k' hk')

/-- **`compose_F1`**: every function `Valid_R` under the contracts `A` makes
    the closed program safe: no run of SemR's machine from an entry meeting its
    precondition ends `Bad`, at any budget and call depth. -/
theorem compose_F1 (m : Module) (A : Nat → List Cons)
    (hall : ∀ g ∈ m.functions, Valid_R m A g.id) : ClosedSafe m A := by
  intro fid f sig args fuel depth hf hargs hpre
  obtain ⟨hmem, hid⟩ := fnOf_mem hf
  obtain ⟨_, _, f', sig', hf', hv⟩ := hall f hmem
  rw [hid, hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  obtain ⟨k0, hs, _⟩ := hv args depth hargs (by rw [hid]; exact hpre)
  rw [hid] at hs
  simp only [runFunction, hs]
  have hk0 : k0.openFrames = [] ∧ k0.nextFrame = 0 ∧ k0.cells = [] ∧ k0.nextCell = 0 ∧
      k0.mem = Mem.empty ∧ k0.stack = [] := by
    simp only [start] at hs
    split at hs
    · exact nomatch hs
    · split at hs
      · exact nomatch hs
      · split at hs
        · exact nomatch hs
        · split at hs
          · exact nomatch hs
          · split at hs
            · exact nomatch hs
            · obtain ⟨_, _, hs⟩ := R_bind_eq_ok hs
              split at hs
              · exact nomatch hs
              · obtain ⟨_, _, hs⟩ := R_bind_eq_ok hs
                cases hs; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine good_run hall fuel k0 ⟨⟨fid, f, sig, args, depth, k0, hf, hargs, hpre, hs, ?_⟩,
    hk0.1, hk0.2.1, hk0.2.2.1, hk0.2.2.2.1, hk0.2.2.2.2.1,
    by rw [hk0.2.2.2.2.2]; trivial⟩
  have : withCtx k0 k0 = k0 := rfl
  rw [this]; exact .refl _

/-- The two together: refuted verification conditions for every function of
    the module make the closed program safe. -/
theorem vc_closed (m : Module) (A : Nat → List Cons)
    (h : ∀ g ∈ m.functions, ∀ p ∈ vc m A g.id, Unsat p) : ClosedSafe m A :=
  compose_F1 m A (fun g hg => vc_sound_F1 m A g.id (h g hg))

end VF5
