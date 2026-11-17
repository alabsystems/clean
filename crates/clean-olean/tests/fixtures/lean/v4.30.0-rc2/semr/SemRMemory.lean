/-
  SemRMemory — the laws of SemR's first memory slice (Trust proven-core RM4c),
  and its byte representation of an integer, which is MiniRust's.

  `SemR.lean` states the memory slice (stack slots: `Alloca`, `Load`, `Store`,
  `GEP`, `Dealloc`) as executable pieces and as the relation's rules, and
  proves the two are one (`step_sound`, `step_complete`). This file proves
  what the memory layer they share means:

  * bytes: a store's bytes are what a load at the same place reads back
    (`readBytes_writeBytes`), a store leaves every byte outside it alone
    (`byteAt_writeBytes_lt`, `byteAt_writeBytes_ge`, and the disjoint-window
    law `readBytes_writeBytes_disjoint`), and a fresh slot reads uninitialized
    (`readBytes_nil`);
  * values: an integer's bytes are its little-endian residue and read back as
    it (`fromLE_leBytes`, `decodeVal_encodeVal_int`), with no uninitialized
    byte (`firstUninit_leBytes`), and so for a `Bool` (`decodeVal_encodeVal_bool`);
    so a `Load` of what a `Store` at the same type wrote is the stored value
    (`readOut_after_store`);
  * undefined behaviour: an access through a dead slot is undefined behaviour
    whatever the offset, size or alignment (`accessAt_dead`, the
    use-after-`StorageDead` law, and in the relation itself
    `step_load_after_dealloc`, `step_store_after_dealloc`,
    `step_double_dealloc`), and so is one past the slot's end (`accessAt_oob`);
    an access that passes the checks reads the slot (`accessAt_ok`);
  * MiniRust's bytes: the bytes SemR stores for an integer of any type and
    residue are the ones libspecr's `Endianness::encode` gives MiniRust's
    integer of that type, little-endian (`encode_minirust`), and MiniRust's
    `Endianness::decode` of them is that integer (`decode_minirust`); every
    run of initialized bytes a `Load` reads decodes in SemR to the residue
    whose MiniRust integer `decode` reads from them (`load_decode_minirust`).
    So SemR's memory holds MiniRust's byte representation, both ways;
  * MiniRust's checks: SemR accepts an alignment exactly when MiniRust's
    `Align::from_bytes` does (`isPow2_minirust`, `checkAlign_minirust`) and
    calls an address aligned exactly when `Align::is_aligned` does
    (`aligned_minirust`); over a MiniRust allocation that agrees with SemR's
    on address, liveness and size (`AllocAgrees`), MiniRust's `check_ptr` is
    undefined behaviour on a dead slot and on an access past its end and
    otherwise yields the same allocation and offset (`check_ptr_eq`), so every
    liveness, alignment and bounds verdict of SemR's `accessAlloc` is
    MiniRust's on the same pointer (`accessAlloc_minirust`; the two name a
    dead, misaligned pointer's undefined behaviour differently, since
    MiniRust checks the alignment first);
  * allocation: the address `Alloca` gives a slot is a multiple of its
    alignment and lies past every earlier allocation (`alloc_fresh`, under
    `Mem.Below`, which the empty memory, an allocation and a write or a
    `Dealloc` keep: `below_empty`, `alloc_fresh`, `below_setNth`), so it is one
    of the addresses MiniRust's `allocate` may pick. SemR runs that one
    choice (the reference interpreter's bump allocator); MiniRust's `allocate`
    picks among all of them and a program is undefined behaviour if any pick
    makes it so, which SemR does not explore (`SemR.lean`, the divergences).

  Not tied to MiniRust here: `Dealloc` (MiniRust's `deallocate` also refuses
  an interior pointer and a dead allocation, but no theorem relates the two),
  MiniRust's whole `load`/`store` (only their `check_ptr` and alignment
  pieces are related), and what a `Load` of uninitialized bytes or an
  `inbounds` `GEP` means (SemR follows the interpreter there; `SemR.lean`
  lists each divergence).

  No `native_decide`, no `partial def`, no `sorry`, no axiom; every closure is
  in Ax0. Clean re-checks it through its reference entry.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import SemRMiniRust

noncomputable section

namespace SemR

/-! ### Bytes -/

theorem byteAt_nil (i : Nat) : byteAt [] i = .uninit := by
  cases i <;> rfl

theorem byteAt_cons_zero (x : AByte) (xs : List AByte) : byteAt (x :: xs) 0 = x := rfl

theorem byteAt_cons_succ (x : AByte) (xs : List AByte) (n : Nat) :
    byteAt (x :: xs) (n + 1) = byteAt xs n := rfl

/-- A fresh slot (no byte written) reads uninitialized everywhere. -/
theorem readBytes_nil (o n : Nat) : readBytes [] o n = uninitBytes n := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    show byteAt [] o :: readBytes [] (o + 1) n = AByte.uninit :: uninitBytes n
    rw [byteAt_nil, ih]

theorem byteAt_setByte_same (d : List AByte) (i : Nat) (b : AByte) : byteAt (setByte d i b) i = b := by
  induction i generalizing d with
  | zero => cases d <;> rfl
  | succ n ih =>
    cases d with
    | nil => show byteAt (setByte [] n b) n = b; exact ih []
    | cons x xs => show byteAt (setByte xs n b) n = b; exact ih xs

theorem byteAt_setByte_ne (d : List AByte) (i j : Nat) (b : AByte) (h : j ≠ i) :
    byteAt (setByte d i b) j = byteAt d j := by
  induction i generalizing d j with
  | zero =>
    cases j with
    | zero => exact absurd rfl h
    | succ j =>
      cases d with
      | nil => show byteAt [] j = byteAt [] (j + 1); rw [byteAt_nil, byteAt_nil]
      | cons x xs => rfl
  | succ n ih =>
    cases j with
    | zero => cases d with
      | nil => show AByte.uninit = byteAt [] 0; rw [byteAt_nil]
      | cons x xs => rfl
    | succ j =>
      cases d with
      | nil =>
        show byteAt (setByte [] n b) j = byteAt [] (j + 1)
        rw [ih [] j (by omega), byteAt_nil, byteAt_nil]
      | cons x xs =>
        show byteAt (setByte xs n b) j = byteAt xs j
        exact ih xs j (by omega)

/-- A store leaves every byte before it alone. -/
theorem byteAt_writeBytes_lt (d : List AByte) (o : Nat) (bs : List AByte) (j : Nat) (h : j < o) :
    byteAt (writeBytes d o bs) j = byteAt d j := by
  induction bs generalizing d o with
  | nil => rfl
  | cons b bs ih =>
    show byteAt (writeBytes (setByte d o b) (o + 1) bs) j = byteAt d j
    rw [ih (setByte d o b) (o + 1) (by omega), byteAt_setByte_ne d o j b (by omega)]

/-- A store leaves every byte after it alone. -/
theorem byteAt_writeBytes_ge (d : List AByte) (o : Nat) (bs : List AByte) (j : Nat)
    (h : o + bs.length ≤ j) : byteAt (writeBytes d o bs) j = byteAt d j := by
  induction bs generalizing d o with
  | nil => rfl
  | cons b bs ih =>
    show byteAt (writeBytes (setByte d o b) (o + 1) bs) j = byteAt d j
    have h' : o + 1 + bs.length ≤ j := by simp only [List.length_cons] at h; omega
    rw [ih (setByte d o b) (o + 1) h', byteAt_setByte_ne d o j b (by simp only [List.length_cons] at h; omega)]

/-- A load reads back exactly the bytes a store at the same offset wrote. -/
theorem readBytes_writeBytes (d : List AByte) (o : Nat) (bs : List AByte) :
    readBytes (writeBytes d o bs) o bs.length = bs := by
  induction bs generalizing d o with
  | nil => rfl
  | cons b bs ih =>
    show byteAt (writeBytes (setByte d o b) (o + 1) bs) o ::
        readBytes (writeBytes (setByte d o b) (o + 1) bs) (o + 1) bs.length = b :: bs
    rw [byteAt_writeBytes_lt _ _ _ _ (by omega), byteAt_setByte_same, ih]

/-- A load's bytes depend only on the bytes of its window. -/
theorem readBytes_ext (d e : List AByte) (o n : Nat)
    (h : ∀ j, o ≤ j → j < o + n → byteAt d j = byteAt e j) : readBytes d o n = readBytes e o n := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    show byteAt d o :: readBytes d (o + 1) n = byteAt e o :: readBytes e (o + 1) n
    rw [h o (by omega) (by omega), ih (o + 1) (fun j h1 h2 => h j (by omega) (by omega))]

/-- A store outside a load's window leaves what the load reads alone. -/
theorem readBytes_writeBytes_disjoint (d : List AByte) (o : Nat) (bs : List AByte) (o2 n : Nat)
    (h : o2 + n ≤ o ∨ o + bs.length ≤ o2) : readBytes (writeBytes d o bs) o2 n = readBytes d o2 n := by
  apply readBytes_ext
  intro j h1 h2
  cases h with
  | inl h => exact byteAt_writeBytes_lt d o bs j (by omega)
  | inr h => exact byteAt_writeBytes_ge d o bs j (by omega)

/-! ### Values -/

theorem leBytes_length (n x : Nat) : (leBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => show (leBytes n (x / 256)).length + 1 = n + 1; rw [ih]

theorem firstUninit_leBytes (n x : Nat) : firstUninit (leBytes n x) = none := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => show (firstUninit (leBytes n (x / 256))).map (· + 1) = none; rw [ih]; rfl

/-- The little-endian image of `x` spells `x` modulo `256^n`. -/
theorem fromLE_leBytes (n x : Nat) : fromLE (leBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => show 0 = x % 256 ^ 0; rw [Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    show x % 256 + 256 * fromLE (leBytes n (x / 256)) = x % 256 ^ (n + 1)
    rw [ih, Nat.pow_succ', Nat.mod_mul]

/-- At either executable target width, integer bytes span exactly its residues.
    The width premise matters: arbitrary natural widths need not be byte-sized. -/
theorem pow_bytes_target (pointerBits : Nat) (hw : pointerBits = 32 ∨ pointerBits = 64)
    (t : IntTy) : 256 ^ (t.bytes pointerBits) = modulus (t.bits pointerBits) := by
  rcases hw with rfl | rfl <;> cases t <;> rfl

/-- The MiniRust correspondence below uses its explicit 64-bit target. -/
theorem pow_bytes (t : IntTy) : 256 ^ t.bytes = modulus t.bits :=
  pow_bytes_target 64 (Or.inr rfl) t

theorem decodeVal_encodeVal_int_target (pointerBits : Nat)
    (hw : pointerBits = 32 ∨ pointerBits = 64) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits pointerBits)) :
    decodeVal (.int t) (leBytes (t.bytes pointerBits) a) = .ok (.int t a) := by
  show R.ok (Val.int t (fromLE (leBytes (t.bytes pointerBits) a))) = R.ok (Val.int t a)
  rw [fromLE_leBytes, pow_bytes_target pointerBits hw, Nat.mod_eq_of_lt ha]

/-- An integer stored is read back as itself. -/
theorem decodeVal_encodeVal_int (t : IntTy) (a : Nat) (ha : a < modulus t.bits) :
    decodeVal (.int t) (leBytes t.bytes a) = .ok (.int t a) :=
  decodeVal_encodeVal_int_target 64 (Or.inr rfl) t a ha

theorem decodeVal_encodeVal_bool (b : Bool) : decodeVal .bool [.init (b2n b)] = .ok (.bool b) := by
  cases b <;> rfl

/-- **Load after store.** A load at integer type `t` of the bytes a store of the
    residue `a` at type `t` wrote at the same offset (over any prior contents)
    binds `a`, whether it is plain or volatile. -/
theorem readOut_after_store_target (pointerBits : Nat)
    (hw : pointerBits = 32 ∨ pointerBits = 64)
    (k : Core) (node : Node) (t : IntTy) (vol : Bool) (d : List AByte)
    (o a : Nat) (ha : a < modulus (t.bits pointerBits)) :
    readOut k node (.int t) vol o
      (readBytes (writeBytes d o (leBytes (t.bytes pointerBits) a)) o (t.bytes pointerBits)) =
      bindResults (next k) node [.int t a] := by
  have e : readBytes (writeBytes d o (leBytes (t.bytes pointerBits) a)) o (t.bytes pointerBits) =
      leBytes (t.bytes pointerBits) a := by
    have := readBytes_writeBytes d o (leBytes (t.bytes pointerBits) a)
    rw [leBytes_length] at this
    exact this
  rw [e]
  unfold readOut
  rw [firstUninit_leBytes]
  show (decodeVal (.int t) (leBytes (t.bytes pointerBits) a) >>= fun v => bindResults (next k) node [v]) = _
  rw [decodeVal_encodeVal_int_target pointerBits hw t a ha]
  rfl

theorem readOut_after_store (k : Core) (node : Node) (t : IntTy) (vol : Bool) (d : List AByte)
    (o a : Nat) (ha : a < modulus t.bits) :
    readOut k node (.int t) vol o (readBytes (writeBytes d o (leBytes t.bytes a)) o t.bytes) =
      bindResults (next k) node [.int t a] :=
  readOut_after_store_target 64 (Or.inr rfl) k node t vol d o a ha

/-! ### Undefined behaviour -/

/-- **Use after `StorageDead`.** Every access through a pointer into a dead slot
    is undefined behaviour, whatever its offset, size and alignment. -/
theorem accessAt_dead (m : Mem) (op : String) (a o size align : Nat) (al : Alloc)
    (hn : nth? m.allocs a = some al) (hl : al.live = false) :
    accessAt m op a o size align = ubR s!"{op}: use after dealloc" := by
  rw [accessAt_some m op a o size align al hn]
  unfold accessAlloc
  rw [hl]
  rfl

/-- An aligned access to a live slot that runs past its end is undefined
    behaviour. -/
theorem accessAt_oob (m : Mem) (op : String) (a o size align : Nat) (al : Alloc)
    (hn : nth? m.allocs a = some al) (hl : al.live = true) (hfit : al.base + o < addrSpace)
    (hal : (al.base + o) % align = 0) (hr : o + size < addrSpace) (hoob : al.size < o + size) :
    accessAt m op a o size align =
      ubR s!"{op}: access [{decStr o}..{decStr (o + size)}) is out of bounds for allocation size {decStr al.size}" := by
  rw [accessAt_some m op a o size align al hn]
  unfold accessAlloc
  have h1 : decide (addrSpace ≤ al.base + o) = false := by simp only [decide_eq_false_iff_not]; omega
  have h2 : ((al.base + o) % align != 0) = false := by simp [hal]
  have h3 : decide (addrSpace ≤ o + size) = false := by simp only [decide_eq_false_iff_not]; omega
  have h4 : decide (al.size < o + size) = true := by simp only [decide_eq_true_eq]; exact hoob
  rw [hl, h1, h2, h3, h4]
  rfl

/-- An access that passes every check reads the slot's record. -/
theorem accessAt_ok (m : Mem) (op : String) (a o size align : Nat) (al : Alloc)
    (hn : nth? m.allocs a = some al) (hl : al.live = true) (hfit : al.base + o < addrSpace)
    (hal : (al.base + o) % align = 0) (hr : o + size < addrSpace) (hin : o + size ≤ al.size) :
    accessAt m op a o size align = .ok al := by
  rw [accessAt_some m op a o size align al hn]
  unfold accessAlloc
  have h1 : decide (addrSpace ≤ al.base + o) = false := by simp only [decide_eq_false_iff_not]; omega
  have h2 : ((al.base + o) % align != 0) = false := by simp [hal]
  have h3 : decide (addrSpace ≤ o + size) = false := by simp only [decide_eq_false_iff_not]; omega
  have h4 : decide (al.size < o + size) = false := by simp only [decide_eq_false_iff_not]; omega
  rw [hl, h1, h2, h3, h4]
  rfl

/-- **Use after `StorageDead`, in the relation.** A `Load` whose pointer
    operand names a dead slot steps (in `Step`, the relation itself) to
    undefined behaviour, once its type and alignment are in the slice. -/
theorem step_load_after_dealloc (m : Module) (k : Core) (results : List Nat) (ty : Ty) (p : Nat)
    (vol : Bool) (al : Option Nat) (a o size align : Nat) (slot : Alloc)
    (hn : nth? k.block.body k.pc = some { inst := .load ty p vol al, results := results })
    (hp : getV k p = .ok (.ptr a o)) (hsz : scalarLayout m.pointerBits ty = .ok size)
    (hal : checkAlign (al.getD size) = .ok align)
    (hs : nth? k.mem.allocs a = some slot) (hl : slot.live = false) :
    Step m k (.done (.ub "Load: use after dealloc")) :=
  Step.load results ty p vol al _ hn
    (Seq.ok _ _ hp (Seq.ok _ _ hsz (Seq.ok _ _ hal (Seq.ok (a, o) _ rfl (Accesses.dead slot hs hl)))))

/-- ... and so does a `Store`. -/
theorem step_store_after_dealloc (m : Module) (k : Core) (results : List Nat) (ty : Ty) (p x : Nat)
    (vol : Bool) (al : Option Nat) (a o size align : Nat) (v : Val) (bs : List AByte) (slot : Alloc)
    (hn : nth? k.block.body k.pc = some { inst := .store ty p x vol al, results := results })
    (hp : getV k p = .ok (.ptr a o)) (hx : getV k x = .ok v) (hsz : scalarLayout m.pointerBits ty = .ok size)
    (himg : storeImage m.pointerBits ty vol size v = .ok bs) (hal : checkAlign (al.getD size) = .ok align)
    (hs : nth? k.mem.allocs a = some slot) (hl : slot.live = false) :
    Step m k (.done (.ub "Store: use after dealloc")) :=
  Step.store results ty p x vol al _ hn
    (Seq.ok _ _ hp (Seq.ok _ _ hx (Seq.ok _ _ hsz (Seq.ok _ _ himg (Seq.ok _ _ hal
      (Seq.ok (a, o) _ rfl (Accesses.dead slot hs hl)))))))

/-- A `Dealloc` of a dead slot (a double `StorageDead`) steps to undefined
    behaviour. -/
theorem step_double_dealloc (m : Module) (k : Core) (results : List Nat) (p a : Nat) (slot : Alloc)
    (hn : nth? k.block.body k.pc = some { inst := .dealloc p, results := results })
    (hp : getV k p = .ok (.ptr a 0)) (hs : nth? k.mem.allocs a = some slot)
    (hl : slot.live = false) :
    Step m k (.done (.ub "Dealloc: allocation is already dead")) :=
  Step.dealloc results p _ hn (Seq.ok _ _ hp (Seq.ok (a, 0) _ rfl (Frees.dead slot rfl hs hl)))

/-! ### MiniRust's byte representation -/

/-- The integer bytes a SemR byte list spells (an uninitialized byte, which no
    integer's image has, as `-1`). -/
def byteInts : List AByte → List Int
  | [] => []
  | .init b :: bs => Int.ofNat b :: byteInts bs
  | .uninit :: bs => -1 :: byteInts bs

theorem pow2_8 : SNat.pow2 8 = 256 := rfl

/-- MiniRust's integer for a residue: the residue, or the residue less `2^w`. -/
theorem readAt_cases (s : Bool) (w a : Nat) :
    readAt s w a = Int.ofNat a - Int.ofNat (modulus w) ∨ readAt s w a = Int.ofNat a := by
  unfold readAt
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- libspecr's little-endian byte loop on a non-negative integer is `leBytes`. -/
theorem sendian_leBytes (n x : Nat) :
    SEndian.leBytes (Int.ofNat x) n = SOut.ok (byteInts (leBytes n x)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    unfold SEndian.leBytes
    have hr : SInt.rem_euclid (Int.ofNat x) 256 = SOut.ok (Int.ofNat (x % 256)) :=
      rem_euclid_eq (Int.ofNat x) 256 (by decide)
    rw [hr]
    simp only [SOut.bind_ok']
    have hs : SInt.shr (Int.ofNat x) 8 = SOut.ok (Int.ofNat (x / 256)) := by
      show SOut.ok (Int.ofNat (SNat.shr x 8)) = _
      unfold SNat.shr
      rw [pow2_8]
    rw [hs]
    simp only [SOut.bind_ok']
    rw [ih]
    simp only [SOut.bind_ok']
    rfl

/-- **SemR's integer bytes are MiniRust's.** For every integer type `t`, either
    signedness `s` and every residue `a`, libspecr's `Endianness::encode`
    (little-endian, MiniRust's `IntType` of `t.bytes` bytes at signedness `s`)
    of the MiniRust integer `readAt s t.bits a` is the byte list SemR stores for
    `a` (`leBytes t.bytes a`). -/
theorem encode_minirust (s : Bool) (t : IntTy) (a : Nat) (ha : a < modulus t.bits) :
    SEndian.encode .LittleEndian (sgnOf s) (Int.ofNat t.bytes) (readAt s t.bits a) =
      SOut.ok (some (byteInts (leBytes t.bytes a))) := by
  have hbits := IntTy.bits_eq t
  have hib : SInt.in_bounds (readAt s t.bits a) (sgnOf s) (Int.ofNat t.bytes) = SOut.ok true := by
    unfold SInt.in_bounds
    rw [bib_in_domain _ s t.bytes t.bytes_pos t.power_domain, ← hbits,
      readAt_emod t.bits s a ha]
    simp only [SOut.bind_ok']
    show SOut.ok (SInt.beq (readAt s t.bits a) (readAt s t.bits (Int.ofNat a).toNat)) = SOut.ok true
    simp [SInt.beq]
  have hpow : SInt.pow 2 (Int.ofNat t.bytes * 8) = SOut.ok (Int.ofNat (modulus t.bits)) := by
    rw [hbits]
    change (if t.bytes * 8 < 4294967296 then _ else _) = _
    rw [if_pos t.power_domain]
    rfl
  have hm : 0 < modulus t.bits := Nat.pow_pos (by decide)
  unfold SEndian.encode
  rw [hib]
  simp only [SOut.bind_ok']
  rw [hpow]
  simp only [SOut.bind_ok']
  have habs : SInt.abs (Int.ofNat t.bytes) = t.bytes := rfl
  rw [habs]
  have hc := readAt_cases s t.bits a
  cases hb : SInt.blt (readAt s t.bits a) 0 with
  | true =>
    have e : readAt s t.bits a + Int.ofNat (modulus t.bits) = Int.ofNat a := by
      simp only [SInt.blt, decide_eq_true_eq] at hb
      rcases hc with h | h <;> rw [h] at hb ⊢ <;> simp only [Int.ofNat_eq_natCast] at hb ⊢ <;> omega
    show SOut.bind (SEndian.leBytes (readAt s t.bits a + Int.ofNat (modulus t.bits)) t.bytes) _ = _
    rw [e, sendian_leBytes]
    rfl
  | false =>
    have e : readAt s t.bits a = Int.ofNat a := by
      simp only [SInt.blt, decide_eq_false_iff_not] at hb
      rcases hc with h | h <;> rw [h] at hb ⊢ <;> simp only [Int.ofNat_eq_natCast] at hb ⊢ <;> omega
    show SOut.bind (SEndian.leBytes (readAt s t.bits a) t.bytes) _ = _
    rw [e, sendian_leBytes]
    rfl


/-! ### MiniRust's decoding of integer bytes -/

theorem sList_reverseAux {α : Type} (l acc : List α) : SList.reverseAux l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [SList.reverseAux, ih]

theorem sList_reverse {α : Type} (l : List α) : SList.reverse l = l.reverse := by
  simp [SList.reverse, sList_reverseAux]

theorem foldBytes_snoc (acc : Int) (l : List Int) (b : Int) :
    SEndian.foldBytes acc (l ++ [b]) = SEndian.foldBytes acc l * 256 + b := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (acc * 256 + x)

theorem byteInts_append (l r : List AByte) : byteInts (l ++ r) = byteInts l ++ byteInts r := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [byteInts, ih]

theorem foldBytes_leBytes (acc : Int) (n x : Nat) :
    SEndian.foldBytes acc (byteInts (leBytes n x)).reverse =
      acc * Int.ofNat (256 ^ n) + Int.ofNat (x % 256 ^ n) := by
  induction n generalizing acc x with
  | zero => simp [leBytes, byteInts, SEndian.foldBytes]
  | succ n ih =>
    show SEndian.foldBytes acc (Int.ofNat (x % 256) :: byteInts (leBytes n (x / 256))).reverse = _
    rw [List.reverse_cons, foldBytes_snoc, ih]
    have hm : x % 256 ^ (n + 1) = x % 256 + 256 * (x / 256 % 256 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    rw [hm, Nat.pow_succ']
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
    grind

theorem leBytes_snoc (n x : Nat) :
    leBytes (n + 1) x = leBytes n x ++ [.init (x / 256 ^ n % 256)] := by
  induction n generalizing x with
  | zero => simp [leBytes]
  | succ n ih =>
    show AByte.init (x % 256) :: leBytes (n + 1) (x / 256) = _
    rw [ih]
    show _ = AByte.init (x % 256) :: (leBytes n (x / 256) ++ _)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- **MiniRust decodes SemR's integer bytes as SemR does.** For every integer
    type `t`, signedness `s` and residue `a`, libspecr's `Endianness::decode`
    (little-endian, at signedness `s`) of the bytes SemR stores for `a` is the
    MiniRust integer `readAt s t.bits a` that SemR's residue `a` stands for:
    the converse of `encode_minirust`. -/
theorem decode_minirust (s : Bool) (t : IntTy) (a : Nat) (ha : a < modulus t.bits) :
    SEndian.decode .LittleEndian (sgnOf s) (byteInts (leBytes t.bytes a)) =
      SOut.ok (readAt s t.bits a) := by
  obtain ⟨n, hn⟩ : ∃ n, t.bytes = n + 1 := ⟨t.bytes - 1, by have := IntTy.bytes_pos t; omega⟩
  have hmod : modulus t.bits = 256 * 256 ^ n := by rw [← pow_bytes, hn, Nat.pow_succ']
  have hhalf : half t.bits = 128 * 256 ^ n := by
    have := half_twice t.bits (by cases t <;> decide); omega
  have hP : 0 < 256 ^ n := Nat.pow_pos (by decide)
  have hB : a / 256 ^ n < 256 := (Nat.div_lt_iff_lt_mul hP).2 (by rw [Nat.mul_comm]; omega)
  have hdm := Nat.div_add_mod a (256 ^ n)
  rw [hn, leBytes_snoc, byteInts_append]
  unfold SEndian.decode
  simp only [sList_reverse, List.reverse_append, byteInts, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [Nat.mod_eq_of_lt hB]
  cases s with
  | false =>
    simp only [sgnOf, Bool.false_eq_true, ↓reduceIte]
    rw [foldBytes_leBytes]
    have hr : readAt false t.bits a = Int.ofNat a := by unfold readAt; rfl
    rw [hr]
    congr 1
    simp only [Int.ofNat_eq_natCast]
    have h2 : a / 256 ^ n * 256 ^ n + a % 256 ^ n = a := by rw [Nat.mul_comm]; exact hdm
    exact_mod_cast h2
  | true =>
    simp only [sgnOf, ↓reduceIte]
    simp only [SInt.ble]
    have hiff : (128 ≤ a / 256 ^ n) ↔ (128 * 256 ^ n ≤ a) := Nat.le_div_iff_mul_le hP
    by_cases hc : 128 * 256 ^ n ≤ a
    · have h1 : decide ((128 : Int) ≤ Int.ofNat (a / 256 ^ n)) = true := by
        simp only [decide_eq_true_eq, Int.ofNat_eq_natCast]; have := hiff.2 hc; omega
      rw [h1]
      simp only
      rw [foldBytes_leBytes]
      have hr : readAt true t.bits a = Int.ofNat a - Int.ofNat (modulus t.bits) := by
        unfold readAt; rw [if_pos (by rw [hhalf]; simp [hc])]
      rw [hr, hmod]
      congr 1
      simp only [Int.ofNat_eq_natCast]
      have h2 : a / 256 ^ n * 256 ^ n + a % 256 ^ n = a := by rw [Nat.mul_comm]; exact hdm
      have h3 : ((a / 256 ^ n : Nat) : Int) * ((256 ^ n : Nat) : Int) + ((a % 256 ^ n : Nat) : Int)
          = (a : Int) := by exact_mod_cast h2
      rw [Int.natCast_mul]
      generalize ((a / 256 ^ n : Nat) : Int) = B at h3 ⊢
      generalize ((256 ^ n : Nat) : Int) = P at h3 ⊢
      generalize ((a % 256 ^ n : Nat) : Int) = r at h3 ⊢
      rw [Int.sub_mul]; omega
    · have h1 : decide ((128 : Int) ≤ Int.ofNat (a / 256 ^ n)) = false := by
        simp only [decide_eq_false_iff_not, Int.ofNat_eq_natCast]; have := mt hiff.1 hc; omega
      rw [h1]
      simp only
      rw [foldBytes_leBytes]
      have hr : readAt true t.bits a = Int.ofNat a := by
        unfold readAt; rw [if_neg (by rw [hhalf]; simp [hc])]
      rw [hr]
      congr 1
      simp only [Int.ofNat_eq_natCast]
      have h2 : a / 256 ^ n * 256 ^ n + a % 256 ^ n = a := by rw [Nat.mul_comm]; exact hdm
      have h3 : ((a / 256 ^ n : Nat) : Int) * ((256 ^ n : Nat) : Int) + ((a % 256 ^ n : Nat) : Int)
          = (a : Int) := by exact_mod_cast h2
      generalize ((a / 256 ^ n : Nat) : Int) = B at h3 ⊢
      generalize ((256 ^ n : Nat) : Int) = P at h3 ⊢
      generalize ((a % 256 ^ n : Nat) : Int) = r at h3 ⊢
      omega


/-- Bytes all initialized to a value below 256: what a load decodes. -/
def ByteImage : List AByte → Prop
  | [] => True
  | .init b :: bs => b < 256 ∧ ByteImage bs
  | .uninit :: _ => False

/-- Initialized bytes are the little-endian image of the number they spell. -/
theorem leBytes_fromLE (bs : List AByte) (h : ByteImage bs) : leBytes bs.length (fromLE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | uninit => cases h
    | init b =>
      obtain ⟨hb, hxs⟩ := h
      show AByte.init ((b + 256 * fromLE xs) % 256) :: leBytes xs.length ((b + 256 * fromLE xs) / 256) = _
      have h1 : (b + 256 * fromLE xs) % 256 = b := by omega
      have h2 : (b + 256 * fromLE xs) / 256 = fromLE xs := by omega
      rw [h1, h2, ih hxs]

theorem fromLE_lt (bs : List AByte) (h : ByteImage bs) : fromLE bs < 256 ^ bs.length := by
  have e := fromLE_leBytes bs.length (fromLE bs)
  rw [leBytes_fromLE bs h] at e
  rw [e]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))

/-- **A load decodes as MiniRust's does.** Whatever initialized bytes a
    `Load` at integer type `t` reads, SemR's value is the residue they spell
    little-endian, and libspecr's `Endianness::decode` of the same bytes (at
    either signedness) is the MiniRust integer that residue stands for. -/
theorem load_decode_minirust (s : Bool) (t : IntTy) (bs : List AByte) (h : ByteImage bs)
    (hl : bs.length = t.bytes) :
    decodeVal (.int t) bs = .ok (.int t (fromLE bs)) ∧
    SEndian.decode .LittleEndian (sgnOf s) (byteInts bs) = SOut.ok (readAt s t.bits (fromLE bs)) := by
  refine ⟨rfl, ?_⟩
  have hlt : fromLE bs < modulus t.bits := by
    have := fromLE_lt bs h; rw [hl, pow_bytes] at this; exact this
  have e := leBytes_fromLE bs h
  rw [hl] at e
  have d := decode_minirust s t (fromLE bs) hlt
  rw [e] at d
  exact d

/-! ### Alignment is MiniRust's -/

theorem isPow2Aux_iff (f n : Nat) (hf : n < f) : SNat.isPow2Aux f n = true ↔ n.isPowerOfTwo := by
  induction f generalizing n with
  | zero => omega
  | succ f ih =>
    match n with
    | 0 => simp [SNat.isPow2Aux, Nat.not_isPowerOfTwo_zero]
    | 1 => simp [SNat.isPow2Aux, Nat.isPowerOfTwo_one]
    | m + 2 =>
      unfold SNat.isPow2Aux
      simp only
      by_cases he : (m + 2) % 2 = 0
      · rw [decide_eq_true he]
        simp only
        rw [ih ((m + 2) / 2) (by omega)]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [Nat.pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => exact ⟨k, by rw [Nat.pow_succ] at hk; omega⟩
      · rw [decide_eq_false he]
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k => rw [Nat.pow_succ] at hk; omega

theorem isPow2_iff (a : Nat) : isPow2 a = true ↔ a.isPowerOfTwo := by
  unfold isPow2
  rw [← Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  rfl

/-- **SemR's alignments are MiniRust's.** `isPow2` (`u64::is_power_of_two`,
    the test `checkAlign` makes of an `Alloca`'s, a `Load`'s or a `Store`'s
    alignment) is libspecr's `Int::is_power_of_two`, so SemR accepts an
    alignment exactly when MiniRust's `Align::from_bytes` does. -/
theorem isPow2_minirust (a : Nat) : isPow2 a = SInt.is_power_of_two (Int.ofNat a) := by
  show isPow2 a = SNat.isPow2Aux (a + 1) a
  apply Bool.eq_iff_iff.2
  rw [isPow2_iff, isPow2Aux_iff (a + 1) a (by omega)]

theorem checkAlign_minirust (a : Nat) :
    (checkAlign a = .ok a ∧ SAlign.from_bytes (Int.ofNat a) = some (Int.ofNat a)) ∨
      (checkAlign a = tyR s!"TypeError: alignment {decStr a} must be a non-zero power of two" ∧
        SAlign.from_bytes (Int.ofNat a) = none) := by
  unfold checkAlign SAlign.from_bytes
  rw [← isPow2_minirust]
  cases isPow2 a <;> simp

/-- An address is aligned in SemR exactly when MiniRust's `Align::is_aligned`
    says so (`addr % align == 0`), for every non-zero alignment. -/
theorem aligned_minirust (x al : Nat) (h : 0 < al) :
    SAlign.is_aligned (Int.ofNat al) (Int.ofNat x) = SOut.ok (!(x % al != 0)) := by
  have hb : SInt.beq (Int.ofNat al) 0 = false := by
    simp only [SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
  simp only [SAlign.is_aligned, SInt.rem, hb, SInt.ofSignedNat, SInt.isNeg, SInt.abs, SOut.bind_ok']
  congr 1
  simp only [SInt.beq]
  by_cases hz : x % al = 0
  · simp [hz]
  · have : ¬ ((x : Int) % (al : Int) = 0) := by omega
    simp only [Int.ofNat_eq_natCast] at *
    simp [hz, this]

/-! ### Liveness and bounds are MiniRust's `check_ptr` -/

/-- SemR's allocation `al` and MiniRust's allocation `v` agree on what an
    access checks: the address, liveness and size (MiniRust's size is its
    data's length). -/
def AllocAgrees (al : Alloc) (v : MR_Allocation) : Prop :=
  v.addr = Int.ofNat al.base ∧ v.live = al.live ∧ v.data.length = al.size

theorem lenNat_eq {α : Type} (l : List α) : SList.lenNat l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [SList.lenNat, ih]

/-- MiniRust's `check_ptr` on a pointer with provenance `a` at byte `o` of
    an allocation that agrees with SemR's `al`, for an access of `size > 0`
    bytes: undefined behaviour when the allocation is dead, then when the
    bytes run past its end, else the allocation and the offset. -/
theorem check_ptr_eq (fuel : Nat) (mm : MR_BasicMemory) (a o size : Nat) (al : Alloc)
    (v : MR_Allocation) (hv : SList.getNat mm.allocations a = some v) (hag : AllocAgrees al v)
    (hs : 0 < size) :
    MRf.BasicMemory.check_ptr (fuel + 2) mm ⟨Int.ofNat (al.base + o), some (⟨Int.ofNat a⟩, ())⟩
        (Int.ofNat size) =
      SOut.ok (if al.live = false then
          SRes.err (MR_TerminationInfo.Ub "dereferencing pointer to dead allocation")
        else if al.size < o + size then
          SRes.err (MR_TerminationInfo.Ub "dereferencing pointer outside the bounds of its allocation")
        else SRes.ok (some (⟨Int.ofNat a⟩, (), Int.ofNat o))) := by
  obtain ⟨haddr, hlive, hsize⟩ := hag
  have hz : SSize.is_zero (Int.ofNat size) = false := by
    simp only [SSize.is_zero, SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
  have hoff : Int.ofNat (al.base + o) - v.addr = Int.ofNat o := by
    rw [haddr]; simp only [Int.ofNat_eq_natCast, Int.natCast_add]; omega
  unfold MRf.BasicMemory.check_ptr
  simp only [hz, SList.index_at, SList.get, hv, SOption.unwrap, SOut.bind_ok', hlive]
  cases hl : al.live with
  | false => simp [SBool.not]
  | true =>
    simp only [SBool.not, hoff, MRf.Allocation.size, SList.len, lenNat_eq, hsize, SSize.from_bytes,
      SInt.blt, SOption.unwrap]
    have h0 : decide (Int.ofNat o < 0) = false := by
      simp only [decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
    have h1 : decide (Int.ofNat al.size < 0) = false := by
      simp only [decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
    rw [h0]
    simp only [h1]
    by_cases hb : al.size < o + size
    · have : decide ((al.size : Int) < (o : Int) + (size : Int)) = true := by
        simp only [decide_eq_true_eq]; omega
      simp [this, hb]
    · have : decide ((al.size : Int) < (o : Int) + (size : Int)) = false := by
        simp only [decide_eq_false_iff_not]; omega
      simp [this, hb]


/-- **SemR's access checks are MiniRust's.** For an access of `size > 0`
    bytes through a pointer with provenance `a` at byte `o` of SemR's
    allocation `al`, where MiniRust's allocation `a` agrees with `al`:
    a dead slot is undefined behaviour in both (`check_ptr`'s "dereferencing
    pointer to dead allocation"); a misaligned address in both
    (`Align::is_aligned` is false); an access past the end in both
    (`check_ptr`'s "outside the bounds"); and an access SemR lets through,
    MiniRust lets through at the same allocation and offset. SemR checks
    liveness before alignment and MiniRust alignment before liveness, so on a
    dead, misaligned pointer the two name different undefined behaviour. -/
theorem accessAlloc_minirust (op : String) (fuel : Nat) (mm : MR_BasicMemory) (a o size align : Nat)
    (al : Alloc) (v : MR_Allocation) (hv : SList.getNat mm.allocations a = some v)
    (hag : AllocAgrees al v) (hs : 0 < size) (hal : 0 < align) :
    (al.live = false →
      accessAlloc op al o size align = ubR s!"{op}: use after dealloc" ∧
      MRf.BasicMemory.check_ptr (fuel + 2) mm ⟨Int.ofNat (al.base + o), some (⟨Int.ofNat a⟩, ())⟩
          (Int.ofNat size) =
        SOut.ok (SRes.err (MR_TerminationInfo.Ub "dereferencing pointer to dead allocation"))) ∧
    (al.live = true → al.base + o < addrSpace → (al.base + o) % align ≠ 0 →
      accessAlloc op al o size align =
        ubR s!"{op}: pointer address {decStr (al.base + o)} is not aligned to {decStr align}" ∧
      SAlign.is_aligned (Int.ofNat align) (Int.ofNat (al.base + o)) = SOut.ok false) ∧
    (al.live = true → al.base + o < addrSpace → (al.base + o) % align = 0 → o + size < addrSpace →
      al.size < o + size →
      accessAlloc op al o size align =
        ubR s!"{op}: access [{decStr o}..{decStr (o + size)}) is out of bounds for allocation size {decStr al.size}" ∧
      MRf.BasicMemory.check_ptr (fuel + 2) mm ⟨Int.ofNat (al.base + o), some (⟨Int.ofNat a⟩, ())⟩
          (Int.ofNat size) =
        SOut.ok (SRes.err
          (MR_TerminationInfo.Ub "dereferencing pointer outside the bounds of its allocation"))) ∧
    (accessAlloc op al o size align = .ok al →
      SAlign.is_aligned (Int.ofNat align) (Int.ofNat (al.base + o)) = SOut.ok true ∧
      MRf.BasicMemory.check_ptr (fuel + 2) mm ⟨Int.ofNat (al.base + o), some (⟨Int.ofNat a⟩, ())⟩
          (Int.ofNat size) =
        SOut.ok (SRes.ok (some (⟨Int.ofNat a⟩, (), Int.ofNat o)))) := by
  have hc := check_ptr_eq fuel mm a o size al v hv hag hs
  have ha := aligned_minirust (al.base + o) align hal
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hl
    refine ⟨?_, ?_⟩
    · unfold accessAlloc; rw [hl]; rfl
    · rw [hc, hl]; rfl
  · intro hl hfit hmis
    refine ⟨?_, ?_⟩
    · unfold accessAlloc
      have h1 : decide (addrSpace ≤ al.base + o) = false := by simp only [decide_eq_false_iff_not]; omega
      have h2 : ((al.base + o) % align != 0) = true := by simp [hmis]
      rw [hl, h1, h2]; rfl
    · rw [ha]; simp [hmis]
  · intro hl hfit hali hr hoob
    refine ⟨?_, ?_⟩
    · unfold accessAlloc
      have h1 : decide (addrSpace ≤ al.base + o) = false := by simp only [decide_eq_false_iff_not]; omega
      have h2 : ((al.base + o) % align != 0) = false := by simp [hali]
      have h3 : decide (addrSpace ≤ o + size) = false := by simp only [decide_eq_false_iff_not]; omega
      have h4 : decide (al.size < o + size) = true := by simp only [decide_eq_true_eq]; exact hoob
      rw [hl, h1, h2, h3, h4]; rfl
    · rw [hc, hl]; simp [hoob]
  · intro hok
    unfold accessAlloc at hok
    cases hl : al.live with
    | false => rw [hl] at hok; cases hok
    | true =>
      rw [hl] at hok
      cases h1 : decide (addrSpace ≤ al.base + o) with
      | true => rw [h1] at hok; cases hok
      | false =>
        rw [h1] at hok
        cases h2 : ((al.base + o) % align != 0) with
        | true => rw [h2] at hok; cases hok
        | false =>
          rw [h2] at hok
          cases h3 : decide (addrSpace ≤ o + size) with
          | true => rw [h3] at hok; cases hok
          | false =>
            rw [h3] at hok
            cases h4 : decide (al.size < o + size) with
            | true => rw [h4] at hok; cases hok
            | false =>
              have hin : ¬ al.size < o + size := by simpa using h4
              refine ⟨?_, ?_⟩
              · rw [ha, h2]; rfl
              · rw [hc, hl]; simp [hin]

/-! ### Allocation: the bump allocator's address is one MiniRust may choose -/

theorem alignUp_aligned (x a : Nat) : alignUp x a % a = 0 := by
  unfold alignUp
  have := Nat.div_add_mod (x + (a - 1)) a
  have e : x + (a - 1) - (x + (a - 1)) % a = a * ((x + (a - 1)) / a) := by omega
  rw [e, Nat.mul_mod_right]

theorem le_alignUp (x a : Nat) (h : 0 < a) : x ≤ alignUp x a := by
  unfold alignUp
  have := Nat.mod_lt (x + (a - 1)) h
  omega

/-- Every allocation of `m` ends (a zero-sized one after its one address) at
    or below the next free address. -/
def Mem.Below (m : Mem) : Prop :=
  ∀ i al, nth? m.allocs i = some al → al.base + max al.size 1 ≤ m.nextAddr

theorem below_empty : Mem.empty.Below := by
  intro i al h
  cases i <;> cases h

theorem nth?_append_one {α : Type} (l : List α) (x : α) (i : Nat) :
    nth? (l ++ [x]) i = if i < l.length then nth? l i else if i = l.length then some x else none := by
  induction l generalizing i with
  | nil => cases i with
    | zero => rfl
    | succ i => simp [nth?]
  | cons y ys ih =>
    cases i with
    | zero => simp [nth?]
    | succ i =>
      show nth? (ys ++ [x]) i = _
      rw [ih]
      simp only [List.length_cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
      rfl

/-- **Allocation picks an aligned, fresh address.** Over a memory whose
    allocations all lie below the next free address (`Mem.Below`, which the
    empty memory, every allocation, every write and every `Dealloc` keep),
    the address `Alloca` gives a new slot is a multiple of its alignment and
    lies at or past the end of every earlier allocation, live or dead; the
    memory after it is `Below` again. So the bump allocator's address is one
    of the addresses MiniRust's `allocate` may pick (aligned, overlapping no
    allocation); SemR runs that one choice and no other. -/
theorem alloc_fresh (m : Mem) (hb : m.Below) (size align : Nat) (h : 0 < align) :
    alignUp m.nextAddr align % align = 0 ∧
    (∀ i al, nth? m.allocs i = some al → al.base + max al.size 1 ≤ alignUp m.nextAddr align) ∧
    Mem.Below { allocs := m.allocs ++
                  [{ base := alignUp m.nextAddr align, size := size, align := align,
                     live := true, data := [] }],
                nextAddr := alignUp m.nextAddr align + max size 1 } := by
  have hle := le_alignUp m.nextAddr align h
  refine ⟨alignUp_aligned _ _, fun i al hi => Nat.le_trans (hb i al hi) hle, ?_⟩
  intro i al hi
  simp only at hi ⊢
  rw [nth?_append_one] at hi
  split at hi
  · have := hb i al hi; omega
  · split at hi
    · cases hi; simp
    · cases hi

theorem nth?_setNth {α : Type} (l : List α) (a i : Nat) (x : α) :
    nth? (setNth l a x) i = if i = a ∧ a < l.length then some x else nth? l i := by
  induction l generalizing a i with
  | nil => cases a <;> simp [setNth, nth?]
  | cons y ys ih =>
    cases a with
    | zero => cases i <;> simp [setNth, nth?]
    | succ a =>
      cases i with
      | zero => simp [setNth, nth?]
      | succ i =>
        show nth? (setNth ys a x) i = _
        rw [ih]
        simp only [List.length_cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
        rfl

theorem nth?_lt {α : Type} (l : List α) (i : Nat) (x : α) (h : nth? l i = some x) : i < l.length := by
  induction l generalizing i with
  | nil => cases h
  | cons y ys ih => cases i with
    | zero => simp
    | succ i => have := ih i h; simp; omega

/-- A write or a `Dealloc` (an allocation's record replaced by one at the same
    address and size) keeps `Mem.Below`. -/
theorem below_setNth (m : Mem) (hb : m.Below) (a : Nat) (al al' : Alloc)
    (hn : nth? m.allocs a = some al) (hbase : al'.base = al.base) (hsize : al'.size = al.size) :
    Mem.Below { m with allocs := setNth m.allocs a al' } := by
  intro i x hi
  simp only at hi ⊢
  rw [nth?_setNth] at hi
  split at hi
  · rename_i hia
    cases hi; rw [hbase, hsize]; rw [hia.1] at *; exact hb a al hn
  · exact hb i x hi

end SemR

end
