/- EqsatResidue: a rule's two sides evaluated on residues, and what that
   evaluation says of SemR's (PKG-U6).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `EqsatRule.Pat.eval` is the meaning of a pattern: SemR's own evaluators on
   SemR values. A decision procedure that the kernel evaluates on every
   assignment of a rule cannot afford it (each operator re-checks the type and
   the range of both operands, on values that carry their type), so this
   module evaluates the same pattern on bare residues (`Pat.evalR`) and proves
   once what its outcome says of `Pat.eval`'s (`evalR_agrees`). Nothing here
   is part of what a rule means: `EqsatRule.Sound` does not reach this module,
   and a wrong `evalR` has no `evalR_agrees`.

   What the evaluator answers (`RR`), and what each answer claims (`Agrees`):
   * `ok v`: `Pat.eval` is the value `v` stands for at the instance type, and
     `v` is well formed there (a residue below the modulus at an integer
     type; never a residue at `bool`);
   * `ub`: `Pat.eval` is undefined behaviour;
   * `bad`: nothing. The evaluator says `bad` wherever it does not follow
     SemR: an unbound variable, `(const INT)` at `bool`, an operand of the
     wrong sort, an operator the sort does not admit, and an operator result
     that is not below the modulus (tested, never assumed: the next operator's
     range check in SemR would refuse it). On an assignment where a side is
     `bad` the test of that assignment answers `false`, under either
     direction and whatever the other side is (`holdsR_bad_left`,
     `holdsR_bad_right`).

   What a procedure tests on one assignment (`checkR`, on the rule's fields),
   and what a `true` proves (`checkR_sound`): if the side conditions hold in
   SemR's reading
   (`CondsHold`), the two sides stand as the direction says (`Holds`). So,
   as `Sound` says: an `equiv` rule needs one common value on both sides; a
   `refines` rule needs that or undefined behaviour on the left. Under
   `refines`, where the left side is undefined behaviour, `Sound` asks nothing
   of the right side; `checkR` still asks that it is not `bad` (a value or
   undefined behaviour stands), so it is stricter than `Sound` there and a
   right side that is not a term never passes. Any other outcome (`bad` on
   either side, undefined behaviour on the right beside a value, undefined
   behaviour on the left of an `equiv` rule) makes `checkR` answer `false`. A
   side condition is decided in the direction that can only lose a rule: `condsR`
   is `true` whenever `CondsHold` holds (`condsR_of_condsHold`), and where it
   is `false` the assignment is skipped.

   How it is written, and why: the kernel evaluates these definitions on each
   of 256 or 65,536 assignments, so every definition on that path is one
   recursor application with closed minor premises (no matcher, no `brecOn`,
   no string, no list but the assignment), the modulus is a parameter (`m`,
   with `m = modulus w` a hypothesis of every lemma) so that it is a literal
   at each use, and the six operators that reduce modulo `m` skip the range
   test their form makes redundant. Measured through Clean's reference entry
   (PKG-U6 step 0): 21 kernel heartbeats per assignment of a one-variable
   rule, against 116 for the same evaluator written with `match`.
-/
import EqsatBasics

namespace EqsatDecide
open SemR EqsatRule

/-- A value of the residue evaluator: a residue, or a `Bool`. -/
inductive RV where
  | res (r : Nat)
  | bit (v : Bool)

/-- An outcome of the residue evaluator (the module header says what each
    claims). -/
inductive RR where
  | ok (v : RV)
  | ub
  | bad

/-- Whether an instance type is an integer type. -/
def isInt : STy → Bool
  | .int _ => true
  | .bool => false

/-- The SemR value a residue value stands for at instance type `T`. A residue
    at `bool` stands for nothing (`RV.WF` excludes it); `false` fills the
    place. -/
def RV.val (T : STy) : RV → Val
  | .res r =>
    match T with
    | .int t => .int t r
    | .bool => .bool false
  | .bit v => .bool v

/-- A residue value is well formed at an instance type with modulus `m`: a
    residue only at an integer type, and below the modulus. -/
def RV.WF (int : Bool) (m : Nat) : RV → Prop
  | .res r => int = true ∧ r < m
  | .bit _ => True

/-- Every value of an assignment is well formed. -/
def EnvWF (int : Bool) (m : Nat) : List RV → Prop
  | [] => True
  | v :: vs => v.WF int m ∧ EnvWF int m vs

/-- `w` is the width of instance type `T` under pointer width `pb`. At `bool`
    there is no width and any `w` stands. -/
def WidthOf (pb : Nat) (T : STy) (w : Nat) : Prop :=
  match T with
  | .int t => t.bits pb = w
  | .bool => True

/-- What an outcome of the residue evaluator says of SemR's outcome. -/
def Agrees (T : STy) (m : Nat) : RR → R Val → Prop
  | .ok v, x => v.WF (isInt T) m ∧ x = .ok (v.val T)
  | .ub, x => ∃ msg, x = .stop (.ub msg)
  | .bad, _ => True

noncomputable section

/-- The value bound to the variable of rank `i`; an unbound rank is `bad`. -/
def getR (env : List RV) (i : Nat) : RR :=
  List.rec (motive := fun _ => Nat → RR) (fun _ => .bad)
    (fun v _ ih i => Nat.rec (motive := fun _ => RR) (.ok v) (fun j _ => ih j) i) env i

/-- A residue, when it is below the modulus. -/
def chk (m r : Nat) : RR :=
  Bool.rec (motive := fun _ => RR) .bad (.ok (.res r)) (Nat.blt r m)

/-- SemR's outcome of one integer operator: a value below the modulus,
    undefined behaviour, or nothing. -/
def ofOp (m : Nat) (x : OpRes Nat) : RR :=
  OpRes.rec (motive := fun _ => RR) (fun r => chk m r) (fun _ => .ub) (fun _ => .bad)
    (fun _ => .bad) x

/-- A binary operator on two residues at an integer type of width `w` and
    modulus `m` (SemR's `intBin`, `intBinR_agrees`). `add sub mul and or xor`
    reduce modulo `m`; the rotations are SemR's expressions under the range
    test; the operators that can be undefined go through SemR's `intBin`;
    `band bor bxor` take Booleans there and are refused. -/
def intBinR (op : BinOp) : Nat → Nat → Nat → Nat → RR :=
  BinOp.rec (motive := fun _ => Nat → Nat → Nat → Nat → RR)
    (fun _ m a b => .ok (.res ((a + b) % m)))
    (fun _ m a b => .ok (.res ((a + (m - b % m)) % m)))
    (fun _ m a b => .ok (.res ((a * b) % m)))
    (fun w m a b => ofOp m (intBin .udiv w a b))
    (fun w m a b => ofOp m (intBin .sdiv w a b))
    (fun w m a b => ofOp m (intBin .urem w a b))
    (fun w m a b => ofOp m (intBin .srem w a b))
    (fun _ m a b => .ok (.res (Nat.land a b % m)))
    (fun _ m a b => .ok (.res (Nat.lor a b % m)))
    (fun _ m a b => .ok (.res (Nat.xor a b % m)))
    (fun w m a b => ofOp m (intBin .shl w a b))
    (fun w m a b => ofOp m (intBin .lshr w a b))
    (fun w m a b => ofOp m (intBin .ashr w a b))
    (fun _ _ _ _ => .bad)
    (fun _ _ _ _ => .bad)
    (fun _ _ _ _ => .bad)
    (fun w m a b => chk m ((a * 2 ^ (b % w)) % m + a / 2 ^ (w - b % w)))
    (fun w m a b => chk m (a / 2 ^ (b % w) + (a * 2 ^ (w - b % w)) % m))
    op

/-- A binary operator on two Booleans where the operand type is `Bool`
    (SemR's `boolBin`). -/
def boolBinR (op : BinOp) : Bool → Bool → RR :=
  BinOp.rec (motive := fun _ => Bool → Bool → RR)
    (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad)
    (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad)
    (fun a c => .ok (.bit (a && c)))
    (fun a c => .ok (.bit (a || c)))
    (fun a c => .ok (.bit (a != c)))
    (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad)
    (fun a c => .ok (.bit (a && c)))
    (fun a c => .ok (.bit (a || c)))
    (fun a c => .ok (.bit (a != c)))
    (fun _ _ => .bad) (fun _ _ => .bad)
    op

/-- A binary operator on two Booleans at an integer type: the operand type is
    `Bool` for `band bor bxor` only (`EqsatRule.binTy`). -/
def boolBinAtIntR (op : BinOp) : Bool → Bool → RR :=
  BinOp.rec (motive := fun _ => Bool → Bool → RR)
    (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad)
    (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad)
    (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad) (fun _ _ => .bad)
    (fun _ _ => .bad)
    (fun a c => .ok (.bit (a && c)))
    (fun a c => .ok (.bit (a || c)))
    (fun a c => .ok (.bit (a != c)))
    (fun _ _ => .bad) (fun _ _ => .bad)
    op

/-- `OP` on two values. `int`: the instance type is an integer type. -/
def binR (int : Bool) (w m : Nat) (op : BinOp) (x y : RV) : RR :=
  RV.rec (motive := fun _ => RR)
    (fun a => RV.rec (motive := fun _ => RR)
      (fun b => Bool.rec (motive := fun _ => RR) .bad (intBinR op w m a b) int)
      (fun _ => .bad) y)
    (fun a => RV.rec (motive := fun _ => RR)
      (fun _ => .bad)
      (fun c => Bool.rec (motive := fun _ => RR) (boolBinR op a c) (boolBinAtIntR op a c) int) y)
    x

/-- A unary operator on a residue (SemR's `intUn`). `neg` and `not` are below
    the modulus by their form; the bit counts and permutations are tested. -/
def intUnR (op : UnOp) : Nat → Nat → Nat → RR :=
  UnOp.rec (motive := fun _ => Nat → Nat → Nat → RR)
    (fun _ m a => .ok (.res ((m - a % m) % m)))
    (fun _ m a => .ok (.res (m - 1 - a % m)))
    (fun w m a => chk m (popcount w a))
    (fun w m a => chk m (ctlzW a w))
    (fun w m a => chk m (cttzW w a))
    (fun w m a => chk m (bswapN (w / 8) a))
    (fun w m a => chk m (bitrevW w a))
    op

/-- A unary `OP`: integer-only, so `bad` on a Boolean and at `bool`. -/
def unR (int : Bool) (w m : Nat) (op : UnOp) (x : RV) : RR :=
  RV.rec (motive := fun _ => RR)
    (fun a => Bool.rec (motive := fun _ => RR) .bad (intUnR op w m a) int)
    (fun _ => .bad) x

/-- `icmp.OP`: two residues at an integer type, two Booleans at `bool`. -/
def cmpR (int : Bool) (w : Nat) (op : ICmpOp) (x y : RV) : RR :=
  RV.rec (motive := fun _ => RR)
    (fun a => RV.rec (motive := fun _ => RR)
      (fun b => Bool.rec (motive := fun _ => RR) .bad (.ok (.bit (icmpR op w a b))) int)
      (fun _ => .bad) y)
    (fun a => RV.rec (motive := fun _ => RR)
      (fun _ => .bad)
      (fun c => Bool.rec (motive := fun _ => RR) (.ok (.bit (icmpR op 1 (b2n a) (b2n c)))) .bad
        int) y)
    x

/-- `select`: a Boolean condition, and two arms of the instance type's sort. -/
def selR (int : Bool) (cv x y : RV) : RR :=
  RV.rec (motive := fun _ => RR)
    (fun _ => .bad)
    (fun c => RV.rec (motive := fun _ => RR)
      (fun a => RV.rec (motive := fun _ => RR)
        (fun b => Bool.rec (motive := fun _ => RR) .bad
          (.ok (.res (Bool.rec (motive := fun _ => Nat) b a c))) int)
        (fun _ => .bad) y)
      (fun a => RV.rec (motive := fun _ => RR)
        (fun _ => .bad)
        (fun b => Bool.rec (motive := fun _ => RR)
          (.ok (.bit (Bool.rec (motive := fun _ => Bool) b a c))) .bad int) y)
      x)
    cv

/-- Sequencing, as `R.bind` orders it: the first outcome that is not a value
    is the outcome. -/
def RR.bind (x : RR) (f : RV → RR) : RR :=
  RR.rec (motive := fun _ => RR) f .ub .bad x

/-- The value of a pattern on residues. `int`: the instance type is an integer
    type, of width `w` and modulus `m` (`evalR_agrees`). The sequencing is
    `RR.bind` unfolded (`evalR_bin` and its siblings state it folded): one
    kernel step less per operator and assignment. -/
def _root_.EqsatRule.Pat.evalR (int : Bool) (w m : Nat) (env : List RV) (p : Pat) : RR :=
  Pat.rec (motive := fun _ => RR)
    (fun i => getR env i)
    (fun i => getR env i)
    (fun neg mag => Bool.rec (motive := fun _ => RR) .bad (.ok (.res (litR w neg mag))) int)
    (.ok (.bit true))
    (.ok (.bit false))
    (fun op _ _ ra rb =>
      RR.rec (motive := fun _ => RR)
        (fun x => RR.rec (motive := fun _ => RR) (fun y => binR int w m op x y) .ub .bad rb)
        .ub .bad ra)
    (fun op _ ra => RR.rec (motive := fun _ => RR) (fun x => unR int w m op x) .ub .bad ra)
    (fun op _ _ ra rb =>
      RR.rec (motive := fun _ => RR)
        (fun x => RR.rec (motive := fun _ => RR) (fun y => cmpR int w op x y) .ub .bad rb)
        .ub .bad ra)
    (fun _ _ _ rc ra rb =>
      RR.rec (motive := fun _ => RR)
        (fun cv => RR.rec (motive := fun _ => RR)
          (fun x => RR.rec (motive := fun _ => RR) (fun y => selR int cv x y) .ub .bad rb)
          .ub .bad ra)
        .ub .bad rc)
    p

/-- Two residue values are the same value. -/
def RV.beq (u v : RV) : Bool :=
  RV.rec (motive := fun _ => Bool)
    (fun a => RV.rec (motive := fun _ => Bool) (fun b => Nat.beq a b) (fun _ => false) v)
    (fun a => RV.rec (motive := fun _ => Bool) (fun _ => false)
      (fun c => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true false c) c a) v)
    u

/-- `EqsatRule.Holds` on residue outcomes. `equiv`: one common value.
    `refines`: one common value, or the left side is undefined behaviour and
    the right side is not `bad`. `Holds` asks nothing of the right side
    there; this asks that it is an outcome of SemR's (`holdsR_bad_right`), so
    a right side that is not a term stands nowhere. -/
def holdsR (d : Dir) (l r : RR) : Bool :=
  RR.rec (motive := fun _ => Bool)
    (fun u => RR.rec (motive := fun _ => Bool) (fun v => u.beq v) false false r)
    (Dir.rec (motive := fun _ => Bool) false
      (RR.rec (motive := fun _ => Bool) (fun _ => true) true false r) d)
    false l

end

/-- `r` is one of `2^0 … 2^(k-1)`. -/
def pow2Upto : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, r => Nat.beq r (2 ^ k) || pow2Upto k r

noncomputable section

/-- `P` of the residue of the variable of rank `i`; `true` where the variable
    has no residue (`EqsatRule.onResidue`). -/
def condR (int : Bool) (env : List RV) (i : Nat) (P : Nat → Bool) : Bool :=
  match int with
  | true =>
    match getR env i with
    | .ok (.res r) => P r
    | _ => true
  | false => true

/-- One side condition on residues (`EqsatRule.Cond.holds`). -/
def _root_.EqsatRule.Cond.holdsR (int : Bool) (w : Nat) (env : List RV) : Cond → Bool
  | .eq i neg mag => condR int env i fun r => Nat.beq r (litR w neg mag)
  | .ne i neg mag => condR int env i fun r => !Nat.beq r (litR w neg mag)
  | .pow2 i => condR int env i fun r => pow2Upto w r
  | .zeroModWidth i => condR int env i fun r => Nat.beq (r % w) 0

/-- The side conditions on residues (`EqsatRule.CondsHold`). -/
def condsR (int : Bool) (w : Nat) (env : List RV) (cs : Conds) : Bool :=
  Conds.rec (motive := fun _ => Bool) true
    (fun c _ ih => Bool.rec (motive := fun _ => Bool) false ih (c.holdsR int w env)) cs

/-- One assignment of a rule, given by its fields (a procedure takes the rule
    apart once, not once per assignment): the side conditions fail, or the
    two sides stand as the direction says (`checkR_sound`). -/
def checkR (d : Dir) (lhs rhs : Pat) (cs : Conds) (int : Bool) (w m : Nat) (env : List RV) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (holdsR d (lhs.evalR int w m env) (rhs.evalR int w m env))
    (condsR int w env cs)

end

/-! ## What the definitions reduce to -/

theorem getR_nil (i : Nat) : getR [] i = .bad := rfl
theorem getR_zero (v : RV) (vs : List RV) : getR (v :: vs) 0 = .ok v := rfl
theorem getR_succ (v : RV) (vs : List RV) (i : Nat) : getR (v :: vs) (i + 1) = getR vs i := rfl

theorem chk_of_lt {m r : Nat} (h : r < m) : chk m r = .ok (.res r) := by
  have hb : Nat.blt r m = true := by rw [Nat.blt_eq]; exact h
  simp only [chk, hb]

theorem chk_cases (m r : Nat) : (chk m r = .ok (.res r) ∧ r < m) ∨ chk m r = .bad := by
  by_cases h : r < m
  · exact .inl ⟨chk_of_lt h, h⟩
  · have hb : Nat.blt r m = false := by
      cases hb : Nat.blt r m
      · rfl
      · exact absurd (Nat.blt_eq ▸ hb) h
    exact .inr (by simp only [chk, hb])

theorem bind_ok (v : RV) (f : RV → RR) : (RR.ok v).bind f = f v := rfl
theorem bind_ub (f : RV → RR) : RR.ub.bind f = .ub := rfl
theorem bind_bad (f : RV → RR) : RR.bad.bind f = .bad := rfl

theorem evalR_var (int : Bool) (w m : Nat) (env : List RV) (i : Nat) :
    (Pat.var i).evalR int w m env = getR env i := rfl
theorem evalR_cvar (int : Bool) (w m : Nat) (env : List RV) (i : Nat) :
    (Pat.cvar i).evalR int w m env = getR env i := rfl
theorem evalR_lit_int (w m : Nat) (env : List RV) (neg : Bool) (mag : Nat) :
    (Pat.lit neg mag).evalR true w m env = .ok (.res (litR w neg mag)) := rfl
theorem evalR_lit_bool (w m : Nat) (env : List RV) (neg : Bool) (mag : Nat) :
    (Pat.lit neg mag).evalR false w m env = .bad := rfl
theorem evalR_tt (int : Bool) (w m : Nat) (env : List RV) :
    Pat.tt.evalR int w m env = .ok (.bit true) := rfl
theorem evalR_ff (int : Bool) (w m : Nat) (env : List RV) :
    Pat.ff.evalR int w m env = .ok (.bit false) := rfl
theorem evalR_bin (int : Bool) (w m : Nat) (env : List RV) (op : BinOp) (a b : Pat) :
    (Pat.bin op a b).evalR int w m env =
      (a.evalR int w m env).bind fun x => (b.evalR int w m env).bind fun y =>
        binR int w m op x y := rfl
theorem evalR_un (int : Bool) (w m : Nat) (env : List RV) (op : UnOp) (a : Pat) :
    (Pat.un op a).evalR int w m env = (a.evalR int w m env).bind fun x => unR int w m op x := rfl
theorem evalR_cmp (int : Bool) (w m : Nat) (env : List RV) (op : ICmpOp) (a b : Pat) :
    (Pat.cmp op a b).evalR int w m env =
      (a.evalR int w m env).bind fun x => (b.evalR int w m env).bind fun y =>
        cmpR int w op x y := rfl
theorem evalR_sel (int : Bool) (w m : Nat) (env : List RV) (c a b : Pat) :
    (Pat.sel c a b).evalR int w m env =
      (c.evalR int w m env).bind fun cv => (a.evalR int w m env).bind fun x =>
        (b.evalR int w m env).bind fun y => selR int cv x y := rfl

theorem condsR_nil (int : Bool) (w : Nat) (env : List RV) : condsR int w env .nil = true := rfl
theorem condsR_cons (int : Bool) (w : Nat) (env : List RV) (c : Cond) (rest : Conds) :
    condsR int w env (.cons c rest) = (c.holdsR int w env && condsR int w env rest) := by
  show Bool.rec (motive := fun _ => Bool) false (condsR int w env rest) (c.holdsR int w env) = _
  cases c.holdsR int w env <;> rfl

theorem checkR_eq (d : Dir) (lhs rhs : Pat) (cs : Conds) (int : Bool) (w m : Nat)
    (env : List RV) :
    checkR d lhs rhs cs int w m env =
      (!condsR int w env cs || holdsR d (lhs.evalR int w m env) (rhs.evalR int w m env)) := by
  show Bool.rec (motive := fun _ => Bool) true _ (condsR int w env cs) = _
  cases condsR int w env cs <;> rfl

/-! ## The agreement of each operator with SemR's -/

theorem agrees_bad (T : STy) (m : Nat) (x : R Val) : Agrees T m .bad x := trivial

theorem agrees_res {t : IntTy} {m r : Nat} (h : r < m) :
    Agrees (.int t) m (.ok (.res r)) (.ok (.int t r)) := ⟨⟨rfl, h⟩, rfl⟩

theorem agrees_bit (T : STy) (m : Nat) (v : Bool) : Agrees T m (.ok (.bit v)) (.ok (.bool v)) :=
  ⟨trivial, rfl⟩

theorem chk_agrees (t : IntTy) (m r : Nat) : Agrees (.int t) m (chk m r) (.ok (.int t r)) := by
  rcases chk_cases m r with ⟨h, hr⟩ | h
  · rw [h]; exact agrees_res hr
  · rw [h]; trivial

theorem ofOp_agrees (t : IntTy) (m : Nat) (x : OpRes Nat) :
    Agrees (.int t) m (ofOp m x) ((liftOp x).bind fun r => .ok (.int t r)) := by
  cases x with
  | ok r => exact chk_agrees t m r
  | ub msg => exact ⟨msg, rfl⟩
  | tyErr msg => exact agrees_bad _ _ _
  | unsup f => exact agrees_bad _ _ _

/-- `intBinR` against SemR's `intBin`, in the form `evalBinop_int` leaves. -/
theorem intBinR_agrees (t : IntTy) (op : BinOp) (w a b : Nat) :
    Agrees (.int t) (modulus w) (intBinR op w (modulus w) a b)
      ((liftOp (intBin op w a b)).bind fun r => .ok (.int t r)) := by
  cases op
  case add => exact agrees_res (mod_modulus_lt w _)
  case sub => exact agrees_res (mod_modulus_lt w _)
  case mul => exact agrees_res (mod_modulus_lt w _)
  case and => exact agrees_res (mod_modulus_lt w _)
  case or => exact agrees_res (mod_modulus_lt w _)
  case xor => exact agrees_res (mod_modulus_lt w _)
  case udiv => exact ofOp_agrees t _ _
  case sdiv => exact ofOp_agrees t _ _
  case urem => exact ofOp_agrees t _ _
  case srem => exact ofOp_agrees t _ _
  case shl => exact ofOp_agrees t _ _
  case lshr => exact ofOp_agrees t _ _
  case ashr => exact ofOp_agrees t _ _
  case rotl => exact chk_agrees t _ _
  case rotr => exact chk_agrees t _ _
  case bAnd => exact agrees_bad _ _ _
  case bOr => exact agrees_bad _ _ _
  case bXor => exact agrees_bad _ _ _

/-- `boolBinR` against SemR's `boolBin`, in the form `evalBinop_bool` leaves. -/
theorem boolBinR_agrees (T : STy) (m : Nat) (op : BinOp) (a c : Bool) :
    Agrees T m (boolBinR op a c) ((liftOp (boolBin op a c)).bind fun r => .ok (.bool r)) := by
  cases op <;> first | exact agrees_bit T m _ | trivial

theorem binTy_bool (op : BinOp) : binTy .bool op = .bool := by cases op <;> rfl

/-- Two residues at an integer type: `intBinR` against SemR's `evalBinop`. -/
theorem intBinR_evalBinop {pb : Nat} (t : IntTy) (op : BinOp) {a b : Nat}
    (ha : a < modulus (t.bits pb)) (hb : b < modulus (t.bits pb)) :
    Agrees (.int t) (modulus (t.bits pb)) (intBinR op (t.bits pb) (modulus (t.bits pb)) a b)
      (evalBinop pb op (binTy (.int t) op) (.int t a) (.int t b)) := by
  cases op
  case bAnd => exact agrees_bad _ _ _
  case bOr => exact agrees_bad _ _ _
  case bXor => exact agrees_bad _ _ _
  all_goals
    show Agrees _ _ _ (evalBinop pb _ (.int t) (.int t a) (.int t b))
    rw [evalBinop_int ha hb]
    exact intBinR_agrees t _ _ a b

/-- Two Booleans at an integer type: only `band bor bxor` take them. -/
theorem boolBinAtIntR_evalBinop (pb : Nat) (t : IntTy) (m : Nat) (op : BinOp) (a c : Bool) :
    Agrees (.int t) m (boolBinAtIntR op a c)
      (evalBinop pb op (binTy (.int t) op) (.bool a) (.bool c)) := by
  cases op
  case bAnd =>
    show Agrees _ _ _ (evalBinop pb _ .bool (.bool a) (.bool c))
    rw [evalBinop_bool]; exact agrees_bit _ _ _
  case bOr =>
    show Agrees _ _ _ (evalBinop pb _ .bool (.bool a) (.bool c))
    rw [evalBinop_bool]; exact agrees_bit _ _ _
  case bXor =>
    show Agrees _ _ _ (evalBinop pb _ .bool (.bool a) (.bool c))
    rw [evalBinop_bool]; exact agrees_bit _ _ _
  all_goals exact agrees_bad _ _ _

/-- `binR` against SemR's `evalBinop` at the operand type `binTy` gives. -/
theorem binR_agrees {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    (op : BinOp) {x y : RV} (hx : x.WF (isInt T) m) (hy : y.WF (isInt T) m) :
    Agrees T m (binR (isInt T) w m op x y) (evalBinop pb op (binTy T op) (x.val T) (y.val T)) := by
  subst hm
  cases T with
  | int t =>
    have hw' : t.bits pb = w := hw
    subst hw'
    cases x with
    | res a =>
      cases y with
      | res b => exact intBinR_evalBinop t op hx.2 hy.2
      | bit c => exact agrees_bad _ _ _
    | bit a =>
      cases y with
      | res b => exact agrees_bad _ _ _
      | bit c => exact boolBinAtIntR_evalBinop pb t _ op a c
  | bool =>
    cases x with
    | res a => exact absurd hx.1 (by decide)
    | bit a =>
      cases y with
      | res b => exact absurd hy.1 (by decide)
      | bit c =>
        show Agrees _ _ (boolBinR op a c) (evalBinop pb op (binTy .bool op) (.bool a) (.bool c))
        rw [binTy_bool, evalBinop_bool]
        exact boolBinR_agrees _ _ op a c

/-- `intUnR` against SemR's `intUn`. -/
theorem intUnR_agrees (t : IntTy) (op : UnOp) (w a : Nat) :
    Agrees (.int t) (modulus w) (intUnR op w (modulus w) a) (.ok (.int t (intUn op w a))) := by
  cases op
  case neg => exact agrees_res (mod_modulus_lt w _)
  case not =>
    refine agrees_res ?_
    have := modulus_pos w
    show modulus w - 1 - a % modulus w < modulus w
    omega
  all_goals exact chk_agrees t _ _

/-- `unR` against SemR's `evalUnop`. -/
theorem unR_agrees {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    (op : UnOp) {x : RV} (hx : x.WF (isInt T) m) :
    Agrees T m (unR (isInt T) w m op x) (evalUnop pb op T.ty (x.val T)) := by
  subst hm
  cases T with
  | int t =>
    have hw' : t.bits pb = w := hw
    subst hw'
    cases x with
    | res a =>
      show Agrees _ _ (intUnR op _ _ a) (evalUnop pb op (.int t) (.int t a))
      rw [evalUnop_int hx.2]
      exact intUnR_agrees t op _ a
    | bit c => exact agrees_bad _ _ _
  | bool =>
    cases x with
    | res a => exact absurd hx.1 (by decide)
    | bit c => exact agrees_bad _ _ _

/-- `cmpR` against SemR's `evalIcmp`. -/
theorem cmpR_agrees {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    (op : ICmpOp) {x y : RV} (hx : x.WF (isInt T) m) (hy : y.WF (isInt T) m) :
    Agrees T m (cmpR (isInt T) w op x y) (evalIcmp pb op T.ty (x.val T) (y.val T)) := by
  subst hm
  cases T with
  | int t =>
    have hw' : t.bits pb = w := hw
    subst hw'
    cases x with
    | res a =>
      cases y with
      | res b =>
        show Agrees _ _ (.ok (.bit (icmpR op _ a b))) (evalIcmp pb op (.int t) (.int t a) (.int t b))
        rw [evalIcmp_int hx.2 hy.2]
        exact agrees_bit _ _ _
      | bit c => exact agrees_bad _ _ _
    | bit a =>
      cases y with
      | res b => exact agrees_bad _ _ _
      | bit c => exact agrees_bad _ _ _
  | bool =>
    cases x with
    | res a => exact absurd hx.1 (by decide)
    | bit a =>
      cases y with
      | res b => exact absurd hy.1 (by decide)
      | bit c =>
        show Agrees _ _ (.ok (.bit (icmpR op 1 (b2n a) (b2n c))))
          (evalIcmp pb op .bool (.bool a) (.bool c))
        rw [evalIcmp_bool]
        exact agrees_bit _ _ _

/-- `selR` against SemR's `selectVal`. -/
theorem selR_agrees {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    {cv x y : RV} (hx : x.WF (isInt T) m) (hy : y.WF (isInt T) m) :
    Agrees T m (selR (isInt T) cv x y) (selectVal pb T.ty (cv.val T) (x.val T) (y.val T)) := by
  subst hm
  cases cv with
  | res r => exact agrees_bad _ _ _
  | bit c =>
    cases T with
    | int t =>
      have hw' : t.bits pb = w := hw
      subst hw'
      cases x with
      | res a =>
        cases y with
        | res b =>
          show Agrees _ _ (.ok (.res (Bool.rec b a c)))
            (selectVal pb (.int t) (.bool c) (.int t a) (.int t b))
          rw [selectVal_int c hx.2 hy.2]
          cases c
          · exact agrees_res hy.2
          · exact agrees_res hx.2
        | bit d => exact agrees_bad _ _ _
      | bit a =>
        cases y with
        | res b => exact agrees_bad _ _ _
        | bit d => exact agrees_bad _ _ _
    | bool =>
      cases x with
      | res a => exact absurd hx.1 (by decide)
      | bit a =>
        cases y with
        | res b => exact absurd hy.1 (by decide)
        | bit d =>
          show Agrees _ _ (.ok (.bit (Bool.rec d a c)))
            (selectVal pb .bool (.bool c) (.bool a) (.bool d))
          rw [selectVal_bool]
          cases c <;> exact agrees_bit _ _ _

/-! ## The agreement of the evaluator -/

theorem getR_agrees (T : STy) (m : Nat) :
    ∀ (env : List RV), EnvWF (isInt T) m env → ∀ i,
      Agrees T m (getR env i) (getVar (env.map (RV.val T)) i)
  | [], _, _ => agrees_bad _ _ _
  | _ :: _, h, 0 => ⟨h.1, rfl⟩
  | _ :: vs, h, i + 1 => getR_agrees T m vs h.2 i

/-- Sequencing: when the first outcomes agree and the continuations agree on
    every well-formed value, the bound outcomes agree. -/
theorem bind_agrees {T : STy} {m : Nat} {x : RR} {X : R Val} {f : RV → RR} {F : Val → R Val}
    (hx : Agrees T m x X) (hf : ∀ v, v.WF (isInt T) m → Agrees T m (f v) (F (v.val T))) :
    Agrees T m (x.bind f) (X.bind F) := by
  cases x with
  | ok v =>
    obtain ⟨hv, rfl⟩ := hx
    exact hf v hv
  | ub =>
    obtain ⟨msg, rfl⟩ := hx
    exact ⟨msg, rfl⟩
  | bad => exact agrees_bad _ _ _

/-- The adequacy of the residue evaluator. At instance type `T` of width `w`
    and modulus `m`, on a well-formed assignment, the outcome of `evalR` says
    of `Pat.eval` on the assignment's values what `Agrees` states: `ok v` is
    the value `v` stands for, `ub` is undefined behaviour, and `bad` claims
    nothing. Every pattern form and every operator of `BinOp`, `UnOp` and
    `ICmpOp` is covered (the operators outside the rule grammar included). -/
theorem evalR_agrees {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    {env : List RV} (henv : EnvWF (isInt T) m env) (p : Pat) :
    Agrees T m (p.evalR (isInt T) w m env) (p.eval pb T (env.map (RV.val T))) := by
  induction p with
  | var i => exact getR_agrees T m env henv i
  | cvar i => exact getR_agrees T m env henv i
  | lit neg mag =>
    cases T with
    | int t =>
      have hw' : t.bits pb = w := hw
      subst hw'; subst hm
      exact agrees_res (litR_lt _ neg mag)
    | bool => exact agrees_bad _ _ _
  | tt => exact agrees_bit T m true
  | ff => exact agrees_bit T m false
  | bin op a b iha ihb =>
    rw [evalR_bin]
    exact bind_agrees iha fun x hx => bind_agrees ihb fun y hy => binR_agrees hw hm op hx hy
  | un op a iha =>
    rw [evalR_un]
    exact bind_agrees iha fun x hx => unR_agrees hw hm op hx
  | cmp op a b iha ihb =>
    rw [evalR_cmp]
    exact bind_agrees iha fun x hx => bind_agrees ihb fun y hy => cmpR_agrees hw hm op hx hy
  | sel c a b ihc iha ihb =>
    rw [evalR_sel]
    exact bind_agrees ihc fun cv _ => bind_agrees iha fun x hx => bind_agrees ihb fun y hy =>
      selR_agrees hw hm hx hy

/-! ## The direction, the side conditions and one assignment -/

theorem beq_eq {u v : RV} (h : u.beq v = true) : u = v := by
  cases u with
  | res a =>
    cases v with
    | res b => exact congrArg RV.res (Nat.eq_of_beq_eq_true h)
    | bit c => exact Bool.noConfusion (show false = true from h)
  | bit a =>
    cases v with
    | res b => exact Bool.noConfusion (show false = true from h)
    | bit c => cases a <;> cases c <;> first | rfl | exact Bool.noConfusion (show false = true from h)

/-- A left side that is `bad` stands under neither direction, whatever the
    right side is. -/
theorem holdsR_bad_left (d : Dir) (r : RR) : holdsR d .bad r = false := rfl

/-- A right side that is `bad` stands under neither direction, whatever the
    left side is: also under `refines` beside a left side that is undefined
    behaviour, where `EqsatRule.Holds` would let it stand. -/
theorem holdsR_bad_right (d : Dir) (l : RR) : holdsR d l .bad = false := by
  cases l <;> cases d <;> rfl

/-- `holdsR` is `EqsatRule.Holds` of the outcomes it was computed from. A
    `bad` side, undefined behaviour on the right beside a value, and
    undefined behaviour on the left of an `equiv` statement all answer
    `false`. -/
theorem holdsR_sound {T : STy} {m : Nat} {d : Dir} {l r : RR} {L R : R Val}
    (hl : Agrees T m l L) (hr : Agrees T m r R) (h : holdsR d l r = true) : Holds d L R := by
  cases l with
  | ok u =>
    cases r with
    | ok v =>
      obtain ⟨_, rfl⟩ := hl
      obtain ⟨_, rfl⟩ := hr
      have huv : u = v := beq_eq h
      subst huv
      cases d
      · exact ⟨_, rfl, rfl⟩
      · exact .inr ⟨_, rfl, rfl⟩
    | ub => exact Bool.noConfusion (show false = true from h)
    | bad => exact Bool.noConfusion (show false = true from h)
  | ub =>
    cases d
    · exact Bool.noConfusion (show false = true from h)
    · obtain ⟨msg, rfl⟩ := hl
      exact .inl ⟨msg, rfl⟩
  | bad => exact Bool.noConfusion (show false = true from h)

theorem pow2Upto_of_lt : ∀ (n k : Nat), k < n → pow2Upto n (2 ^ k) = true
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    by_cases hk : k = n
    · subst hk; simp [pow2Upto]
    · have := pow2Upto_of_lt n k (by omega)
      simp [pow2Upto, this]

/-- A power of two below `2^w` is found by `pow2Upto w`. -/
theorem pow2Upto_complete {w r : Nat} (hr : r < modulus w) (h : ∃ k, r = 2 ^ k) :
    pow2Upto w r = true := by
  obtain ⟨k, rfl⟩ := h
  refine pow2Upto_of_lt w k ?_
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hr

/-- The residue the evaluator reads for a variable is the residue
    `EqsatRule.onResidue` reads. -/
theorem getVar_of_getR_res {t : IntTy} :
    ∀ (env : List RV) (i : Nat) (r : Nat), getR env i = .ok (.res r) →
      getVar (env.map (RV.val (.int t))) i = .ok (.int t r)
  | [], _, _, h => absurd h (by simp [getR_nil])
  | v :: _, 0, r, h => by
    have hv : v = .res r := by simpa [getR_zero] using h
    subst hv; rfl
  | _ :: vs, i + 1, r, h => getVar_of_getR_res vs i r h

theorem getR_res_lt {m : Nat} :
    ∀ (env : List RV), EnvWF true m env → ∀ (i r : Nat), getR env i = .ok (.res r) → r < m
  | [], _, _, _, h => absurd h (by simp [getR_nil])
  | v :: _, hwf, 0, r, h => by
    have hv : v = .res r := by simpa [getR_zero] using h
    subst hv; exact hwf.1.2
  | _ :: vs, hwf, i + 1, r, h => getR_res_lt vs hwf.2 i r h

/-- `condR` is `true` wherever `onResidue` holds of a property `P` decides in
    that direction. -/
theorem condR_of_onResidue {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    {env : List RV} (henv : EnvWF (isInt T) m env) (i : Nat) {P : Nat → Nat → Prop}
    {Pb : Nat → Bool} (hP : ∀ r, r < m → P w r → Pb r = true)
    (h : onResidue pb T (env.map (RV.val T)) i P) : condR (isInt T) env i Pb = true := by
  cases T with
  | bool => rfl
  | int t =>
    have hw' : t.bits pb = w := hw
    subst hw'
    show (match getR env i with | .ok (.res r) => Pb r | _ => true) = true
    cases hg : getR env i with
    | ok v =>
      cases v with
      | res r =>
        have hv := getVar_of_getR_res (t := t) env i r hg
        have hlt := getR_res_lt env henv i r hg
        simp only [onResidue, hv] at h
        exact hP r hlt h
      | bit c => rfl
    | ub => rfl
    | bad => rfl

/-- A side condition that holds in SemR's reading is `true` on residues. -/
theorem holdsR_of_holds {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    (hm : m = modulus w) {env : List RV} (henv : EnvWF (isInt T) m env) (c : Cond)
    (h : c.holds pb T (env.map (RV.val T))) : c.holdsR (isInt T) w env = true := by
  subst hm
  cases c with
  | eq i neg mag =>
    have h' : onResidue pb T (env.map (RV.val T)) i fun w r => r = litR w neg mag := h
    refine condR_of_onResidue hw henv i (fun r _ hr => ?_) h'
    subst hr; exact Nat.beq_refl _
  | ne i neg mag =>
    have h' : onResidue pb T (env.map (RV.val T)) i fun w r => r ≠ litR w neg mag := h
    refine condR_of_onResidue hw henv i (fun r _ hr => ?_) h'
    cases hb : Nat.beq r (litR w neg mag)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hr
  | pow2 i =>
    have h' : onResidue pb T (env.map (RV.val T)) i fun _ r => ∃ k, r = 2 ^ k := h
    exact condR_of_onResidue hw henv i (fun r hlt hr => pow2Upto_complete hlt hr) h'
  | zeroModWidth i =>
    have h' : onResidue pb T (env.map (RV.val T)) i fun w r => r % w = 0 := h
    refine condR_of_onResidue hw henv i (fun r _ hr => ?_) h'
    show Nat.beq (r % w) 0 = true
    rw [hr]; rfl

/-- The side conditions are decided in the direction that can only lose a
    rule: where they hold, `condsR` is `true`. -/
theorem condsR_of_condsHold {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    (hm : m = modulus w) {env : List RV} (henv : EnvWF (isInt T) m env) :
    ∀ (cs : Conds), CondsHold pb T (env.map (RV.val T)) cs → condsR (isInt T) w env cs = true
  | .nil, _ => rfl
  | .cons c rest, h => by
    rw [condsR_cons, holdsR_of_holds hw hm henv c h.1, condsR_of_condsHold hw hm henv rest h.2]
    rfl

/-- What a `true` of `checkR` proves of one assignment: under the side
    conditions, the two sides stand as the direction says, in SemR's own
    evaluation. With the fields of a rule `r` this is the body of
    `EqsatRule.Sound r T` at the assignment `env.map (RV.val T)`. -/
theorem checkR_sound {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    {env : List RV} (henv : EnvWF (isInt T) m env) (d : Dir) (lhs rhs : Pat) (cs : Conds)
    (h : checkR d lhs rhs cs (isInt T) w m env = true) :
    CondsHold pb T (env.map (RV.val T)) cs →
      Holds d (lhs.eval pb T (env.map (RV.val T))) (rhs.eval pb T (env.map (RV.val T))) := by
  intro hc
  rw [checkR_eq, condsR_of_condsHold hw hm henv cs hc] at h
  exact holdsR_sound (evalR_agrees hw hm henv lhs) (evalR_agrees hw hm henv rhs) h

end EqsatDecide
