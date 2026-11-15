/-
  VF5Calc — the F1 calculus over SemR: affine terms, the symbolic executor `sx`,
  the verification condition `vc`, and the checker that pairs it with VF4's
  `chk_LIA_cases` (Trust's proven-core plan, VF5; SBC M1).

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  The calculus reads a SemR `Module` (the decoded artifact) and, per function,
  produces a list of OBLIGATIONS: each a conjunction of linear constraints
  `Σ aᵢ·xᵢ ≤ b` (VF4's `ChkLIA.Cons`) that must be unsatisfiable over ℤ. An
  obligation is emitted where the run could go wrong (a failed `Assert`, an
  `Unreachable`, an operator's undefined behaviour, a call whose arguments miss
  the callee's precondition); a construct outside F1 emits the EMPTY
  obligation `[]`, which every assignment satisfies, so no certificate can
  discharge it (fail closed: `vc` is `False` there).

  Rules of the file: no `native_decide`, `partial`, `sorry`, `axiom`,
  `opaque`, `implemented_by`, `extern` or `unsafe`; every definition is total by
  structural recursion.

  The fragment F1 (SBC M1's scope, read on SemR):
  * `bool` and integer values up to 64 bits, in blocks and SSA values;
  * acyclic control flow: `sx` explores every path with a budget of steps, so
    a cycle exhausts it and emits `[]`;
  * the operators of `intBin` but `rotl`/`rotr`, the unary `neg` and `not`,
    the checked trio, `icmp`, `select`, `copy`, integer and `Bool` constants,
    `assert`, `unreachable`, `br`, `condBr`, `ret`, and `call` read through the
    callee's precondition (an untrusted annotation, so a call is a contract
    check plus fresh results);
  * every other value is an opaque scalar: a fresh variable with only its
    range known.

  Bools are never symbolic: every operation that produces a `Bool` from
  integers (`icmp`, the overflow flag) FORKS the path into the cases that
  decide it, each case carrying the linear constraints that select it.
-/
import VF5Sem

namespace VF5

open SemR

abbrev Cons := ChkLIA.Cons

/-! ## Affine terms over the path's integer variables -/

/-- `k + Σ co[i]·xᵢ`. -/
structure Aff where
  co : List Int
  k : Int

def Aff.eval (e : Aff) (ρ : Nat → Int) : Int := ChkLIA.dot e.co ρ + e.k

def Aff.c (n : Int) : Aff := ⟨[], n⟩

def unitVec : Nat → List Int
  | 0 => [1]
  | n + 1 => 0 :: unitVec n

def Aff.v (i : Nat) : Aff := ⟨unitVec i, 0⟩

def Aff.add (a b : Aff) : Aff := ⟨ChkLIA.addVec a.co b.co, a.k + b.k⟩

def Aff.smul (c : Int) (a : Aff) : Aff := ⟨ChkLIA.scale c a.co, c * a.k⟩

def Aff.sub (a b : Aff) : Aff := a.add (b.smul (-1))

def Aff.addC (a : Aff) (n : Int) : Aff := ⟨a.co, a.k + n⟩

/-- The constraint `e ≤ 0`. -/
def le0 (e : Aff) : Cons := ⟨e.co, -e.k⟩

/-- The constraint `a ≤ b`. -/
def leA (a b : Aff) : Cons := le0 (a.sub b)

/-- `a + n ≤ b`. -/
def leAn (a : Aff) (n : Int) (b : Aff) : Cons := le0 ((a.addC n).sub b)

/-- The term is a constant (no variable has a non-zero coefficient). -/
def Aff.isConst (e : Aff) : Bool := ChkLIA.allZero e.co

/-- `2^w` as an integer. -/
def Mw (w : Nat) : Int := (modulus w : Int)

/-- `2^(w-1)` as an integer. -/
def Hw (w : Nat) : Int := (half w : Int)

/-! ## Symbolic values and states -/

/-- A symbolic value: an integer of type `t` whose residue is the term's value,
    a known `Bool`, or a known fieldless enum value (D-2(b): every operation
    that produces one forks the path per variant, so its tag is known). -/
inductive SV where
  | int (t : IntTy) (e : Aff)
  | bool (b : Bool)
  | enm (id : Nat) (lanes : List Val)

def SV.ty : SV → Ty
  | .int t _ => .int t
  | .bool _ => .bool
  | .enm id _ => .enum id

structure SSt where
  blk : Block
  pc : Nat
  env : List (Nat × SV)
  cs : List Cons
  nv : Nat

def slook : List (Nat × SV) → Nat → Option SV
  | [], _ => none
  | (k, v) :: rest, x => if k == x then some v else slook rest x

def slooks (env : List (Nat × SV)) : List Nat → Option (List SV)
  | [] => some []
  | x :: xs =>
    match slook env x, slooks env xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The obligation nothing discharges: outside F1. -/
def FAIL : List (List Cons) := [[]]

/-- The range constraints of a `w`-bit residue `e`: `0 ≤ e ≤ 2^w - 1`. -/
def rangeCs (w : Nat) (e : Aff) : List Cons :=
  [le0 (e.smul (-1)), le0 (e.addC (-(Mw w - 1)))]

/-- A continuing branch of one operator: extra constraints, the values it
    binds, and the next fresh variable. -/
structure Br where
  cs : List Cons
  vals : List SV
  nv : Nat

/-- A fresh opaque `w`-bit integer: variable `nv`, its range only. -/
def freshInt (t : IntTy) (nv : Nat) : List Cons × SV × Nat :=
  (rangeCs t.bits (Aff.v nv), .int t (Aff.v nv), nv + 1)

/-- The sign split of a `w`-bit residue: `e < 2^(w-1)` (non-negative) or not. -/
def signSplit (w : Nat) (e : Aff) : List (List Cons × Bool) :=
  [([le0 (e.addC (-(Hw w - 1)))], false), ([le0 ((Aff.c (Hw w)).sub e)], true)]

/-- The biased value `(e + 2^(w-1)) mod 2^w` (`SemR.biased`), split on the sign. -/
def biasSplit (w : Nat) (e : Aff) : List (List Cons × Aff) :=
  [([le0 (e.addC (-(Hw w - 1)))], e.addC (Hw w)),
   ([le0 ((Aff.c (Hw w)).sub e)], e.addC (-(Hw w)))]

/-- The constraints that decide `icmpR op w a b` on the residues `ea`, `eb`, one
    list per case, with the case's answer. -/
def cmpCases (op : ICmpOp) (w : Nat) (ea eb : Aff) : List (List Cons × Bool) :=
  let ult (x y : Aff) : List (List Cons × Bool) := [([leAn x 1 y], true), ([leA y x], false)]
  let ule (x y : Aff) : List (List Cons × Bool) := [([leA x y], true), ([leAn y 1 x], false)]
  let sgn (f : Aff → Aff → List (List Cons × Bool)) : List (List Cons × Bool) :=
    (biasSplit w ea).flatMap fun (c1, x) =>
      (biasSplit w eb).flatMap fun (c2, y) =>
        (f x y).map fun (c3, r) => (c1 ++ c2 ++ c3, r)
  match op with
  | .eq => [([leA ea eb, leA eb ea], true), ([leAn ea 1 eb], false), ([leAn eb 1 ea], false)]
  | .ne => [([leA ea eb, leA eb ea], false), ([leAn ea 1 eb], true), ([leAn eb 1 ea], true)]
  | .ult => ult ea eb
  | .ule => ule ea eb
  | .ugt => ult eb ea
  | .uge => ule eb ea
  | .slt => sgn ult
  | .sle => sgn ule
  | .sgt => sgn (fun x y => ult y x)
  | .sge => sgn (fun x y => ule y x)

/-! ## VF7: integers read bit by bit

  Bitwise operations, shifts, narrowing casts and unsigned division or remainder
  by a power of two are EXACT in this calculus (VF7's first slice, Clean
  `docs/DECISIONS.md` R206): a `w`-bit residue `a` is read as `w` BIT TERMS,
  little-endian, each `0` or `1` at the path's assignment, with
  `a = Σ 2^i·bᵢ` (`bitSum`). A bit term is a known bit, a path variable `xⱼ`
  whose range `0 ≤ xⱼ ≤ 1` is a constraint of the path (`bitCs j`), or `1 - xⱼ`.

  `getBits` finds a term's bits: the term itself when it already is such a sum
  (`ownBits`, a guess `ownChk` checks: the sum's coefficients equal the term's
  and every variable it reads has its `0 ≤ xⱼ ≤ 1` among the path's
  constraints), a decomposition the path already made of the same term
  (`decompOf`, checked constraint by constraint: the fresh decomposition's
  constraints are themselves constraints of the path, so a second operator on
  one value reads the same bits), or a fresh decomposition (`freshBits`: `w` new variables, their ranges,
  and `e = Σ 2^i·xᵢ`). Every guess is checked, none trusted.

  On bits: `&`, `|`, `^` act bit by bit — a known bit decides, two unknown bits
  give a fresh bit `z` with the linear constraints that make it their AND, OR or
  XOR over `{0, 1}`; a shift by a known amount moves the list (an arithmetic
  shift right repeats the sign bit); a shift by an unknown amount forks the path
  on each in-range amount (`amounts`), the out-of-range one staying SemR's
  undefined behaviour; a narrowing `trunc`/`zext` keeps the low bits; `udiv` and
  `urem` by a constant `2^j` are a shift and a mask. The obligations stay linear
  and VF4's `chk_LIA_cases` discharges them.
-/

/-- A bit term: known, path variable `xⱼ` (`0` or `1` on the path), or `1 - xⱼ`. -/
inductive BT where
  | k (b : Bool)
  | v (j : Nat)
  | n (j : Nat)

def BT.aff : BT → Aff
  | .k b => Aff.c (if b then 1 else 0)
  | .v j => Aff.v j
  | .n j => (Aff.c 1).sub (Aff.v j)

def BT.kv : BT → Option Bool
  | .k b => some b
  | _ => none

/-- `1 - b`. -/
def BT.flip : BT → BT
  | .k b => .k (!b)
  | .v j => .n j
  | .n j => .v j

/-- `Σ 2^i·bᵢ`, little-endian. -/
def bitSum : List BT → Aff
  | [] => Aff.c 0
  | b :: bs => b.aff.add ((bitSum bs).smul 2)

/-- The range of a bit variable: `0 ≤ xⱼ ≤ 1`. -/
def bitCs (j : Nat) : List Cons := rangeCs 1 (Aff.v j)

/-- Integer equality by `Nat.beq` on the constructors (cheap for the kernel's
    evaluation, unlike `decide` through `Int.decEq`). -/
def intEqb : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

def listEqb : List Int → List Int → Bool
  | [], [] => true
  | a :: as, b :: bs => intEqb a b && listEqb as bs
  | _, _ => false

/-- `c` is literally one of `cs`. -/
def memC (c : Cons) : List Cons → Bool
  | [] => false
  | d :: ds => (listEqb c.coeffs d.coeffs && intEqb c.bound d.bound) || memC c ds

/-- `l` is `j` zeros, then `x`. -/
def zerosThen (x : Int) : List Int → Nat → Bool
  | [y], 0 => intEqb y x
  | y :: l, j + 1 => intEqb y 0 && zerosThen x l j
  | _, _ => false

/-- The bit variables of a path, in one pass: each `j` whose range `-xⱼ ≤ 0`,
    `xⱼ ≤ 1` (`bitCs j`, as every reading appends it) stands among `cs`. -/
def bitVarsOf : List Cons → List Nat
  | [] => []
  | c1 :: tl =>
    match tl with
    | [] => []
    | c2 :: _ =>
      if zerosThen (-1) c1.coeffs (c1.coeffs.length - 1) && intEqb c1.bound 0 &&
          zerosThen 1 c2.coeffs (c1.coeffs.length - 1) && intEqb c2.bound 1
      then (c1.coeffs.length - 1) :: bitVarsOf tl else bitVarsOf tl

def memN (j : Nat) : List Nat → Bool
  | [] => false
  | k :: ks => Nat.beq j k || memN j ks

/-- The bit's variable is one of the path's bit variables `vs`. -/
def bitOK (vs : List Nat) : BT → Bool
  | .k _ => true
  | .v j => memN j vs
  | .n j => memN j vs

def allOK (vs : List Nat) : List BT → Bool
  | [] => true
  | b :: bs => bitOK vs b && allOK vs bs

/-- The term is `0`: every coefficient and the constant. -/
def affZero (e : Aff) : Bool := ChkLIA.allZero e.co && ChkLIA.isZero e.k

/-- `bs` are `w` bits of `e` by the term's own shape. -/
def ownChk (w : Nat) (cs : List Cons) (e : Aff) (bs : List BT) : Bool :=
  bs.length == w && affZero ((bitSum bs).sub e) && allOK (bitVarsOf cs) bs

/-- The first variable from `j` on whose coefficient's magnitude has bit `i`,
    and whether that coefficient is negative. -/
def coAt (i : Nat) : Nat → List Int → Option (Nat × Bool)
  | _, [] => none
  | j, c :: cs => if c.natAbs / 2 ^ i % 2 == 1 then some (j, ChkLIA.isNeg c) else coAt i (j + 1) cs

def negSum : List Int → Int
  | [] => 0
  | c :: cs => (if ChkLIA.isNeg c then c else 0) + negSum cs

/-- The guess that `e` already is a sum of bits: each coefficient a sum of
    distinct powers of two read as that variable at those positions (a negative
    one as `1 - xⱼ`), the rest of the constant's bits known. `ownChk` decides it. -/
def ownBits (w : Nat) (e : Aff) : List BT :=
  let K := (e.k + negSum e.co).toNat
  (List.range w).map fun i =>
    match coAt i 0 e.co with
    | some (j, true) => .n j
    | some (j, false) => .v j
    | none => .k (K / 2 ^ i % 2 == 1)

/-- The bit variables `x_n, …, x_{n+w-1}`. -/
def bitVars (n : Nat) : Nat → List BT
  | 0 => []
  | w + 1 => .v n :: bitVars (n + 1) w

/-- Their ranges. -/
def varsCs (n : Nat) : Nat → List Cons
  | 0 => []
  | w + 1 => bitCs n ++ varsCs (n + 1) w

def firstNZ : Nat → List Int → Option Nat
  | _, [] => none
  | i, c :: cs => if c == 0 then firstNZ (i + 1) cs else some i

/-- A fresh decomposition of `e`: `w` new bit variables from `nv`, their ranges,
    and `e = Σ 2^i·x_{nv+i}`. -/
def freshBits (w : Nat) (e : Aff) (nv : Nat) : List Cons × List BT × Nat :=
  (le0 (e.sub (bitSum (bitVars nv w))) :: le0 ((bitSum (bitVars nv w)).sub e) :: varsCs nv w,
   bitVars nv w, nv + w)

/-- `p` is a prefix of `l`, constraint by constraint. -/
def prefixC : List Cons → List Cons → Bool
  | [], _ => true
  | c :: cs, d :: ds => (listEqb c.coeffs d.coeffs && intEqb c.bound d.bound) && prefixC cs ds
  | _ :: _, [] => false

/-- A decomposition of `e` the path already made: `freshBits w e n`'s constraints,
    contiguous among `ds` as the reading appended them (checked constraint by
    constraint, so no guess is trusted). -/
def decompOf (w : Nat) (e : Aff) : List Cons → Option (List BT)
  | [] => none
  | d :: ds =>
    match (if intEqb d.bound (-e.k) then firstNZ 0 (e.sub ⟨d.coeffs, -d.bound⟩).co else none) with
    | some n =>
      if Nat.ble e.co.length n && prefixC (freshBits w e n).1 (d :: ds) then some (bitVars n w)
      else decompOf w e ds
    | none => decompOf w e ds

/-- The `w` bits of `e` on a path with constraints `cs` and next fresh variable
    `nv`: the constraints the reading adds, the bits, the next fresh variable. -/
def getBits (w : Nat) (cs : List Cons) (e : Aff) (nv : Nat) : List Cons × List BT × Nat :=
  if ownChk w cs e (ownBits w e) then ([], ownBits w e, nv) else
  match decompOf w e cs with
  | some bs => ([], bs, nv)
  | none => freshBits w e nv

/-- A fresh bit `z = x_nv` with its range and the constraints `c z`. -/
def zBit (c : Aff → List Cons) (nv : Nat) : List Cons × BT × Nat :=
  (c (Aff.v nv) ++ bitCs nv, .v nv, nv + 1)

/-- `x AND y`: known when either is; else `z ≤ x`, `z ≤ y`, `x + y - 1 ≤ z`. -/
def andBit (x y : BT) (nv : Nat) : List Cons × BT × Nat :=
  match x.kv, y.kv with
  | some false, _ => ([], .k false, nv)
  | some true, _ => ([], y, nv)
  | none, some false => ([], .k false, nv)
  | none, some true => ([], x, nv)
  | none, none => zBit (fun z => [leA z x.aff, leA z y.aff, leAn (x.aff.add y.aff) (-1) z]) nv

/-- `x OR y`: known when either is `1`, the other when one is `0`; else
    `x ≤ z`, `y ≤ z`, `z ≤ x + y`. -/
def orBit (x y : BT) (nv : Nat) : List Cons × BT × Nat :=
  match x.kv, y.kv with
  | some true, _ => ([], .k true, nv)
  | some false, _ => ([], y, nv)
  | none, some true => ([], .k true, nv)
  | none, some false => ([], x, nv)
  | none, none => zBit (fun z => [leA x.aff z, leA y.aff z, leA z (x.aff.add y.aff)]) nv

/-- `x XOR y`: the other or its complement when one is known; else
    `z ≤ x + y`, `x - y ≤ z`, `y - x ≤ z`, `z + x + y ≤ 2`. -/
def xorBit (x y : BT) (nv : Nat) : List Cons × BT × Nat :=
  match x.kv, y.kv with
  | some b, _ => ([], if b then y.flip else y, nv)
  | none, some b => ([], if b then x.flip else x, nv)
  | none, none => zBit (fun z => [leA z (x.aff.add y.aff), leA (x.aff.sub y.aff) z,
      leA (y.aff.sub x.aff) z, leA (z.add (x.aff.add y.aff)) (Aff.c 2)]) nv

/-- A bit operation, bit by bit. -/
def zipBits (f : BT → BT → Nat → List Cons × BT × Nat) : List BT → List BT → Nat →
    List Cons × List BT × Nat
  | x :: xs, y :: ys, nv =>
    let r := f x y nv
    let rs := zipBits f xs ys r.2.2
    (r.1 ++ rs.1, r.2.1 :: rs.2.1, rs.2.2)
  | _, _, nv => ([], [], nv)

/-- `a·2^j mod 2^w`: `j` zeros, then the low `w - j` bits. -/
def shlBits (j : Nat) (xs : List BT) : List BT :=
  List.replicate j (.k false) ++ xs.take (xs.length - j)

/-- `a / 2^j`: the high bits, then `j` zeros. -/
def lshrBits (j : Nat) (xs : List BT) : List BT := xs.drop j ++ List.replicate j (.k false)

/-- The last bit (the sign bit of a signed reading). -/
def lastBit : List BT → BT
  | [] => .k false
  | [x] => x
  | _ :: y :: ys => lastBit (y :: ys)

/-- SemR's `ashr`: the high bits, then `j` copies of the sign bit. -/
def ashrBits (j : Nat) (xs : List BT) : List BT :=
  xs.drop j ++ List.replicate j (lastBit xs)

/-- `a mod 2^j`: the low `j` bits, then zeros. -/
def maskBits (j : Nat) (xs : List BT) : List BT :=
  xs.take j ++ List.replicate (xs.length - j) (.k false)

/-- A constant `j < w` the path already fixes `eb` to: `eb ≤ j` and `j ≤ eb` are
    both constraints of the path (an earlier fork on the same amount). -/
def fixedAt (w : Nat) (cs : List Cons) (eb : Aff) : List Cons → Option Nat
  | [] => none
  | d :: ds =>
    let j := d.bound + eb.k
    if listEqb d.coeffs eb.co && !ChkLIA.isNeg j && ChkLIA.isNeg (j - (w : Int)) &&
        memC (leA eb (Aff.c j)) cs && memC (leA (Aff.c j) eb) cs then some j.toNat
    else fixedAt w cs eb ds

/-- The shift amounts a path may take: the constant when it is one in range, the
    one the path fixes, else every amount below the width. -/
def amounts (w : Nat) (cs : List Cons) (eb : Aff) : List Nat :=
  if eb.isConst && !ChkLIA.isNeg eb.k && ChkLIA.isNeg (eb.k - (w : Int)) then [eb.k.toNat] else
  match fixedAt w cs eb cs with
  | some j => [j]
  | none => List.range w

/-- One branch per amount `j`: `eb = j`, the value's bits moved by `f j`. -/
def shiftBrs (t : IntTy) (f : Nat → List BT → List BT) (eb : Aff) (cs : List Cons)
    (r : List Cons × List BT × Nat) : List Br :=
  (amounts t.bits cs eb).map fun (j : Nat) =>
    ⟨r.1 ++ [leA eb (Aff.c (j : Int)), leA (Aff.c (j : Int)) eb], [.int t (bitSum (f j r.2.1))], r.2.2⟩

/-- `j` with `2^j = c`, `j < w`. -/
def log2Of (w : Nat) (c : Int) : Option Nat := (List.range w).find? fun j => intEqb ((2 ^ j : Nat) : Int) c

/-- The bitwise operation `f` on `ea`, `eb`: one branch. -/
def bitwiseBr (t : IntTy) (f : BT → BT → Nat → List Cons × BT × Nat) (ea eb : Aff) (nv : Nat)
    (cs : List Cons) : Br :=
  let ra := getBits t.bits cs ea nv
  let rb := getBits t.bits cs eb ra.2.2
  let rz := zipBits f ra.2.1 rb.2.1 rb.2.2
  ⟨ra.1 ++ rb.1 ++ rz.1, [.int t (bitSum rz.2.1)], rz.2.2⟩

/-- The `w` bits of `e` moved by `f`, as a value of type `t` (an unsigned
    division or remainder by `2^j`, a narrowing cast): one branch. -/
def bitsBr (w : Nat) (t : IntTy) (f : List BT → List BT) (e : Aff) (nv : Nat) (cs : List Cons) : Br :=
  let r := getBits w cs e nv
  ⟨r.1, [.int t (bitSum (f r.2.1))], r.2.2⟩

/-- An integer `BinOp` of type `t` on `ea`, `eb`, on a path with constraints
    `cs`: the obligations of its undefined behaviour (each must be
    unsatisfiable together with the path) and its continuing branches. `none`:
    outside F1. -/
def binCases (op : BinOp) (t : IntTy) (ea eb : Aff) (nv : Nat) (cs : List Cons) :
    Option (List (List Cons) × List Br) :=
  let w := t.bits
  let M := Mw w
  let fresh : List Br := let (c, v, n) := freshInt t nv; [⟨c, [v], n⟩]
  match op with
  | .add =>
    some ([], [⟨[le0 ((ea.add eb).addC (-(M - 1)))], [.int t (ea.add eb)], nv⟩,
               ⟨[le0 ((Aff.c M).sub (ea.add eb))], [.int t ((ea.add eb).addC (-M))], nv⟩])
  | .sub =>
    some ([], [⟨[leA eb ea], [.int t (ea.sub eb)], nv⟩,
               ⟨[leAn ea 1 eb], [.int t ((ea.sub eb).addC M)], nv⟩])
  | .mul =>
    if eb.isConst then
      let p := ea.smul eb.k
      let (c, v, n) := freshInt t nv
      some ([], [⟨[le0 (p.addC (-(M - 1)))], [.int t p], nv⟩,
                 ⟨le0 ((Aff.c M).sub p) :: c, [v], n⟩])
    else some ([], fresh)
  | .udiv =>
    match (if eb.isConst then log2Of w eb.k else none) with
    | some j => some ([[le0 eb]], [bitsBr w t (lshrBits j) ea nv cs])
    | none => some ([[le0 eb]], fresh)
  | .urem =>
    match (if eb.isConst then log2Of w eb.k else none) with
    | some j => some ([[le0 eb]], [bitsBr w t (maskBits j) ea nv cs])
    | none => some ([[le0 eb]], fresh)
  | .sdiv | .srem =>
    some ([[le0 eb], [leA ea (Aff.c (Hw w)), leA (Aff.c (Hw w)) ea,
                      leA eb (Aff.c (M - 1)), leA (Aff.c (M - 1)) eb]], fresh)
  | .shl => some ([[leA (Aff.c (w : Int)) eb]], shiftBrs t shlBits eb cs (getBits w cs ea nv))
  | .lshr => some ([[leA (Aff.c (w : Int)) eb]], shiftBrs t lshrBits eb cs (getBits w cs ea nv))
  | .ashr => some ([[leA (Aff.c (w : Int)) eb]], shiftBrs t ashrBits eb cs (getBits w cs ea nv))
  | .and => some ([], [bitwiseBr t andBit ea eb nv cs])
  | .or => some ([], [bitwiseBr t orBit ea eb nv cs])
  | .xor => some ([], [bitwiseBr t xorBit ea eb nv cs])
  | .bAnd | .bOr | .bXor => some ([], fresh)
  | .rotl | .rotr => none

/-- The checked trio `(r, flag)` of type `t` on `ea`, `eb`: its branches. -/
def ovfCases (op : OvfOp) (t : IntTy) (ea eb : Aff) (nv : Nat) : List Br :=
  let w := t.bits
  let M := Mw w
  -- the wrapped result: `(sum, no wrap)` and `(sum - M, wrap)`
  let addW : List (List Cons × Aff) :=
    [([le0 ((ea.add eb).addC (-(M - 1)))], ea.add eb),
     ([le0 ((Aff.c M).sub (ea.add eb))], (ea.add eb).addC (-M))]
  let subW : List (List Cons × Aff) :=
    [([leA eb ea], ea.sub eb), ([leAn ea 1 eb], (ea.sub eb).addC M)]
  let signed (ws : List (List Cons × Aff)) (flag : Bool → Bool → Bool → Bool) : List Br :=
    ws.flatMap fun (cw, r) =>
      (signSplit w ea).flatMap fun (c1, sa) =>
        (signSplit w eb).flatMap fun (c2, sb) =>
          (signSplit w r).map fun (c3, sr) =>
            ⟨cw ++ c1 ++ c2 ++ c3, [.int t r, .bool (flag sa sb sr)], nv⟩
  match op, t.signed with
  | .add, false =>
    [⟨[le0 ((ea.add eb).addC (-(M - 1)))], [.int t (ea.add eb), .bool false], nv⟩,
     ⟨[le0 ((Aff.c M).sub (ea.add eb))], [.int t ((ea.add eb).addC (-M)), .bool true], nv⟩]
  | .sub, false =>
    [⟨[leA eb ea], [.int t (ea.sub eb), .bool false], nv⟩,
     ⟨[leAn ea 1 eb], [.int t ((ea.sub eb).addC M), .bool true], nv⟩]
  | .add, true => signed addW (fun sa sb sr => sa == sb && sr != sa)
  | .sub, true => signed subW (fun sa sb sr => sa != sb && sr != sa)
  | .mul, false =>
    let (c, v, n) := freshInt t nv
    if eb.isConst then
      let p := ea.smul eb.k
      [⟨[le0 (p.addC (-(M - 1)))], [.int t p, .bool false], nv⟩,
       ⟨le0 ((Aff.c M).sub p) :: c, [v, .bool true], n⟩]
    else [⟨c, [v, .bool false], n⟩, ⟨c, [v, .bool true], n⟩]
  | .mul, true =>
    let (c, v, n) := freshInt t nv
    [⟨c, [v, .bool false], n⟩, ⟨c, [v, .bool true], n⟩]

/-- Integer `UnOp`: `neg` and `not`; `none` outside F1. -/
def unCases (op : UnOp) (t : IntTy) (ea : Aff) : Option (List Br) :=
  let M := Mw t.bits
  match op with
  | .neg => some [⟨[le0 ea], [.int t (Aff.c 0)], 0⟩,
                  ⟨[le0 ((Aff.c 1).sub ea)], [.int t ((Aff.c M).sub ea)], 0⟩]
  | .not => some [⟨[], [.int t ((Aff.c (M - 1)).sub ea)], 0⟩]
  | _ => none

/-- Static type agreement: the symbolic value has exactly type `t`. -/
def svIs (v : SV) (t : Ty) : Bool := v.ty.beq t

def isF1Int (t : IntTy) : Bool := decide (t.bits ≤ 64)

def svsAre : List SV → List Ty → Bool
  | [], [] => true
  | v :: vs, t :: ts => svIs v t && svsAre vs ts
  | _, _ => false

/-- `bindParams`, symbolically. -/
def sbindParams (env : List (Nat × SV)) : List (Nat × Ty) → List SV → Option (List (Nat × SV))
  | [], [] => some env
  | (x, t) :: ps, v :: vs => if svIs v t then sbindParams ((x, v) :: env) ps vs else none
  | _, _ => none

/-- The integer view of a symbolic argument: an integer's term, a `Bool`'s 0/1,
    an enum's `0` (`valInt`). -/
def SV.aff : SV → Aff
  | .int _ e => e
  | .bool b => Aff.c (if b then 1 else 0)
  | .enm _ _ => Aff.c 0

/-- `EnumOK`, decided: the value's one lane is the tag at the enum's tag type
    and the residue of one of its discriminants. -/
def enumOKb (m : Module) (id : Nat) (lanes : List Val) : Bool :=
  match findEnum m.enums id, lanes with
  | some d, [.int t a] =>
    isF1Enum d && t.code == d.tag.code && d.discs.any (fun disc => a == resid d.tag.bits disc)
  | _, _ => false

/-- Every valid value of a fieldless enum: one per variant. -/
def enumVals (m : Module) (id : Nat) : Option (List SV) :=
  match findEnum m.enums id with
  | some d =>
    if isF1Enum d then some (d.discs.map fun disc => .enm id [.int d.tag (resid d.tag.bits disc)])
    else none
  | none => none

/-- Substitute the argument terms for the callee's parameter variables
    `x₀, x₁, …` in `Σ aᵢ·xᵢ`. -/
def substCo : List Int → List Aff → Aff
  | a :: as, e :: es => ((e.smul a).add (substCo as es))
  | _, _ => Aff.c 0

/-- The NEGATION of `c` under the substitution: `Σ aᵢ·eᵢ ≥ b + 1`. -/
def negSubst (c : Cons) (args : List Aff) : Cons :=
  le0 ((Aff.c (c.bound + 1)).sub (substCo c.coeffs args))

/-- Fresh results of the types `ts`: integers are fresh variables (range only),
    `Bool`s fork both ways. -/
def freshVals (m : Module) : List Ty → Nat → Option (List (List Cons × List SV × Nat))
  | [], nv => some [([], [], nv)]
  | .int t :: ts, nv =>
    match freshVals m ts (nv + 1) with
    | none => none
    | some rs => some (rs.map fun (c, vs, n) => (rangeCs t.bits (Aff.v nv) ++ c, .int t (Aff.v nv) :: vs, n))
  | .bool :: ts, nv =>
    match freshVals m ts nv with
    | none => none
    | some rs => some (rs.flatMap fun (c, vs, n) => [(c, .bool false :: vs, n), (c, .bool true :: vs, n)])
  | .enum id :: ts, nv =>
    match enumVals m id, freshVals m ts nv with
    | some es, some rs => some (rs.flatMap fun (c, vs, n) => es.map fun e => (c, e :: vs, n))
    | _, _ => none
  | _ :: _, _ => none

/-- `0 ≤ b` with `b < 0`: a constraint false on its own (a branch of an operator on
    constants that the values do not take). -/
def trivFalse (c : Cons) : Bool := ChkLIA.allZero c.coeffs && ChkLIA.isNeg c.bound

/-- Continue after `node` with each branch: bind its values to the node's
    results (`bindResults`) and run `cont`. A branch with a constraint false on its
    own is not taken by any run and is dropped (VF7). -/
def contBrs (cont : SSt → List (List Cons)) (s : SSt) (node : Node) (bs : List Br) :
    List (List Cons) :=
  bs.flatMap fun b =>
    if b.cs.any trivFalse then [] else
    if node.results.length == b.vals.length then
      cont { s with pc := s.pc + 1, env := (node.results.zip b.vals).reverse ++ s.env,
                    cs := s.cs ++ b.cs, nv := max s.nv b.nv }
    else FAIL

def jumpS (cont : SSt → List (List Cons)) (fn : Func) (s : SSt) (target : Nat)
    (args : List SV) : List (List Cons) :=
  match findBlock fn.blocks target with
  | none => FAIL
  | some b =>
    match sbindParams s.env b.params args with
    | none => FAIL
    | some env => cont { s with blk := b, pc := 0, env := env }

/-- The static checks a call needs to enter its callee (`execNode`'s `call`
    arm and `start`), on the argument values' types. -/
def callOk (f : Func) (sig : FuncTy) (args : List SV) : Bool :=
  !sig.vararg && svsAre args sig.params && !f.blocks.isEmpty &&
    (match findBlock f.blocks f.entry with
     | none => false
     | some b => (sbindParams [] b.params args).isSome)

/-- An integer cast of `e : t` to `dst` on a path with constraints `cs`,
    symbolically: its branches; `none` outside F1. A widening `zext`/`trunc` or
    a same-width `bitcast` keeps the residue; `sext` forks on the sign; a
    narrowing `zext`/`trunc` keeps the low bits (VF7); a narrowing `sext`, which
    the producer does not emit (a narrowing is a `trunc`), is an opaque scalar. -/
def castCases (op : CastOp) (t : IntTy) (dst : Ty) (e : Aff) (nv : Nat) (cs : List Cons) :
    Option (List Br) :=
  let fresh (t' : IntTy) : List Br := [⟨rangeCs t'.bits (Aff.v nv), [.int t' (Aff.v nv)], nv + 1⟩]
  match op, dst with
  | .zext, .int t' | .trunc, .int t' =>
    if isF1Int t' then some (if t.bits ≤ t'.bits then [⟨[], [.int t' e], nv⟩] else
      [bitsBr t.bits t' (List.take t'.bits) e nv cs]) else none
  | .trunc, .bool => some [⟨[], [.bool false], nv⟩, ⟨[], [.bool true], nv⟩]
  | .bitcast, .int t' =>
    if t.bits == t'.bits && isF1Int t' then some [⟨[], [.int t' e], nv⟩] else none
  | .sext, .int t' =>
    if isF1Int t' then
      some (if t.bits ≤ t'.bits then
        [⟨[le0 (e.addC (-(Hw t.bits - 1)))], [.int t' e], nv⟩,
         ⟨[le0 ((Aff.c (Hw t.bits)).sub e)], [.int t' (e.addC (Mw t'.bits - Mw t.bits))], nv⟩]
      else fresh t')
    else none
  | _, _ => none

/-- Every case constant of a `switch` over `t`, evaluated as the interpreter
    does (`constant_to_value` at the scrutinee's type); `none` when one is not
    an integer of `t`. -/
def caseConsts (m : Module) (t : IntTy) : List (Const × Nat × List Nat) → Option (List (Nat × Nat × List Nat))
  | [] => some []
  | (c, tg, as) :: rest =>
    match constVal m 8 (.int t) c, caseConsts m t rest with
    | .ok (.int _ ci), some cs => some ((ci, tg, as) :: cs)
    | _, _ => none

/-- Some `d` among `cs` has the coefficients `nc` and a bound summing with `b` below `0`. -/
def contraWith (nc : List Int) (b : Int) : List Cons → Bool
  | [] => false
  | d :: ds => (listEqb d.coeffs nc && ChkLIA.isNeg (b + d.bound)) || contraWith nc b ds

/-- `c` contradicts a constraint of the path by itself (or is false alone): some `d` among `cs` has
    the negated coefficients and the two bounds sum below `0`. -/
def contra (cs : List Cons) (c : Cons) : Bool :=
  trivFalse c || contraWith (ChkLIA.scale (-1) c.coeffs) c.bound cs

/-- A comparison's cases without those that contradict the path outright (VF7:
    a value compared twice forks once). -/
def pruneCases (cs : List Cons) (l : List (List Cons × Bool)) : List (List Cons × Bool) :=
  l.filter fun p => !(p.1.any (contra cs))

/-- The operator encodings a calculus uses. The calculus of F1 is `stdCalc`;
    the mutant calculi `VF5Mutants` refutes change one field each. -/
structure Calc where
  bin : BinOp → IntTy → Aff → Aff → Nat → List Cons → Option (List (List Cons) × List Br)
  ovf : OvfOp → IntTy → Aff → Aff → Nat → List Br
  cmp : ICmpOp → Nat → Aff → Aff → List (List Cons × Bool)
  cast : CastOp → IntTy → Ty → Aff → Nat → List Cons → Option (List Br)

def stdCalc : Calc := ⟨binCases, ovfCases, cmpCases, castCases⟩

/-- One node, symbolically: the obligations it emits and those of its
    continuations. `A` is the precondition annotation per function id. -/
def snodeC (C : Calc) (m : Module) (A : Nat → List Cons) (fn : Func) (sig : FuncTy)
    (cont : SSt → List (List Cons)) (s : SSt) (node : Node) : List (List Cons) :=
  let one (v : SV) : List (List Cons) := contBrs cont s node [⟨[], [v], s.nv⟩]
  match node.inst with
  | .binop op ty l r =>
    match slook s.env l, slook s.env r with
    | some (.bool a), some (.bool b) =>
      if svIs (.bool a) ty && svIs (.bool b) ty then
        match boolBin op a b with
        | .ok c => one (.bool c)
        | _ => FAIL
      else FAIL
    | some (.int ta ea), some (.int tb eb) =>
      if svIs (.int ta ea) ty && svIs (.int tb eb) ty && isF1Int ta then
        match C.bin op ta ea eb s.nv s.cs with
        | none => FAIL
        | some (ubs, bs) => ubs.map (fun u => s.cs ++ u) ++ contBrs cont s node bs
      else FAIL
    | _, _ => FAIL
  | .unop op ty x =>
    match slook s.env x with
    | some (.int ta ea) =>
      if svIs (.int ta ea) ty && isF1Int ta then
        match unCases op ta ea with
        | none => FAIL
        | some bs => contBrs cont s node (bs.map fun b => { b with nv := s.nv })
      else FAIL
    | _ => FAIL
  | .overflow op ty l r =>
    match slook s.env l, slook s.env r with
    | some (.int ta ea), some (.int tb eb) =>
      if svIs (.int ta ea) ty && svIs (.int tb eb) ty && isF1Int ta then
        contBrs cont s node (C.ovf op ta ea eb s.nv)
      else FAIL
    | _, _ => FAIL
  | .icmp op ty l r =>
    match slook s.env l, slook s.env r with
    | some (.bool a), some (.bool b) =>
      if svIs (.bool a) ty && svIs (.bool b) ty then one (.bool (icmpR op 1 (b2n a) (b2n b))) else FAIL
    | some (.int ta ea), some (.int tb eb) =>
      if svIs (.int ta ea) ty && svIs (.int tb eb) ty && isF1Int ta then
        contBrs cont s node ((pruneCases s.cs (C.cmp op ta.bits ea eb)).map fun (c, r) => ⟨c, [.bool r], s.nv⟩)
      else FAIL
    | _, _ => FAIL
  | .const ty c =>
    match ty, c with
    | .int t, .int p => if isF1Int t then one (.int t (Aff.c ((p % modulus t.bits : Nat) : Int))) else FAIL
    | .bool, .bool b => one (.bool b)
    | .enum id, c =>
      match constVal m 8 (.enum id) c with
      | .ok (.enum id' ls) => if enumOKb m id' ls then one (.enm id' ls) else FAIL
      | _ => FAIL
    | _, _ => FAIL
  | .copy ty x =>
    match slook s.env x with
    | some v => if svIs v ty then one v else FAIL
    | none => FAIL
  | .select ty c t e =>
    match slook s.env c, slook s.env t, slook s.env e with
    | some (.bool b), some tv, some ev =>
      if svIs tv ty && svIs ev ty then one (if b then tv else ev) else FAIL
    | _, _, _ => FAIL
  | .extractField ty agg field =>
    match slook s.env agg with
    | some (.enm id ls) =>
      match evalExtract m ty (.enum id ls) field with
      | .ok (.int t a) => if isF1Int t && decide (a < modulus t.bits) then one (.int t (Aff.c a)) else FAIL
      | .ok (.bool b) => one (.bool b)
      | _ => FAIL
    | _ => FAIL
  | .cast op src dst x =>
    match slook s.env x with
    | some (.int t e) =>
      if svIs (.int t e) src && isF1Int t then
        match C.cast op t dst e s.nv s.cs with
        | some bs => contBrs cont s node bs
        | none => FAIL
      else FAIL
    | some (.bool b) =>
      if svIs (.bool b) src then
        match evalCast 64 op src dst (.bool b) with
        | .ok (.int t a) => if isF1Int t && decide (a < modulus t.bits) then one (.int t (Aff.c a)) else FAIL
        | .ok (.bool b') => one (.bool b')
        | _ => FAIL
      else FAIL
    | _ => FAIL
  | .switch x dflt dArgs cases =>
    let go (r : R (Option (Nat × List Nat))) : List (List Cons) :=
      match r with
      | .ok (some (tg, as)) =>
        match slooks s.env as with
        | some vs => jumpS cont fn s tg vs
        | none => FAIL
      | .ok none =>
        match slooks s.env dArgs with
        | some vs => jumpS cont fn s dflt vs
        | none => FAIL
      | .stop _ => FAIL
    match slook s.env x with
    | some (.int t e) =>
      if e.isConst then
        if decide (0 ≤ e.k) then go (switchTarget m (.int t e.k.toNat) cases) else FAIL
      else
        match caseConsts m t cases, slooks s.env dArgs with
        | some cs, some dvs =>
          cs.flatMap (fun (ci, tg, as) =>
            match slooks s.env as with
            | some vs => jumpS cont fn { s with cs := s.cs ++ [leA e (Aff.c ci), leA (Aff.c ci) e] } tg vs
            | none => FAIL) ++
          jumpS cont fn s dflt dvs
        | _, _ => FAIL
    | some (.bool b) => go (switchTarget m (.bool b) cases)
    | _ => FAIL
  | .assert c _ =>
    match slook s.env c with
    | some (.bool true) => cont { s with pc := s.pc + 1 }
    | some (.bool false) => [s.cs]
    | _ => FAIL
  | .unreachable => [s.cs]
  | .br target args =>
    match slooks s.env args with
    | some vs => jumpS cont fn s target vs
    | none => FAIL
  | .condBr c tT tA eT eA =>
    match slook s.env c with
    | some (.bool true) =>
      match slooks s.env tA with
      | some vs => jumpS cont fn s tT vs
      | none => FAIL
    | some (.bool false) =>
      match slooks s.env eA with
      | some vs => jumpS cont fn s eT vs
      | none => FAIL
    | _ => FAIL
  | .ret xs =>
    match slooks s.env xs with
    | some vs => if svsAre vs sig.returns then [] else FAIL
    | none => FAIL
  | .call callee args =>
    match slooks s.env args, fnOf m callee with
    | some vs, some (f, csig) =>
      if callOk f csig vs && node.results.length == csig.returns.length then
        match freshVals m csig.returns s.nv with
        | none => FAIL
        | some rs =>
          (A callee).map (fun c => s.cs ++ [negSubst c (vs.map SV.aff)]) ++
          contBrs cont s node (rs.map fun (c, vs', n) => ⟨c, vs', n⟩)
      else FAIL
    | _, _ => FAIL
  | _ => FAIL

/-- The symbolic executor: every path from `s`, with a budget of `n` nodes per
    path (a cycle exhausts it). -/
def sxC (C : Calc) (m : Module) (A : Nat → List Cons) (fn : Func) (sig : FuncTy) :
    Nat → SSt → List (List Cons)
  | 0, _ => FAIL
  | n + 1, s =>
    match nth? s.blk.body s.pc with
    | none => FAIL
    | some node => snodeC C m A fn sig (sxC C m A fn sig n) s node

def snode (m : Module) (A : Nat → List Cons) (fn : Func) (sig : FuncTy)
    (cont : SSt → List (List Cons)) (s : SSt) (node : Node) : List (List Cons) :=
  snodeC stdCalc m A fn sig cont s node

def sx (m : Module) (A : Nat → List Cons) (fn : Func) (sig : FuncTy) : Nat → SSt → List (List Cons) :=
  sxC stdCalc m A fn sig

/-- The entry states of a function: parameter `i` is variable `i` (an integer
    with its range, a `Bool` forked both ways), under the precondition. -/
def entryVals (m : Module) : List Ty → Nat → Option (List (List Cons × List SV))
  | [], _ => some [([], [])]
  | .int t :: ts, i =>
    if isF1Int t then
      match entryVals m ts (i + 1) with
      | none => none
      | some rs => some (rs.map fun (c, vs) => (rangeCs t.bits (Aff.v i) ++ c, .int t (Aff.v i) :: vs))
    else none
  | .bool :: ts, i =>
    match entryVals m ts (i + 1) with
    | none => none
    | some rs => some (rs.flatMap fun (c, vs) =>
        [(le0 (Aff.v i) :: c, .bool false :: vs),
         (le0 ((Aff.c 1).sub (Aff.v i)) :: le0 ((Aff.v i).addC (-1)) :: c, .bool true :: vs)])
  | .enum id :: ts, i =>
    match enumVals m id, entryVals m ts (i + 1) with
    | some es, some rs => some (rs.flatMap fun (c, vs) => es.map fun e => (c, e :: vs))
    | _, _ => none
  | _ :: _, _ => none

/-- The default step budget per path. -/
def budget (f : Func) : Nat := (f.blocks.map fun b => b.body.length).foldl (· + ·) 0 + 1

/-- The verification condition of a calculus `C` for function `fid` under the precondition
    annotation `A`: the obligations, each to be refuted. Its 64-bit integer
    calculus refuses other target widths and non-executable scalar layouts. -/
def vcC (C : Calc) (m : Module) (A : Nat → List Cons) (fid : Nat) : List (List Cons) :=
  if m.pointerBits != 64 then FAIL else
  if !m.executableTarget then FAIL else
  match fnOf m fid with
  | none => FAIL
  | some (f, sig) =>
    if sig.vararg || f.blocks.isEmpty then FAIL else
    match findBlock f.blocks f.entry with
    | none => FAIL
    | some b =>
      if !((A fid).all fun c => decide (c.coeffs.length ≤ sig.params.length)) then FAIL else
      match entryVals m sig.params 0 with
      | none => FAIL
      | some es =>
        es.flatMap fun (c, vs) =>
          match sbindParams [] b.params vs with
          | none => FAIL
          | some env =>
            sxC C m A f sig (budget f)
              { blk := b, pc := 0, env := env, cs := c ++ A fid, nv := sig.params.length }

/-- **The verification condition** of F1. -/
def vc (m : Module) (A : Nat → List Cons) (fid : Nat) : List (List Cons) := vcC stdCalc m A fid

/-- Pairs every obligation with a certificate and runs VF4's checker; the
    lengths must agree. -/
def checkVCC (C : Calc) (m : Module) (A : Nat → List Cons) (fid : Nat)
    (certs : List (List ChkLIA.Step)) : Bool :=
  let ob := vcC C m A fid
  ob.length == certs.length && ChkLIA.chk_LIA_cases (ob.zip certs)

def checkVC (m : Module) (A : Nat → List Cons) (fid : Nat) (certs : List (List ChkLIA.Step)) : Bool :=
  checkVCC stdCalc m A fid certs

end VF5
