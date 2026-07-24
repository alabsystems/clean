/-
Carrier-parity P0 differential-reducer ground truth
(designs/2026-07-03-carrier-types-bitvec-parity.md §5 P0.6, gate A6).

Emits `op_table.tsv`: one deterministic row per sampled operation,
`category<TAB>op<TAB>lhs<TAB>rhs<TAB>expected`, where

  - uint8/16/32/64 operands and Nat results are decimal;
  - bool results are `true`/`false`; Decidable results `isTrue`/`isFalse`;
  - char operands are decimal code points;
  - string operands/results are lowercase-hex UTF-8 bytes (`-` = empty).

Values are evaluated by Lean itself (#eval semantics == kernel semantics for
these total ops on concrete literals — design §1.3/§1.4). USize is
deliberately ABSENT: genuine v4.30 USize is width-abstract and its
width-dependent ops do not reduce (design §1.5); Clean's P0 pin lives in
`crates/clean-kernel/tests/carrier_differential.rs` and must be flipped to
expect stuckness in Phase 1.

Regenerate (byte-stable for a given toolchain):

  ~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean --run \
    tests/fixtures/carrier_v4_30/gen_op_table.lean > \
    tests/fixtures/carrier_v4_30/op_table.tsv
-/

def hexByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  let hi := digits[(b.toNat / 16) % 16]!
  let lo := digits[b.toNat % 16]!
  String.ofList [hi, lo]

def encStr (s : String) : String :=
  if s.isEmpty then "-"
  else String.join (s.toUTF8.toList.map hexByte)

def row (cat op lhs rhs expected : String) : String :=
  s!"{cat}\t{op}\t{lhs}\t{rhs}\t{expected}"

def boolS (b : Bool) : String := if b then "true" else "false"
def decS (b : Bool) : String := if b then "isTrue" else "isFalse"

def u8Vals : List Nat := [0, 1, 2, 3, 5, 254, 255]
def u16Vals : List Nat := [0, 1, 2, 3, 5, 65534, 65535]
def u32Vals : List Nat := [0, 1, 2, 3, 5, 4294967294, 4294967295]
def u64Vals : List Nat := [0, 1, 2, 3, 5, 18446744073709551614, 18446744073709551615]

def emitU8 (a b : Nat) : List String :=
  let x := UInt8.ofNat a
  let y := UInt8.ofNat b
  let c := "uint8"
  let la := toString a
  let lb := toString b
  [ row c "add" la lb (toString (x + y).toNat)
  , row c "sub" la lb (toString (x - y).toNat)
  , row c "mul" la lb (toString (x * y).toNat)
  , row c "div" la lb (toString (x / y).toNat)
  , row c "mod" la lb (toString (x % y).toNat)
  , row c "land" la lb (toString (x &&& y).toNat)
  , row c "lor" la lb (toString (x ||| y).toNat)
  , row c "xor" la lb (toString (x ^^^ y).toNat)
  , row c "shiftLeft" la lb (toString (x <<< y).toNat)
  , row c "shiftRight" la lb (toString (x >>> y).toNat)
  , row c "beq" la lb (boolS (x == y))
  , row c "blt" la lb (boolS (x < y))
  , row c "ble" la lb (boolS (x ≤ y))
  , row c "decEq" la lb (decS (x == y))
  , row c "decLt" la lb (decS (x < y))
  , row c "decLe" la lb (decS (x ≤ y))
  , row c "complement" la "-" (toString (~~~x).toNat)
  , row c "toNat" la "-" (toString x.toNat)
  ]

def emitU16 (a b : Nat) : List String :=
  let x := UInt16.ofNat a
  let y := UInt16.ofNat b
  let c := "uint16"
  let la := toString a
  let lb := toString b
  [ row c "add" la lb (toString (x + y).toNat)
  , row c "sub" la lb (toString (x - y).toNat)
  , row c "mul" la lb (toString (x * y).toNat)
  , row c "div" la lb (toString (x / y).toNat)
  , row c "mod" la lb (toString (x % y).toNat)
  , row c "land" la lb (toString (x &&& y).toNat)
  , row c "lor" la lb (toString (x ||| y).toNat)
  , row c "xor" la lb (toString (x ^^^ y).toNat)
  , row c "shiftLeft" la lb (toString (x <<< y).toNat)
  , row c "shiftRight" la lb (toString (x >>> y).toNat)
  , row c "beq" la lb (boolS (x == y))
  , row c "blt" la lb (boolS (x < y))
  , row c "ble" la lb (boolS (x ≤ y))
  , row c "decEq" la lb (decS (x == y))
  , row c "decLt" la lb (decS (x < y))
  , row c "decLe" la lb (decS (x ≤ y))
  , row c "complement" la "-" (toString (~~~x).toNat)
  , row c "toNat" la "-" (toString x.toNat)
  ]

def emitU32 (a b : Nat) : List String :=
  let x := UInt32.ofNat a
  let y := UInt32.ofNat b
  let c := "uint32"
  let la := toString a
  let lb := toString b
  [ row c "add" la lb (toString (x + y).toNat)
  , row c "sub" la lb (toString (x - y).toNat)
  , row c "mul" la lb (toString (x * y).toNat)
  , row c "div" la lb (toString (x / y).toNat)
  , row c "mod" la lb (toString (x % y).toNat)
  , row c "land" la lb (toString (x &&& y).toNat)
  , row c "lor" la lb (toString (x ||| y).toNat)
  , row c "xor" la lb (toString (x ^^^ y).toNat)
  , row c "shiftLeft" la lb (toString (x <<< y).toNat)
  , row c "shiftRight" la lb (toString (x >>> y).toNat)
  , row c "beq" la lb (boolS (x == y))
  , row c "blt" la lb (boolS (x < y))
  , row c "ble" la lb (boolS (x ≤ y))
  , row c "decEq" la lb (decS (x == y))
  , row c "decLt" la lb (decS (x < y))
  , row c "decLe" la lb (decS (x ≤ y))
  , row c "complement" la "-" (toString (~~~x).toNat)
  , row c "toNat" la "-" (toString x.toNat)
  ]

def emitU64 (a b : Nat) : List String :=
  let x := UInt64.ofNat a
  let y := UInt64.ofNat b
  let c := "uint64"
  let la := toString a
  let lb := toString b
  [ row c "add" la lb (toString (x + y).toNat)
  , row c "sub" la lb (toString (x - y).toNat)
  , row c "mul" la lb (toString (x * y).toNat)
  , row c "div" la lb (toString (x / y).toNat)
  , row c "mod" la lb (toString (x % y).toNat)
  , row c "land" la lb (toString (x &&& y).toNat)
  , row c "lor" la lb (toString (x ||| y).toNat)
  , row c "xor" la lb (toString (x ^^^ y).toNat)
  , row c "shiftLeft" la lb (toString (x <<< y).toNat)
  , row c "shiftRight" la lb (toString (x >>> y).toNat)
  , row c "beq" la lb (boolS (x == y))
  , row c "blt" la lb (boolS (x < y))
  , row c "ble" la lb (boolS (x ≤ y))
  , row c "decEq" la lb (decS (x == y))
  , row c "decLt" la lb (decS (x < y))
  , row c "decLe" la lb (decS (x ≤ y))
  , row c "complement" la "-" (toString (~~~x).toNat)
  , row c "toNat" la "-" (toString x.toNat)
  ]

/-- Valid code points only (Char.ofNat maps invalid to 0 — covered too). -/
def charVals : List Nat :=
  [0, 65, 97, 955, 55295, 55296, 57344, 65535, 65536, 128640, 1114111, 1114112]

def emitChar (cp : Nat) : List String :=
  let ch := Char.ofNat cp
  [ row "char" "ofNatToNat" (toString cp) "-" (toString ch.toNat)
  , row "char" "utf8Size" (toString cp) "-" (toString ch.utf8Size)
  ]

def stringPairs : List (String × String) :=
  [ ("", ""), ("", "a"), ("a", ""), ("a", "a"), ("a", "b")
  , ("ab", "ab"), ("ab", "ba"), ("ab", "cd"), ("abc", "abcd")
  , ("aé", "x"), ("αβγ", "δ"), ("🚀", "x"), ("a🚀", "b") ]

def emitString (s t : String) : List String :=
  let c := "string"
  let ls := encStr s
  let lt := encStr t
  [ row c "append" ls lt (encStr (s ++ t))
  , row c "length" ls "-" (toString s.length)
  , row c "utf8ByteSize" ls "-" (toString s.utf8ByteSize)
  , row c "beq" ls lt (boolS (s == t))
  , row c "decEq" ls lt (decS (s == t))
  , row c "isEmpty" ls "-" (boolS s.isEmpty)
  ]

def stringPushCases : List (String × Nat) :=
  [("", 97), ("a", 98), ("aé", 955), ("x", 128640)]

def emitPush (s : String) (cp : Nat) : List String :=
  [ row "string" "push" (encStr s) (toString cp)
      (encStr (s.push (Char.ofNat cp))) ]

/-- BitVec arith/logic/comparison ground truth, one category per width
    (`bitvec8`/`bitvec16`/`bitvec32`/`bitvec64`). `lhs`/`rhs` are decimal payloads
    (< 2^w). Consumed by `carrier_differential_tests.rs`'s bitvec reducer lane,
    which reads the width from the category and calls `BitVec.<op>` with
    `[width, a, b]`. Shifts are emitted separately (`emitBVShift`) with bounded
    Lean-computable shift amounts. -/
def emitBVBin (w : Nat) (a b : Nat) : List String :=
  let x : BitVec w := BitVec.ofNat w a
  let y : BitVec w := BitVec.ofNat w b
  let c := s!"bitvec{w}"
  let la := toString a
  let lb := toString b
  [ row c "add" la lb (toString (BitVec.add x y).toNat)
  , row c "sub" la lb (toString (BitVec.sub x y).toNat)
  , row c "mul" la lb (toString (BitVec.mul x y).toNat)
  , row c "udiv" la lb (toString (BitVec.udiv x y).toNat)
  , row c "umod" la lb (toString (BitVec.umod x y).toNat)
  , row c "and" la lb (toString (BitVec.and x y).toNat)
  , row c "or" la lb (toString (BitVec.or x y).toNat)
  , row c "xor" la lb (toString (BitVec.xor x y).toNat)
  , row c "ult" la lb (boolS (BitVec.ult x y))
  , row c "ule" la lb (boolS (BitVec.ule x y))
  , row c "slt" la lb (boolS (BitVec.slt x y))
  , row c "sle" la lb (boolS (BitVec.sle x y))
  ]

/-- Unary BitVec ops (`not`/`neg`), one row per value (`rhs` = `-`). -/
def emitBVUn (w : Nat) (a : Nat) : List String :=
  let x : BitVec w := BitVec.ofNat w a
  let c := s!"bitvec{w}"
  let la := toString a
  [ row c "not" la "-" (toString (BitVec.not x).toNat)
  , row c "neg" la "-" (toString (BitVec.neg x).toNat)
  ]

/-- Shift amounts (RAW Nat, NOT mod-width at the BitVec layer). Bounded so
    `#eval` can actually compute `x <<< s` (Lean builds `2^s` before truncating,
    so astronomically large `s` panics — the native reducer still returns the
    correct `0`, but we can only pin values Lean can evaluate). Covers boundary
    (`w-1`, `w`, `w+1`) and moderate over-width shifts. -/
def bvShifts : List Nat := [0, 1, 2, 3, 5, 7, 15, 31, 63, 64, 65, 100]

def emitBVShift (w : Nat) (a s : Nat) : List String :=
  let x : BitVec w := BitVec.ofNat w a
  let c := s!"bitvec{w}"
  let la := toString a
  let ls := toString s
  [ row c "shiftLeft" la ls (toString (BitVec.shiftLeft x s).toNat)
  , row c "ushiftRight" la ls (toString (BitVec.ushiftRight x s).toNat)
  ]

def main : IO Unit := do
  IO.println "# carrier differential op table — generated by gen_op_table.lean (v4.30.0-rc2); do not hand-edit"
  IO.println "# category\top\tlhs\trhs\texpected"
  for a in u8Vals do
    for b in u8Vals do
      for r in emitU8 a b do IO.println r
  for a in u16Vals do
    for b in u16Vals do
      for r in emitU16 a b do IO.println r
  for a in u32Vals do
    for b in u32Vals do
      for r in emitU32 a b do IO.println r
  for a in u64Vals do
    for b in u64Vals do
      for r in emitU64 a b do IO.println r
  for cp in charVals do
    for r in emitChar cp do IO.println r
  for (s, t) in stringPairs do
    for r in emitString s t do IO.println r
  for (s, cp) in stringPushCases do
    for r in emitPush s cp do IO.println r
  -- BitVec arith/logic/comparison + shift rows (widths 8/16/32/64). The
  -- per-width value lists (near-max entries) exercise wraparound, sign bits,
  -- and div/mod; shift amounts come from the bounded `bvShifts` list. Appended
  -- last so the uint/char/string prefix stays byte-stable.
  for a in u8Vals do
    for b in u8Vals do
      for r in emitBVBin 8 a b do IO.println r
    for r in emitBVUn 8 a do IO.println r
    for s in bvShifts do
      for r in emitBVShift 8 a s do IO.println r
  for a in u16Vals do
    for b in u16Vals do
      for r in emitBVBin 16 a b do IO.println r
    for r in emitBVUn 16 a do IO.println r
    for s in bvShifts do
      for r in emitBVShift 16 a s do IO.println r
  for a in u32Vals do
    for b in u32Vals do
      for r in emitBVBin 32 a b do IO.println r
    for r in emitBVUn 32 a do IO.println r
    for s in bvShifts do
      for r in emitBVShift 32 a s do IO.println r
  for a in u64Vals do
    for b in u64Vals do
      for r in emitBVBin 64 a b do IO.println r
    for r in emitBVUn 64 a do IO.println r
    for s in bvShifts do
      for r in emitBVShift 64 a s do IO.println r
