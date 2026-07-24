/-
  THREAD T3 — Pillar B kill-gate measurement.

  QUESTION (binary go/no-go): does the Lean *kernel* reduce a real
  byte-decode computation by `decide` / `rfl` *without* `native_decide`?
  If yes (axioms stay [propext, Classical.choice, Quot.sound]) an in-kernel
  reflective ONNX decoder is feasible; if it needs `native_decide`
  (pulling in `Lean.ofReduceBool`) it is a NO-GO for kernel-checked decode.

  We exercise the SAME kernel-reduction machinery a real decoder would:

   (a) REAL bytes embedded from
       benchmarks/vnncomp2024/benchmarks/test/test_tiny.onnx (232 bytes).
       Verified offsets (od -An -tu1): the model carries protobuf-encoded
       TensorProto initializers whose `raw_data` (field 9, wire tag 0x4a = 74)
       holds 4-byte IEEE-754 little-endian floats, e.g. the W0 weight
       record `74 4 0 0 128 63`  (tag 74, len 4, bytes 0,0,128,63 = 1.0f)
       and the B0 bias `74 4 0 0 0 0` (bytes 0,0,0,0 = 0.0f).

   (b) f32leToDyadic : decode 4 LE bytes (IEEE-754 binary32) to an EXACT
       dyadic `(num : ℤ, e : ℤ)` meaning `num * 2^e`, via pure Nat/Int bit
       ops (mantissa/exponent split) — NO `Rat` division/gcd on the hot path.
       varintDecode : a minimal protobuf LEB128 varint reader over List UInt8.

   (c) `example ... := by decide` (and `by rfl`) on concrete inputs, each with
       a named theorem and `#print axioms` so the build log IS the measurement.

  ───────────────────────────────────────────────────────────────────────────
  MEASURED VERDICT (see build log + #print axioms below):

   * GO for pure Nat/Int byte decode.  The varint reader and the
     *structured-dyadic* float decoder (`Int × Int`, value = num·2^e) BOTH
     reduce by `decide` AND `rfl` in-kernel, axioms stay
     [propext, Classical.choice, Quot.sound].  No `native_decide`, no
     `Lean.ofReduceBool`.

   * NO-GO for a `Rat`-VALUED decoder via `decide`.  Returning the value as a
     reduced `Rat` (`dyadicToRat`, which performs `Rat` mul/division and hence
     gcd normalization) makes `decide` get STUCK in the kernel — the
     `instDecidableEqRat` instance does not reduce on the computed `.num`.
     (We document this as `dyadic_to_rat_*` lemmas proved WITHOUT `decide`,
     via the kernel-reduced dyadic plus `norm_num`, instead of by `decide`.)

  ENGINEERING UPSHOT: an in-kernel reflective ONNX decoder is feasible iff it
  decodes to a *structured dyadic* (num, exp) with Nat/Int bit ops and keeps
  `Rat` normalization OFF the decide path — exactly how the existing
  Int-pair `CertCheckerZ` decide pattern already operates.
  ───────────────────────────────────────────────────────────────────────────

  No `native_decide`, no `Lean.ofReduceBool`, no `sorry`.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Crownproof
namespace ReflectDecodeSpike

/-! ## (a) Real bytes from test_tiny.onnx -/

/-- First 16 bytes of the file (od -An -tu1, offset 0). -/
def onnxHead16 : List UInt8 :=
  [8, 7, 58, 223, 1, 10, 21, 10, 2, 87, 48, 10, 3, 88, 95, 48]

/-- The W0 initializer raw_data record as it literally appears in the file:
    protobuf tag `74` (field 9 = raw_data, wire type 2), length `4`,
    then the 4 IEEE-754 little-endian bytes `0 0 128 63` = 1.0f. -/
def w0RawDataRecord : List UInt8 := [74, 4, 0, 0, 128, 63]

/-- The B0 initializer raw_data record: tag 74, len 4, bytes `0 0 0 0` = 0.0f. -/
def b0RawDataRecord : List UInt8 := [74, 4, 0, 0, 0, 0]

/-! ## (b1) IEEE-754 binary32 little-endian → EXACT structured dyadic

    We reconstruct the unsigned 32-bit word from 4 little-endian bytes with
    pure `Nat` shifts/ors, split off sign / 8-bit exponent / 23-bit mantissa,
    and return `(num, e) : ℤ × ℤ` with the EXACT real value `num * 2^e`.
    This is all Nat/Int — no `Rat`, no gcd — so it reduces in the kernel. -/

/-- Assemble a little-endian u32 (as a `Nat`) from 4 bytes. -/
def u32le (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24)

/-- Decode 4 little-endian IEEE-754 binary32 bytes to an EXACT structured
    dyadic `(num, e)` with value `num * 2^e`:

      normal   (exp≠0):  num = ±(2^23 + mantissa),  e = exp - 127 - 23
      subnormal(exp=0):  num = ± mantissa,          e =   1 - 127 - 23

    (Inf/NaN, exp=255, are not modeled — they never occur as finite weights;
    for them this returns the same formula, harmless for the measurement.) -/
def f32leToDyadic (b0 b1 b2 b3 : UInt8) : Int × Int :=
  let u    := u32le b0 b1 b2 b3
  let sign := u >>> 31
  let exp  := (u >>> 23) &&& 0xff
  let mant := u &&& 0x7fffff
  let magNum : Nat := if exp = 0 then mant else (1 <<< 23) ||| mant
  let e : Int := if exp = 0 then (1 - 127 - 23 : Int)
                            else ((exp : Int) - 127 - 23)
  let num : Int := if sign = 1 then -(magNum : Int) else (magNum : Int)
  (num, e)

/-- The math meaning of a structured dyadic as a `Rat` (value = num · 2^e).
    NOTE: this performs `Rat` division for negative `e`, so equalities about it
    do NOT `decide` in-kernel — they are proved via the reduced dyadic +
    `norm_num` below.  This is the documented NO-GO path. -/
def dyadicToRat : Int × Int → Rat
  | (num, Int.ofNat n)   => (num : Rat) * (2 ^ n : Rat)
  | (num, Int.negSucc n) => (num : Rat) / (2 ^ (n + 1) : Rat)

/-! ## (b2) protobuf LEB128 varint reader over `List UInt8` -/

/-- Read one LEB128 varint from the front of a byte list. `fuel` bounds the
    loop (a varint is at most 10 bytes). Returns value and remaining bytes. -/
def varintGo : Nat → Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0,        _,   _,     _        => none
  | _,        acc, _,     []       => some (acc, [])
  | (fuel+1), acc, shift, b :: bs  =>
      let lo : Nat := b.toNat &&& 0x7f
      let acc' := acc ||| (lo <<< shift)
      if b.toNat &&& 0x80 = 0 then
        some (acc', bs)                       -- high bit clear → last byte
      else
        varintGo fuel acc' (shift + 7) bs     -- continue

/-- Decode a varint from the front of the list (≤10 bytes), or `none`. -/
def varintDecode (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs with
  | []     => none
  | _ :: _ => varintGo 10 0 0 bs

/-! ## (c) KERNEL-REDUCTION MEASUREMENT (GO path: Nat/Int, `decide`/`rfl`)

    Each theorem is closed by `decide` or `rfl` with NO `native_decide`, then
    `#print axioms` prints the actual measurement.  GO iff the axiom set stays
    [propext, Classical.choice, Quot.sound]; any `Lean.ofReduceBool` = NO-GO. -/

-- u32 assembly of the real 1.0f bytes: 0 0 128 63 → 0x3f800000 = 1065353216
theorem u32le_w0 : u32le 0 0 128 63 = 1065353216 := by decide
#print axioms u32le_w0

-- W0 float decode: real bytes 0,0,128,63 → dyadic (8388608, -23) = 1.0
theorem f32_w0 : f32leToDyadic 0 0 128 63 = (8388608, -23) := by decide
#print axioms f32_w0

-- B0 float decode: real bytes 0,0,0,0 → dyadic (0, -149) = 0.0
theorem f32_b0 : f32leToDyadic 0 0 0 0 = (0, -149) := by decide
#print axioms f32_b0

-- 0.5f bytes 0 0 0 63 (0x3f000000) → dyadic (8388608, -24) = 1/2
theorem f32_half : f32leToDyadic 0 0 0 63 = (8388608, -24) := by decide
#print axioms f32_half

-- -2.5f = 0xC0200000, LE bytes 0 0 32 192 → dyadic (-10485760, -22) = -5/2
theorem f32_neg : f32leToDyadic 0 0 32 192 = (-10485760, -22) := by decide
#print axioms f32_neg

-- And by definitional `rfl` (not just `decide`) on a real decode.
-- (The 2^23 shift needs a deeper unfold budget than the default for `rfl`.)
set_option maxRecDepth 4000 in
theorem f32_w0_rfl : f32leToDyadic 0 0 128 63 = (8388608, -23) := by rfl
#print axioms f32_w0_rfl

-- varint: single byte 4 (the `len` field of a raw_data record) → 4
theorem vint_len : varintDecode [4] = some (4, []) := by decide
#print axioms vint_len

-- varint: the W0 raw_data record: leading tag `74` is a 1-byte varint
theorem vint_w0tag :
    varintDecode w0RawDataRecord = some (74, [4, 0, 0, 128, 63]) := by decide
#print axioms vint_w0tag

-- multi-byte varint: bytes 223,1 (at file offset 3) →  (223&0x7f) | (1<<7) = 223
theorem vint_multi : varintDecode [223, 1] = some (223, []) := by decide
#print axioms vint_multi

-- and by `rfl` on the multi-byte varint:
theorem vint_multi_rfl : varintDecode [223, 1] = some (223, []) := by rfl
#print axioms vint_multi_rfl

/-! ## End-to-end GO slice: protobuf record → bytes → exact dyadic, all by `decide` -/

/-- The W0 raw_data protobuf record decodes its tag, and the embedded 4 bytes
    decode to the exact dyadic weight (8388608, -23) = 1.0.  A tiny end-to-end
    reflective-decoder slice, fully reduced by the kernel. -/
theorem w0_record_end_to_end :
    (varintDecode w0RawDataRecord = some (74, [4, 0, 0, 128, 63]))
    ∧ f32leToDyadic 0 0 128 63 = (8388608, -23) := by decide
#print axioms w0_record_end_to_end

/-! ## (d) The documented NO-GO path: `Rat`-VALUED decode does NOT `decide`.

    These equalities are TRUE and we PROVE them — but NOT by `decide`
    (which gets stuck in the `Rat` `DecidableEq` instance on the computed
    `.num`).  We prove them via the kernel-reduced dyadic + `norm_num`.
    The fact that we *cannot* use `decide` here is itself the NO-GO evidence
    for Rat-valued kernel decode. -/

/-- `dyadicToRat (num, -(n+1)) = num / 2^(n+1)` by definitional `rfl`,
    giving us a handle to rewrite the `match` away without `decide`. -/
theorem dyadicToRat_negSucc (num : Int) (n : Nat) :
    dyadicToRat (num, Int.negSucc n) = (num : Rat) / (2 ^ (n + 1) : Rat) := rfl

theorem w0_value_is_one : dyadicToRat (f32leToDyadic 0 0 128 63) = 1 := by
  -- f32leToDyadic ... reduces (Nat/Int) to (8388608, -23 = negSucc 22);
  -- dyadicToRat is then 8388608 / 2^23, which norm_num evaluates to 1.
  -- (decide would hang in the Rat DecidableEq instance — the NO-GO.)
  rw [f32_w0]
  show dyadicToRat (8388608, Int.negSucc 22) = 1
  rw [dyadicToRat_negSucc]; norm_num

theorem b0_value_is_zero : dyadicToRat (f32leToDyadic 0 0 0 0) = 0 := by
  rw [f32_b0]
  show dyadicToRat (0, Int.negSucc 148) = 0
  rw [dyadicToRat_negSucc]; norm_num

theorem half_value : dyadicToRat (f32leToDyadic 0 0 0 63) = 1 / 2 := by
  rw [f32_half]
  show dyadicToRat (8388608, Int.negSucc 23) = 1 / 2
  rw [dyadicToRat_negSucc]; norm_num

theorem neg_value : dyadicToRat (f32leToDyadic 0 0 32 192) = -5 / 2 := by
  rw [f32_neg]
  show dyadicToRat (-10485760, Int.negSucc 21) = -5 / 2
  rw [dyadicToRat_negSucc]; norm_num

#print axioms w0_value_is_one
#print axioms b0_value_is_zero
#print axioms half_value
#print axioms neg_value

end ReflectDecodeSpike
end Crownproof
