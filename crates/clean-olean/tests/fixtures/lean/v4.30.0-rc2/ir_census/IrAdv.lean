/-!
IR census fixture: shapes the Mathlib-closure differential never meets, each
compared with the pinned toolchain's own oracle (`lean_ir/adversarial_tests.rs`).
A NON-`module` file, so its IR stays in its `.olean`.
-/

-- `ExternEntry.adhoc` (a bare `@[extern]`), `inline`, and two entries at once.
@[extern] opaque adhocFn : Nat → Nat

@[extern c inline "#1 + #2"] opaque inlineFn : UInt32 → UInt32 → UInt32

@[extern c inline "lean_box(#1)" cpp "cppSym"] opaque twoEntries : USize → Nat

-- Names `Name.toString` must escape; the second carries a newline, which
-- Lean's formatter breaks at the current nesting.
def «weird name» (n : Nat) : Nat := n + 7

def «line
break» (n : Nat) : Nat := n + 8

def callsWeird (b : Bool) (n : Nat) : Nat := if b then «line
break» n + 1 else «weird name» n

-- A string literal with NUL, CR, a control character, DEL, a non-BMP
-- character and the escape delimiters.
def ctrlStr : String := "a\x00b\rc\x1f\x7fd𝔽»«"

-- The tagged-scalar / MPZ boundary: 2^63 is the smallest one-limb MPZ,
-- 2^63 - 1 the largest tagged `Nat`, 2^64 the smallest two-limb MPZ.
def n63 : Nat := 9223372036854775808
def n63m1 : Nat := 9223372036854775807
def n64 : Nat := 18446744073709551616

def f32 (x : Float32) : Float32 := x + x * 2

def u16 (x : UInt16) (y : UInt8) : UInt16 := x + y.toUInt16

-- `DeclInfo.sorryDep?` in a non-`module` file, at both levels.
def usesSorry : Nat := sorry
def callsSorry (n : Nat) : Nat := usesSorry + n
