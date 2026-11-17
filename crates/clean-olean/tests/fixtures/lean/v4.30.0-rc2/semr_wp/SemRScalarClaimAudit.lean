/- Scalar claim interpretation and hostile binding/encoding controls.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRBooleanClaimText
import SemRScalarClaim
import SemRUnsignedSelect

set_option maxRecDepth 8192

namespace SemRScalarClaimAudit
open SemRBooleanClaim

def ascii (s : String) : Bytes := s.toList.map Char.toNat
def c : Name := [99]
def x : Name := [120]
def y : Name := [121]
def r : Name := [114]
def varJson (name : Name) : Json := .object [(ascii "var", .string name)]
def binary (op : String) (left right : Json) : Json :=
  .object [(ascii "op", .string (ascii op)), (ascii "lhs", left), (ascii "rhs", right)]
def declaration (name : Name) (sort : String) : Json :=
  .object [(ascii "name", .string name), (ascii "sort", .string (ascii sort))]
def guardedBody : Json := binary "and"
  (binary "implies" (varJson c) (binary "eq" (varJson r) (varJson x)))
  (binary "implies" (.object [(ascii "op", .string (ascii "not")),
    (ascii "expr", varJson c)]) (binary "eq" (varJson r) (varJson y)))
def guarded (xSort : String := "int") : Json := .object [
  (ascii "schema", .string (ascii "trust-wp.trust-formula.v1")),
  (ascii "variables", .array [declaration c "bool", declaration x xSort,
    declaration y "int", declaration r "int"]),
  (ascii "body", guardedBody)]
def guardedBytes : Bytes := (encodeJson 4096 (guarded "int")).getD []
def guardedExpression : Expr := .binary .and
  (.binary .implies (.var c) (.intCompare .eq (.var r) (.var x)))
  (.binary .implies (.not (.var c)) (.intCompare .eq (.var r) (.var y)))

theorem original_claim_decoded :
    decodeClaim 4096 (guarded "int") = some guardedExpression := rfl

theorem guarded_interpretation (condition : Bool) (left right result : Int) :
    checkedTypedJson 4096 guardedBytes (guarded "int")
      ([(c, condition)], [(x, left), (y, right), (r, result)]) =
      some ((!condition || result == left) && (condition || result == right)) := by
  cases condition <;> rfl

/-- Arbitrary mathematical integer inputs, without finite enumeration. -/
theorem selected_value_satisfies_original (condition : Bool) (left right : Int) :
    checkedTypedJson 4096 guardedBytes (guarded "int")
      ([(c, condition)], [(x, left), (y, right),
        (r, if condition then left else right)]) = some true := by
  rw [guarded_interpretation]
  cases condition <;> simp

theorem full_unsigned_value_is_exact :
    checkedTypedJson 4096 guardedBytes (guarded "int")
      ([(c, false)], [(x, 0), (y, 18446744073709551615),
        (r, 18446744073709551615)]) = some true := rfl

theorem changed_result_is_false :
    checkedTypedJson 4096 guardedBytes (guarded "int")
      ([(c, false)], [(x, 0), (y, 18446744073709551615), (r, 0)]) = some false := rfl

theorem changed_bytes_refused (env : TypedEnv) :
    checkedTypedJson 4096 (guardedBytes ++ [32]) (guarded "int") env = none := rfl

theorem mixed_sort_refused : decodeClaim 4096 (guarded "bool") = none := rfl

theorem unbound_integer_refused :
    evalTyped [(c, false)] [(x, 0), (r, 0)] guardedExpression = none := rfl

theorem integer_encoding_exact : encodeJson 1 (.integer 18446744073709551615) =
    some (ascii "18446744073709551615") := rfl

theorem negative_encoding_exact : encodeJson 1 (.integer (-9223372036854775808)) =
    some (ascii "-9223372036854775808") := rfl

theorem exact_large_integer_arithmetic :
    IntExpr.eval [] (.binary .add (.literal 9223372036854775807)
      (.binary .add (.literal 9223372036854775807) (.literal 1))) =
      some 18446744073709551615 := rfl

theorem native_binding_uses_exact_unsigned_residue (pointerBits : Nat)
    (ty : SemR.IntTy) (raw : Nat)
    (range : raw < SemR.modulus (ty.bits pointerBits)) (unsigned : ty.signed = false) :
    boundValue pointerBits (.int ty) (.int ty raw) =
      some (.integer (Int.ofNat raw)) := by
  simp [boundValue, SemRUnsignedSelect.checkedUInt _ _ _ range, unsigned]

theorem wrong_native_width_refused :
    boundValue 64 (.int .u8) (.int .u64 1) = none := rfl

theorem out_of_range_native_value_refused :
    boundValue 64 (.int .u64) (.int .u64 18446744073709551616) = none := rfl

theorem signed_native_value_refused :
    boundValue 64 (.int .i64) (.int .i64 1) = none := rfl

theorem poison_native_value_refused :
    boundValue 64 (.int .u64) (.poison (.int .u64)) = none := rfl

theorem duplicate_entry_id_refused (m : SemR.Module) (k : SemR.Core) :
    entryTypedEnv m [(0, x, .bool), (0, y, .int .u64)] k = none := rfl

theorem duplicate_entry_name_refused (m : SemR.Module) (k : SemR.Core) :
    entryTypedEnv m [(0, x, .bool), (1, x, .int .u64)] k = none := rfl

theorem cross_sort_contract_binding_refused (m : SemR.Module) :
    contractTypedEnv m [(x, .param 0, .bool), (x, .result 0, .int .u64)]
      [.bool true] [.int .u64 0] = none := rfl

/-- The original declared divisor guard is decoded as integer comparison,
    without rewriting its bytes into another formula format. -/
theorem divisor_text_decoded :
    decodeTypedText 4096 [] [ascii "d"] (ascii "d != 0") =
      some (.intCompare .ne (.var (ascii "d")) (.literal 0)) := rfl

theorem divisor_text_interpretation (value : Int) :
    checkedTypedText 4096 (ascii "d != 0") [] [ascii "d"]
      ([], [(ascii "d", value)]) = some (value != 0) := rfl

theorem zero_divisor_guard_is_false :
    checkedTypedText 4096 (ascii "d != 0") [] [ascii "d"]
      ([], [(ascii "d", 0)]) = some false := rfl

theorem full_unsigned_divisor_guard_is_true :
    checkedTypedText 4096 (ascii "d != 0") [] [ascii "d"]
      ([], [(ascii "d", 18446744073709551615)]) = some true := rfl

theorem integer_text_precedence :
    checkedTypedText 4096 (ascii "d + 2 * 3 == 9") [] [ascii "d"]
      ([], [(ascii "d", 3)]) = some true := rfl

theorem parenthesized_integer_text :
    checkedTypedText 4096 (ascii "(d + 2) * 3 == 9") [] [ascii "d"]
      ([], [(ascii "d", 1)]) = some true := rfl

theorem integer_text_associativity :
    checkedTypedText 4096 (ascii "8 - 3 - 2 == 3") [] [] ([], []) = some true := rfl

theorem negative_integer_text :
    checkedTypedText 4096 (ascii "-2 * 3 < -1") [] [] ([], []) = some true := rfl

theorem mixed_boolean_integer_text :
    checkedTypedText 4096 (ascii "c ==> d != 0") [c] [ascii "d"]
      ([(c, true)], [(ascii "d", 1)]) = some true := rfl

theorem wrong_text_binding_sort_refused :
    decodeTypedText 4096 [ascii "d"] [] (ascii "d != 0") = none := rfl

theorem unbound_text_integer_refused :
    checkedTypedText 4096 (ascii "d != 0") [] [ascii "d"] ([], []) = none := rfl

theorem hidden_unknown_text_name_refused :
    decodeTypedText 4096 [] [] (ascii "false && d != 0") = none := rfl

theorem cross_sort_text_name_refused :
    decodeTypedText 4096 [ascii "d"] [ascii "d"] (ascii "true") = none := rfl

theorem duplicate_text_integer_name_refused :
    decodeTypedText 4096 [] [ascii "d", ascii "d"] (ascii "true") = none := rfl

theorem unsupported_text_division_refused :
    decodeTypedText 4096 [] [ascii "d"] (ascii "d / 0 == 1") = none := rfl

theorem trailing_text_bytes_refused :
    decodeTypedText 4096 [] [ascii "d"] (ascii "d != 0 junk") = none := rfl

theorem integer_as_boolean_text_refused :
    decodeTypedText 4096 [] [ascii "d"] (ascii "d") = none := rfl

theorem cross_sort_text_equality_refused :
    decodeTypedText 4096 [c] [ascii "d"] (ascii "c == d") = none := rfl

theorem boolean_text_ordering_refused :
    decodeTypedText 4096 [c] [] (ascii "c < true") = none := rfl

theorem unsupported_text_annotation_refused :
    decodeTypedText 4096 [] [ascii "d"] (ascii "(d : bool) != 0") = none := rfl

theorem zero_text_fuel_refused :
    decodeTypedText 0 [] [ascii "d"] (ascii "d != 0") = none := rfl

end SemRScalarClaimAudit
