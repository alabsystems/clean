/-
  Checked Boolean claim bytes for the existing native WP formats.
  This is a claim codec, not another program semantics.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import NativeContractSyntax

namespace SemRBooleanClaim

inductive Binary where
  | and | or | implies | eq | ne
  deriving DecidableEq

/-- One interpretation of the supported Boolean constructors. -/
def Binary.apply : Binary → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .implies, a, b => !a || b
  | .eq, a, b => a == b
  | .ne, a, b => a != b

inductive Expr where
  | literal (value : Bool)
  | var (name : Name)
  | not (value : Expr)
  | binary (op : Binary) (left right : Expr)
  | ite (condition yes no : Expr)
  | intCompare (op : IntComparison) (left right : IntExpr)
  deriving DecidableEq

def lookup (env : Env) (name : Name) : Option Bool :=
  (env.find? (fun row => row.1 == name)).map Prod.snd

/-- An unbound name refuses, including in an unselected branch. -/
def evalTyped (env : Env) (integers : IntEnv) : Expr → Option Bool
  | .literal value => some value
  | .var name => lookup env name
  | .not value => do pure (!(← evalTyped env integers value))
  | .binary op left right => do
      pure (op.apply (← evalTyped env integers left) (← evalTyped env integers right))
  | .ite condition yes no => do
      let c ← evalTyped env integers condition
      let y ← evalTyped env integers yes
      let n ← evalTyped env integers no
      pure (if c then y else n)
  | .intCompare op left right => do
      pure (op.apply (← left.eval integers) (← right.eval integers))

/-- The existing Boolean interface uses the same interpretation with no
    integer bindings; no second Boolean evaluator is retained. -/
def eval (env : Env) (expression : Expr) : Option Bool := evalTyped env [] expression

/-- The existing native structured encoder expands selection into Boolean
    connectives. The proof below justifies that expansion for every input. -/
def lower : Expr → Expr
  | .literal value => .literal value
  | .var name => .var name
  | .intCompare op left right => .intCompare op left right
  | .not value => .not (lower value)
  | .binary op left right => .binary op (lower left) (lower right)
  | .ite condition yes no =>
      .binary .or (.binary .and (lower condition) (lower yes))
        (.binary .and (.not (lower condition)) (lower no))

theorem selection_as_connectives (c y n : Bool) :
    ((c && y) || ((!c) && n)) = (if c then y else n) := by
  cases c <;> cases y <;> cases n <;> rfl

theorem lower_typed_sound (env : Env) (integers : IntEnv) (expression : Expr) :
    evalTyped env integers (lower expression) = evalTyped env integers expression := by
  induction expression with
  | literal value => rfl
  | var name => rfl
  | intCompare op left right => rfl
  | not value ih => simp [lower, evalTyped, ih]
  | binary op left right ihl ihr => simp [lower, evalTyped, ihl, ihr]
  | ite condition yes no ihc ihy ihn =>
      cases hc : evalTyped env integers condition <;>
        cases hy : evalTyped env integers yes <;>
        cases hn : evalTyped env integers no <;>
        simp [lower, evalTyped, ihc, ihy, ihn, hc, hy, hn,
          Binary.apply, selection_as_connectives]

theorem lower_sound (env : Env) (expression : Expr) :
    eval env (lower expression) = eval env expression := lower_typed_sound env [] expression

/-- Raw JSON data proposed by an untrusted producer. Actual-byte equality and
    strict shape decoding are checked independently in the kernel. -/
inductive Json where
  | boolean (value : Bool)
  | integer (value : Int)
  | string (value : Bytes)
  | array (values : List Json)
  | object (fields : List (Bytes × Json))

private def colon : Bytes := [58]
private def comma : Bytes := [44]
private def quote : Nat := 34
private def slash : Nat := 92
private def trueToken : Bytes := [116,114,117,101]
private def falseToken : Bytes := [102,97,108,115,101]
private def boolToken : Bytes := [98,111,111,108]
private def nameKey : Bytes := [110,97,109,101]
private def sortKey : Bytes := [115,111,114,116]
private def schemaKey : Bytes := [115,99,104,101,109,97]
private def variablesKey : Bytes := [118,97,114,105,97,98,108,101,115]
private def resultKey : Bytes := [114,101,115,117,108,116]
private def bodyKey : Bytes := [98,111,100,121]
private def boolKey : Bytes := [98,111,111,108]
private def intKey : Bytes := [105,110,116]
private def varKey : Bytes := [118,97,114]
private def opKey : Bytes := [111,112]
private def exprKey : Bytes := [101,120,112,114]
private def lhsKey : Bytes := [108,104,115]
private def rhsKey : Bytes := [114,104,115]
private def notToken : Bytes := [110,111,116]
private def claimSchema : Bytes :=
  [116,114,117,115,116,45,119,112,46,116,114,117,115,116,45,102,111,114,109,117,108,97,46,118,49]

def Binary.token : Binary → Bytes
  | .and => [97,110,100]
  | .or => [111,114]
  | .implies => [105,109,112,108,105,101,115]
  | .eq => [101,113]
  | .ne => [110,101]

def binaryOfToken (token : Bytes) : Option Binary :=
  if token = Binary.token .and then some .and else
  if token = Binary.token .or then some .or else
  if token = Binary.token .implies then some .implies else
  if token = Binary.token .eq then some .eq else
  if token = Binary.token .ne then some .ne else none

theorem binary_token_roundtrip (op : Binary) : binaryOfToken op.token = some op := by
  cases op <;> rfl

private def hexDigit (value : Nat) : Nat := if value < 10 then 48 + value else 87 + value

private def escapeByte (value : Nat) : Bytes :=
  if value = quote then [slash, quote] else
  if value = slash then [slash, slash] else
  if value = 8 then [slash,98] else
  if value = 12 then [slash,102] else
  if value = 10 then [slash,110] else
  if value = 13 then [slash,114] else
  if value = 9 then [slash,116] else
  if value < 32 then [slash,117,48,48,hexDigit (value / 16),hexDigit (value % 16)] else [value]

def jsonString (value : Bytes) : Bytes := [quote] ++ value.flatMap escapeByte ++ [quote]

private def joined (separator : Bytes) : List Bytes → Bytes
  | [] => []
  | first :: rest => first ++ (rest.flatMap (separator ++ ·))

/-- The order in the proposed object is preserved, so both actual native JSON
    feature layouts can be checked against their original bytes. -/
def encodeJson : Nat → Json → Option Bytes
  | 0, _ => none
  | fuel + 1, value =>
      match value with
      | .boolean value => some (if value then trueToken else falseToken)
      | .integer value => some ((toString value).toList.map Char.toNat)
      | .string value => some (jsonString value)
      | .array values => do
          let encoded ← values.mapM (encodeJson fuel)
          pure ([91] ++ joined comma encoded ++ [93])
      | .object fields => do
          let encoded ← fields.mapM fun (key, value) => do
            pure (jsonString key ++ colon ++ (← encodeJson fuel value))
          pure ([123] ++ joined comma encoded ++ [125])

private def field (key : Bytes) (fields : List (Bytes × Json)) : Option Json :=
  (fields.find? (fun row => row.1 == key)).map Prod.snd

private def unique (names : List Name) : Bool := names.eraseDups.length == names.length

private def onlyFields (fields : List (Bytes × Json)) (allowed : List Bytes) : Bool :=
  unique (fields.map Prod.fst) && fields.all (fun row => allowed.contains row.1)

private def exactFields (fields : List (Bytes × Json)) (allowed : List Bytes) : Bool :=
  onlyFields fields allowed && fields.length == allowed.length

private def stringField (key : Bytes) (fields : List (Bytes × Json)) : Option Bytes := do
  let .string value ← field key fields | none
  pure value

private def intBinaryOfToken (token : Bytes) : Option IntBinary :=
  if token = [97,100,100] then some .add else
  if token = [115,117,98] then some .sub else
  if token = [109,117,108] then some .mul else none

private def intComparisonOfToken (token : Bytes) : Option IntComparison :=
  if token = [101,113] then some .eq else
  if token = [110,101] then some .ne else
  if token = [108,116] then some .lt else
  if token = [108,101] then some .le else
  if token = [103,116] then some .gt else
  if token = [103,101] then some .ge else none

/-- Exact arithmetic on the typed claim's mathematical integers, never on
    machine-word casts or a sampled integer domain. -/
def decodeIntBody : Nat → List Name → Option Name → Json → Option IntExpr
  | 0, _, _, _ => none
  | fuel + 1, names, result, .object fields => do
      if let some (.integer value) := field intKey fields then
        if exactFields fields [intKey] then return .literal value else none
      else if let some (.string name) := field varKey fields then
        if exactFields fields [varKey] && names.contains name then return .var name else none
      else if let some (.boolean true) := field resultKey fields then
        if !exactFields fields [resultKey] then none else return .var (← result)
      else
        let op ← stringField opKey fields
        if op = [110,101,103] then
          if !exactFields fields [opKey, exprKey] then none else
            return .neg (← decodeIntBody fuel names result (← field exprKey fields))
        else
          if !exactFields fields [opKey, lhsKey, rhsKey] then none else
            return .binary (← intBinaryOfToken op)
              (← decodeIntBody fuel names result (← field lhsKey fields))
              (← decodeIntBody fuel names result (← field rhsKey fields))
  | _ + 1, _, _, _ => none

/-- One typed Boolean decoder, extended by integer predicates. Unknown fields,
    duplicate keys, undeclared names and mixed sorts keep refusing. -/
def decodeTypedBody : Nat → List Name → List Name → Option Name → Option Name →
    Json → Option Expr
  | 0, _, _, _, _, _ => none
  | fuel + 1, names, integers, result, intResult, .object fields => do
      if let some (.boolean value) := field boolKey fields then
        if exactFields fields [boolKey] then return .literal value else none
      else if let some (.string name) := field varKey fields then
        if exactFields fields [varKey] && names.contains name then return .var name else none
      else if let some (.boolean true) := field resultKey fields then
        if !exactFields fields [resultKey] then none else return .var (← result)
      else
        let op ← stringField opKey fields
        if op = notToken then
          if !exactFields fields [opKey, exprKey] then none else
            return .not (← decodeTypedBody fuel names integers result intResult
              (← field exprKey fields))
        else
          if !exactFields fields [opKey, lhsKey, rhsKey] then none else
            let left ← field lhsKey fields
            let right ← field rhsKey fields
            let boolOperands := do
              pure (← decodeTypedBody fuel names integers result intResult left,
                    ← decodeTypedBody fuel names integers result intResult right)
            if let some (left, right) := boolOperands then
              return .binary (← binaryOfToken op) left right
            else
              return .intCompare (← intComparisonOfToken op)
                (← decodeIntBody fuel integers intResult left)
                (← decodeIntBody fuel integers intResult right)
  | _ + 1, _, _, _, _, _ => none

/-- Compatibility with the original Boolean decoder API. -/
def decodeBody (fuel : Nat) (names : List Name) (result : Option Name)
    (value : Json) : Option Expr := decodeTypedBody fuel names [] result none value

/-- The canonical structured native codec's ASCII SMT-symbol domain.
    These names are opaque keys, including SSA and place-projection sigils. -/
private def validName (name : Name) : Bool :=
  let letter := fun b => (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)
  match name with
  | [] => false
  | first :: rest =>
      (first == 95 || letter first) && rest.all (fun b =>
        letter b || (48 ≤ b && b ≤ 57) ||
          [95,35,46,91,93,42,64,45,59,61].contains b)

inductive ClaimSort where
  | bool | int
  deriving DecidableEq

private def claimSort (token : Bytes) : Option ClaimSort :=
  if token = boolToken then some .bool else if token = intKey then some .int else none

private def binding (value : Json) : Option (Name × ClaimSort) := do
  let .object fields := value | none
  if !exactFields fields [nameKey, sortKey] then none else
    let name ← stringField nameKey fields
    let sort ← claimSort (← stringField sortKey fields)
    if validName name then some (name, sort) else none

private def resultBinding (value : Json) : Option (Name × ClaimSort) := do
  let .object fields := value | none
  if !onlyFields fields [nameKey, sortKey] then none else
    let sort ← claimSort (← stringField sortKey fields)
    match field nameKey fields with
    | none => some (resultKey, sort)
    | some (.string name) => if validName name then some (name, sort) else none
    | _ => none

def decodeClaim (fuel : Nat) (value : Json) : Option Expr := do
  let .object fields := value | none
  if !onlyFields fields [schemaKey, variablesKey, resultKey, bodyKey] then none else
    let schema ← stringField schemaKey fields
    if schema.map (fun b => if b = 95 then 45 else b) != claimSchema then none else
      let declarations ← match field variablesKey fields with
        | none => some []
        | some (.array values) => values.mapM binding
        | _ => none
      let result ← match field resultKey fields with
        | none => some none
        | some value => (resultBinding value).map some
      let declarations := declarations ++ result.toList
      if !unique (declarations.map Prod.fst) then none else
        let names := declarations.filterMap fun (name, sort) =>
          if sort = .bool then some name else none
        let integers := declarations.filterMap fun (name, sort) =>
          if sort = .int then some name else none
        let boolResult := result.bind fun (name, sort) =>
          if sort = .bool then some name else none
        let intResult := result.bind fun (name, sort) =>
          if sort = .int then some name else none
        decodeTypedBody fuel names integers boolResult intResult (← field bodyKey fields)

/-- A predicate over the exact structured claim bytes, not a renamed or
    reprinted expression supplied by Rust. -/
def checkedTypedJson (fuel : Nat) (bytes : Bytes) (proposed : Json)
    (env : TypedEnv) : Option Bool := do
  let encoded ← encodeJson fuel proposed
  if encoded = bytes then evalTyped env.1 env.2 (← decodeClaim fuel proposed) else none

/-- Legacy Boolean callers use the same exact-byte checker and interpretation. -/
def checkedJson (fuel : Nat) (bytes : Bytes) (proposed : Json) (env : Env) : Option Bool :=
  checkedTypedJson fuel bytes proposed (env, [])

theorem checked_typed_json_eval (fuel : Nat) (bytes : Bytes) (proposed : Json)
    (expression : Expr) (env : TypedEnv)
    (encoded : encodeJson fuel proposed = some bytes)
    (decoded : decodeClaim fuel proposed = some expression) :
    checkedTypedJson fuel bytes proposed env = evalTyped env.1 env.2 expression := by
  simp [checkedTypedJson, encoded, decoded]

theorem checked_json_eval (fuel : Nat) (bytes : Bytes) (proposed : Json)
    (expression : Expr) (env : Env)
    (encoded : encodeJson fuel proposed = some bytes)
    (decoded : decodeClaim fuel proposed = some expression) :
    checkedJson fuel bytes proposed env = eval env expression := by
  simp [checkedJson, checkedTypedJson, eval, encoded, decoded]

/-- A successful check entails the complete actual-byte equation, a strictly
    typed decoded expression, and that same expression's interpretation. -/
theorem checked_typed_json_sound (fuel : Nat) (bytes : Bytes) (proposed : Json)
    (env : TypedEnv) (value : Bool)
    (accepted : checkedTypedJson fuel bytes proposed env = some value) :
    ∃ expression, encodeJson fuel proposed = some bytes ∧
      decodeClaim fuel proposed = some expression ∧
      evalTyped env.1 env.2 expression = some value := by
  unfold checkedTypedJson at accepted
  cases encoded : encodeJson fuel proposed with
  | none => simp [encoded] at accepted
  | some actual =>
      by_cases same : actual = bytes
      · subst actual
        cases decoded : decodeClaim fuel proposed with
        | none => simp [encoded, decoded] at accepted
        | some expression =>
            exact ⟨expression, rfl, rfl, by simpa [encoded, decoded] using accepted⟩
      · simp [encoded, same] at accepted

theorem checked_json_sound (fuel : Nat) (bytes : Bytes) (proposed : Json)
    (env : Env) (value : Bool)
    (accepted : checkedJson fuel bytes proposed env = some value) :
    ∃ expression, encodeJson fuel proposed = some bytes ∧
      decodeClaim fuel proposed = some expression ∧ eval env expression = some value :=
  checked_typed_json_sound fuel bytes proposed (env, []) value accepted

end SemRBooleanClaim
