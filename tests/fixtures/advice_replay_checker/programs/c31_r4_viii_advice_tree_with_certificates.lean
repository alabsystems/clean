/-!
R4 item (viii), formulation (B) of the design's 3.2: mutually inductive
advice types in which a head step carries a list of conversion
certificates; three functions mutually and structurally recursive on them
(the list of certificates has its own member); the bytes are decoded to that
tree first; and item (vi) repeated for it: a ground acceptance closed by
`rfl` and `decide`.
-/

inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

def Tm.beq : Tm → Tm → Bool
  | .lit m, .lit n => m == n
  | .succ a, .succ b => Tm.beq a b
  | _, _ => false

mutual
/-- A head-reduction run: stop, or contract the head redex, checking the
step's certificates, then continue. -/
inductive Head where
  | stop : Head
  | core : List Cert → Head → Head
/-- A conversion certificate: the two sides are equal as they are, or after
reducing each by its own run. -/
inductive Cert where
  | refl : Cert
  | reduce : Head → Head → Cert
end

mutual
def whnf : Head → Tm → Except String Tm
  | .stop, t => .ok t
  | .core cs rest, .succ (.lit n) =>
    match certs cs (.lit n) (.lit n) with
    | .ok () => whnf rest (.lit (n + 1))
    | .error e => .error e
  | .core _ _, _ => .error "core does not apply"
def conv : Cert → Tm → Tm → Except String Unit
  | .refl, a, b => if Tm.beq a b then .ok () else .error "refl: sides differ"
  | .reduce ha hb, a, b =>
    match whnf ha a with
    | .error e => .error e
    | .ok a' =>
      match whnf hb b with
      | .error e => .error e
      | .ok b' => if Tm.beq a' b' then .ok () else .error "reduce: sides differ"
def certs : List Cert → Tm → Tm → Except String Unit
  | [], _, _ => .ok ()
  | c :: cs, a, b =>
    match conv c a b with
    | .ok () => certs cs a b
    | .error e => .error e
end

-- The decoder. Byte format: `0` stop; `1 k <k certs> <head>` core; a cert is
-- `0` refl or `1 <head> <head>` reduce. Structurally recursive on a counter.
mutual
def decHead : Nat → List Nat → Option (Head × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: bs => some (.stop, bs)
  | fuel + 1, 1 :: k :: bs =>
    match decCerts fuel k bs with
    | some (cs, bs') =>
      match decHead fuel bs' with
      | some (rest, bs'') => some (.core cs rest, bs'')
      | none => none
    | none => none
  | _ + 1, _ => none
def decCert : Nat → List Nat → Option (Cert × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: bs => some (.refl, bs)
  | fuel + 1, 1 :: bs =>
    match decHead fuel bs with
    | some (ha, bs') =>
      match decHead fuel bs' with
      | some (hb, bs'') => some (.reduce ha hb, bs'')
      | none => none
    | none => none
  | _ + 1, _ => none
def decCerts : Nat → Nat → List Nat → Option (List Cert × List Nat)
  | 0, _, _ => none
  | _ + 1, 0, bs => some ([], bs)
  | fuel + 1, k + 1, bs =>
    match decCert fuel bs with
    | some (c, bs') =>
      match decCerts fuel k bs' with
      | some (cs, bs'') => some (c :: cs, bs'')
      | none => none
    | none => none
end

/-- Decode the bytes, then check the conversion `a ≡ b` by the certificate. -/
def checkBytes (bytes : List Nat) (a b : Tm) : Except String Unit :=
  match decCert 64 bytes with
  | some (c, []) => conv c a b
  | some _ => .error "trailing bytes"
  | none => .error "undecodable advice"

def accepts : Except String Unit → Bool
  | .ok () => true
  | .error _ => false

/-- `succ (lit 1) ≡ lit 2`: reduce the left by one step whose certificate is
`refl`, and the right by none. -/
def honest : List Nat := [1, 1, 1, 0, 0, 0]

/-- The same step carrying two certificates, the second a reduction. -/
def twoCerts : List Nat := [1, 1, 2, 0, 1, 0, 0, 0, 0]

/-- A step whose certificate reduces `lit 1` by a `core` step that does not
apply. -/
def badCert : List Nat := [1, 1, 1, 1, 1, 0, 0, 0, 0, 0]

theorem honest_accepted_by_rfl :
    accepts (checkBytes honest (.succ (.lit 1)) (.lit 2)) = true := rfl

theorem honest_accepted_by_decide :
    accepts (checkBytes honest (.succ (.lit 1)) (.lit 2)) = true := by decide

theorem corrupt_refused_by_decide :
    accepts (checkBytes honest (.succ (.lit 1)) (.lit 3)) = false := by decide

def verdict (name : String) (r : Except String Unit) : String :=
  match r with
  | .ok () => s!"{name}: ACCEPT"
  | .error e => s!"{name}: REFUSE {e}"

def main : IO Unit := do
  IO.println (verdict "one-step" (checkBytes honest (.succ (.lit 1)) (.lit 2)))
  IO.println (verdict "two-certs" (checkBytes twoCerts (.succ (.lit 1)) (.lit 2)))
  IO.println (verdict "bad-cert" (checkBytes badCert (.succ (.lit 1)) (.lit 2)))
  IO.println (verdict "not-a-redex" (checkBytes honest (.succ (.succ (.lit 0))) (.lit 2)))
  IO.println (verdict "wrong-claim" (checkBytes honest (.succ (.lit 1)) (.lit 3)))
  IO.println (verdict "truncated" (checkBytes [1, 1, 1, 0] (.succ (.lit 1)) (.lit 2)))
  IO.println (verdict "trailing" (checkBytes (honest ++ [0]) (.succ (.lit 1)) (.lit 2)))
  IO.println (verdict "refl" (checkBytes [0] (.lit 4) (.lit 4)))
