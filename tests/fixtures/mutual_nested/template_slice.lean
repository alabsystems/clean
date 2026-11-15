-- Blocks 4-6 (trust-ir Template.lean:75/127/176), minimized: fixed
-- parameters `σ η`, calls under `Option.bind` lambdas, different codomains.
inductive Ty where
  | I8 : Ty
  | Tuple : List Ty → Ty
  | Ref : Ty → Ty
inductive TemplateTy where
  | I8 : TemplateTy
  | Tuple : List TemplateTy → TemplateTy
  | Ref : TemplateTy → TemplateTy
  | param : Nat → TemplateTy

mutual
def substTy (σ η : Nat → Option Ty) : TemplateTy → Option Ty
  | .I8 => some (.I8)
  | .Tuple a0 => (substTys σ η a0).bind fun a0' => some (.Tuple a0')
  | .Ref a0 => (substTy σ η a0).bind fun a0' => some (.Ref a0')
  | .param i => σ i
def substTys (σ η : Nat → Option Ty) : List TemplateTy → Option (List Ty)
  | [] => some []
  | t :: ts => (substTy σ η t).bind fun t' => (substTys σ η ts).bind fun ts' => some (t' :: ts')
end

mutual
def embed : Ty → TemplateTy
  | .I8 => .I8
  | .Tuple a0 => .Tuple (embeds a0)
  | .Ref a0 => .Ref (embed a0)
def embeds : List Ty → List TemplateTy
  | [] => []
  | t :: ts => embed t :: embeds ts
end

mutual
def refsOk (σ η : Nat → Option Ty) : TemplateTy → Bool
  | .I8 => true
  | .Tuple a0 => refsOks σ η a0
  | .Ref a0 => refsOk σ η a0
  | .param i => (σ i).isSome
def refsOks (σ η : Nat → Option Ty) : List TemplateTy → Bool
  | [] => true
  | t :: ts => refsOk σ η t && refsOks σ η ts
end

theorem ok1 : refsOk (fun _ => some .I8) (fun _ => none) (.Tuple [.param 0, .Ref .I8]) = true := by decide
theorem sub1 : substTy (fun _ => some .I8) (fun _ => none) (.Tuple [.param 0, .Ref (.param 3)]) = some (.Tuple [.I8, .Ref .I8]) := rfl
theorem emb1 : embed (.Tuple [.I8, .Ref .I8]) = .Tuple [.I8, .Ref .I8] := rfl
