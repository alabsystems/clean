-- Negative control of eqns_theorem_simp.lean: the `.ref` arm calls its sibling on
-- the major premise itself, not a field.
inductive Ty where
  | i8 : Ty
  | tuple : List Ty → Ty
  | ref : Ty → Ty
inductive TT where
  | i8 : TT
  | tuple : List TT → TT
  | ref : TT → TT
  | param : Nat → TT
mutual
def substTy (σ : Nat → Option Ty) : TT → Option Ty
  | .i8 => some .i8
  | .tuple a0 => (substTys σ a0).bind fun a0' => some (.tuple a0')
  | .ref a0 => (substTy σ a0).bind fun a0' => some (.ref a0')
  | .param i => σ i
def substTys (σ : Nat → Option Ty) : List TT → Option (List Ty)
  | [] => some []
  | t :: ts => (substTy σ t).bind fun t' => (substTys σ ts).bind fun ts' => some (t' :: ts')
end
mutual
def embed : Ty → TT
  | .i8 => .i8
  | .tuple a0 => .tuple (embeds a0)
  | .ref a0 => .ref (embed a0)
def embeds : List Ty → List TT
  | [] => []
  | t :: ts => embed t :: embeds ts
end
mutual
theorem substTy_embed (σ : Nat → Option Ty) : ∀ t : Ty, substTy σ (embed t) = some t
  | .i8 => by simp [embed, substTy]
  | .tuple a0 => by simp [embed, substTy, substTys_embeds σ a0]
  | .ref a0 => by simp [embed, substTy, substTy_embed σ (.ref a0)]
theorem substTys_embeds (σ : Nat → Option Ty) : ∀ ts : List Ty, substTys σ (embeds ts) = some ts
  | [] => by simp [embeds, substTys]
  | t :: ts => by simp [embeds, substTys, substTy_embed σ t, substTys_embeds σ ts]
end
