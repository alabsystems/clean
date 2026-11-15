-- RM1 fixture: the shape of TrustIr.Pred.impliesFuel (trust-ir Pred.lean:532).
inductive Space where
  | Index
  | Member

inductive P where
  | Interval   : Int → Int → P
  | FiniteSet  : List Nat → P
  | InUniverse : Nat → Space → P
  | NonZero    : P
  | NonNull    : P
  | Conj       : List P → P
  | Disj       : List P → P
  | Top        : P
  | Bottom     : P

def spaceBeq : Space → Space → Bool
  | .Index, .Index => true
  | .Member, .Member => true
  | _, _ => false

def P.beq : P → P → Bool
  | .NonZero, .NonZero => true
  | .NonNull, .NonNull => true
  | .Top, .Top => true
  | .Bottom, .Bottom => true
  | .InUniverse u s, .InUniverse v t => u == v && spaceBeq s t
  | _, _ => false

def P.impliesFuel (U : List Nat) : Nat → P → P → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    match a, b with
    | .Bottom, _ => true
    | _, .Bottom => false
    | _, .Top => true
    | .Top, _ => false
    | a, b =>
      if P.beq a b then true
      else if (match a with
               | .Conj cs => cs.any (fun c => P.impliesFuel U fuel c b)
               | _ => false) then true
      else if (match b with
               | .Disj cs => cs.any (fun c => P.impliesFuel U fuel a c)
               | _ => false) then true
      else
        match b with
        | .Conj cs => cs.all (fun c => P.impliesFuel U fuel a c)
        | _ =>
          match a with
          | .Disj cs => cs.all (fun c => P.impliesFuel U fuel c b)
          | _ =>
              match b with
              | .InUniverse ub sb =>
                match a with
                | .InUniverse ua sa =>
                  if spaceBeq sa sb = false then false
                  else
                    match U.get? ua, U.get? ub with
                    | some ua', some ub' =>
                      match sa with
                      | .Member => decide (ua' ≤ ub')
                      | .Index => ua' == ub'
                    | _, _ => false
                | _ => false
              | _ => false

theorem implies_bottom : P.impliesFuel [] 1 .Bottom .NonZero = true := rfl
theorem implies_refl : P.impliesFuel [] 1 .NonNull .NonNull = true := rfl
theorem implies_conj_left :
    P.impliesFuel [] 2 (.Conj [.NonZero, .NonNull]) .NonNull = true := rfl
theorem implies_disj_left :
    P.impliesFuel [] 2 (.Disj [.NonZero, .NonNull]) .NonNull = false := rfl
theorem implies_member :
    P.impliesFuel [3, 5] 1 (.InUniverse 0 .Member) (.InUniverse 1 .Member) = true := rfl
theorem implies_space_mismatch :
    P.impliesFuel [3, 5] 1 (.InUniverse 0 .Index) (.InUniverse 1 .Member) = false := rfl
theorem implies_index :
    P.impliesFuel [3, 5] 1 (.InUniverse 0 .Index) (.InUniverse 1 .Index) = false := rfl
