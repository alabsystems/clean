-- RM1 fixture: one definition per join-point gate (elab_match/join_point.rs).
-- Each definition has one match whose last arm is the shape that gate
-- judges; the theorems pin the values Lean 4.8.0 computes.
inductive C where
  | c0
  | c1
  | c2
  | c3

-- Applied: an irrefutable catch-all with control flow of its own.
def gApplied (x : C) (b : Bool) : Nat :=
  match x with
  | .c0 => 1
  | _ => if b then 2 else 3

theorem gApplied_c0 : gApplied .c0 true = 1 := rfl
theorem gApplied_c2 : gApplied .c2 false = 3 := rfl

-- PlainBody: the catch-all body has no control flow (cost filter).
def gPlain (x : C) (n : Nat) : Nat :=
  match x with
  | .c0 => 1
  | _ => n + 2

theorem gPlain_c3 : gPlain .c3 5 = 7 := rfl

-- RefutableCatchAll: the last arm is a constructor pattern.
def gRefutable (x : C) (b : Bool) : Nat :=
  match x with
  | .c0 => 1
  | .c1 => 2
  | .c2 => 3
  | .c3 => if b then 4 else 5

theorem gRefutable_c3 : gRefutable .c3 false = 5 := rfl

-- DiscriminantHypothesis: `match h : e`.
def gHyp (x : C) (b : Bool) : Nat :=
  match h : x with
  | .c0 => 1
  | _ => if b then 2 else 3

theorem gHyp_c1 : gHyp .c1 true = 2 := rfl

-- ExpectedTypeUnknown: an unannotated `let` value has no expected type.
def gLetOpen (x : C) (b : Bool) : Nat :=
  let y := match x with
    | .c0 => (1 : Nat)
    | _ => if b then 2 else 3
  y

theorem gLetOpen_c1 : gLetOpen .c1 false = 3 := rfl

-- ExpectedTypeOpen: no return type. As in Lean, the inferred header's result
-- is a metavariable, so the match's expected type is still open.
def gOpen (x : C) (b : Bool) :=
  match x with
  | .c0 => (1 : Nat)
  | _ => if b then 2 else 3

theorem gOpen_c1 : gOpen .c1 false = 3 := rfl

-- MotiveMentionsDiscriminant: the expected type depends on the discriminant.
def gDep (n : Nat) (b : Bool) : Fin (n + 1) :=
  match n with
  | 0 => ⟨0, Nat.zero_lt_succ 0⟩
  | _ => if b then ⟨0, Nat.zero_lt_succ _⟩ else ⟨0, Nat.zero_lt_succ _⟩

theorem gDep_val : (gDep 3 false).val = 0 := rfl

-- DependentMotive: a match inside a branch of a dependent-motive match.
def gDepInner (n : Nat) (x : C) (b : Bool) : Fin (n + 1) :=
  match n with
  | 0 => ⟨0, Nat.zero_lt_succ 0⟩
  | k + 1 =>
    match x with
    | .c0 => ⟨0, Nat.zero_lt_succ _⟩
    | _ => if b then ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ k)⟩ else ⟨k + 1, Nat.lt_succ_self (k + 1)⟩

theorem gDepInner_val : (gDepInner 2 .c3 true).val = 1 := rfl

-- RecursionArgument: a match on an induction-hypothesis field.
def gRec : Nat → Bool → Nat
  | 0, _ => 0
  | n + 1, b =>
    match n with
    | 0 => 1
    | _ => if b then gRec n b + 10 else 2

theorem gRec_three : gRec 3 true = 21 := rfl

-- ExpectedTypeOpen: `List.length`'s argument is elaborated against `List ?α`.
def gOpenList (x : C) (b : Bool) : Nat :=
  List.length (match x with
    | .c0 => []
    | _ => if b then [1, 2] else [3])

theorem gOpenList_c1 : gOpenList .c1 true = 2 := rfl
