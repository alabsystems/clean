def Var := Nat
def Assignment := Var -> Prop
def Formula := Assignment -> Prop
def Clause := Assignment -> Prop

def Both (left right : Prop) : Prop :=
  forall (Result : Prop), (left -> right -> Result) -> Result

def Satisfiable (formula : Formula) : Prop :=
  forall (Result : Prop), ((assignment : Assignment) -> formula assignment -> Result) -> Result

def FullFormula (remaining : Formula) (deleted : Clause) : Formula :=
  fun assignment => Both (remaining assignment) (deleted assignment)

def ForcedByRemaining (remaining : Formula) (deleted : Clause) : Prop :=
  forall (assignment : Assignment), remaining assignment -> deleted assignment

def Equisat (left right : Formula) : Prop :=
  Both (Satisfiable left -> Satisfiable right) (Satisfiable right -> Satisfiable left)

theorem forced_clause_deletion_forward
    (remaining : Formula) (deleted : Clause) :
    Satisfiable (FullFormula remaining deleted) -> Satisfiable remaining :=
  fun fullSat Result keep =>
    fullSat Result
      (fun assignment fullH =>
        fullH Result
          (fun remainingH deletedH => keep assignment remainingH))

theorem forced_clause_deletion_backward
    (remaining : Formula) (deleted : Clause)
    (forced : ForcedByRemaining remaining deleted) :
    Satisfiable remaining -> Satisfiable (FullFormula remaining deleted) :=
  fun remainingSat Result keep =>
    remainingSat Result
      (fun assignment remainingH =>
        keep assignment
          (fun PairResult pairKeep =>
            pairKeep remainingH (forced assignment remainingH)))

theorem forced_clause_deletion_equisat
    (remaining : Formula) (deleted : Clause)
    (forced : ForcedByRemaining remaining deleted) :
    Equisat (FullFormula remaining deleted) remaining :=
  fun Result keep =>
    keep
      (forced_clause_deletion_forward remaining deleted)
      (forced_clause_deletion_backward remaining deleted forced)

