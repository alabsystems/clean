def dispatchExcept (onError onOk : Nat → Nat) (value : Except Nat Nat) : Nat :=
  @Except.casesOn Nat Nat (fun _ => Nat) value onError onOk

def runLeft (n : Nat) : Nat :=
  dispatchExcept (fun value => value) (fun _ => 99) (Except.error n)

def runRight (n : Nat) : Nat :=
  dispatchExcept (fun value => value) (fun _ => 99) (Except.ok n)

def dispatchPair (f : Nat → Nat → Nat) (value : Prod Nat Nat) : Nat :=
  @Prod.casesOn Nat Nat (fun _ => Nat) value (fun first => f first)

def runPair (n : Nat) : Nat :=
  dispatchPair (fun _ second => second) (Prod.mk 99 n)

def dispatchFunction (onError onOk : Nat → Nat → Nat) (value : Except Nat Nat) : Nat → Nat :=
  @Except.casesOn Nat Nat (fun _ => Nat → Nat) value onError onOk

def runFunctionLeft (n : Nat) : Nat :=
  dispatchFunction (fun first _ => first) (fun _ second => second) (Except.error n) 17

def runFunctionRight (n : Nat) : Nat :=
  dispatchFunction (fun first _ => first) (fun _ second => second) (Except.ok n) 17

def lambdaLong (value : Except Nat Nat) : Nat :=
  @Except.casesOn Nat Nat (fun _ => Nat) value (fun n => n) (fun n => n)

def runLambdaLong (n : Nat) : Nat :=
  lambdaLong (Except.ok n)

def nullaryCase (fallback : Nat) (value : Option Nat) : Nat :=
  @Option.casesOn Nat (fun _ => Nat) value fallback (fun n => n)

def runNone (n : Nat) : Nat :=
  nullaryCase n Option.none
