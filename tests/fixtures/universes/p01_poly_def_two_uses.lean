def id2.{u} {A : Sort u} (a : A) : A := a
def useProp : True := id2 True.intro
def useType : Nat := id2 Nat.zero
