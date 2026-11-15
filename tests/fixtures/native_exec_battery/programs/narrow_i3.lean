def f (a b : Int) : Int := a / b
def main : IO Unit := IO.println (toString (f 10 3))
