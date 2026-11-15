@[extern "clean_battery_no_such_symbol"]
def bump (n : Nat) : Nat := n + 1

def main : IO Unit := IO.println (toString (bump 1))
