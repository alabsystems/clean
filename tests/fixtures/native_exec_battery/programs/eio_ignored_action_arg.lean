def skip (a : IO Unit) : IO Unit := pure ()

def main : IO Unit := skip (IO.println "a")
