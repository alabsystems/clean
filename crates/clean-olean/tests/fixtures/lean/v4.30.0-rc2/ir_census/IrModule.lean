module

/-!
IR census fixture: a `module` file. Its `.olean.private` keeps only the `meta`
closure with bodies (every other public declaration becomes an opaque
`extern`), and the full IR goes to the separate `.ir` file
(`Lean.IR.declMapExt.exportEntriesFnEx`, `Lean/Compiler/IR/CompilerM.lean`).
-/

public def modPub (n : Nat) : Nat := n + 1

def modPriv (n : Nat) : Nat := n * 3

@[expose] public def modExposed (xs : List Nat) : Nat := xs.foldl (· + ·) 0

public meta def modMeta (n : Nat) : Nat := n + 2

public def modUsesPriv (n : Nat) : Nat := modPriv n + modPub n
