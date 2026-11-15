/-
  SemRForged — the negative control of Clean's SemR audit
  (`crates/clean-olean/tests/semr_reference.rs`). It declares, in SemR's
  namespace, what SemR must never carry, hidden the way the RM4 review hid it
  from the first tripwire (a `'"'` character literal, which a lexer without
  character literals reads as the opening of a string that swallows the rest
  of the file): a theorem closed by `native_decide` (at v4.30 its proof cites
  an auxiliary axiom of its own) and a `partial def` (an opaque constant
  beside an unsafe implementation). The audit must report both by name and
  nothing else; the tripwire must report `native_decide` and `partial`.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
namespace SemR

def dq : Char := '"'

theorem smuggled : 10 < 11 := by native_decide

partial def spin (n : Nat) : Nat := spin (n + 1)

def honest : Nat := 3

theorem honest_eq : honest = 3 := rfl

end SemR
