-- Only commands, no declaration: `clean check` refuses the file as vacuous,
-- `lean` prints each command's output and exits 0.
#check Nat
#check (1 : Nat)
#eval 1 + 1
#eval "hi"
