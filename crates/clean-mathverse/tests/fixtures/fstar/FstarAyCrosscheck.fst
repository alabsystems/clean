module FstarAyCrosscheck
// The exact lemmas clean-mathverse/fstar_ay admits to bedrock via ay
// reconstruction. F* discharges each by SMT (Z3); ay reconstructs a Clean
// kernel proof reducing to the 3 axioms. This file proves F* AGREES they hold.
let le_refl       (a:int)       : Lemma (a <= a) = ()
let le_trans      (a b c:int)   : Lemma (requires a<=b /\ b<=c) (ensures a<=c) = ()
let le_antisymm   (a b:int)     : Lemma (requires a<=b /\ b<=a) (ensures a==b) = ()
let lt_trans      (a b c:int)   : Lemma (requires a<b /\ b<c) (ensures a<c) = ()
let lt_irrefl     (a:int)       : Lemma (~(a < a)) = ()
let le_of_lt      (a b:int)     : Lemma (requires a<b) (ensures a<=b) = ()
let lt_of_lt_of_le(a b c:int)   : Lemma (requires a<b /\ b<=c) (ensures a<c) = ()
let lt_of_le_of_lt(a b c:int)   : Lemma (requires a<=b /\ b<c) (ensures a<c) = ()
let eq_trans      (a b c:int)   : Lemma (requires a==b /\ b==c) (ensures a==c) = ()
let eq_symm       (a b:int)     : Lemma (requires a==b) (ensures b==a) = ()
let le_of_eq      (a b:int)     : Lemma (requires a==b) (ensures a<=b) = ()
