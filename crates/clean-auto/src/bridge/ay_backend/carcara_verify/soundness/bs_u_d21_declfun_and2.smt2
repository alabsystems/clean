(set-logic ALL)
(declare-fun and (Bool Bool) Bool)
(assert (not (and true true)))
(check-sat)
