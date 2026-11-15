(set-logic QF_LRA)
(declare-fun . () Real)
(assert (not (= 1. 1.0)))
(check-sat)
