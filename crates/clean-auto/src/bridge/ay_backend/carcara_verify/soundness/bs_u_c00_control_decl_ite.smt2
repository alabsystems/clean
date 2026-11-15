(set-logic ALL)
(declare-fun ite (Bool Int) Int)
(assert (= (ite true 0) 1))
(check-sat)
