(set-logic ALL)
(declare-fun ite (Bool Int Int) Int)
(assert (= (ite true 0 1) 5))
(check-sat)
