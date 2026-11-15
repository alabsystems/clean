(set-logic ALL)
(declare-fun + (Int Int) Int)
(assert (= (+ 1 1) 7))
(check-sat)
