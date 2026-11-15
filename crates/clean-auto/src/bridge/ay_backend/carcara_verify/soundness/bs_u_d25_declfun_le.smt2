(set-logic ALL)
(declare-fun <= (Int Int) Bool)
(assert (not (<= 0 1)))
(check-sat)
