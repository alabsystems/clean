(set-logic ALL)
(declare-datatypes ((D 0)) (((= (ea Int)))))
(assert (not (= (= 0) (= 1))))
(check-sat)
