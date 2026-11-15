(set-logic ALL)
(declare-datatypes ((D 0)) (((mk (not Int)))))
(assert (= (not (mk 0)) 0))
(check-sat)
