(set-logic ALL)
(declare-datatypes ((D 0)) (((ite (ia Bool) (ib Int)))))
(assert (not (= (ite true 0) (ite false 0))))
(check-sat)
