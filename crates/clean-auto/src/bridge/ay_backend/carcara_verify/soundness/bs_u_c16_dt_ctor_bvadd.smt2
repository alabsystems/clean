(set-logic ALL)
(declare-datatypes ((D 0)) (((bvadd (pa (_ BitVec 2)) (pb (_ BitVec 2))))))
(assert (not (= (bvadd #b01 #b00) (bvadd #b00 #b01))))
(check-sat)
