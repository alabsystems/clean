(set-logic ALL)
(declare-datatypes ((D 0)) (((or (oa Bool) (ob Bool)))))
(assert (not (= (or true false) (or false true))))
(check-sat)
