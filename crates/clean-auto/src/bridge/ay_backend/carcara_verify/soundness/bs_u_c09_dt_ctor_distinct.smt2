(set-logic ALL)
(declare-datatypes ((D 0)) (((distinct (da Int) (db Int)) (other))))
(assert (not (= (distinct 0 0) (distinct 0 1))))
(check-sat)
