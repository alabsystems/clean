(set-logic ALL)
(declare-datatypes ((D 0)) (((+ (pa Int) (pb Int)))))
(assert (not (= (+ 1 0) (+ 0 1))))
(check-sat)
