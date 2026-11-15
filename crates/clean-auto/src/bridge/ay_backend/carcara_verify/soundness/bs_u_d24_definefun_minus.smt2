(set-logic ALL)
(define-fun - ((a Int) (b Int)) Int 7)
(assert (= (- 1 1) 7))
(check-sat)
