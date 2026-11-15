(set-logic ALL)
(define-fun = ((a Int) (b Int)) Bool false)
(assert (not (= 0 0)))
(check-sat)
