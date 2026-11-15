(set-logic ALL)
(define-fun ite ((c Bool) (a Int) (b Int)) Int 5)
(assert (= (ite true 0 1) 5))
(check-sat)
