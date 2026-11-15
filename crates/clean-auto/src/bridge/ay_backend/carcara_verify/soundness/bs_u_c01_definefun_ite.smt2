(set-logic ALL)
(define-fun ite ((b Bool) (x Int)) Int 1)
(assert (= (ite true 0) 1))
(check-sat)
