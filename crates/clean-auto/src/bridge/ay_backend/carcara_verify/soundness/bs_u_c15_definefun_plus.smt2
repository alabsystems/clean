(set-logic ALL)
(define-fun + ((x Int) (y Int)) Int 7)
(assert (= (+ 1 1) 7))
(check-sat)
