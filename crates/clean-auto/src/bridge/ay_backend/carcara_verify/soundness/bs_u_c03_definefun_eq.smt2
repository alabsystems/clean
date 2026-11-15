(set-logic ALL)
(define-fun = ((x Int)) Bool true)
(assert (not (= 0)))
(check-sat)
