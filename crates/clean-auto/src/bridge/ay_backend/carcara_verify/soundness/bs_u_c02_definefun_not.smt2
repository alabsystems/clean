(set-logic ALL)
(define-fun not ((x Int)) Bool true)
(assert (not 0))
(check-sat)
