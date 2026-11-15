(set-logic ALL)
(define-fun xor ((a Bool) (b Bool)) Bool true)
(assert (xor true true))
(check-sat)
