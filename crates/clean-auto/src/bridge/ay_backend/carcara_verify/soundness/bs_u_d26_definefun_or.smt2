(set-logic ALL)
(define-fun or ((a Bool) (b Bool)) Bool false)
(assert (not (or true true)))
(check-sat)
