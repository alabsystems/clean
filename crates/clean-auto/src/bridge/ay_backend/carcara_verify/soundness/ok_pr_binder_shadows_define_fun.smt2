(set-logic ALL)
(define-fun k () Int 5)
(assert (forall ((k Int)) (= k 5)))
(check-sat)
