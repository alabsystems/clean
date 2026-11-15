(set-logic ALL)
(define-fun k () Int 5)
(assert (exists ((k Int)) (not (= k 5))))
(check-sat)
