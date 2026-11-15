(set-logic ALL)
(declare-const a Bool)
(assert (not (or (not (forall ((x Bool)) (let ((y x)) (= y x)))) (let ((y a)) (= y a)))))
(check-sat)
