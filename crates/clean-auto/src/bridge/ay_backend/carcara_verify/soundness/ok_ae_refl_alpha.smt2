(set-logic ALL)
(declare-const y Bool)
(assert (not (= (forall ((x Bool)) (or x y)) (forall ((w Bool)) (or w y)))))
(check-sat)
