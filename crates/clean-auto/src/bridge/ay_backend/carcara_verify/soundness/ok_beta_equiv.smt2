(set-logic ALL)
(declare-const y Int)
(assert (not (= ((lambda ((z Int) (w Int)) (+ z w)) y) (lambda ((w Int)) (+ y w)))))
(check-sat)
