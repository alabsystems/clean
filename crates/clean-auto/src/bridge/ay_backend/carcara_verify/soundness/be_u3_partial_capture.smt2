(set-logic ALL)
(declare-const y Int)
(assert (not (= ((lambda ((z Int) (y Int)) (+ z y)) y) (lambda ((y Int)) (+ y y)))))
(check-sat)
