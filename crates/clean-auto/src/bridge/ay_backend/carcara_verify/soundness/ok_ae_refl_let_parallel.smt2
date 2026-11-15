(set-logic ALL)
(declare-const x Bool)
(assert (not (= (let ((a true) (b x)) (and a b)) (let ((c true) (b x)) (and c b)))))
(check-sat)
