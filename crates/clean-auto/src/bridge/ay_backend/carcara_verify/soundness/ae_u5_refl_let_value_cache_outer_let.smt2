(set-logic ALL)
(declare-const p Bool)
(assert (not (= (let ((u p)) (let ((u (not u)) (w u)) (or u w))) (let ((v p)) (let ((z (not v)) (w v)) (or v w))))))
(check-sat)
