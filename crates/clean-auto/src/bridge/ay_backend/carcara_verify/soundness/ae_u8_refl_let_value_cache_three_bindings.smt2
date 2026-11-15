(set-logic ALL)
(declare-const a Bool)
(assert (not (= (let ((u a)) (let ((u (not u)) (w u) (k true)) (or u w))) (let ((v a)) (let ((z (not v)) (w v) (k true)) (or v w))))))
(check-sat)
