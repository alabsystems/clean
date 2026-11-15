(set-logic ALL)
(assert (not (= (forall ((u Bool)) (let ((u (not u)) (w u)) (or u w))) (forall ((v Bool)) (let ((z (not v)) (w v)) (or v w))))))
(check-sat)
