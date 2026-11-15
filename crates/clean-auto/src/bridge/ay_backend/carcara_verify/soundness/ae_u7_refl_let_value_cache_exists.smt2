(set-logic ALL)
(assert (not (= (exists ((u Bool)) (let ((u (not u)) (w u)) (and u w))) (exists ((v Bool)) (let ((z (not v)) (w v)) (and v w))))))
(check-sat)
