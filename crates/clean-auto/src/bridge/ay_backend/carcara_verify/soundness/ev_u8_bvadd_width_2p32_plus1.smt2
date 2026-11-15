(set-logic ALL)
(assert (not (= (= (bvadd (concat ((_ sign_extend 4294967295) #b0) #b1) (concat ((_ sign_extend 4294967295) #b0) #b1)) (concat ((_ sign_extend 4294967295) #b0) #b0)) true)))
(check-sat)
