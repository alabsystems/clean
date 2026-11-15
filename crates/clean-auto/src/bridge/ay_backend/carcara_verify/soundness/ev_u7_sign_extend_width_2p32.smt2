(set-logic ALL)
(assert (not (= (= ((_ sign_extend 4294967295) #b1) ((_ sign_extend 4294967295) #b0)) true)))
(check-sat)
