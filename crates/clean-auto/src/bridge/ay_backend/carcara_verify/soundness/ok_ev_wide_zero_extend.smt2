(set-logic ALL)
(assert (not (= (= ((_ zero_extend 4095) #b1) ((_ zero_extend 4095) #b0)) false)))
(check-sat)
