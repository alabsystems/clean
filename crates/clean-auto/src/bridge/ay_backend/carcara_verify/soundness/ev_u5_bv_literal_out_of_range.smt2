(set-logic ALL)

(assert (not (= (= (_ bv5 2) #b01) false)))
(check-sat)
