(set-logic ALL)

(assert (not (= (= (_ bv5 2) #b01) true)))
(check-sat)
