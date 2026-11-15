(set-logic ALL)

(assert (not (= (bvult #b10 (_ bv5 2)) true)))
(check-sat)
