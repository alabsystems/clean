(set-logic ALL)
(declare-const x Int)
(assert (! (= x 1) :named ite))
(check-sat)
