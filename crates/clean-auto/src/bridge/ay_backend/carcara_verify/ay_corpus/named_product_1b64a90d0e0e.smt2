(set-logic QF_BV)
(declare-const sa_v82 (_ BitVec 64))
(assert (not (= (bvmul sa_v82 (_ bv1 64)) sa_v82)))
(check-sat)
