(set-logic ALL)
(declare-datatypes ((D 0)) (((and (aa Bool) (ab Bool)))))
(assert (not (= (and true false) (and false true))))
(check-sat)
