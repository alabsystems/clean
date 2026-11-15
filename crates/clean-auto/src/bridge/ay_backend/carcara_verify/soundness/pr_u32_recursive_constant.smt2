(set-logic QF_UFLIA)
(define-fun-rec c () Int (+ c 1))
(check-sat)
