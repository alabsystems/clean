(set-logic UFLIA)
(define-fun-rec f ((x Int)) Int (+ (f x) 1))
(check-sat)
