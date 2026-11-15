(set-logic UFLIA)
(define-funs-rec ((f ((n Int)) Int) (g ((n Int)) Int)) ((+ (g n) 1) (f n)))
(check-sat)
