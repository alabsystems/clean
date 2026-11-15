(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(check-sat-assuming ((not p)))
