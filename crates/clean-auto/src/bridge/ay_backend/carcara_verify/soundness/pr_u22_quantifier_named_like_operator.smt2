(set-logic ALL)
(assert (str.in_re "a" re.all))
(assert (not (forall ((re.all RegLan)) (str.in_re "a" re.all))))
(check-sat)
