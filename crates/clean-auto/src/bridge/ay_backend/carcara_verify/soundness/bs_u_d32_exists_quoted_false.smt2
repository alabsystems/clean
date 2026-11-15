(set-logic ALL)
(assert (exists ((|false| Bool)) |false|))
(check-sat)
