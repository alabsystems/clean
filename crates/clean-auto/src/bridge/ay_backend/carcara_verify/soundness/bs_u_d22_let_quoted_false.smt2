(set-logic ALL)
(assert (let ((|false| true)) |false|))
(check-sat)
