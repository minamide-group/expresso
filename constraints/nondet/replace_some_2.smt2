(set-logic QF_S)

(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (= y (str.replace_some x "a" "ba")))
(assert (str.in.re y (re.++ re.all (str.to.re "b"))))

(check-sat) ; should be unsat
