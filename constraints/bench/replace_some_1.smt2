(set-logic QF_S)

(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.+ (str.to.re "a"))))
(assert (= y (str.replace_some x "a" "b")))
(assert (str.in.re y (re.+ (str.to.re "ab"))))

(check-sat) ; should be sat
(get-model)
