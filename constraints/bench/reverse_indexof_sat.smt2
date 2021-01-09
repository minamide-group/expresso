(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.++ (re.* (str.to.re "b")) (re.* (str.to.re "a")))))
(assert (= y (str.reverse x)))

(assert (not (< (str.indexof y "a" 0) (str.indexof y "b" 0))))

(check-sat)
(get-model)
