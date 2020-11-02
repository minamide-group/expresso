(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)
(declare-const y String)

(assert (= y (str.++ x0 "b" x1 "d" x2)))
(assert (str.in.re y (str.to.re "abcde")))
(assert (> (str.len x0) 0))
(assert (> (str.len x1) 0))
(assert (> (str.len x2) 0))

(check-sat)
(get-model)
