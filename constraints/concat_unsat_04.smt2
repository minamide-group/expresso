(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)
(declare-const x3 String)
(declare-const x4 String)
(assert (= x1 (str.++ x0 x0)))
(assert (= x2 (str.++ x1 x1)))
(assert (= x3 (str.++ x2 x2)))
(assert (= x4 (str.++ x3 x3)))
(assert (str.in.re x1 (re.+ (str.to.re "ab"))))
(assert (str.in.re x4 (re.+ (str.to.re "aa"))))
(check-sat)
(get-model)
