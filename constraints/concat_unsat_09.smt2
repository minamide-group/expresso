(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)
(declare-const x3 String)
(declare-const x4 String)
(declare-const x5 String)
(declare-const x6 String)
(declare-const x7 String)
(declare-const x8 String)
(declare-const x9 String)
(assert (= x1 (str.++ x0 x0)))
(assert (= x2 (str.++ x1 x1)))
(assert (= x3 (str.++ x2 x2)))
(assert (= x4 (str.++ x3 x3)))
(assert (= x5 (str.++ x4 x4)))
(assert (= x6 (str.++ x5 x5)))
(assert (= x7 (str.++ x6 x6)))
(assert (= x8 (str.++ x7 x7)))
(assert (= x9 (str.++ x8 x8)))
(assert (str.in.re x1 (re.+ (str.to.re "ab"))))
(assert (str.in.re x9 (re.+ (str.to.re "aa"))))
(check-sat)
