(declare-const x String)
(declare-const y String)
(declare-const i Int)

(assert (str.in.re x (re.++ re.all (str.to.re "ab") re.all)))
(assert (= i (str.indexof x "ab")))
(assert (= y (str.substr x i 2)))
(assert (str.in.re y (re.comp (str.to.re "ab"))))

(check-sat) ; unsat
