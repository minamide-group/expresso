(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.++ re.all (str.to.re "ab") re.all)))
(assert (= y (str.substr x (str.indexof x "ab" 0) 2)))
(assert (str.in.re y (re.comp (str.to.re "ab"))))

(check-sat) ; unsat
