(declare-const x String)
(declare-const y String)

(assert (= y (str.substr x (str.indexof x "ab" 0) 2)))
(assert (str.in.re y (re.comp (re.union (str.to.re "ab") (str.to.re "")))))

(check-sat) ; unsat
