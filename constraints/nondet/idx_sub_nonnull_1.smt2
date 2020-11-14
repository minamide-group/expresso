(declare-const x String)
(declare-const y String)
(declare-const i Int)
(declare-const l Int)

(assert (= i (str.indexof x "ab" 0)))
(assert (= y (str.substr x i l)))
(assert (= l 2))
(assert (str.in.re y (re.comp (re.union (str.to.re "ab") (str.to.re "")))))

(check-sat) ; unsat
