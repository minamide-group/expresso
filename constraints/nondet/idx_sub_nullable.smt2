(declare-const x String)
(declare-const y String)
(declare-const i Int)
(declare-const l Int)

(assert (= i (str.indexof x "ab" 0)))
(assert (= y (str.substr x i l)))
(assert (= l 2))
(assert (str.in.re y (re.comp (str.to.re "ab"))))

(check-sat) ; sat
(get-model) ; x -> "", i -> -1, y -> ""
