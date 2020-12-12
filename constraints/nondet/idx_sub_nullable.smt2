(declare-const x String)
(declare-const y String)

(assert (= y (str.substr x (str.indexof x "ab" 0) 2)))
(assert (str.in.re y (re.comp (str.to.re "ab"))))

(check-sat) ; sat
(get-model) ; x -> "", i -> -1, y -> ""
