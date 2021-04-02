(declare-const x String)
(declare-const y String)

(assert (= y (str.substr x (str.indexof x "aab" 0) (str.len x))))
(assert (str.in.re y (re.comp (re.++ (str.to.re "aab") re.all))))

(check-sat) ; should be sat
(get-model)

;; OSTRICH (2f3ea5c): (error "Multiple definitions found for x, input is not straightline")
