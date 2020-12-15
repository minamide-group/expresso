(declare-const x String)
(declare-const y String)
(declare-const i Int)

;; If x has substring "aa",
(assert (str.in.re x (re.++ re.all (str.to.re "aa") re.all)))
;; then substring of x from the first occurence of it
(assert (= y (str.substr x (str.indexof x "aa" 0) (str.len x))))
;; should contain "aa" as its prefix.
(assert (str.in.re y (re.comp (re.++ (str.to.re "aa") re.all))))

(check-sat) ; should be unsat

;; Result:
;; PSST (ce07444): unsat in about 700 ms
;; OSTRICH (2f3ea5c): (error "Multiple definitions found for x, input is not straightline")
