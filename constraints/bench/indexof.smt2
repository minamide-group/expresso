(declare-const x String)
(declare-const y String)

;; If x has substring "aab",
(assert (str.in.re x (re.++ re.all (str.to.re "aab") re.all)))
;; then substring of x from the first occurence of it
(assert (= y (str.substr x (str.indexof x "aab" 0) (str.len x))))
;; should contain "aab" as its prefix.
(assert (str.in.re y (re.comp (re.++ (str.to.re "aab") re.all))))

(check-sat) ; should be unsat

;; Result:
;; PSST (ce07444): unsat in about 1.2 s
;; OSTRICH (2f3ea5c): (error "Multiple definitions found for x, input is not straightline")
