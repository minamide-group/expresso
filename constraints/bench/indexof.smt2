(declare-const x String)
(declare-const y String)

;; If x has substring "aab",
(assert (str.in.re x (re.++ re.all (str.to.re "aab") re.all)))
;; then substring of x from the first occurence of it
(assert (= y (str.substr x (str.indexof x "aab" 0) (str.len x))))
;; should contain "aab" as its prefix.
(assert (str.in.re y (re.comp (re.++ (str.to.re "aab") re.all))))

(check-sat) ; should be unsat

;; OSTRICH (2f3ea5c): (error "Multiple definitions found for x, input is not straightline")

;; PSST benchmark
;; 01-09 17:56:44.025 indexof - start compilation
;; 01-09 17:56:44.032 indexof - got the following PSSTs:
;; 01-09 17:56:44.032 indexof - #0: (4,2,3,13,1,3)
;; 01-09 17:56:44.032 indexof - #1: (10,1,3,23,1,5)
;; 01-09 17:56:44.032 indexof - compose (4,2,3,13,1,3) and (10,1,3,23,1,5)
;; 01-09 17:56:44.063 indexof - composition done, got PSST (29,2,6,85,4,4)
;; 01-09 17:56:44.111 indexof - checking done, UNSAT
