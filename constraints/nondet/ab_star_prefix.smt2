(set-logic QF_S)

(declare-const x String)
(declare-const y String)

;; x ∈ (ab)*
;; y w = x for some w
;; y ∉ (ab)*|((ab)*a)
(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (str.prefixof y x))
(assert (str.in.re y (re.comp (re.union
                               (re.* (str.to.re "ab"))
                               (re.++ (re.* (str.to.re "ab")) (str.to.re "a"))))))

(check-sat) ; unsat
