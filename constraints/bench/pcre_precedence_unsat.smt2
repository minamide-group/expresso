(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (re.union (str.to.re "ab") (str.to.re "abb")))))
(assert (= y (str.replace_pcre
              x
              (pcre.+ (pcre.alt (str.to_pcre "abb") (str.to_pcre "ab")))
              (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)

;; PSST benchmark
;; 01-09 22:35:04.225 pcre_precedence_unsat - start compilation
;; 01-09 22:35:04.245 pcre_precedence_unsat - got the following PSSTs:
;; 01-09 22:35:04.245 pcre_precedence_unsat - #0: (14,2,0,36,1,0)
;; 01-09 22:35:04.245 pcre_precedence_unsat - #1: (7,1,0,15,1,0)
;; 01-09 22:35:04.245 pcre_precedence_unsat - compose (14,2,0,36,1,0) and (7,1,0,15,1,0)
;; 01-09 22:35:04.255 pcre_precedence_unsat - composition done, got PSST (1,0,0,0,0,1)
;; 01-09 22:35:04.272 pcre_precedence_unsat - checking done, UNSAT
