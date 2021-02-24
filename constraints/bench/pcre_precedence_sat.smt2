(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (re.union (str.to.re "ab") (str.to.re "abb")))))
(assert (= y (str.replace_pcre
              x
              (pcre.+ (pcre.alt (str.to_pcre "ab") (str.to_pcre "abb")))
              (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)
(get-model)

;; PSST benchmark
;; 01-09 17:56:39.128 pcre_precedence_sat - start compilation
;; 01-09 17:56:39.150 pcre_precedence_sat - got the following PSSTs:
;; 01-09 17:56:39.150 pcre_precedence_sat - #0: (8,2,0,19,1,0)
;; 01-09 17:56:39.150 pcre_precedence_sat - #1: (7,1,0,15,1,0)
;; 01-09 17:56:39.150 pcre_precedence_sat - compose (8,2,0,19,1,0) and (7,1,0,15,1,0)
;; 01-09 17:56:39.157 pcre_precedence_sat - composition done, got PSST (8,2,0,11,1,1)
;; 01-09 17:56:39.177 pcre_precedence_sat - checking done, SAT
;; 01-09 17:56:39.196 pcre_precedence_sat - got model (Map(x -> abb, y -> b),Map())
