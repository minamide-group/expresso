;; Slow for both left assoc and right assoc
;; because concat (resp. replaceall) causes variable (resp. states) blow-up.
(set-logic QF_S)

(declare-const x String)
(declare-const y String)
(declare-const xy String)
(declare-const z String)

(assert (= xy (str.++ x y)))
(assert (= z (str.replaceall xy "<script>" "")))
(assert (str.in.re
         z
         (str.to.re "<script>")))

(check-sat)
(get-model)
