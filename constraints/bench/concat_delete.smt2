;; 連接してから replaceall
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
