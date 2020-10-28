;; <sc>
;; DSST: 4.22 secs
;; NSST: 1.33 secs, 28/28 -> 83/82 -> 141/126
;; <script>
;; DSST: 247.60 secs
;; NSST: 16.06 secs, 66/66 -> 417/416 -> 775/730 states
(declare-const x0 String)
(declare-const x1 String)
(declare-const y0 String)
(declare-const y1 String)
(declare-const xy String)

(assert (= x1 (str.replaceall x0 "<script>" "")))
(assert (= y1 (str.replaceall y0 "<script>" "")))
(assert (= xy (str.++ x1 y1)))
(assert (str.in.re xy (str.to.re "<script>")))

(check-sat)
(get-model)
