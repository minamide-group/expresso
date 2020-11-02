;; SST: 104.40 secs
;; NSST: 2.84 secs, 91 -> 175 -> 183 states
(declare-const x0 String)
(declare-const x1 String)
(declare-const y0 String)
(declare-const y1 String)
(declare-const xy String)

(assert (= x1 (str.replaceall x0 "<script>" "a")))
(assert (= y1 (str.replaceall y0 "<script>" "a")))
(assert (= xy (str.++ x1 y1)))
(assert (str.in.re xy (str.to.re "a<script>a")))

(check-sat)
(get-model)
