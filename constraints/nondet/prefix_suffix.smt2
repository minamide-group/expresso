;; This constarint cannot be solved by OSTRICH
;; The latest release of OSTRICH outputs "unknown",
;; and master branch build says it is not straight-line.
(set-logic QF_S)

(declare-const x String)
(declare-const prefix String)
(declare-const suffix String)
(declare-const y String)

;; x ∉ .*<script>.*
;; prefix suffix = x
;; y := preffix suffix (thus y == x)
;; y ∈ .*<script>.*
(assert (str.in.re x (re.comp (re.++ (re.++ re.all (str.to.re "<script>")) re.all))))
(assert (str.prefixof prefix x))
(assert (str.suffixof suffix x))
(assert (= y (str.++ prefix suffix)))
(assert (= (str.len y) (str.len x)))
(assert (str.in.re y (re.++ (re.++ re.all (str.to.re "<script>")) re.all)))

(check-sat)
