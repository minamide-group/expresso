(set-logic QF_S)

(declare-const x String)
(declare-const prefix String)
(declare-const suffix String)
(declare-const y String)

(assert (= prefix (str.take_prefix x)))
(assert (= suffix (str.take_suffix x)))
(assert (= y (str.++ prefix suffix)))

(assert (str.in.re x (re.comp (re.++ (re.++ re.all (str.to.re "<script>")) re.all))))
(assert (str.in.re y (re.++ (re.++ re.all (str.to.re "<script>")) re.all)))

(assert (= (str.len y) (str.len x)))

(check-sat)
