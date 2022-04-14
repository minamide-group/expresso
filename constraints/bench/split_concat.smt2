(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(declare-const i Int)

(assert (= y (str.substr x 0 i)))
(assert (= z (str.substr x i (- (str.len x) i))))
(assert (= w (str.++ y z)))

(assert (not (= x w)))

(check-sat)
(get-model)
