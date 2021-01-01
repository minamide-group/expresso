(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (= z (str.substr x 0 (str.len y))))
(assert (not (= (str.len z) (str.len x))))
(check-sat)
(get-model)
