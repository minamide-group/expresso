;; Longer string has a prefix with the same length as shorter one.
(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (<= (str.len x) (str.len y)))
(assert (= z (str.substr y 0 (str.len x))))
(assert (not (= (str.len z) (str.len x))))
(check-sat)
