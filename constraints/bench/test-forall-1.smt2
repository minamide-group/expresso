(declare-const x Int)
(declare-const y String)
(assert (forall ((x Int)) (= x 0)))
(check-sat)
