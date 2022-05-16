(declare-const x String)
(declare-const i Int)

(assert (forall ((ui Int)) (= ui i)))

(check-sat)
