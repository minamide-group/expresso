(declare-const x String)

(assert (forall ((i Int)) (=> (< i 3) (< i (str.len x)))))
(assert (forall ((i Int)) (=> (> i 3) (> i (str.len x)))))
;; (assert (forall ((i Int)) (= (str.code_at x (+ i 1)) 97))) ; should raise an exception

(assert (str.in.re x (re.+ (str.to.re "a"))))

(check-sat)
(get-model)
