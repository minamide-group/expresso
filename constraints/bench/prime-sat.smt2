(declare-const x String)
(declare-const l Int)

;; length of x is prime
(assert (forall ((i Int)) (=> (and (> i 1) (< i l)) (> (mod l i) 0))))
(assert (= (str.len x) l))
(assert (> l 7))

(assert (str.in.re x (re.++ (re.+ (str.to.re "ab")) (str.to.re "a"))))

(check-sat)
(get-model)
