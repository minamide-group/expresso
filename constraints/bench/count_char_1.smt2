(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const i Int)

(assert (= y (str.substr x 0 i)))
(assert (= z (str.substr x i (- (str.len x) i))))
(assert (<= 0 i))
(assert (< i (str.len x)))
(assert (not
         (= (str.count_char x "a")
              (+ (str.count_char y "a")
                 (str.count_char z "a")))))

(check-sat)