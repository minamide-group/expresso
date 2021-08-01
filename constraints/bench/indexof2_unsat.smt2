(declare-const x String)
(declare-const y String)
(declare-const i Int)

(assert (str.in.re x (re.++ (str.to.re "aab") re.all)))
(assert (= i (str.indexof x "aab" 0)))
(assert (= y (str.substr x i (- (str.len x) i))))
(assert (str.in.re y (re.comp (re.++ (str.to.re "aab") re.all))))

(check-sat)

;; OSTRICH (824cec8): (error "Internal exception: java.lang.Exception: Multiple definitions found for x, input is not straightline")
