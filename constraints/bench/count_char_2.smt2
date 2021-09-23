(declare-const x String)

(assert (= (str.count_char x "a") 5))
(assert (= (str.count_char x "b") 5))
(assert (= (str.len x) 10))
(assert (str.in.re x
          (re.++ (re.* (str.to.re "a"))
                 (re.* (str.to.re "b")))))

(check-sat)
(get-model)