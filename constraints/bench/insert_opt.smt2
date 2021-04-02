;; for_slide.smt2 と等価だが insert を使う
;; str.insert は SMT-LIB にはない
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const i Int)

(assert (str.in.re x (re.* (re.++ (str.to.re "a") (str.to.re "b")))))
(assert (str.in.re y (re.* (re.++ (str.to.re "a") (str.to.re "b")))))
(assert (= z (str.insert x y i)))       ; x を y の位置 i に挿入
(assert (str.in.re z (re.comp (re.* (re.++ (str.to.re "a") (str.to.re "b"))))))

(check-sat)
(get-model)
