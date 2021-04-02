;; substr 3 回 + 等価性
(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)
(declare-const y String)
(declare-const i Int)
(declare-const l Int)

(assert (= y (str.substr x0 i l)))
(assert (= x1 (str.substr x0 i (- (str.len x0) i))))
(assert (= x2 (str.substr x1 0 l)))
(assert (not (= x2 y)))
(check-sat)
