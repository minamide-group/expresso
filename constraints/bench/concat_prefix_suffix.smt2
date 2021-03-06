;; cat_pre_suf.smt2 と似ているが，x が具体的でアルファベットが大きい
(declare-const x String)
(declare-const p String)
(declare-const s String)
(declare-const y String)
(declare-const i Int)

(assert (str.in.re x (str.to.re "<script>")))
(assert (and (<= 0 i) (< i (str.len x))))
(assert (= p (str.substr x 0 i)))
(assert (= s (str.substr x i (str.len x))))
(assert (= y (str.++ p s)))
(assert (str.in.re y (re.comp (str.to.re "<script>"))))
(check-sat)
