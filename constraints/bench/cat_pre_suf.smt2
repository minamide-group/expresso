;; プレフィックスとサフィックスに分解して連接したら元に戻る
(declare-const x String)
(declare-const p String)
(declare-const s String)
(declare-const y String)
(declare-const i Int)

(assert (and (<= 0 i) (< i (str.len x))))
(assert (= p (str.substr x 0 i)))
(assert (= s (str.substr x i (str.len x))))
(assert (= y (str.++ p s)))
(assert (not (= x y)))
(check-sat)
