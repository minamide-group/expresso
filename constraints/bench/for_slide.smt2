;; 卒論発表用に用意したもの
;; (ab)* に (ab)* を insert した結果が (ab)* とは限らない
(declare-const x String)
(declare-const p String)
(declare-const s String)
(declare-const y String)
(declare-const z String)
(declare-const i Int)
(declare-const j Int)

(assert (str.in.re x (re.* (re.++ (str.to.re "a") (str.to.re "b")))))
(assert (str.in.re y (re.* (re.++ (str.to.re "a") (str.to.re "b")))))
(assert (= j i))
(assert (= p (str.substr x 0 j)))
(assert (= s (str.substr x j (- (str.len x) j))))
(assert (= z (str.++ p y s)))
(assert (str.in.re z (re.comp (re.* (re.++ (str.to.re "a") (str.to.re "b"))))))

(check-sat)
(get-model)
