;; for_slide と似ている
;; しかしこちらは preimage のほうが速い
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const p String)
(declare-const s String)
(declare-const l Int)

(assert (str.in.re x (re.comp (str.to.re "<script>"))))
(assert (= p (str.substr x 0 l)))
(assert (= s (str.substr x l (- (str.len x) l))))
(assert (= z (str.++ p y s)))
(assert (and (< 0 (str.len y)) (<= (str.len y) 6)))
(assert (str.in.re z (str.to.re "<script>")))

(check-sat)
(get-model)
