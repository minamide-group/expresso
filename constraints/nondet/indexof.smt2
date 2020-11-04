;; i := indexof x "aa" (leftmost semantics)
;; suffixof y x
;; (len y) == (len x) - i
;; y ∉ aa.*
(declare-const x String)
(declare-const y String)
(declare-const i Int)

;; (assert (= i (str.indexof x "aa"))) can be encoded as follows:
(declare-const t String)
;; Helper function `str.until_first' returns longet prefix of `x' that excludes leftmost "aa".
;; If `x' does not contain "aa", then `t' will be `x' followed by additional one character.
(assert (= t (str.until_first x "aa")))
(assert (or (and (<= (str.len t) (str.len x)) (= i (str.len t)))
            (and (> (str.len t) (str.len x)) (= i (- 1)))))

(assert (str.suffixof y x))
(assert (= (str.len y) (- (str.len x) i)))
(assert (str.in.re y (re.comp (re.++ (str.to.re "aa") re.all))))

(check-sat) ; should be unsat
