;; Solvable in around 9 s
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

;; sat
;; (model
;;  (define-fun x () String "<ipt>")
;;  (define-fun y () String "scr")
;;  (define-fun z () String "<script>")
;;  (define-fun p () String "<")
;;  (define-fun s () String "ipt>")
;;  (define-fun i () Int 0)
;;  (define-fun l () Int 1)
;;  (define-fun n () Int 4)
;;  (define-fun .s0 () String "<")
;;  (define-fun .s1 () String "")
;;  )
