(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)
(declare-const x3 String)
(assert (= x1 (str.++ x0 x0)))
(assert (= x2 (str.++ x1 x1)))
(assert (= x3 (str.++ x2 x2)))
(assert (str.in.re x1 (re.+ (str.to.re "ab"))))
(assert (str.in.re x3 (re.+ (str.to.re "aa"))))
(check-sat)

;; PSST benchmark
;; 01-09 17:56:26.328 concat_unsat_03 - start compilation
;; 01-09 17:56:26.337 concat_unsat_03 - got the following PSSTs:
;; 01-09 17:56:26.337 concat_unsat_03 - #0: (2,3,0,3,1,0)
;; 01-09 17:56:26.338 concat_unsat_03 - #1: (3,3,0,6,1,0)
;; 01-09 17:56:26.338 concat_unsat_03 - #2: (4,3,0,9,1,0)
;; 01-09 17:56:26.338 concat_unsat_03 - #3: (11,1,0,24,1,0)
;; 01-09 17:56:26.338 concat_unsat_03 - compose (2,3,0,3,1,0) and (3,3,0,6,1,0)
;; 01-09 17:56:26.344 concat_unsat_03 - compose (4,7,0,9,1,1) and (4,3,0,9,1,0)
;; 01-09 17:56:26.354 concat_unsat_03 - compose (4,15,0,9,1,2) and (11,1,0,24,1,0)
;; 01-09 17:56:26.537 concat_unsat_03 - composition done, got PSST (1,0,0,0,0,3)
;; 01-09 17:56:26.550 concat_unsat_03 - checking done, UNSAT

;; DSST benchmark
;; SST number: 4
;; SST List:
;; Q: 2,  X: 1, Delta: 3, Eta: 3
;; Q: 5,  X: 2, Delta: 7, Eta: 7
;; Q: 4,  X: 3, Delta: 9, Eta: 9
;; Q: 7,  X: 4, Delta: 13, Eta: 13

;; Start Composition of SSTs:
;;     Q: 2,  X: 1, Delta: 3, Eta: 3
;;     Q: 5,  X: 2, Delta: 7, Eta: 7

;;     Start Composition to Monoid SST:
;;         21:31:54
;;             Find s0     : 21:31:54
;;             Find states : 21:31:54
;;                 Q     : 12
;;                 Delta : 18
;;             Find vars   : 21:31:54
;;             Find f1     : 21:31:54
;;             Find f2     : 21:31:54
;;             Trim states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find eta    : 21:31:54
;;     End Composition to Monoid SST:
;;         21:31:54
;;         Q: 4,  X: 5, Delta: 4, Eta: 4

;;     Start Trim Vars of Monoid SST:
;;         21:31:54
;;     End Trim Vars of Monoid SST:
;;         21:31:54
;;         Q: 4,  X: 3, Delta: 4, Eta: 4

;;     Start Conversion to SST:
;;         21:31:54
;;             Find s0     : 21:31:54
;;             Find states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find vars   : 21:31:54
;;             Find f      : 21:31:54
;;             Find delta  : 21:31:54
;;             Trim states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find eta    : 21:31:54
;;     End Conversion to SST:
;;         21:31:54
;;         Q: 4,  X: 12, Delta: 4, Eta: 4

;;     Start Trim Vars of SST:
;;         21:31:54
;;     End Trim Vars of SST:
;;         21:31:54
;;         Q: 4,  X: 3, Delta: 4, Eta: 4
;; End Composition SST. The result is:
;;     Q: 4,  X: 3, Delta: 4, Eta: 4
;;     time : 0.108s

;; Start Composition of SSTs:
;;     Q: 4,  X: 3, Delta: 4, Eta: 4
;;     Q: 4,  X: 3, Delta: 9, Eta: 9

;;     Start Composition to Monoid SST:
;;         21:31:54
;;             Find s0     : 21:31:54
;;             Find states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find vars   : 21:31:54
;;             Find f1     : 21:31:54
;;             Find f2     : 21:31:54
;;             Trim states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find eta    : 21:31:54
;;     End Composition to Monoid SST:
;;         21:31:54
;;         Q: 4,  X: 12, Delta: 4, Eta: 4

;;     Start Trim Vars of Monoid SST:
;;         21:31:54
;;     End Trim Vars of Monoid SST:
;;         21:31:54
;;         Q: 4,  X: 5, Delta: 4, Eta: 4

;;     Start Conversion to SST:
;;         21:31:54
;;             Find s0     : 21:31:54
;;             Find states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find vars   : 21:31:54
;;             Find f      : 21:31:54
;;             Find delta  : 21:31:54
;;             Trim states : 21:31:54
;;                 Q     : 4
;;                 Delta : 4
;;             Find eta    : 21:31:54
;;     End Conversion to SST:
;;         21:31:54
;;         Q: 4,  X: 30, Delta: 4, Eta: 4

;;     Start Trim Vars of SST:
;;         21:31:54
;;     End Trim Vars of SST:
;;         21:31:54
;;         Q: 4,  X: 5, Delta: 4, Eta: 4
;; End Composition SST. The result is:
;;     Q: 4,  X: 5, Delta: 4, Eta: 4
;;     time : 0.027s

;; Start Composition of SSTs:
;;     Q: 4,  X: 5, Delta: 4, Eta: 4
;;     Q: 7,  X: 4, Delta: 13, Eta: 13

;;     Start Composition to Monoid SST:
;;         21:31:54
;;             Find s0     : 21:31:54
;;             Find states : 21:31:54
;;                 Q     : 5
;;                 Delta : 5
;;             Find vars   : 21:31:54
;;             Find f1     : 21:31:54
;;             Find f2     : 21:31:54
;;             Trim states : 21:31:54
;;                 Q     : 0
;;                 Delta : 0
;;             Find eta    : 21:31:54
;;     End Composition to Monoid SST:
;;         21:31:54
;;         Q: 0,  X: 35, Delta: 0, Eta: 0

;;     Start Trim Vars of Monoid SST:
;;         21:31:54
;;     End Trim Vars of Monoid SST:
;;         21:31:54
;;         Q: 0,  X: 0, Delta: 0, Eta: 0

;;     Start Conversion to SST:
;;         21:31:54
;;             Find s0     : 21:31:54
;;             Find states : 21:31:54
;;                 Q     : 1
;;                 Delta : 0
;;             Find vars   : 21:31:54
;;             Find f      : 21:31:54
;;             Find delta  : 21:31:54
;;             Trim states : 21:31:54
;;                 Q     : 0
;;                 Delta : 0
;;             Find eta    : 21:31:54
;;     End Conversion to SST:
;;         21:31:54
;;         Q: 0,  X: 0, Delta: 0, Eta: 0

;;     Start Trim Vars of SST:
;;         21:31:54
;;     End Trim Vars of SST:
;;         21:31:54
;;         Q: 0,  X: 0, Delta: 0, Eta: 0
;; End Composition SST. The result is:
;;     Q: 0,  X: 0, Delta: 0, Eta: 0
;;     time : 0.007s

;; unsat

;; ________________________________________________________
;; Executed in  785.99 millis    fish           external
;;    usr time  1246.53 millis  613.00 micros  1245.91 millis
;;    sys time  113.26 millis  108.00 micros  113.16 millis
