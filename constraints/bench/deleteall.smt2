;; <sc>
;; DSST: 4.22 secs
;; <script>
;; DSST: 247.60 secs 変数減らしたらもう少し速かった気がする
;; NSST: 2.52 secs
(declare-const x0 String)
(declare-const x1 String)
(declare-const y0 String)
(declare-const y1 String)
(declare-const xy String)

(assert (= x1 (str.replaceall x0 "<script>" "")))
(assert (= y1 (str.replaceall y0 "<script>" "")))
(assert (= xy (str.++ x1 y1)))
(assert (str.in.re xy (str.to.re "<script>")))

(check-sat)
(get-model)

;; PSST benchmark
;; 01-09 17:56:24.371 deleteall - start compilation
;; 01-09 17:56:24.617 deleteall - got the following PSSTs:
;; 01-09 17:56:24.619 deleteall - #0: (10,2,0,99,1,0)
;; 01-09 17:56:24.620 deleteall - #1: (11,2,0,110,1,0)
;; 01-09 17:56:24.621 deleteall - #2: (5,3,0,44,1,0)
;; 01-09 17:56:24.621 deleteall - #3: (15,1,0,145,1,0)
;; 01-09 17:56:24.621 deleteall - compose (10,2,0,99,1,0) and (11,2,0,110,1,0)
;; 01-09 17:56:24.925 deleteall - compose (19,3,0,198,1,1) and (5,3,0,44,1,0)
;; 01-09 17:56:25.058 deleteall - compose (19,5,0,198,1,2) and (15,1,0,145,1,0)
;; 01-09 17:56:25.785 deleteall - composition done, got PSST (443,5,0,559,9,3)
;; 01-09 17:56:26.054 deleteall - checking done, SAT
;; 01-09 17:56:26.312 deleteall - got model (HashMap(y0 -> ipt>, xy -> <script>, x0 -> <scr, y1 -> ipt>, x1 -> <scr),Map())


;; DSST benchmark
;; SST number: 4
;; SST List:
;; Q: 10,  X: 2, Delta: 81, Eta: 81
;; Q: 11,  X: 2, Delta: 90, Eta: 90
;; Q: 5,  X: 3, Delta: 36, Eta: 36
;; Q: 14,  X: 1, Delta: 45, Eta: 45
;; Start Composition of SSTs:
;;     Q: 10,  X: 2, Delta: 81, Eta: 81
;;     Q: 11,  X: 2, Delta: 90, Eta: 90
;;     Start Composition to Monoid SST:
;;         00:28:00
;;             Find s0     : 00:28:00
;;             Find states : 00:28:00
;;                 Q     : 562
;;                 Delta : 4788
;;             Find vars   : 00:28:01
;;             Find f1     : 00:28:01
;;             Find f2     : 00:28:01
;;             Trim states : 00:28:01
;;                 Q     : 562
;;                 Delta : 4788
;;             Find eta    : 00:28:01
;;     End Composition to Monoid SST:
;;         00:28:01
;;         Q: 562,  X: 22, Delta: 4788, Eta: 4788
;;     Start Trim Vars of Monoid SST:
;;         00:28:01
;;     End Trim Vars of Monoid SST:
;;         00:28:01
;;         Q: 562,  X: 2, Delta: 4788, Eta: 4788
;;     Start Conversion to SST:
;;         00:28:01
;;             Find s0     : 00:28:01
;;             Find states : 00:28:01
;;                 Q     : 562
;;                 Delta : 4788
;;             Find vars   : 00:28:02
;;             Find f      : 00:28:02
;;             Find delta  : 00:28:02
;;             Trim states : 00:28:02
;;                 Q     : 562
;;                 Delta : 4788
;;             Find eta    : 00:28:02
;;     End Conversion to SST:
;;         00:28:02
;;         Q: 562,  X: 8, Delta: 4788, Eta: 4788
;;     Start Trim Vars of SST:
;;         00:28:02
;;     End Trim Vars of SST:
;;         00:28:02
;;         Q: 562,  X: 3, Delta: 4788, Eta: 4788
;; End Composition SST. The result is:
;;     Q: 562,  X: 3, Delta: 4788, Eta: 4788
;;     time : 2.086s
;; Start Composition of SSTs:
;;     Q: 562,  X: 3, Delta: 4788, Eta: 4788
;;     Q: 5,  X: 3, Delta: 36, Eta: 36
;;     Start Composition to Monoid SST:
;;         00:28:02
;;             Find s0     : 00:28:02
;;             Find states : 00:28:02
;;                 Q     : 832
;;                 Delta : 6948
;;             Find vars   : 00:28:03
;;             Find f1     : 00:28:03
;;             Find f2     : 00:28:03
;;             Trim states : 00:28:03
;;                 Q     : 832
;;                 Delta : 6948
;;             Find eta    : 00:28:03
;;     End Composition to Monoid SST:
;;         00:28:03
;;         Q: 832,  X: 15, Delta: 6948, Eta: 6948
;;     Start Trim Vars of Monoid SST:
;;         00:28:03
;;     End Trim Vars of Monoid SST:
;;         00:28:03
;;         Q: 832,  X: 3, Delta: 6948, Eta: 6948
;;     Start Conversion to SST:
;;         00:28:03
;;             Find s0     : 00:28:03
;;             Find states : 00:28:03
;;                 Q     : 832
;;                 Delta : 6948
;;             Find vars   : 00:28:04
;;             Find f      : 00:28:04
;;             Find delta  : 00:28:04
;;             Trim states : 00:28:04
;;                 Q     : 832
;;                 Delta : 6948
;;             Find eta    : 00:28:04
;;     End Conversion to SST:
;;         00:28:05
;;         Q: 832,  X: 18, Delta: 6948, Eta: 6948
;;     Start Trim Vars of SST:
;;         00:28:05
;;     End Trim Vars of SST:
;;         00:28:05
;;         Q: 832,  X: 5, Delta: 6948, Eta: 6948
;; End Composition SST. The result is:
;;     Q: 832,  X: 5, Delta: 6948, Eta: 6948
;;     time : 3.108s
;; Start Composition of SSTs:
;;     Q: 832,  X: 5, Delta: 6948, Eta: 6948
;;     Q: 14,  X: 1, Delta: 45, Eta: 45
;;     Start Composition to Monoid SST:
;;         00:28:05
;;             Find s0     : 00:28:05
;;             Find states : 00:28:05
;;                 Q     : 16246
;;                 Delta : 130419
;;             Find vars   : 00:28:13
;;             Find f1     : 00:28:13
;;             Find f2     : 00:28:13
;;             Trim states : 00:28:13
;;                 Q     : 534
;;                 Delta : 644
;;             Find eta    : 00:28:46
;;     End Composition to Monoid SST:
;;         00:28:46
;;         Q: 534,  X: 70, Delta: 644, Eta: 644
;;     Start Trim Vars of Monoid SST:
;;         00:28:46
;;     End Trim Vars of Monoid SST:
;;         00:28:46
;;         Q: 534,  X: 12, Delta: 644, Eta: 644
;;     Start Conversion to SST:
;;         00:28:46
;;             Find s0     : 00:28:46
;;             Find states : 00:28:46
;;                 Q     : 534
;;                 Delta : 644
;;             Find vars   : 00:28:46
;;             Find f      : 00:28:46
;;             Find delta  : 00:28:46
;;             Trim states : 00:28:46
;;                 Q     : 534
;;                 Delta : 644
;;             Find eta    : 00:28:46
;;     End Conversion to SST:
;;         00:28:46
;;         Q: 534,  X: 24, Delta: 644, Eta: 644
;;     Start Trim Vars of SST:
;;         00:28:46
;;     End Trim Vars of SST:
;;         00:28:46
;;         Q: 534,  X: 12, Delta: 644, Eta: 644
;; End Composition SST. The result is:
;;     Q: 534,  X: 12, Delta: 644, Eta: 644
;;     time : 40.862s
;; sat
;; (model
;;   (define-fun x0 () String
;;     "<scr")
;;   (define-fun y0 () String
;;     "ipt>")
;;   (define-fun x1 () String
;;     "<scr")
;;   (define-fun y1 () String
;;     "ipt>")
;;   (define-fun xy () String
;;     "<script>")
;; )


;; Nondeterministic checker benchmark
;; ## SOLVER LEFT FOLDING FINISHED
;; ---
;; Composition ingredients:
;;  1:      NsstSummary(11,2,91,1,1,1)
;;  2:      NsstSummary(11,2,100,1,1,1)
;; Composition took 390 ms
;; Detailed elapsed time:
;;  Backward state exploration      311 ms
;;  Removing unreachable    0 ms
;;  MSST construction (overall)     315 ms
;;  NSST construction (overall)     361 ms
;;  Removing redundant variables    28 ms
;; Sizes of intermidiate products:
;;  States  17 -> 17 (1.0)
;; Resulting SST:   NsstSummary(18,3,170,1,1,1)
;; ---
;; Composition ingredients:
;;  1:      NsstSummary(18,3,170,1,1,1)
;;  2:      NsstSummary(5,3,40,1,1,1)
;; Composition took 102 ms
;; Detailed elapsed time:
;;  Backward state exploration      45 ms
;;  Removing unreachable    1 ms
;;  MSST construction (overall)     48 ms
;;  NSST construction (overall)     85 ms
;;  Removing redundant variables    17 ms
;; Sizes of intermidiate products:
;;  States  18 -> 18 (1.0)
;; Resulting SST:   NsstSummary(18,5,170,1,1,1)
;; ---
;; Composition ingredients:
;;  1:      NsstSummary(18,5,170,1,1,1)
;;  2:      NsstSummary(15,1,131,1,1,1)
;; Composition took 816 ms
;; Detailed elapsed time:
;;  Backward state exploration      572 ms
;;  Removing unreachable    5 ms
;;  MSST construction (overall)     583 ms
;;  NSST construction (overall)     719 ms
;;  Removing redundant variables    97 ms
;; Sizes of intermidiate products:
;;  States  442 -> 442 (1.0)
;; Resulting SST:   NsstSummary(442,5,557,1,9,1)
;; sat
;; (model
;;   (define-fun y0 () String "script>")
;;   (define-fun xy () String "<script>")
;;   (define-fun x0 () String "<")
;;   (define-fun y1 () String "script>")
;;   (define-fun x1 () String "<")
