(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (str.in.re x (re.* (re.union (str.to.re "a") (str.to.re "b")))))
(assert (= y (str.replaceall x "ab" "c")))
(assert (= z (str.replaceall y "ac" "aaaa")))
(assert (<= (+ (str.len x) 5) (str.len z)))
(check-sat)
(get-model)

;; PSST benchmark
;; 01-09 17:56:38.724 replaceall_int - start compilation
;; 01-09 17:56:38.732 replaceall_int - got the following PSSTs:
;; 01-09 17:56:38.732 replaceall_int - #0: (3,2,0,8,1,0)
;; 01-09 17:56:38.733 replaceall_int - #1: (4,2,0,12,1,0)
;; 01-09 17:56:38.733 replaceall_int - #2: (5,1,2,15,1,3)
;; 01-09 17:56:38.733 replaceall_int - compose (3,2,0,8,1,0) and (4,2,0,12,1,0)
;; 01-09 17:56:38.739 replaceall_int - compose (7,3,0,20,2,1) and (5,1,2,15,1,3)
;; 01-09 17:56:38.755 replaceall_int - composition done, got PSST (7,3,3,15,2,2)
;; 01-09 17:56:38.780 replaceall_int - checking done, SAT
;; 01-09 17:56:38.813 replaceall_int - got model (Map(x -> bbbbbbaabaabaabaabaaba, y -> bbbbbbacacacacaca, z -> bbbbbbaaaaaaaaaaaaaaaaaaaaa),Map())
