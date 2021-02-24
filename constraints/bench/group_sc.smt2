;; 6 s
(declare-const x String)
(declare-const y String)

(assert (= y (str.replace_pcre x
                               (pcre.++
                                (str.to_pcre "{")
                                (pcre.group (pcre.*? pcre.allchar))
                                (str.to_pcre ":")
                                (pcre.group (pcre.*? pcre.allchar))
                                (str.to_pcre "}"))
                               (pcre.replacement "<" 1 ">" 2 "</" 1 ">"))))
(assert (str.in.re y (re.++ re.all (str.to.re "<sc>") (re.* re.allchar) (str.to.re "</sc>") re.all)))
(check-sat)
(get-model)

;; PSST benchmark
;; 01-09 17:56:39.320 group_sc - start compilation
;; 01-09 17:56:39.622 group_sc - got the following PSSTs:
;; 01-09 17:56:39.622 group_sc - #0: (20,5,0,191,1,0)
;; 01-09 17:56:39.622 group_sc - #1: (12,1,0,112,1,0)
;; 01-09 17:56:39.622 group_sc - compose (20,5,0,191,1,0) and (12,1,0,112,1,0)
;; 01-09 17:56:41.363 group_sc - composition done, got PSST (530,5,0,5345,1,1)
;; 01-09 17:56:42.696 group_sc - checking done, SAT
;; 01-09 17:56:43.971 group_sc - got model (Map(x -> {sc:}, y -> <sc></sc>),Map())
