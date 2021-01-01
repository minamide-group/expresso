;; <script>.*</script> -- 60 s
;; <script>.+</script> -- 200 s
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
(assert (str.in.re y (re.++ re.all (str.to.re "<script>") (re.+ re.allchar) (str.to.re "</script>") re.all)))
;; (assert (str.in.re y (re.++ re.all (str.to.re "<script>alert(1);</script>") re.all)))
(check-sat)
(get-model)
