(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.comp (re.++ re.all (str.to.re "script") re.all))))
(assert
 (= y
    (str.replace_pcre_all
     x
     (pcre.++
      (str.to_pcre "{")
      (pcre.group (pcre.*? pcre.allchar))
      (str.to_pcre ":")
      (pcre.group (pcre.*? pcre.allchar))
      (str.to_pcre "}"))
     (pcre.replacement "<" 1 ">" 2 "</" 1 ">"))))
(assert (str.in.re y (re.++ re.all (str.to.re "<script>") (re.+ re.allchar) (str.to.re "</script>") re.all)))
(check-sat)
