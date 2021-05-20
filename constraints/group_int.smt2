(declare-const x String)
(declare-const y String)

(assert
 (= y
    (str.replace_pcre
     x
     (pcre.++
      (str.to_pcre "{")
      (pcre.group (pcre.*? pcre.allchar))
      (str.to_pcre ":")
      (pcre.group (pcre.*? pcre.allchar))
      (str.to_pcre "}"))
     (pcre.replacement "<" 1 ">" 2 "</" 1 ">"))))
(assert (= (str.len y) 101))

(check-sat)
(get-model)
