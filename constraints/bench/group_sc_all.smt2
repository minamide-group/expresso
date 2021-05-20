;; キャプチャグループを含む sat な例
(declare-const x String)
(declare-const y String)

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
(assert (str.in.re y (re.++ re.all (str.to.re "<sc>") (re.* re.allchar) (str.to.re "</sc>") re.all)))
(check-sat)
(get-model)
