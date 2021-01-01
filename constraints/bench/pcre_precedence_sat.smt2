(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (re.union (str.to.re "ab") (str.to.re "abb")))))
(assert (= y (str.replace_pcre
              x
              (pcre.+ (pcre.alt (str.to_pcre "ab") (str.to_pcre "abb")))
              (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)
(get-model)
