(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)

;; x1 = x0.replaceAll(/(a*)(b*)/, "\2\1")
;; x2 = x1.replaceAll(/(b*)(a*)/, "\2\1")
;; x1 != x2
(assert
 (= x1
    (str.replace_pcre_all x0
                          (pcre.++ (pcre.group (pcre.+ (str.to_pcre "a")))
                                   (pcre.group (pcre.+ (str.to_pcre "b"))))
                          (pcre.replacement 2 1))))
(assert
 (= x2
    (str.replace_pcre_all x1
                          (pcre.++ (pcre.group (pcre.+ (str.to_pcre "b")))
                                   (pcre.group (pcre.+ (str.to_pcre "a"))))
                          (pcre.replacement 2 1))))
(assert (not (= x0 x2)))

(check-sat)
(get-model)
