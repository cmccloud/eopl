;; Exercise 1.1 - Notes
;; Exercise 1.2 - Notes
;; Exercise 1.3 - Notes
;; Exercise 1.4 - Show that (-7 . (3 . (14 . ()))) is in List-of-Int
;; List-of-Int
;; (Int . List-of-Int)
;; (-7 . List-of-Int)
;; (-7 . (Int . List-of-Int))
;; (-7 . (3 . List-of-Int))
;; (-7 . (3 . (Int . List-of-Int)))
;; (-7 . (3 . (14 . List-of-Int))
;; (-7 . (3 . (14 . ()))
;; Exercise 1.5 - Notes
;; Exercise 1.6 - Notes
;; Exercise 1.7
(define (nth-element lst n)
  "nth-element: List x Int => SchemeVal
usage: (nth-element lst n) = the n-th element of lst"
  (if (> n (length lst))
      (report-list-too-short lst n)
      (if (zero? n)
          (car lst)
          (nth-element (cdr lst) (- n 1)))))

(define (report-list-too-short lst n)
  (error 'nth-element "~a does not contain ~a elements" lst n))

;; Exercise 1.8
(define (drop-until s los)
  "drop-until: Sym x Listof(Sym) => Listof(Sym)
usage: (drop-until s los) = Listof(Sym) formed by dropping
all elements up to the first instance of s, inclusive."
  (if (null? los)
      '()
      (if (eqv? (car los) s)
          (cdr los)
          (drop-until s (cdr los)))))







