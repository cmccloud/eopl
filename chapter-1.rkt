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

(define (test-1.8)
  (and (equal? (drop-until 's '(a b c d s e f g))
               '(e f g))
       (equal? (drop-until 's '())
               null)
       (equal? (drop-until 'a '(b c d e f))
               null)))


;; Exercise 1.9
(define (my-remove s los)
  "my-remove: Sym x Listof(Sym) => Listof(Sym)
usage: (my-remove s los) = Listof(Sym) formed by removing
all instances of s from los"
  (if (null? los) '()
      (if (eqv? (car los) s)
          (my-remove s (cdr los))
          (cons (car los) (my-remove s (cdr los))))))

(define (test-1.9)
  (and (equal? (my-remove 's '(a b c s d s e f s s g))
               '(a b c d e f g))
       (equal? (my-remove 's '(a b c d e f))
               '(a b c d e f))
       (equal? (my-remove 's '(s s s s s s s))
               null)))

(define (occurs-free? var exp)
  "occurs-free?: Sym x LcExp => Bool
usage: returns #t if the symbol var occurs free in exp,
otherwise returns #f"
  (cond ((symbol? exp) (eqv? var exp))
        ((eqv? (car exp) 'lambda)
         (and (not (eqv? var (car (cadr exp))))
              (occurs-free? var (caddr exp))))
        (else
         (or (occurs-free? var (car exp))
             (occurs-free? var (cadr exp))))))

(define (subst new old slist)
  "subst: Sym x Sym x S-list => S-list"
  (cond ((null? slist) null)
        ((symbol? (car slist))
         (if (eqv? (car slist) old)
             (cons new (subst new old (cdr slist)))
             (cons (car slist) (subst new old (cdr slist)))))
        (else
         (cons (subst new old (car slist))
               (subst new old (cdr slist))))))

(define (tree-each fn tree)
  "tree-each: Fn x Tree => Tree"
  (cond ((null? tree) null)
        ((pair? (car tree))
         (cons (tree-each fn (car tree))
               (tree-each fn (cdr tree))))
        (else (cons (fn (car tree))
                    (tree-each fn (cdr tree))))))

(define (subst2 new old slist)
  (tree-each
   (lambda (elt) (if (eqv? elt old) new elt))
   slist))




