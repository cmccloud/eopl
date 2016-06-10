#lang eopl
(require eopl)

;;; 2.1 Specifying Data via Interfaces
;; ******************************************

;; Exercise 2.1
(define Base-N 16)

(define (zero)
  "zero:: => Bignum
usage: (zero) produces the bignum whose value is zero."
  '())

(define is-zero? null?)

(define (successor big-num)
  "sucessor:: Bignum => Bignum
usage: (successor big-num) produces the bignum whose value is equal
to big-num +1"
  (cond ((is-zero? big-num) (list 1))
        ((< (car big-num) (- Base-N 1)) (cons (+ 1 (car big-num))
                                              (cdr big-num)))
        (else (cons 0 (successor (cdr big-num))))))

(define (predecessor big-num)
  "predecessor:: Bignum => Bignum
usage: (predecessor big-num) produces the bignum whose value is equal
to big-num -1"
  (cond ((is-zero? big-num) big-num)
        ((equal? big-num '(1)) (zero))
        ((= 0 (car big-num))
         (cons (- Base-N 1) (predecessor (cdr big-num))))
        (else (cons (- (car big-num) 1)
                    (cdr big-num)))))

(define (+big-num bn1 bn2)
  "+big-num:: Bignum x Bignum => Bignum
usage: (+big-num bn1 bn2) produces the bignum whose value is equal to the
sum of bn1 and bn2"
  (if (is-zero? bn1)
      bn2
      (+big-num (predecessor bn1) (successor bn2))))

(define (*big-num bn1 bn2)
  "*big-num:: Bignum x Bignum => Bignum
usage: (*big-num bn1 bn2) produces the bignum whose value is equal to the
product of bn1 and bn2"
  (define (*big-num-helper bn1 bn2 n)
    (cond ((is-zero? bn1) (zero))
          ((is-zero? (predecessor bn1)) bn2)
          (else (*big-num-helper (predecessor bn1) (+big-num bn2 n) n))))
  (*big-num-helper bn1 bn2 bn2))

(define (fact-big-num bn)
  "fact-big-num:: Bignum => Bignum
usage: (fact-big-num bn) calculates the factorial of bn"
  (cond ((is-zero? bn) (zero))
        ((is-zero? (predecessor bn)) bn)
        (else (*big-num bn (fact-big-num (predecessor bn))))))

;; Exercise 2.2 - Notes

;; Exercise 2.3
;; Diff-Tree Specification
;; Diff-tree::= (one) | (diff Diff-tree Diff-tree)
(define (dt-one)
  "dt-one:: => Diff-tree
usage: (dt-one) produces the dt representing the number 1"
  '(one))

(define (dt-zero)
  "dt-zero:: => Diff-tree
usage: (dt-zero) produces the dt representing the number 0"
  '(diff (one) (one)))

(define (dt-zero? dt)
  "dt-zero?:: Diff-tree => Bool
usage: (dt-zero? dt) returns #t dt is a valid representation of the number 0,
otherwise returns #f"
  (cond ((equal? dt '(one)) #f)
        (else (= (dt->int (cadr dt))
                 (dt->int (caddr dt))))))

(define (dt->int dt)
  "dt->int:: Diff-tree => Int
usgae: (dt->int dt) returns the value of dt, represented as an integer"
  (if (equal? dt '(one))
      1
      (- (dt->int (cadr dt))
         (dt->int (caddr dt)))))

(define (dt-successor dt)
  "dt-successor:: Diff-tree => Diff-tree
usage: (dt-successor dt) returns a Diff-tree whose value is equal to the
value of dt +1"
  `(diff ,dt (diff ,(dt-zero) ,(dt-one))))

(define (dt-predecessor dt)
  "dt-predecessor:: Diff-tree => Diff-tree
usage: (dt-predecessor dt) returns a Diff-tree whose value is equal to the
value of dt -1"
  `(diff ,dt (diff ,(dt-one) ,(dt-zero))))

(define (dt-plus dt1 dt2)
  "dt-plus:: Diff-tree x Diff-tree => Diff-tree
usage: (dt-plus dt1 dt2) returns a Diff-tree whose value is equal to the
sum of dt1 and dt2"
  `(diff ,dt1 (diff ,(dt-zero) ,dt2)))


