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

;; 2.2.1 The Environmental Interface
;; Environment Specification
;; (empty-env) = {0}
;; (apply-env {f} var) = f(var)
;; (extend-env var v {}) = {g} where g(var1) = v iff var1 = var, or f(var1)

;; Exercise 2.4
;; Stack Specification
;; Constructors:
;;   (empty-stack) = {0}
;;   (push v {f}) = {g} such that (pop {g}) = {f} and (top {g}) = v
;;   (pop {f}) = {0} | {g} given that {g} = (push v {h}) 
;; Observers:
;;   (empty-stack? {f}) = #t iff {f} = {0}, #f otherwise
;;   (top {f}) = v given that {f} = (push v {g})

;; 2.2.2 Data Structure Representation
;; Env-exp::= (empty-env) | (extend-env Identifier Scheme-value Env-exp)
;; Env::= (empty-env) | (extend-env Var SchemeVal Env)
(define (empty-env)
  "empty-env:: => Env"
  '(empty-env))

(define (extend-env var val env)
  "extend-env:: Var x SchemeVal x Env => Env"
  (list 'extend-env var val env))

(define (apply-env env search-var)
  "apply-env:: Env x Var => SchemeVal"
  (cond ((eqv? (car env) 'empty-env)
         (report-no-binding-found search-var))
        ((eqv? (car env) 'extend-env)
         (let ((saved-var (cadr env))
               (saved-val (caddr env))
               (saved-env (cadddr env)))
           (if (eqv? search-var saved-var)
               saved-val
               (apply-env saved-env search-var))))
        (else (report-invalid-env env))))

(define (report-no-binding-found search-var)
  (eopl:error 'apply-env "No binding for ~s" search-var))

(define (report-invalid-env env)
  (eopl:error 'apply-env "Bad environment: ~s" env))

;; Exercise 2.5
(define (empty-env)
  "empty-env:: => Env"
  null)

(define (extend-env var val env)
  "extend-env:: Var x SchemeVal x Env => Env"
  (cons (cons var val) env))

(define (apply-env env search-var)
  "apply-env:: Env x Var => SchemeVal"
  (cond ((eqv? env (empty-env))
         (report-no-binding-found search-var))
        ((pair? env)
         (let* ((inner-env (car env))
                (outer-env (cdr env))
                (saved-var (car inner-env))
                (saved-val (cdr inner-env)))
           (if (eqv? search-var saved-var)
               saved-val
               (apply-env outer-env search-var))))
        (else (report-invalid-env env))))

(define (env-test)
  (let ((env-one (extend-env
                  'a 1 (extend-env
                        'b 2 (extend-env
                              'c 3 (empty-env))))))
    (and (equal? (apply-env env-one 'a) 1)
         (equal? (apply-env env-one 'c) 3)
         (equal? (apply-env env-one 'b) 2))))

;; Exercise 2.6 - 2.8 - Skip

;; Exercise 2.10
(define (extend-env* vars vals env)
  "extend-env*:: Listof(Var) x Listof(SchemeVal) x Env => Env
usage: (extend-env vars vals env) given two equal lenght lists
of variables and values, sequentially extends env with (var1 val1...varN valN)"
  (foldl (lambda (bindings env)
           (extend-env (car bindings) (cdr bindings) env))
         env
         (map cons vars vals)))

(define (extend-env*-test)
  (let ((env-one (extend-env* '(a b c) '(1 2 3) (empty-env))))
    (and (equal? (apply-env env-one 'a) 1)
         (equal? (apply-env env-one 'b) 2)
         (equal? (apply-env env-one 'c) 3))))

;; Exercise 2.11
(define (empty-env)
  "empty-env:: => Env"
  null)

(define (extend-env var val env)
  "extend-env:: Var x SchemeVal x Env => Env"
  (cons (cons (list var) (list val)) env))

(define (extend-env* vars vals env)
  "extend-env*:: Listof(Var) x Listof(SchemeVal) x Env => Env
usage: (extend-env vars vals env) given two equal lenght lists
of variables and values, sequentially extends env with (var1 val1...varN valN)"
  (cons (cons vars vals) env))

(define (apply-env env search-var)
  "apply-env:: Env x Var => SchemeVal"
  (define (find-binding search-var saved-vars saved-vals)
    (cond ((null? saved-vars) #f)
          ((eqv? search-var (car saved-vars))
           (car saved-vals))
          (else (find-binding search-var (cdr saved-vars) (cdr saved-vals)))))
  (cond ((eqv? env (empty-env))
         (report-no-binding-found search-var))
        ((pair? env)
         (let* ((inner-env (car env))
                (outer-env (cdr env))
                (saved-vars (car inner-env))
                (saved-vals (cdr inner-env)))
           (or (find-binding search-var saved-vars saved-vals)
               (apply-env outer-env search-var))))))

(define (apply-env-test)
  (let ((env-one (extend-env
                  'a 1
                  (extend-env*
                   '(b c d) '(2 3 4)
                   (extend-env
                    'a 5 (empty-env))))))
    (and (equal? (apply-env env-one 'a) 1)
         (equal? (apply-env env-one 'c) 3)
         (equal? (apply-env env-one 'd) 4))))

;; 2.2.3 Procedural Representation
(define (empty-env)
  "empty-env:: => Env"
  (lambda (search-var) (report-no-binding-found search-var)))

(define (extend-env saved-var saved-val saved-env)
  "extend-env:: Var x SchemeVal x Env => Env"
  (lambda (search-var)
    (if (eqv? search-var saved-var)
        saved-val
        (apply-env saved-env search-var))))

(define (apply-env env search-var)
  "apply-env:: Env x Var => SchemeVal"
  (env search-var))

;; Exercise 2.12
(define (empty-stack)
  "empty-stack:: => Stack"
  (lambda (command)
    (cond ((equal? command 'top)
           (eopl:error 'empty-stack "Stack is empty"))
          (else (empty-stack)))))

(define (push stack val)
  "push:: Stack x SchemeVal => Stack"
  (lambda (command)
    (cond ((equal? command 'pop) stack)
          ((equal? command 'top) val)
          (else (stack val)))))

(define (top stack)
  "top:: Stack => SchemeVal"
  (stack 'top))

(define (pop stack)
  "pop:: Stack => Stack"
  (stack 'pop))

(define (stack-test)
  (let* ((a (empty-stack))
         (b (push a 1))
         (c (push b 2)))
    (and (equal? (top b) 1)
         (equal? (top c) 2)
         (equal? (top (pop c)) 1))))

;; Exercise 2.13
(define (empty-env)
  "empty-env:: => Env"
  (list (lambda (search-var) (report-no-binding-found search-var))
        (lambda () #t)))

(define (extend-env saved-var saved-val saved-env)
  "extend-env:: Var x SchemeVal x Env => Env"
  (list (lambda (search-var)
          (if (eqv? search-var saved-var)
              saved-val
              (apply-env saved-env search-var)))
        (lambda () #f)))

(define (apply-env env search-var)
  "apply-env:: Env x Var => SchemeVal"
  ((car env) search-var))

(define (empty-env? env)
  "empty-env?:: Env => Bool"
  ((cadr env)))

(define (empty-env?-test)
  (let* ((a (empty-env))
         (b (extend-env 'a 1 a)))
    (and (equal? (empty-env? a) #t)
         (equal? (empty-env? b) #f))))
