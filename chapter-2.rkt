#lang eopl
(require eopl)
(require rackunit)

;;; 2.1 Specifying Data via Interfaces
;; *****************************************************************************

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

(define (add-big-num bn1 bn2)
  "add-big-num:: Bignum x Bignum => Bignum
usage: (add-big-num bn1 bn2) produces the bignum whose value is equal to the
sum of bn1 and bn2"
  (if (is-zero? bn1)
      bn2
      (add-big-num (predecessor bn1) (successor bn2))))

(define (mult-big-num bn1 bn2)
  "mult-big-num:: Bignum x Bignum => Bignum
usage: (mult-big-num bn1 bn2) produces the bignum whose value is equal to the
product of bn1 and bn2"
  (define (mult-big-num-helper bn1 bn2 n)
    (cond ((is-zero? bn1) (zero))
          ((is-zero? (predecessor bn1)) bn2)
          (else (mult-big-num-helper (predecessor bn1) (add-big-num bn2 n) n))))
  (mult-big-num-helper bn1 bn2 bn2))

(define (fact-big-num bn)
  "fact-big-num:: Bignum => Bignum
usage: (fact-big-num bn) calculates the factorial of bn"
  (cond ((is-zero? bn) (zero))
        ((is-zero? (predecessor bn)) bn)
        (else (mult-big-num bn (fact-big-num (predecessor bn))))))

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
;; *****************************************************************************

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
    (check-equal? (apply-env env-one 'a) 1)
    (check-equal? (apply-env env-one 'c) 3)
    (check-equal? (apply-env env-one 'b) 2)))

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

(let ((env-one (extend-env* '(a b c) '(1 2 3) (empty-env))))
  (check-equal? (apply-env env-one 'a) 1)
  (check-equal? (apply-env env-one 'b) 2)
  (check-equal? (apply-env env-one 'c) 3))

(define (extend-env*-test)
  (let ((env-one (extend-env* '(a b c) '(1 2 3) (empty-env))))
    (check-equal? (apply-env env-one 'a) 1)
    (check-equal? (apply-env env-one 'b) 2)
    (check-equal? (apply-env env-one 'c) 3)))

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
    (check-equal? (apply-env env-one 'a) 1)
    (check-equal? (apply-env env-one 'c) 3)
    (check-equal? (apply-env env-one 'd) 4)))

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
    (check-equal? (top b) 1)
    (check-equal? (top c) 2)
    (check-equal? (top (pop c)) 1)))

;; Exercise 2.13 & Exercise 2.14
(define (empty-env)
  "empty-env:: => Env"
  (list (lambda (search-var) (report-no-binding-found search-var))
        (lambda () #t)
        (lambda (search-var) #f)))

(define (extend-env saved-var saved-val saved-env)
  "extend-env:: Var x SchemeVal x Env => Env"
  (list (lambda (search-var)
          (if (eqv? search-var saved-var)
              saved-val
              (apply-env saved-env search-var)))
        (lambda () #f)
        (lambda (search-var)
          (if (eqv? search-var saved-var)
              #t
              (has-binding? saved-env search-var)))))

(define (apply-env env search-var)
  "apply-env:: Env x Var => SchemeVal"
  ((car env) search-var))

(define (empty-env? env)
  "empty-env?:: Env => Bool"
  ((cadr env)))

(define (has-binding? env search-var)
  "has-binding?:: Env x Var => Bool"
  ((caddr env) search-var))

(define (empty-env?-test)
  (let* ((a (empty-env))
         (b (extend-env 'a 1 a)))
    (check-equal? (empty-env? a) #t)
    (check-equal? (empty-env? b) #f)))

(define (has-binding?-test)
  (let* ((a (empty-env))
         (b (extend-env 'a 1 a))
         (c (extend-env 'b 2 b)))
    (check-equal? (has-binding? a 'a) #f)
    (check-equal? (has-binding? b 'a) #t)
    (check-equal? (has-binding? b 'b) #f)
    (check-equal? (has-binding? c 'b) #t)))

;; 2.3 Interfaces for Recursive Data Types
;; *****************************************************************************
;; Constructors
;;   var-exp:: Var => Lc-exp
;;   lambda-exp:: Var x Lc-exp => Lc-exp
;;   app-exp:: Lc-exp x Lc-exp => Lc-exp
;; Predicates
;;   var-exp?:: Lc-exp => Bool
;;   lambda-exp?:: Lc-exp => Bool
;;   app-exp?:: Lc-exp => Bool
;; Extractors
;;   var-exp->var:: Lc-exp => Var
;;   lambda-exp->bound-var:: Lc-exp => Var
;;   lambda-exp->body:: Lc-exp => Lc-exp
;;   app-exp->rator:: Lc-exp => Lc-exp
;;   app-exp->rand:: Lc-exp => Lc-exp
(define (occurs-free? search-var exp)
  "occurs-free?:: Sym x LcExp => Bool"
  (cond ((var-exp? exp) (eqv? search-var (var-exp->var exp)))
        ((lambda-exp? exp)
         (and (not (eqv? search-var (lambda-exp->bound-var exp)))
              (occurs-free? search-var (lambda-exp->body exp))))
        (else
         (or (occurs-free? serach-var (app-exp->rator exp))
             (occurs-free? search-var (app-exp->rand exp))))))

;; Exercise 2.15
(define (var-exp var)
  "var-exp:: Var => LcExp"
  var)

(define (lambda-exp var exp)
  "lambda-exp:: Var x LcExp => LcExp"
  `(lambda (,var) exp))

(define (app-exp exp1 exp2)
  "app-exp:: LcExp x LcExp => LcExp"
  `(,exp1 ,exp2))

(define (var-exp? exp)
  "var-exp?:: LcExp => Bool"
  (symbol? exp))

(define (lambda-exp? exp)
  "lambda-exp?:: LcExp => Bool"
  (eqv? (car exp) 'lambda))

(define (app-exp? exp)
  "app-exp?:: LcExp => Bool"
  (and (list? exp)
       (= (length exp) 2)))

(define (var-exp->var exp)
  "var-exp->var:: LcExp => Var"
  exp)

(define (lambda-exp->bound-var exp)
  "lambda-exp->bound-var:: LcExp => Var"
  (caadr exp))

(define (lambda-exp->body exp)
  "lambda-exp->body:: LcExp => LcExp"
  (caddr exp))

(define (app-exp->rator exp)
  "app-exp->rator:: LcExp => LcExp"
  (car exp))

(define (app-exp->rand exp)
  "app-exp->rand:: LcExp => LcExp"
  (cadr exp))

;; Exercise 2.16
(define (lambda-exp var exp)
  "lambda-exp:: Var x LcExp => LcExp"
  `(lambda ,var exp))

(define (lambda-exp->bound-var exp)
  "lambda-exp->bound-var:: LcExp => Var"
  (cadr exp))

;; Exercise 2.17
(define (var-exp exp) `(var-exp ,exp))

(define (lambda-exp var exp) `(lambda-exp ,var ,exp))

(define (app-exp rator rand) `(app-exp ,rator ,rand))

(define (var-exp? exp)
  (and (pair? exp) (eqv? (car exp) 'var-exp)))

(define (lambda-exp? exp)
  (and (pair? exp) (eqv? (car exp) 'lambda-exp)))

(define (app-exp? exp)
  (and (pair? exp) (eqv? (car exp) 'app-exp)))

(define (var-exp->var exp) (cadr exp))

(define (lambda-exp->bound-var exp) (cadr exp))

(define (lambda-exp->body exp) (caddr exp))

(define (app-exp->rator exp) (cadr exp))

(define (app-exp->rand exp) (caddr exp))

;; Exercise 2.18
;; NodeInSequence::= (Int Listof(Int) Listof(Int))
(define (number->sequence num)
  "number->seqeuence:: Int => Sequence"
  (list num null null))

(define (current-element bidi-seq)
  "current-element:: Sequence => Int"
  (car bidi-seq))

(define (at-left-end? bidi-seq)
  "at-left-end?:: Sequence => Bool"
  (null? (cadr bidi-seq)))

(define (at-right-end? bidi-seq)
  "at-right-end?:: Sequence => Bool"
  (null? (caddr bidi-seq)))

(define (move-to-left bidi-seq)
  "move-to-left:: Sequence => Sequence"
  (unless (at-left-end? bidi-seq)
    (list (car (cadr bidi-seq))
          (cdr (cadr bidi-seq))
          (cons (current-element bidi-seq)
                (caddr bidi-seq)))))

(define (move-to-right bidi-seq)
  "move-to-right:: Sequence => Sequence"
  (unless (at-right-end? bidi-seq)
    (list (car (caddr bidi-seq))
          (cons (current-element bidi-seq)
                (cadr bidi-seq))
          (cdr (caddr bidi-seq)))))

(define (insert-to-left n bidi-seq)
  "insert-to-left:: Int x Sequence => Sequence"
  (list (current-element bidi-seq)
        (cons n (cadr bidi-seq))
        (caddr bidi-seq)))

(define (insert-to-right n bidi-seq)
  "insert-to-right:: Int x Sequence => Sequence"
  (list (current-element bidi-seq)
        (cadr bidi-seq)
        (cons n (caddr bidi-seq))))

(define (bidi-seq-test)
  (let ((seq '(6 (5 4 3 2 1) (7 8 9))))
    (check-equal? (current-element seq) 6)
    (check-equal? (move-to-left seq) '(5 (4 3 2 1) (6 7 8 9)))
    (check-equal? (move-to-right seq) '(7 (6 5 4 3 2 1) (8 9)))
    (check-equal? (insert-to-left 13 seq) '(6 (13 5 4 3 2 1) (7 8 9)))
    (check-equal? (insert-to-right 13 seq) '(6 (5 4 3 2 1) (13 7 8 9)))))
