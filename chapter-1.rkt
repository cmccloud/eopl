#lang eopl
(require eopl)
;;; Section 1.1 - Recursively Specified Data
;; ***********************************************

;; 1.1.1 Inductive Specification
;; Definition 1.1.1:
;; A natural number n is in S if and only if
;; 1. n = 0, or
;; 2. n - 3 is a member of S
(define (in-S? n)
  "in-S:: N => Bool
usage: (in-S? n) = #t if n is in S, #f otherwise"
  (cond ((zero? n) #t)
        ((< n 0) #f)
        (else (in-S? (- n 3)))))

;; Definition 1.1.2:
;; Define the set of S to be the smallet set contained in N
;; and satisfying the following two properties:
;; 1. 0 is a member of S, and
;; 2. if n is a member of S, then n + 3 is a member of S

;; Definition 1.1.3:
;; List of Integers, top down
;; A Scheme list is a list of integers if and only if either
;; 1. It is the empty list, or
;; 2. It is a pair whose car is an integer and whose cdr is a list of integers

;; Definition 1.1.4:
;; List of Integers, bottom up
;; The set List-of-Int is the smallet set of Scheme lists satisfying
;; the following two properties:
;; 1. () is a member of List-of-Int, and
;; 2. if n is a member of Int and l is a member of List-of-Int then
;; (n . l) is a member of List-of-Int

;; Definition 1.1.5:
;; List of Integers, rules of inference
;; Axiom: () is a member of List-of-Int
;; If (n is a member of Int AND l is a member of List-of-Int)
;; then (n . l) is a member of List-of-Int

;; Exercise 1.1 - Notes
;; Exercise 1.2 - Notes
;; Exercise 1.3 - The Set of all Natural Numbers

;; 1.1.2 Defining Sets Using Grammars
;; List-of-Int::= ()
;; List-of-Int::= (Int . List-of-Int)

;; List-of-Int::= ()
;;            ::= (Int . List-of-Int)

;; List-of-Int::= () | (Int . List-of-Int)

;; List-of-Int::=({Int}*)

;; Exercise 1.4 -
;; List-of-Int
;; (Int . List-of-Int)
;; (-7 . List-of-Int)
;; (-7 . (Int . List-of-Int))
;; (-7 . (3 . List-of-Int))
;; (-7 . (3 . (Int . List-of-Int)))
;; (-7 . (3 . (14 . List-of-Int)))
;; (-7 . (3 . (14 . ())))

;; Defintion 1.1.6:
;; S-list, S-exp
;; S-list::= ({S-exp}*)
;; S-exp::= Symbol | S-list

;; Defintion 1.1.7:
;; Binary Tree
;; Bintree::= Int | (Symbol Bintree Bintree)

;; Defintion 1.1.8:
;; Lamda Expression
;; LcExp::= Identifier | (lambda (Identifier) LcExp) | (LcExp LcExp)
;; Where Identifier is any symbol other than lambda

;; 1.1.3 Induction
;; Exercise 1.5 Prove that if e is a member of LcExp, then there are the
;; same number of left and right parenthesis in e.
;; The proof is by induction on the size of e, where we take the size of
;; e to be the number of Lambda Expressions in e. The induction hypothesis,
;; IH(k), is that any LcExp of size <= k is balanced with respect to the
;; number of parenthesis.
;; 1. Let k be an integer such that IH(k) holds - We must show that
;; IH(k+1) holds
;; a. k could be of the form Identifier, which is 0 right and 0 left parenthesis and is balanced
;; b. k could be of the form (lambda (Identifier) LcExp) which is balanced if and only if LcExp
;; is balanced. Because LcExp must be smaller than k, LcExp is covered by the induction hypothesis.
;; c. k could be of the form (LcExp LcExp) which is balanced iff both LcExps are balanced.
;; Because both LcExps must be smaller than k, both are covered by the induction hypothesis.

;;; 1.2 Deriving Recursive Programs
;; ***********************************************

(define (nth-element lst n)
  "nth-element:: List x Int => SchemeVal
usage: (nth-element lst n) = the n-th element of lst"
  (if (null? lst)
      (report-list-too-short n)
      (if (zero? n)
          (car lst)
          (nth-element (cdr list) (- n 1)))))

(define (report-list-too-short lst n)
  (eopl:error 'nth-element
              "~s does not have ~s elements.~%" lst (+ n 1)))

;; Exercise 1.6 - We might attempt to take the car of null.
;; Exercise 1.7 -
(define (nth-element lst n)
  "nth-element:: List x Int => SchemeVal
usage: (nth-element lst n) = the n-th element of lst"
  (define (-nth-element lst n)
    (if (zero? n)
        (car lst)
        (-nth-element (cdr lst) (- n 1))))
  (if (<= (length lst) n)
      (report-list-too-short lst n)
      (-nth-element lst n)))

;; List-of-Symbol::= () | (Symbol . List-of-Symbol)
(define (remove-first s los)
  "remove-first:: Sym x Listof(Sym) => Listof(Sym)
usage: (remove-first s los) returns a list which the same
elements as los, except that the first occurence of the symbol
s is removed."
  (cond ((null? los) null)
        ((eqv? s (car los)) (cdr los))
        (else (cons (car los)
                    (remove-first s (cdr los))))))

;; Exercise 1.8
(define (drop-until s los)
  "drop-until:: Sym x Listof(Sym) => Listof(Sym)
usage: (drop-until s los) returns a list with the same elements
as los, except that every element up until and including the first
instance of s is removed."
  (cond ((null? los) null)
        ((eqv? s (car los)) (cdr los))
        (else (drop-until s (cdr los)))))

;; Exercise 1.9
(define (remove s los)
  "remove:: Sym x Listof(Sym) => Listof(Sym)
usage: (remove s los) returns a list with the same elements
as los, except that all instances of s are removed."
  (cond ((null? los) null)
        ((eqv? s (car los)) (remove s (cdr los)))
        (else (cons (car los)
                    (remove s (cdr los))))))

(define (occurs-free? var exp)
  "occurs-free?:: Sym x LcExp => Bool
usage: (occurs-free? var exp) returns #6 if var is unbound anywhere
in exp, #f otherwise."
  (cond ((symbol? exp) (eqv? var exp))
        ((eqv? (car exp) 'lambda)
         (and (not (eqv? (caadr exp) var))
              (occurs-free? var (caddr exp))))
        (else (or (occurs-free? var (car exp))
                  (occurs-free? var (cadr exp))))))

(define (subst new old slist)
  "subst:: Sym x Sym x Listof(Sym) => Listof(Sym)
usage: (subst new old slist) returns a list which each instance
of old in slist replaced with new."
  (define (subst-in-s-exp new old sexp)
    (if (symbol? sexp)
        (if (eqv? old sexp) new sexp)
        (subst new old sexp)))
  (if (null? slist) null
      (cons (subst-in-s-exp new old (car slist))
            (subst new old (cdr slist)))))

;; Exercise 1.11 - subst is responsible for the decomposition
;; of sexp into smaller substructures.

;; Exercise 1.12
(define (subst-inline new old slist)
  "subst-inline:: Sym x Sym x Listof(Sym) => Listof(Sym)
usage: (subst-inline new old slist) returns a list which each instance
of old in slist replaced with new."
  (cond ((null? slist) null)
        ((symbol? (car slist))
         (if (eqv? (car slist) old)
             (cons new (subst-inline new old (cdr slist)))
             (cons (car slist) (subst-inline new old (cdr slist)))))
        (else (cons (subst-inline new old (car slist))
                    (subst-inline new old (cdr slist))))))

;; Exercise 1.13
(define (subst-map new old slist)
  "subst-map:: Sym x Sym x Listof(Sym) => Listof(Sym)
usage: (subst-map new old slist) returns a list which each instance
of old in slist replaced with new."
  (map (lambda (sexp)
         (if (symbol? sexp)
             (if (eqv? sexp old) new sexp)
             (subst-map new old sexp)))
       slist))

;;; 1.3 Auxiliary Procedures and Context Arguments
;; ***********************************************
(define (number-elements-from lst n)
  "number-elements-from:: Listof(SchemeVal) x Int => Listof(List(Int,SchemeVal))
usage: (number-elements-from lst n) creates a list of lists with each element
in lst accompanied by an integer starting with n and ending with n + (length lst) - 1"
  (if (null? lst) null
      (cons (list n (car lst))
            (number-elements-from (cdr lst) (+ n 1)))))

(define (number-elements lst)
  "number-elements:: List => ListOf(List(Int, SchemeVal))"
  (number-elements-from lst 0))

(define (list-sum lst)
  "list-sum:: Listof(Int) => Int"
  (if (null? lst) 0
      (+ (car lst)
         (list-sum (cdr lst)))))

(define (partial-vector-sum v n)
  "partial-vector-sum:: Vectorof(Int) x Int => Int
usage: if 0 <= n < length(v), then
(partial-vector-sum v n) = Sum(v0...vn)"
(if (zero? n)
    (vector-ref v 0)
    (+ (vector-ref v n)
       (partial-vector-sum v (- n 1)))))

(define (vector-sum v)
  "vector-sum:: Vectorof(Int) => Int"
  (let ((n (vector-length v)))
    (if (zero? n) 0
        (partial-vector-sum v (- n 1)))))

;; Exercise 1.14 - Notes
;; Exercise 1.15
(define (duple n x)
  "duple:: Int x SchemeVal => Listof(SchemeVal)
usage: (duple n x) returns a list with n instances of x"
  (if (zero? n) null
      (cons x (duple (- n 1) x))))

(define (duple-test)
  (and (equal? (duple 2 3) '(3 3))
       (equal? (duple 4 '(ha ha)) '((ha ha) (ha ha) (ha ha) (ha ha)))
       (equal? (duple 0 '(blah)) '())))

;; Exercise 1.16
(define (invert lst)
  "invert:: Listof(2-lists) => Listof(2-lists)
usage: (invert lst) returns a list with each 2-list reversed"
  (define (invert-2-list lst)
    "invert-2-list:: 2-list => 2-list
usage: (invert-2-list lst) returns a reversed 2-list"
    (list (cadr lst) (car lst)))
  (map invert-2-list lst))

(define (invert-test)
  (equal? (invert '((a 1) (a 2) (1 b) (2 b)))
          '((1 a) (2 a) (b 1) (b 2))))

;; Exercise 1.17
(define (down lst)
  "down:: List => Listof(Lists)
usage: wraps parentheses around each top-level element of lst"
  (map list lst))

(define (down-test)
  (and (equal? (down '(1 2 3))
               '((1) (2) (3)))
       (equal? (down '((a) (fine) (idea)))
               '(((a)) ((fine)) ((idea))))
       (equal? (down '(a (more (complicated)) object))
               '((a) ((more (complicated))) (object)))))

;; Exercise 1.18
(define (swapper s1 s2 slist)
  "swapper:: Sym x Sym x Listof(Sym)
usage: (swapper s1 s2 slist) returns a list the same as
slist but with all occurrences of s1 replaced by s2
and vis versa."
  (define (swap-in-sexp s1 s2 sexp)
    "swap-in-sexp:: Sym x Sym x Sexp => Sexp
usage: (swap-in-sexp s1 s2 sexp) returns a sexp with all
occurances of s1 swapped with s2 and vis versa."
    (if (symbol? sexp)
        (cond ((eqv? sexp s1) s2)
              ((eqv? sexp s2) s1)
              (else sexp))
        (swapper s1 s2 sexp)))
  (map (lambda (sexp) (swap-in-sexp s1 s2 sexp))
       slist))

(define (swapper-test)
  (and (equal? (swapper 'a 'd '(a b c d))
               '(d b c a))
       (equal? (swapper 'a 'd '(a d () c d))
               '(d a () c a))
       (equal? (swapper 'x 'y '((x) y (z (x))))
               '((y) x (z (y))))))

;; Exercise 1.19
(define (list-set lst n x)
  "list-set:: List x Int x Sym => List
usage: (list-set lst n x) returns a list like lst, except the n-th element
using zero-based indexing, is x."
  (cond ((null? lst)
         (if (> n 0)
             (eopl:error 'list-set "List is short by ~s elements." n)
             null))
        ((zero? n)
         (cons x (cdr lst)))
        (else (cons (car lst) (list-set (cdr lst) (- n 1) x)))))

(define (list-set-test)
  (and (equal? (list-set '(a b c d) 2 '(1 2))
               '(a b (1 2) d))
       (equal? (list-ref (list-set '(a b c d) 3 '(1 5 10)) 3)
               '(1 5 10))))

;; Exercise 1.20
(define (count-occurrences s slist)
  "count-occurrences:: Sym x Listof(Sym) => Int
usage: (count-occurrences s slist) returns the number of occurrences of s
in slist."
  (list-sum (map (lambda (sexp)
                   (if (symbol? sexp) (if (eqv? sexp s) 1 0)
                       (count-occurrences s sexp)))
                 slist)))

(define (count-occurrences-test)
  (and (= (count-occurrences 'x '((f x) y ((x z) x)))
          3)
       (= (count-occurrences 'x '((f x) y ((x z) () x)))
          3)
       (= (count-occurrences 'w '((f x) y (((x z) x))))
          0)))

;; Exercise 1.21
(define (product sos1 sos2)
  "product:: Listof(Sym) x Listof(Sym) => Listof(2-lists)
usage: (product so1 so2) where sos1 and sos2 are each a list
of symbols without repetitions, returns a list of 2-lists that
represent the Cartesian product of sos1 and sos2."
  (foldl (lambda (sym1 acc)
           (append acc
                   (map (lambda (sym2)
                          (list sym1 sym2))
                        sos2)))
         null
         sos1))

(define (product-test)
  (equal? (product '(a b c) '(x y))
          '((a x) (a y) (b x) (b y) (c x) (c y))))

;; Exercise 1.22
(define (filter-in pred lst)
  "filter-in:: Procedure x List => List
usage: (filter-in pred lst) returns the lst of those elements in lst
that satisfy the predicate pred."
  (cond ((null? lst) null)
        ((pred (car lst))
         (cons (car lst) (filter-in pred (cdr lst))))
        (else (filter-in pred (cdr lst)))))

(define (filter-in-test)
  (and (equal? (filter-in number? '(a 2 (1 3) b 7))
               '(2 7))
       (equal? (filter-in symbol? '(a (b c) 17 foo))
               '(a foo))))

;; Exercise 1.23
(define (list-index-from-n pred lst n)
  "list-index-from-n:: Procedure x List x Int => Int
usage: (list-index-from-n pred lst n) returns the n based position of the first
element in lst that satisfies the predicate pred, otherwise returns #f."
  (cond ((null? lst) #f)
        ((pred (car lst)) n)
        (else (list-index-from-n pred (cdr lst) (+ n 1)))))

(define (list-index pred lst)
  "list-index:: Procedure x List => Int
usage: (list-index pred lst) returns the 0 based position of the first element
in lst that satisfied the predicate pred, otherwise returns #f."
  (list-index-from-n pred lst 0))

(define (list-index-test)
  (and (= (list-index number? '(a 2 (1 3) b 7))
          1)
       (= (list-index symbol? '(a (b c) 17 foo))
          0)
       (equal? (list-index symbol? '(1 2 (a b) 3))
               #f)))

;; Exercise 1.24
(define (every? pred lst)
  "every?:: Procedure x List => Bool
usage: (every? pred lst) returns #f if any elements in lst fails to
satisfy pred, otherwise returns #t."
  (cond ((null? lst) #t)
        ((pred (car lst)) (every? pred (cdr lst)))
        (else #f)))

(define (every?-test)
  (and (equal? (every? number? '(a b c 3 e)) #f)
       (equal? (every? number? '(1 2 3 4 5)) #t)))

;; Exercise 1.25
(define (exists? pred lst)
  "exists?:: Procedure x List => Bool
usage: (exists? pred lst) returns #t if any element in lst satisfies
pred, otherwise returns #f."
  (cond ((null? lst) #f)
        ((pred (car lst)) #t)
        (else (exists? pred (cdr lst)))))

(define (exists?-test)
  (and (equal? (exists? number? '(a b c 3 e)) #t)
       (equal? (exists? number? '(a b c d e)) #f)))

;; Exercise 1.26
(define (up lst)
  "up:: List => List
usage: (up lst) removes a pair of parentheses from each top-level element
of lst. If a top-level element is not a list, in it included as is."
  (foldl (lambda (element acc)
           (append acc (if (pair? element) element (list element))))
         null
         lst))

(define (up-test)
  (and (equal? (up '((1 2) (3 4)))
               '(1 2 3 4))
       (equal? (up '((x (y)) z))
               '(x (y) z))))

;; Exercise 1.27
(define (flatten slist)
  "flatten:: Listof(Sym) => Listof(Sym)
usage: (flatten slist) reutrns a list of the symbols contained in slist
in the order in which they occur when slist is printed. Intuitively, flatten
removes all the inner parentheses from its argument."
  (foldl (lambda (sexp acc)
           (append acc (if (symbol? sexp) (list sexp) (flatten sexp))))
         null
         slist))

(define (flatten-test)
  (and (equal? (flatten '(a b c))
               '(a b c))
       (equal? (flatten '((a) () (b ()) () (c)))
               '(a b c))
       (equal? (flatten '((a b) c (((d)) e)))
               '(a b c d e))
       (equal? (flatten '(a b (() (c))))
               '(a b c))))

;; Exercise 1.28
(define (merge loi1 loi2)
  "merge:: Listof(Int) x Listof(Int) => Listof(Int)
usage: (merge loi1 loi2) where loi1 and loi2 are lists of integers that are
sorted in ascending order, returns a sorted list of all the intergers in
loi1 and loi2 "
  (cond ((null? loi1) loi2)
        ((null? loi2) loi1)
        ((< (car loi1) (car loi2))
         (cons (car loi1) (merge (cdr loi1) loi2)))
        (else
         (cons (car loi2) (merge loi1 (cdr loi2))))))

(define (merge-test)
  (and (equal? (merge '(1 4) '(1 2 8))
               '(1 1 2 4 8))
       (equal? (merge '(35 62 81 90 91) '(3 83 85 90))
               '(3 35 62 81 83 85 90 90 91))))

;; Exercise 1.29
(define (take n lst)
  "take:: Int x List => List
usage: (take n lst) returns the list of the first n elements of lst."
  (cond ((null? lst) null)
        ((zero? n) null)
        (else (cons (car lst)
                    (take (- n 1) (cdr lst))))))

(define (drop n lst)
  "drop:: Int x List => List
usage: (drop n lst) returns the list produced by removing the first n
elements from lst."
  (cond ((null? lst) null)
        ((zero? n) lst)
        (else (drop (- n 1) (cdr lst)))))

(define (first-half lst)
  "first-half:: List => List
usage: (first-half lst) returns the list produced by taking the first
n elements from lst where n = (floor (/ (length lst) 2))."
  (take (floor (/ (length lst) 2)) lst))

(define (second-half lst)
  "second-half:: List => List
usage: (second-half lst) returns the list produced by removing the first
n elements from lst where n = (floor (/ (length lst) 2))."
  (drop (floor (/ (length lst) 2)) lst))

(define (sort loi)
  "sort:: Listof(Ints) => Listof(Ints)
usage: (sort loi) returns a list of the elements in loi in ascending order."
  (cond ((null? loi) null)
        ((= 1 (length loi)) loi)
        ((= 2 (length loi)) (merge (list (car loi)) (list (cadr loi))))
        (else (merge (sort (first-half loi))
                     (sort (second-half loi))))))

(define (sort-test)
  (and (equal? (sort '(8 2 5 2 3))
           '(2 2 3 5 8))
       (equal? (sort '())
               '())))

;; Exercise 1.30
(define (merge/predicate pred loi1 loi2)
  "merge/predicate:: Procedure x Listof(Ints) x Listof(Ints) => Listof(Ints)
usage: (merge/predicate pred loi1 loi2) where loi1 and loi2 are internally
sorted according to pred, returns a list of integers sorted by pred."
  (cond ((null? loi1) loi2)
        ((null? loi2) loi1)
        ((pred (car loi1) (car loi2))
         (cons (car loi1) (merge/predicate pred (cdr loi1) loi2)))
        (else (cons (car loi2) (merge/predicate pred loi1 (cdr loi2))))))

(define (sort/predicate pred loi)
  "sort/predicate:: Procedure x Listof(Ints) => Listof(Ints)
usage: (sort/predicate pred loi) returns of a list of elements sorted
by the predicate."
  (cond ((null? loi) null)
        ((= 1 (length loi)) loi)
        ((= 2 (length loi))
         (merge/predicate pred (list (car loi)) (list (cadr loi))))
        (else (merge/predicate pred
                               (sort/predicate pred (first-half loi))
                               (sort/predicate pred (second-half loi))))))

(define (sort/predicate-test)
  (and (equal? (sort/predicate < '(8 2 5 2 3))
               '(2 2 3 5 8))
       (equal? (sort/predicate > '(8 2 5 2 3))
               '(8 5 3 2 2))))

;; Exercise 1.31
(define (leaf n)
  "leaf:: Int => Int
usage: (leaf n) returns n."
  n)

(define (interior-node sym left-branch right-branch)
  "interior-node:: Sym x BinTree x Bintree => BinTree
usage: (interior-node sym left-branch right-branch) produces a binary tree
whose contents are equal to sym, and whose branches are left-branch and
right-branch, respectively."
  (list sym left-branch right-branch))

(define (leaf? bintree)
  "leaf:: BinTree => Bool
usage: (leaf? bintree) returns #t if bintree is a leaf node, #f otherwise."
  (integer? bintree))

(define (lson bintree)
  "lson:: Bintree => BinTree
usage: (lson bintree) returns the left branch of a given binary tree."
  (cadr bintree))

(define (rson bintree)
  "rson:: BinTree => BinTree
usage: (rson bintree) returns the right branch of a given binary tree."
  (caddr bintree))

(define (contents-of bintree)
  "contents-of:: BinTree => Sym | Int
usage: (contents-of bintree) returns a symbol if bintree is an interior node,
or an integer if bintree is a leaf node."
  (if (leaf? bintree)
      bintree
      (car bintree)))

;; Exercise 1.32
(define (double-tree bintree)
  "double-tree:: BinTree => BinTree
usage: (double-tree bintree) produces a bintree like the original, but with all the
integers in the leaves doubled."
  (if (leaf? bintree) (leaf (* 2 (contents-of bintree)))
      (interior-node (contents-of bintree)
                     (double-tree (lson bintree))
                     (double-tree (rson bintree)))))

(define (double-tree-test)
  (let ((tree-one (interior-node 'foo
                                 (interior-node 'bar
                                                (leaf 1)
                                                (leaf 2))
                                 (leaf 3)))
        (tree-two (leaf 8)))
    (and (equal? (double-tree tree-one)
                 '(foo (bar 2 4)
                       6))
         (equal? (double-tree tree-two)
                 16))))

;; Exercise 1.33
(define (mark-leaves-with-red-depth-from-n bintree n)
  "make-leaves-with-red-depth-from-n:: BinTree x Int => Bintree
usage: (mark-leaves-with-red-depth-from-n bintree n) takes a bintree
and produces a bintree of the same shape as the original, except that
in the new tree, each leaf contains the n + integer of nodes between it and
the root that contain the symbol red."
  (cond ((leaf? bintree) (leaf n))
        ((eqv? (contents-of bintree) 'red)
         (interior-node 'red
                        (mark-leaves-with-red-depth-from-n
                         (lson bintree)
                         (+ n 1))
                        (mark-leaves-with-red-depth-from-n
                         (rson bintree)
                         (+ n 1))))
        (else (interior-node (contents-of bintree)
                             (mark-leaves-with-red-depth-from-n
                              (lson bintree)
                              n)
                             (mark-leaves-with-red-depth-from-n
                              (rson bintree)
                              n)))))

(define (mark-leaves-with-red-depth bintree)
  "make-leaves-with-red-depth-from-n:: BinTree => Bintree
usage: (mark-leaves-with-red-depth-from-n bintree n) takes a bintree
and produces a bintree of the same shape as the original, except that
in the new tree, each leaf contains the integer of nodes between it and
the root that contain the symbol red."
  (mark-leaves-with-red-depth-from-n bintree 0))

(define (mark-leaves-with-red-depth-test)
  (equal? (mark-leaves-with-red-depth
           (interior-node 'red
                          (interior-node 'bar
                                         (leaf 26)
                                         (leaf 12))
                          (interior-node 'red
                                         (leaf 11)
                                         (interior-node 'quux
                                                        (leaf 117)
                                                        (leaf 14)))))
          '(red (bar 1 1) (red 2 (quux 2 2)))))

;; Exercise 1.34
(define (path n bst)
  "path:: Int x BinTree => ListOf({Left|Right}*)
usage: (path n bst) returns a list of lefts and rights showing how to find
the node containing n. If n is not found, returns the empty lst."
  (define (build-path n bst path)
    "build-path:: Int x BinTre x List => ListOf({Left|Right}*)"
    (cond ((null? bst) null)
          ((= n (car bst)) path)
          ((> n (car bst)) (build-path n (caddr bst) (append path '(Right))))
          (else (build-path n (cadr bst) (append path '(Left))))))
  (build-path n bst null))

(define (path-test)
  (equal? (path 17 '(14 (7 () (12 () ()))
                        (26 (20 (17 () ())
                                ())
                            (31 () ()))))
          '(Right Left Left)))
;; Exercise 1.35
(define (tree-map procedure bintree)
  "tree-map:: Procedure x BinTree => BinTree
usage: (tree-map procedure bintree) produces a new bintree where the contents
of each node, both leaves and interior, are the product of procedure applied to the
previous value."
  (if (leaf? bintree) (procedure (contents-of bintree))
      (interior-node (procedure (contents-of bintree))
                     (tree-map procedure (lson bintree))
                     (tree-map procedure (rson bintree)))))

(define (number-leaves bintree)
  "number-leaves:: BinTree => BinTree
usage: (number-leaves bintree) produced a bintree like the original, except the contents
of the leaves are numbered starting from 0."
  (define counter
    "counter:: => Int
usage: (counter) returns an integer, initially set to 0, which is incremented each time
counter is called."
    (let ((count 0))
      (lambda ()
        (let ((stored count))
          (set! count (+ count 1))
          stored))))
  (tree-map (lambda (contents)
              (if (number? contents)
                  (counter)
                  contents))
            bintree))

(define (number-leaves-test)
  (equal? (number-leaves
           (interior-node 'foo
                          (interior-node 'bar
                                         (leaf 26)
                                         (leaf 12))
                          (interior-node 'baz
                                         (leaf 11)
                                         (interior-node 'quux
                                                        (leaf 117)
                                                        (leaf 14)))))
          '(foo (bar 0 1) (baz 2 (quux 3 4)))))

;; Exercise 1.36
(define (g 2-list lst)
  "g:: 2-List x Listof(2-list) => Listof(2-list)
usage: (g 2-list lst) increments the first value of each 2-list in lst
and then appends 2-list to the resulting list."
  (cons 2-list
        (map (lambda (2-list)
               (list (+ 1 (car 2-list))
                     (cadr 2-list)))
             lst)))

(define (number-elements-with-g lst)
  "number-elements-with-g:: List => ListOf(List(Int, SchemeVal))"
  (if (null? lst) null
      (g (list 0 (car lst))
         (number-elements (cdr lst)))))
