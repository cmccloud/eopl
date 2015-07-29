(ns eopl.chapter2)
;; Abstract Data Type: A data type whose representation is separted from it's use by an interface.

;; Client code which manipulates a data type only through the procedures in that data type's interface
;; is said to be representation-independent.

;; The specification for the representation of a data type is denoted by '[v]'.

;; (zero) = [0]
;; (is-zero? [n]) = {n = 0 -> t | n != 0 -> f}
;; (successor [n]) = [n + 1] (n >= 0)
;; (predecessor [n+1]) = [n] (n >= 0)

;; If the representation of a type is hidden, so that it cannot be exposed by
;; any operation, the type is said to be opaque, otherwise it is said to be
;; transparent.

;; Diff-tree:== (one) | (diff Diff-tree Diff-tree)
;; diff: Diff-Tree x Diff-tree -> Diff-tree

(defn diff [x y]
  (list 'diff x y))

(defn value-of [diff-tree]
  (if (= diff-tree '(one))
    1
    (- (value-of (nth diff-tree 1))
       (value-of (nth diff-tree 2)))))

(defn zero [] (diff '(one) '(one)))

(defn is-zero? [diff-tree]
  (if (= diff-tree '(one))
    false
    (= (value-of (nth diff-tree 1))
       (value-of (nth diff-tree 2)))))

(defn predecessor [diff-tree]
  (diff diff-tree '(one)))

(defn negate [diff-tree]
  (diff (zero)
        diff-tree))

(defn successor [diff-tree]
  (diff diff-tree (negate '(one))))

(defn diff-tree-plus [x y]
  (diff x (negate y)))


