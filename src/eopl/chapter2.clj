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

;; Exercise 2.1 - Implement the four required operations for bigits.
;; Bigit::= '() | (r . [q]) {n = qN + r, 0 <= r <0 N}

(def ^:dynamic bigits-base 16)

(defn b-zero
  "b-zero: -> Bigit
  Returns the Bigit = [0]."
  [] '())

(defn b-is-zero?
  "b-is-zero? Bigit -> Bool
  Returns true iff bigit = [n]."
  [bigit]
  (every? #(= % 0) bigit))

(defn b-successor
  "b-succesor: Bigit -> Bigit
  Given a bigit of [n], returns a bigit of [n+1]."
  [bigit]
  (let [limit (dec bigits-base)]
    (cond (empty? bigit) '(1)
          (< (first bigit) limit)
          (cons (inc (first bigit)) (rest bigit))
          :else (cons 0 (b-successor (rest bigit))))))

(defn b-predecessor
  "b-predecessor: Bigit -> Bigit
  Given a bigit of [n], returns a bigit of [n-1]."
  [bigit]
  (let [limit (dec bigits-base)]
    (cond (empty? bigit) (list limit)
          (b-is-zero? bigit) (b-zero)
          (pos? (first bigit))
          (cons (dec (first bigit)) (rest bigit))
          :else (cons limit (b-predecessor (rest bigit))))))

(defn b-addition
  "b-addition: Bigit x Bigit -> Bigit
  Given bigit x = [n] bigit y = [m], returns the bigit = [n + m]."
  [x y]
  (cond (b-is-zero? x) y
        (b-is-zero? y) x
        :else (b-addition (b-successor x) (b-predecessor y))))

(defn make-bigit
  "make-bigit: Int -> Bigit
  Given an Integer, produces the bigit [n]."
  [n]
  (if (<= n (dec bigits-base))
    (list n)
    (cons (rem n bigits-base)
          (make-bigit (quot n bigits-base)))))

;; Exercise 2.3 - Define a representation of all the integers, negative and non-negative
;; as diff-trees.
;; Diff-tree:== (one) | (diff Diff-tree Diff-tree)
(defn diff
  "diff: Diff-tree x Diff-tree -> Diff-tree
  Returns a diff-tree which represents [n] = x - y."
  [x y]
  (list 'diff x y))

(defn value-of
  "value-of: Diff-tree -> Int
  Returns the value of a diff-tree as a clojure integer."
  [diff-tree]
  (if (= diff-tree '(one))
    1
    (- (value-of (nth diff-tree 1))
       (value-of (nth diff-tree 2)))))

(defn zero
  "zero: -> diff-tree
  Returns the diff-tree [0]."
  [] (diff '(one) '(one)))

(defn is-zero?
  "is-zero?: Diff-tree -> Bool
  Returns true iff diff-tree = [0]."
  [diff-tree]
  (if (= diff-tree '(one))
    false
    (= (value-of (nth diff-tree 1))
       (value-of (nth diff-tree 2)))))

(defn predecessor
  "predecessor: Diff-Tree -> Diff-tree
  Given a diff-tree of [n], returns a valid representation
  of [n-1]."
  [diff-tree]
  (diff diff-tree '(one)))

(defn negate
  "negate: Diff-tree -> Diff-tree
  Given a diff-tree of [n], returns a diff-tree of [-n]."
  [diff-tree]
  (diff (zero)
        diff-tree))

(defn successor
  "successor: Diff-tree -> Diff-tree
  Given a diff-tree of [n], returns a diff-tree of [n+1]."
  [diff-tree]
  (diff diff-tree (negate '(one))))

(defn diff-tree-plus
  "diff-tree-plus: Diff-tree x Diff-tree -> Diff-tree
  Given diff-trees x = [n], y = [m], returns a diff-tree
  of [n + m]."
  [x y]
  (diff x (negate y)))

;; Exercise 2.4 - Specification for Stacks
;; (empty-stack) = [0]
;; (empty-stack? stack) = {true where stack = [0] | false}
;; (top stack) = {v where stack = (push [g] v) | nil where stack = [0]}
;; (pop stack) = {[g] where stack = (push [g] v) | [0] where stack = [0]}
;; (push stack v) = {[g] where (top [g]) = v & (pop [g]) = stack}

