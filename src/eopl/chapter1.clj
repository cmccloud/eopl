(ns eopl.chapter1)

;; 1.15 - duple
(defn duple
  "duple: Int x Exp -> ListOf(Exp)
  Returns a list containing n copies of exp"
  [n exp]
  (into list (repeat n exp)))

;; 1.16 - invert
(defn invert
  "invert: ListOf(ListOf(x, y)) -> ListOf(ListOf(y,x))
  Returns a list which each 2-list reversed"
  [col]
  (into list (map reverse col)))

;; 1.17 - down
(defn down
  "down: List -> List
  Wraps parentheses around top-level element of list"
  [col]
  (into list (map list col)))

;; 1.18 - swapper
(defn swapper
  "swapper: Sym x Sym x S-list"
  [s1 s2 s-list]
  (into list (map #(get {s1 s2 s2 s1} % %) s-list)))

;; 1.19 - list-set
(defn list-set
  "list-set: List x Int x Exp
  Returns a list like List, with the nth element replaced with x"
  [col n x]
  (if (empty? col)
    nil
    (if (zero? n)
      (cons x (rest col))
      (cons (first col)
            (list-set (rest col) (dec n) x)))))

;; 1.20 - count-occurrences
(defn count-occurrences
  "count-occurences: Sym x S-list -> Int
  Returns the number of occurences of Sym in S-list"
  [target s-list]
  (reduce #(+ %1 (if (= %2 target) 1 0)) 0 s-list))

;; 1.21 - product
(defn product
  "product: SoS x SoS -> List
  Returns the cartesian product of sets S1 and S2"
  [s1 s2]
  (for [x s1 y s2]
    [x y]))

;; 1.22 - filter-in
(defn filter-in
  "filter-in: Fn x List -> List
  Returns the list of those elements in list that satisfy p."
  [p s]
  (if (empty? s)
    nil
    (if (p (first s))
      (cons (first s) (filter-in p (rest s)))
      (filter-in p (rest s)))))

;; 1.23 - list-index
(defn list-index
  "list-index: Fn x List -> Int | Bool
  Returns the 0-based position of the first element in s that satisfy p."
  ([p s] (list-index 0 p s))
  ([n p s]
   (cond
     (empty? s) false
     (p (first s)) n
     :else (recur (inc n) p (rest s)))))

;; 1.24 - every?
(defn every?
  "every?: Fn x List -> Bool
  Returns false if any element of s fails to satisfy p, otherwise returns true"
  [p s]
  (or (empty? s)
      (and (p (first s))
           (recur p (rest s)))))

;; 1.25 - exists?
(defn exists?
  "exists?: Fn x List -> Bool
  Returns true if any element of s satisfies p, otherwise returns false"
  [p s]
  (not (every? (complement p) s)))

;; 1.26 - up
(defn up
  "up: List -> List
  Removes a pair of parentheses from each top-level element of list. If a top
  level form is not a list, it is included, as is."
  [s]
  (mapcat #(if (sequential? %) % (list %)) s))

;; 1.27 - flatten
(defn flatten
  "flatten: S-List -> List
  Returns a list of the symbols contained in s-list in depth-first order."
  [s-list]
  (if (sequential? s-list)
    (mapcat flatten s-list)
    s-list))

;; 1.28 - merge
(defn merge
  "merge: LoI x LoI -> LoI
  Where s1 s2 are lists of integers that are sorted in ascending order,
  returns a sorted list of all the integers of s1 and s2."
  [s1 s2]
  (cond (empty? s1) s2
        (empty? s2) s1
        (< (first s1) (first s2))
        (cons (first s1) (merge (rest s1) s2))
        :else (cons (first s2) (merge s1 (rest s2)))))

;; 1.29 - sort
(defn sort
  "sort: LoI -> LoI
  Returns sorted list of LoI"
  [s]
  (let [l (count s)]
    (if (<= l 1) s
        (merge (sort (take (/ l 2) s))
               (sort (drop (/ l 2) s))))))

;; 1.30 - sort/predicate
(defn merge-by
  "merge-by: P x LoI x LoI -> LoI
  As merge, but uses binary predicate p.
  s1 and s2 must be internally sorted p-wise"
  ([s1 s2] (merge-by < s1 s2))
  ([s1 s2 p]
   (cond (empty? s1) s2
         (empty? s2) s1
         (p (first s1) (first s2))
         (cons (first s1) (merge-by (rest s1) s2 p))
         :else (cons (first s2) (merge-by s1 (rest s2) p)))))

(defn sort-by
  "sort-by: Fn x LoI -> LoI
  As sort, but uses binary predicate p to determine sort order."
  [p s]
  (let [l (count s)]
    (if (<= l 1) s
        (merge-by (sort-by p (take (/ l 2) s))
                  (sort-by p (take (/ l 2) s)) p))))

;; 1.31 - leaf, interior-node, leaf? lson, rson, contents-of
;; Bintree:== Int | (Sym BinTree BinTree)
(defn leaf
  "leaf: Int -> Int"
  [n] n)

(defn interior-node
  "interior-node: Sym x BinTree x BinTree -> List(Sym BinTree BinTree)"
  [sym ltree rtree]
  (list sym ltree rtree))

(defn leaf?
  "leaf?: LcExp -> Bool
  Returns true if exp is a leaf, false otherwise."
  [exp]
  (integer? exp))

(defn lson
  "lson: Bintree -> Bintree | nil
  Returns the left side of a Bintree, or nil if left side does not exist."
  [t]
  (nth t 1))

(defn rson
  "rson: Bintree -> Bintree | nil
  Returns the right side of a Bintree, or nil if right side does not exist."
  [t]
  (nth t 2))

(defn contents-of
  "contents-of: Bintree -> Sym | Int
  Extracts the contents of a Bintree."
  [t]
  (if (leaf? t) t
      (nth t 0)))

;; 1.32 - double-tree
(defn double-tree
  "double-tree: Bintree -> Bintree
  Returns a new bintree, like the original, but with all the integers
  in the leaves doubled."
  [t]
  (if (leaf? t)
    (leaf (* 2 (contents-of t)))
    (interior-node (contents-of t)
                   (double-tree (lson t))
                   (double-tree (rson t)))))

;; 1.33 - mark-leaves-with-red-depth
(defn mark-depth
  "mark-depth: Int x Bintree -> Bintree"
  [n bintree]
  (if (leaf? bintree)
    (leaf n)
    (let [m (if (= 'red (contents-of bintree)) (inc n) n)]
      (interior-node (contents-of bintree)
                     (mark-depth m (lson bintree))
                     (mark-depth m (rson bintree))))))

(defn mark-leaves-with-red-depth
  "mark-leaves-with-red-depth: Bintree -> Bintree
  Produces a bintree with the same shape as the original, except that in
  the new tree, each leaf contains the integers of nodes between it and the
  root which contains the symbol 'red."
  [bintree]
  (if (= 'red (contents-of bintree))
    (interior-node (contents-of bintree)
                   (mark-depth 1 (lson bintree))
                   (mark-depth 1 (rson bintree)))
    (interior-node (contents-of bintree)
                   (mark-leaves-with-red-depth (lson bintree))
                   (mark-leaves-with-red-depth (rson bintree)))))

;; 1.34 - path
(defn path
  "path: Int x BST -> List
  Returns a list of 'lefts' and 'rights' showing how to find the node containing
  n. If n is found at root, returns the empty list."
  [n bst]
  (let [v (contents-of bst)]
    (cond (= n v) nil
          (< n v) (cons 'left (path n (lson bst)))
          :else (cons 'right (path n (rson bst))))))

;; 1.35 - number-leaves
(defn count-leaves
  "count-leaves: Bintree -> Int
  Returns the number of leaves contained in bintree."
  [bintree]
  (if (leaf? bintree)
    1
    (+ (count-leaves (lson bintree))
       (count-leaves (rson bintree)))))

(defn number-leaves
  "number-leaves: Bintree x Int -> Bintree
  Produces a bintree like the original, except the contents of the leaves
  are numbered starting from int."
  ([bintree] (number-leaves bintree 0))
  ([bintree n]
   (if (leaf? bintree)
     (leaf n)
     (interior-node (contents-of bintree)
                    (number-leaves (lson bintree) n)
                    (number-leaves (rson bintree)
                                   (+ n (count-leaves (lson bintree))))))))

;; 1.36 - g
(defn g
  "g: Cell x ListofCells -> ListofCells
  Cell: (Int Exp)
  Given a cell and a List of Cells, produces a list of Cells
  with the first value of every cell in s incremented by one."
  [cell s]
  (cons cell (map #(cons (inc (first %)) (rest %)) s)))
