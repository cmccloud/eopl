(ns eopl.chapter-1)

(defn occurs-free?
  "occurs-free?: Sym x LcExp -> Bool
  Given a symbol, sym, and a lambda expression, exp, describes whether or not that symbol
  occurs in exp outside some lambda binding of the same sym."
  [sym exp]
  (cond
    (symbol? exp) (= sym exp)
    (= (first exp) 'lambda)
    (and (not= (first (first (rest exp))) sym) (occurs-free? sym (first (rest (rest exp)))))
    :else (or (occurs-free? sym (first exp)) (occurs-free? sym (first (rest exp))))))

(defn subst
  "subst: Sym x Sym x S-list -> S-list
  Given two symbols, new and old, and an s-list,
  returns a new list with all instances of old replaced with new"
  [new old s-list]
  (if (symbol? s-list)
    (if (= old s-list) new s-list)
    (map (partial subst new old) s-list)))

