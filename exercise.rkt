#lang scheme

(require trs2impl)

;;; Yue exercise code

#;(defrel (teacupo t)
    (disj2 (== t 'tea) (== t 'cup)))


(defrel (nullo x)
  (== '() x))


(defrel (conso a d p)
  (== p (cons a d)))


(defrel (caro p a)
  (fresh (d) (conso a d p)))


(defrel (cdro p d)
  (fresh (a) (conso a d p)))


(defrel (pairo p)
  (fresh (x y) (conso x y p)))


(defrel (singletono l)
  (fresh (a) (== `(,a) l)))


(defrel (listo l)
  (conde
   ((nullo l))
   ((fresh (d)
           (cdro l d) (listo d)))))


(defrel (lolo l)
  (conde
   ((nullo l))
   ((fresh (a d)
           (conso a d l)
           (listo a)
           (lolo d)))))


(defrel (loso l)
  (conde
   ((nullo l))
   ((fresh (x y)
           (conso x y l)
           (singletono x)
           (loso y)))))


(defrel (membero x l)
  (fresh (a d)
         (conso a d l)
         (conde
          ((== a x))
          ((membero x d)))))


(defrel (proper-membero x l)
  (fresh (a d)
         (listo d)
         (conso a d l)
         (conde
          ((== a x))
          ((membero x d)))))

(defrel (appendo s l out)
  (conde
   ((nullo s) (== l out))
   ((fresh (a d res)
           (conso a d s)
           (conso a res out)
           (appendo d l res)))))

(defrel (bad-appendo s l out)
  (conde
   ((nullo s) (== l out))
   ((fresh (a d res)
           (conso a d s)
           (bad-appendo d l res)
           (conso a res out)))))

; minimal witness of badness
; (run 2 (x y) (bad-appendo x y '()))


(defrel (unwrapo x out)
  (conde
   ((fresh (a) (caro x a) (unwrapo a out)))
   ((== x out))))

(defrel (memo x l out)
  (conde
   ((caro l x) (== l out))
   ((fresh (d) (cdro l d) (memo x d out)))))

(defrel (rembero x l out)
  (conde
   ((nullo l) (== out '()))
   ((conso x out l))
   ((fresh (a d res)
           (conso a d l)
           (conso a res out)
           (rembero x d res)))))

(defrel (alwayso)
  (conde
   (succeed)
   ((alwayso))))


(defrel (garlic-or-oniono q)
  (conde
   ((== 'garlic q) (alwayso))
   ((== 'onion q))))

; interleaved search

(defrel (garlic-or-Oniono q)
  (conde
   ((== 'garlic q) (alwayso))
   ((== 'onion q) (alwayso))))


(defrel (nevero) (nevero))

(defrel (succeed-or-losto)
  (conde
   ((nevero))
   (succeed)))

(defrel (very-recursiveo)
  (conde
   ((nevero))
   ((very-recursiveo))
   ((alwayso))
   ((very-recursiveo))
   ((nevero))))

(defrel (bit-xoro x y r)
  (conde
   ((== x 0)(== y 0)(== r 0))
   ((== x 1)(== y 1)(== r 0))
   ((== x 1)(== y 0)(== r 1))
   ((== x 0)(== y 1)(== r 1))))

(defrel (bit-ando x y r)
  (conde
   ((== x 0)(== y 0)(== r 0))
   ((== x 1)(== y 1)(== r 1))
   ((== x 1)(== y 0)(== r 0))
   ((== x 0)(== y 1)(== r 0))))


(defrel (half-addero x y r c)
  (bit-xoro x y r)
  (bit-ando x y c))

(defrel (full-addero b x y r c)
  (fresh (r-xy c-xy c-rxy-b)
         (half-addero x y r-xy c-xy)
         (half-addero r-xy b r c-rxy-b)
         (bit-xoro c-xy c-rxy-b c)))

(define (build-number n)
  (cond
    ((odd? n) (cons 1 (build-number (/ (- n 1) 2))))
    ((and (not (zero? n)) (even? n)) (cons 0 (build-number (/ n 2))))
    ((zero? n) '())))

(defrel (poso n)
  (fresh (a d) (== n `(,a . ,d))))

(defrel (>1o n)
  (fresh (a ad dd)
         (== `(,a ,ad . ,dd) n)))


#;(run* x (conda
           ((== 'olive x) succeed)
           (succeed (== 'oil x))))

#;(run* x
        (conda
         ((== 'virin x) fail)
         ((== 'olive x) succeed)
         (succeed (== 'oil x))))

; compare with above
#;(run* x
        (conde
         ((== 'virin x) fail)
         ((== 'olive x) succeed)
         (succeed (== 'oil x))))

#;(run* q
        (fresh (x y)
               (== 'split x)
               (== 'pea y)
               (conda
                ((== 'split x) (== x y))
                (succeed succeed))))

#;(run* q
        (fresh (x y)
               (== 'split x)
               (== 'pea y)
               (conda
                ((== x y)(== 'split x))
                (succeed succeed))))

#;(run* q
        (fresh (x y)
               (== 'split x)
               (== 'pea y)
               (conde
                ((== x y)(== 'split x))
                (succeed succeed))))

(defrel (not-pastao x)
  (conda
   ((== 'pasta x) fail)
   (succeed succeed)))

#;(run 2 x (not-pastao x))

#;(run* x
        (conda
         ((not-pastao x) fail)
         ((== 'spaghetti x) succeed)))

#;(run* x
        (== 'spaghetti x)
        (conda
         ((not-pastao x) fail)
         ((== 'spaghetti x) succeed)))

#;(run 5 q
       (conda
        ((alwayso) succeed)
        (succeed fail)))

#;(run* q
        (condu
         ((alwayso) succeed)
         (succeed fail)))

#;(run 3 q
       (condu
        (succeed (alwayso))
        (succeed fail)))

#;(run 1 q
       (conda
        ((alwayso) succeed)
        (succeed fail))
       fail)

#;(run 1 q
       (condu
        ((alwayso) succeed)
        (succeed fail))
       fail)

(defrel (teacupo t)
  (conde
   ((== t 'tea))
   ((== t 'cup))))

(defrel (onceo g)
  (condu
   (g succeed)
   (succeed fail)))

#;(run* x
      (onceo (teacupo x)))

; the above equals 
#;(run* x
      (condu
       ((conde
         ((== x 'tea))
         ((== x 'cup))) succeed)
       (succeed fail)))

#;(run* x
      (conde
       ((conde
         ((== x 'tea))
         ((== x 'cup))) succeed)
       ((== #f x) succeed)))

(run* x
      (conda
       ((conde
         ((== x 'tea))
         ((== x 'cup))) succeed)
       ((== #f x) succeed)))