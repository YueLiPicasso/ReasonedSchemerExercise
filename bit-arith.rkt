#lang scheme

(require trs2impl)

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

(defrel (bit-nando x y r)
  (conde
   ((== x 0)(== y 0)(== r 1))
   ((== x 1)(== y 1)(== r 0))
   ((== x 1)(== y 0)(== r 1))
   ((== x 0)(== y 1)(== r 1))))

(defrel (half-addero x y r c)
  (conde
   ((== x 0)(== y 0)(== r 0)(== c 0))
   ((== x 0)(== y 1)(== r 1)(== c 0))
   ((== x 1)(== y 0)(== r 1)(== c 0))
   ((== x 1)(== y 1)(== r 0)(== c 1))))

(defrel (full-addero b x y r c)
  (conde
   ((== b 0)(== x 0)(== y 0)(== r 0)(== c 0))
   ((== b 0)(== x 0)(== y 1)(== r 1)(== c 0))
   ((== b 0)(== x 1)(== y 0)(== r 1)(== c 0))
   ((== b 0)(== x 1)(== y 1)(== r 0)(== c 1))
   ((== b 1)(== x 0)(== y 0)(== r 1)(== c 0))
   ((== b 1)(== x 0)(== y 1)(== r 0)(== c 1))
   ((== b 1)(== x 1)(== y 0)(== r 0)(== c 1))
   ((== b 1)(== x 1)(== y 1)(== r 1)(== c 1))))


(defrel (poso n)
  (fresh (a d) (== n `(,a . ,d))))

(defrel (>1o n)
  (fresh (a b c)
         (== `(,a ,b . ,c) n)))

(defrel (addero b n m r)
  (conde
   ((== 0 b)(== '() m)(== n r))
   ((== 0 b)(poso m)(== '() n)(== m r))
   ((== 1 b)(== '() m)(addero 0 n '(1) r))
   ((== 1 b)(poso m)(== '() n)(addero 0 '(1) m r))
   ((== '(1) n)(== '(1) m)
               (fresh (a c)
                      (== `(,a ,c) r)
                      (full-addero b 1 1 a c)))
   ((== '(1) n)(gen-addero b n m r))
   ((>1o n)(== '(1) m)(>1o r)(addero b '(1) n r))
   ((>1o n)(gen-addero b n m r))))


(defrel (gen-addero b n m r)
  (fresh (a c d e x y z)
         (== `(,a . ,x) n)
         (== `(,d . ,y) m) (poso y)
         (== `(,c . ,z) r)(poso z)
         (full-addero b a d c e)
         (addero e x y z)))

(defrel (+o n m k) (addero 0 n m k))

(defrel (-o n m k) (+o m k n))

(defrel (lengtho l n)
  (conde
   ((== l '())(== n '()))
   ((fresh (a d ld) (== `(,a . ,d) l)
           (+o '(1) ld n)
           (lengtho d ld)))))

(defrel (sign-bito int s n)
  (== `(,s . ,n) int))

(defrel (bit-flipo b1 b2)
  (conde
   ((== b1 0)(== b2 1))
   ((== b1 1)(== b2 0))))

(defrel (sumo int1 int2 int)
  (conde
   ((fresh (sgn n1 n2 absum) 
           (sign-bito int1 sgn n1)
           (sign-bito int2 sgn n2)
           (+o n1 n2 absum)
           (== int `(,sgn . ,absum))))
   ((fresh (n1 n2 sg1 sg2 diff)
           (sign-bito int1 sg1 n1)
           (sign-bito int2 sg2 n2)
           (bit-flipo sg1 sg2)
           (conde
            ((-o n1 n2 diff)(== int `(,sg1 . ,diff)))
            ((-o n2 n1 diff)(== int `(,sg2 . ,diff))))))))

(defrel (*o n m p) ; n is multiplier and m the multiplicand
  (conde
   ((== n '())(== p '()))
   ((poso n)(== m '())(== p '()))
   ((poso m)(== n '(1))(== p m))
   ((>1o n)(== m '(1))(== p n))
   ((fresh (x z)
           (>1o m)
           (== `(0 . ,x) n)(poso x)
           (== `(0 . ,z) p)(poso z)
           (*o x m z)))
   ((fresh (x y)
           (== `(1 . ,x) n)(poso x)
           (== `(0 . ,y) m)(poso y)
           (*o m n p)))
   ((fresh (x y)
           (== `(1 . ,x) n)(poso x)
           (== `(1 . ,y) m)(poso y)
           (odd-*o x n m p)))))

(defrel (odd-*o x n m p)
  (fresh (q)
         (bound-*o q p n m)
         (*o x m q)
         (+o `(0 . ,q) m p)))

(defrel (bound-*o q p n m)
  (conde
   ((== '() q)(poso p))
   ((fresh (a0 a1 a2 x y z)
           (== `(,a0 . ,x) q)
           (== `(,a1 . ,y) p)
           (conde
            ((== '() n)
             (== `(,a2 . ,z) m)
             (bound-*o x y z '()))
            ((== `(,a2 . ,z) n)
             (bound-*o x y z m)))))))


(defrel (=lo n m)
  (conde
   ((== '() n)(== '() m))
   ((== '(1) n)(== '(1) m))
   ((fresh (a x b y)
           (== `(,a . ,x) n)(poso x)
           (== `(,b . ,y) m)(poso y)
           (=lo x y)))))

(defrel (<lo n m)
  (conde
   ((== '() n)(poso m))
   ((== '(1) n)(>1o m))
   ((fresh (a x b y)
           (== `(,a . ,x) n)(poso x)
           (== `(,b . ,y) m)(poso y)
           (<lo x y)))))

(defrel (<=lo n m)
  (conde
   ((=lo n m))
   ((<lo n m))))

(defrel (<o n m)
  (conde
   ((<lo n m))
   ((=lo n m)
    (fresh (x)
           (poso x)
           (+o n x m)))))

(defrel (<=o n m)
  (conde
   ((== n m))
   ((<o n m))))

#;(defrel (/o n m q r)
  (conde
   ((== q '())(== n r)(<o n m))
   ((== q '(1))(== r '())(== n m)(<o r m))
   ((<o m n)(<o r m)
            (fresh (mq)
                   (<=lo mq n)
                   (*o m q mq)
                   (+o mq r n)))))

(defrel (splito n r l h)
  (conde
   ((== '() n)(== '() h)(== '() l))
   ((fresh (b n^)
           (== `(0 ,b . ,n^) n)(== '() r)
           (== `(,b . ,n^) h)(== '() l)))
   ((fresh (n^)
           (== `(1 . ,n^) n)(== '() r)
           (== n^ h)(== '(1) l)))
   ((fresh (b n^ a r^)
          (== `(0 ,b . ,n^) n)
          (== `(,a . ,r^) r)(== '() l)
          (splito `(,b . ,n^) r^ '() h)))
   ((fresh (n^ a r^)
           (== `(1 . ,n^) n)
           (== `(,a . ,r^) r)(== '(1) l)
           (splito n^ r^ '() h)))
   ((fresh (b n^ a r^ l^)
           (== `(,b . ,n^) n)
           (== `(,a . ,r^) r)
           (== `(,b . ,l^) l)
           (poso l^)
           (splito n^ r^ l^ h)))))

(defrel (/o n m q r)
  (conde
   ((== '() q)(== r n)(<o n m))
   ((== '(1) q)(=lo m n)(+o r m n)
               (<o r m))
   ((poso q)(<lo m n)(<o r m)
            (n-wider-than-mo n m q r))))

(defrel (n-wider-than-mo n m q r)
  (fresh (nh nl qh ql)
         (fresh (mql mrql rr rh)
                (splito n r nl nh)
                (splito q r ql qh)
                (conde
                 ((== '() nh)
                  (== '() qh)
                  (-o nl r mql)
                  (*o m ql mql))
                 ((poso nh)
                  (*o m ql mql)
                  (+o r mql mrql)
                  (-o mrql nl rr)
                  (splito rr r '() rh)
                  (/o nl m qh rh))))))

