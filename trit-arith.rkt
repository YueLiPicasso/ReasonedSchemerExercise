#lang scheme

(require trs2impl)

; trinary digit -- trit 0, 1 and 2
; encoding a natural number using trits
; 0 '()
; 1 '(1)
; 2 '(2)
; 3 '(0 1)
; 4 '(1 1)
; 5 '(2 1)
; 6 '(0 2)
; etc

; convert a nat to a list of trits 
(define (build-number n)
  (cond
    ((eq? n 0) '())
    ((> n 0)
     (cons
      (modulo n 3)
      (build-number (/ (- n (modulo n 3)) 3))))))

(defrel (half-addero n m r c) ; n m r c are trits 
  (conde
   ((== n 0)(== m 0)(== r 0)(== c 0))
   ((== n 0)(== m 1)(== r 1)(== c 0))
   ((== n 0)(== m 2)(== r 2)(== c 0))
   ((== n 1)(== m 0)(== r 1)(== c 0))
   ((== n 1)(== m 1)(== r 2)(== c 0))
   ((== n 1)(== m 2)(== r 0)(== c 1))
   ((== n 2)(== m 0)(== r 2)(== c 0))
   ((== n 2)(== m 1)(== r 0)(== c 1))
   ((== n 2)(== m 2)(== r 1)(== c 1))))

(defrel (full-addero t n m r c) ; t is carry-in trit, n m r c are trits
  (conde
   ((== t 0)(== n 0)(== m 0)(== r 0)(== c 0)) 
   ((== t 0)(== n 0)(== m 1)(== r 1)(== c 0)) 
   ((== t 0)(== n 0)(== m 2)(== r 2)(== c 0)) 
   ((== t 0)(== n 1)(== m 0)(== r 1)(== c 0)) 
   ((== t 0)(== n 1)(== m 1)(== r 2)(== c 0))
   ((== t 0)(== n 1)(== m 2)(== r 0)(== c 1))
   ((== t 0)(== n 2)(== m 0)(== r 2)(== c 0))
   ((== t 0)(== n 2)(== m 1)(== r 0)(== c 1))
   ((== t 0)(== n 2)(== m 2)(== r 1)(== c 1)) ; t = 0
   ((== t 1)(== n 0)(== m 0)(== r 1)(== c 0))
   ((== t 1)(== n 0)(== m 1)(== r 2)(== c 0))
   ((== t 1)(== n 0)(== m 2)(== r 0)(== c 1))
   ((== t 1)(== n 1)(== m 0)(== r 2)(== c 0))
   ((== t 1)(== n 1)(== m 1)(== r 0)(== c 1))
   ((== t 1)(== n 1)(== m 2)(== r 1)(== c 1))
   ((== t 1)(== n 2)(== m 0)(== r 0)(== c 1))
   ((== t 1)(== n 2)(== m 1)(== r 1)(== c 1))
   ((== t 1)(== n 2)(== m 2)(== r 2)(== c 1)))) ; t = 2

(defrel (poso n)
  (fresh (a b) (== n `(,a . ,b))))

(defrel (>2o n)
  (fresh (a b c) (== n `(,a ,b . ,c))))


(defrel (addero t n m r) ; t -- carry-in trit, n m r -- btrinary numbers
  (conde
   ((== t 0)(== n '())(== r m))
   ((== t 0)(poso n)(== m '())(== r n))
   ((== t 1)(== n '())(addero 0 '(1) m r))
   ((== t 1)(poso n)(== m '())(addero 0 n '(1) r))
   ((poso n)(poso m)(gen-addero t n m r))))

(defrel (gen-addero t n m r)
  (fresh (a b c x y z e) 
         (== `(,a . ,x) n)
         (== `(,b . ,y) m)
         (== `(,c . ,z) r)
         (full-addero t a b c e)
         (addero e x y z)))

(defrel (+o n m r) (addero 0 n m r))