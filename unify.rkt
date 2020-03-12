#lang scheme

(define (var name) (vector name))
(define var? vector?)

(define x (var 'x))
(define y (var 'y))
(define z (var 'z))
(define u (var 'u))
(define v (var 'v))
(define w (var 'w))


(define empty-s '())


;; straight forward logic
#; (define (walk v s)
     (let ((a (assv v s)))
       (cond
         ((pair? a)
          (cond
            ((or (not (var? (cdr a)))
                 (and (var? (cdr a))
                      (not (assv (cdr a) s))))
             (cdr a))
            (else (walk (cdr a) s))))
         (else v))))

;; logic simplified by boolean algebra
#; (define (walk v s)
     (let ((a (assv v s)))
       (cond
         ((pair? a)
          (cond
            ((not (and
                   (var? (cdr a))
                   (assv (cdr a) s)))
             (cdr a))
            (else (walk (cdr a) s))))
         (else v))))


;; swap cond lines and use let
#; (define (walk v s)
     (let ((a (assv v s)))
       (cond
         ((pair? a)
          (let ((ca (cdr a)))
            (cond
              ((and (var? ca)
                    (assv ca s))
               (walk ca s))
              (else ca))))
         (else v))))


;; logic further simplified
;; by exploiting recursion
#; (define (walk v s)
     (let ((a (assv v s)))
       (cond
         ((pair? a)
          (let ((ca (cdr a)))  
            (cond
              ((var? ca) (walk ca s))
              (else ca))))
         (else v))))


;; by trs2 authors
;; further exploits recursion
(define (walk e s)
  (let ((a (and (var? e)(assv e s))))
    (cond
      ((pair? a)(walk (cdr a) s))
      (else e))))


;(walk x `((,x . a)(,y . b)))
;
;(walk x `((,x . ,z)(,y . b)))
;
;(walk x `((,x . `(,y a))(,y . b)))
;
;(walk x `((,x . ,y)(,y . b)))
;
;(walk u `((,x . a)(,y . b)))

(define (ext-s x v s)
  (cond
    ((occurs? x v s) #f)
    (else (cons `(,x . ,v) s))))

(define (occurs? x v s)
  (let ((e (walk v s)))
    (cond
      ((var? e)(eqv? e x))
      ((pair? e)
       (or (occurs? x (car e) s)
           (occurs? x (cdr e) s)))
      (else #f))))

(define (unify u v s)
  (let ((u (walk u s))(v (walk v s)))
    (cond
      ((eqv? u v) s)
      ((var? u)(ext-s u v s))
      ((var? v)(ext-s v u s))
      ((and (pair? u)(pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s
              (unify (cdr u) (cdr v) s))))
      (else #f))))

(define (== u v)
  (lambda (s)
    (let ((s (unify u v s)))
      (if s `(,s) '()))))

(define succeed
  (lambda (s) `(,s)))

(define fail
  (lambda (s) '()))

(define (append-inf s-inf t-inf)
  (cond
    ((null? s-inf) t-inf)
    ((pair? s-inf)
     (cons (car s-inf)
           (append-inf (cdr s-inf) t-inf)))
    (else (lambda ()
            (append-inf t-inf (s-inf))))))

(define (disj2 g1 g2)
  (lambda (s)
    (append-inf (g1 s) (g2 s))))

(define (nevero)
  (lambda (s)
    (lambda () ((nevero) s))))

#;(let ((s-inf ((disj2 (== 'olive x) (nevero)) empty-s))) s-inf)

#;(let ((s-inf ((disj2 (== 'olive x) (nevero)) empty-s)))
    (let ((cs (cdr s-inf))) cs))

#;(let ((s-inf ((disj2 (nevero) (== 'olive x)) empty-s)))
    s-inf)

#;(let ((s-inf ((disj2 (nevero) (== 'olive x)) empty-s)))
    (s-inf))

(define (alwayso)
  (lambda (s)
    (lambda ()
      ((disj2 succeed (alwayso)) s))))

#;(((alwayso) empty-s))

#;(let ((s-inf (((alwayso) empty-s))))
    (cons (car s-inf) '()))

#;(let ((s-inf (((alwayso) empty-s))))
    (cons (car s-inf)
          (let ((s-inf ((cdr s-inf))))
            (cons (car s-inf) '()))))

#;(let ((s-inf (((alwayso) empty-s))))
    (cons (car s-inf)
          (let ((s-inf ((cdr s-inf))))
            (cons (car s-inf)
                  (let ((s-inf ((cdr s-inf))))
                    (cons (car s-inf) '()))))))

(define (take-inf n s-inf)
  (cond
    ((and n (zero? n))'())
    ((null? s-inf) '())
    ((pair? s-inf)
     (cons (car s-inf)
           (take-inf (and n (sub1 n))
                     (cdr s-inf))))
    (else (take-inf n (s-inf)))))

#;(let ((k (length
            (take-inf 5
                      ((disj2 (== 'olive x)
                              (== 'oil x))
                       empty-s)))))
    `(Found ,k not 5 substitutions))

#;(map length
       (take-inf 5
                 ((disj2 (== 'olive x)
                         (== 'oil x))
                  empty-s)))

(define (append-map-inf g s-inf)
  (cond
    ((null? s-inf) '())
    ((pair? s-inf)
     (append-inf (g (car s-inf))
                 (append-map-inf g (cdr s-inf))))
    (else (lambda ()
            (append-map-inf g (s-inf))))))

(define (conj2 g1 g2)
  (lambda (s)
    (append-map-inf g2 (g1 s))))

(define (call/fresh name f)
  (f (var name)))

#;(take-inf 1 ((call/fresh 'kiwi
                           (lambda (fruit)
                             (== 'plum fruit)))
               empty-s))

(define (reify-name n)
  (string->symbol
   (string-append "_"
                  (number->string n))))

(define (walk* v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v)
       (cons
        (walk* (car v) s)
        (walk* (cdr v) s)))
      (else v))))

(define (reify-s v r)
  (let ((v (walk v r)))
    (cond
      ((var? v)
       (let ((n (length r)))
         (let ((rn (reify-name n)))
           (cons `(,v . ,rn) r))))
      ((pair? v)
       (let ((r (reify-s (car v) r)))
         (reify-s (cdr v) r)))
      (else r))))

#;(reify-s x '())

#;(reify-s `(,x ,y) '())

#;(reify-s y `((,x . _0)))

#;(reify-s `(,x e) '())

#;(reify-s `(,x ,x) '())

#;(reify-s x `((,x . _0)))

#;(reify-s `(,x (e ,y) ((,z))) '())

(define (reify v)
  (lambda (s)
    (let ((v (walk* v s)))
      (let ((r (reify-s v empty-s)))
        (walk* v r)))))


#;(let ((a1 `(,x . (,u ,w ,y ,z ((ice) ,z))))
        (a2 `(,y . corn))
        (a3 `(,w . (,v ,u))))
    (let ((s `(,a1 ,a2 ,a3)))
      (walk* x s)))

#;(let ((a1 `(,x . (,u ,w ,y ,z ((ice) ,z))))
        (a2 `(,y . corn))
        (a3 `(,w . (,v ,u))))
    (let ((s `(,a1 ,a2 ,a3)))
      ((reify x) s)))

#;(map (reify x)
       (take-inf 5
                 ((disj2 (== 'olive x)
                         (== 'oil x)) empty-s)))

(define (run-goal n g)
  (take-inf n (g empty-s)))


#;(map (reify x)
       (run-goal 5
                 (disj2 (== 'olive x)
                        (== 'oil x))))

(define (ifte g1 g2 g3)
  (lambda (s)
    (let loop ((s-inf (g1 s)))
      (cond
        ((null? s-inf) (g3 s))
        ((pair? s-inf) (append-map-inf g2 s-inf))
        (else (lambda () (loop (s-inf))))))))

; my version of ifte by resolved named-let

(define (ifte-helper s-inf)
  (lambda (g2 g3 s)
    (cond
      ((null? s-inf) (g3 s))
      ((pair? s-inf) (append-map-inf g2 s-inf))
      (else (lambda () ((ifte-helper (s-inf)) g2 g3 s))))))

(define (iftes g1 g2 g3)
  (lambda (s)
    ((ifte-helper (g1 s)) g2 g3 s)))

#;((iftes succeed (== x 'olive) (== x 'oil)) empty-s)

#;((iftes fail (== x 'olive) (== x 'oil)) empty-s)

#;((iftes (disj2 (== y 'spicy) (== y 'greek))
          (== x 'olive) (== x 'oil)) empty-s)

#;((ifte succeed (== x 'olive) (== x 'oil)) empty-s)

#;((ifte fail (== x 'olive) (== x 'oil)) empty-s)

#;((ifte (disj2 (== y 'spicy) (== y 'greek))
         (== x 'olive) (== x 'oil)) empty-s)

(define (nullo x)
  (== '() x))

(define (conso a d p)
  (== p (cons a d)))

(define (appendo left right total)
  (lambda (s)
    ((disj2 (conj2 (nullo left) (== right total))
            (call/fresh
             'a
             (lambda (a)
               (call/fresh
                'd
                (lambda (d)
                  (call/fresh
                   'res
                   (lambda (res)
                     (conj2 (conso a d left)
                            (conj2 (conso a res total)
                                   (appendo d right res))))))))))
     s)))

(let ((r ((appendo x y '(1 2 3)) empty-s)))
  (let ((s1 (car r)))
    (let ((s2 (car (cdr r))))
      (let ((s3 (car (cdr (cdr r)))))
        (let ((s4 (car (cdr (cdr (cdr r))))))
          (list
           (list `(,x . ,(walk* x s1)) `(,y . ,(walk* y s1)))
           (list `(,x . ,(walk* x s2)) `(,y . ,(walk* y s2)))
           (list `(,x . ,(walk* x s3)) `(,y . ,(walk* y s3)))
           (list `(,x . ,(walk* x s4)) `(,y . ,(walk* y s4)))))))))
  

(let ((q (var 'q)))
  (map (reify q)
       (run-goal
        #f
        (call/fresh
         'x
         (lambda (x)
           (call/fresh
            'y
            (lambda (y)
              (conj2
               (== q `(,x ,y))
               (appendo x y
                        '(cake & ice d t))))))))))