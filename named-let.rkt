#lang scheme

(define (sepnum numbers nonneg neg)
  (cond
    ((null? numbers) (list nonneg neg))
    ((>= (car numbers) 0)
     (sepnum (cdr numbers)
             (cons (car numbers) nonneg)
             neg))
    (else
     (sepnum (cdr numbers)
             nonneg
             (cons (car numbers) neg)))))

(sepnum '(3 -2 1 6 -5) '() '())

(let loop
  ((numbers '(3 -2 1 6 -5))
   (nonneg '())
   (neg '()))
  (cond
    ((null? numbers) (list nonneg neg))
    ((>= (car numbers) 0)
     (loop (cdr numbers)
             (cons (car numbers) nonneg)
             neg))
    (else
     (loop (cdr numbers)
             nonneg
             (cons (car numbers) neg)))))