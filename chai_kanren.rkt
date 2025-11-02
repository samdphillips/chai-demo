#lang racket/base

(require (for-syntax racket/base
                     syntax/parse)
         hosted-minikanren
         (except-in racket/match ==))

(define (->peano n)
  (for/fold ([r 'Z]) ([i (in-range n)]) (list 'S r)))

(define (peano-> p [r 0])
  (match p
    ['Z r]
    [`(S ,p) (peano-> p (add1 r))]))

(define-term-macro pn
  (syntax-parser
    [(_ n)
     #:declare n (expr/c #'exact-nonnegative-integer?)
     #'(term-from-expression (->peano n.c))]))

(define-term-macro num
  (syntax-parser
    [(_ p)
     #'(term-from-expression (peano-> p))]))

;; this generates infinite answers which may be a problem
#;
(defrel (peanoo v)
  (conde
   [(== 'Z v)]
   [(fresh (v^)
      (== v `(S ,v^))
      (peanoo v^))]))

(defrel (<o i j)
  (conde
   [(== i 'Z) (=/= j 'Z)]
   [(=/= i 'Z) (== j 'Z) fail]
   [(fresh (i^ j^)
      (sub1o i i^)
      (sub1o j j^)
      (<o i^ j^))]))

(defrel (<=o i j)
  (conde [(== i j)] [(<o i j)]))

(defrel (maxo m n o)
  (conde
   [(== m n) (== m o)]
   [(=/= m n) (== n o) (<o m n)]
   [(=/= m n) (== m o) (<o n m)]))

(defrel (mino m n o)
  (conde
   [(== m n) (== m o)]
   [(=/= m n)
    (conde
     [(== o n) (<o n m)]
     [(== o m) (<o m n)])]))

(defrel (add1o m n)
  (== n `(S ,m)))

(defrel (sub1o m n)
  (add1o n m))

(defrel (pluso m n o)
  (conde
   [(== m 'Z) (== n o)]
   [(fresh (m^ o^)
      (sub1o m m^)
      (sub1o o o^)
      (pluso m^ n o^))]))

(defrel (multo m n o)
  (conde
   [(<o o n) fail]
   [(<o o m) fail]
   [(== m 'Z) (== o 'Z)]
   [(== n 'Z) (== o 'Z)]
   [(== m (pn 1)) (== o n)]
   [(== n (pn 1)) (== o m)]
   [(=/= n (pn 1)) (=/= m (pn 1))
    (=/= m 'Z) (=/= n 'Z)
    (<o n o) (<o m o)
    (fresh (m^ n^)
      (sub1o m m^)
      (pluso n n^ o)
      (multo m^ n n^))]))

(defrel (arityo v)
  (fresh (m n)
    (== v `(ar ,m ,n))
    (<=o m n)))

(defrel (arity-overlapo u v)
  (conde
   [(== u v)]
   [(=/= u v)
    (fresh (u0 u1 v0 v1)
      (== u `(ar ,u0 ,u1))
      (== v `(ar ,v0 ,v1))
      (<=o u0 v0)
      (<=o v0 u1)
      (arityo u)
      (arityo v))]
   [(=/= u v)
    (fresh (u0 u1 v0 v1)
      (== u `(ar ,u0 ,u1))
      (== v `(ar ,v0 ,v1))
      (<=o u0 v1)
      (<=o v1 u1)
      (arityo u)
      (arityo v))]))

(defrel (join-arityo u v w)
  (conde
   ;; u-v equiv
   [(== u v) (== u w)]
   ;; u const
   [(fresh (u^ v0 v1)
      (=/= u v)
      (== u `(ar ,u^ ,u^))
      (=/= v0 v1)
      (== v `(ar ,v0 ,v1))
      (<=o v0 u^)
      (<=o u^ v1)
      (== u w))]
   ;; u-v swap
   [(fresh (u0 u1 v^)
      (=/= u v)
      (== u `(ar ,u0 ,u1))
      (=/= u0 u1)
      (== v `(ar ,v^ ,v^))
      (join-arityo v u w))]
   ;; narrowing
   [(fresh (u0 u1 v0 v1 w0 w1)
      (=/= u v)
      (arity-overlapo u v)
      (== u `(ar ,u0 ,u1))
      (== v `(ar ,v0 ,v1))
      (== w `(ar ,w0 ,w1))
      (maxo u0 v0 w0)
      (mino u1 v1 w1))]))
