#lang debug racket/base

(require racket/format
         racket/list
         racket/match
         (only-in racket/math nonnegative-integer?)
         racket/set
         racket/treelist)

(module+ test
  (require rackunit))

(define (warning who msg . vals)
  (eprintf "~a: ~a~%" who (apply format msg vals)))

(define (arity? v)
  (match v
    [(or (? nonnegative-integer?)
         (list '>= (? nonnegative-integer?))) #t]
    [_ #f]))

(define (arity-exact? v)
  (and (arity? v) (nonnegative-integer? v)))

(define (check-arity who v)
  (unless (arity? v)
    (error who "expected arity: ~a" v)))

(define (arity-decl? term)
  (match term
    [(list (? arity?) (? arity?)) #t]
    [_ #f]))

(define var? symbol?)

(define (known-return-arity rator)
  (match rator
    [(or '+ '- '* '/ 'add1 'sub1) 1]
    [(or 'quotient/remainder) 2]
    [_ '(>= 0)]))

(define (join-arities a b)
  (match* (a b)
    [(_ (== a)) a]
    [((? nonnegative-integer?) (? nonnegative-integer?)) #f]
    [((list '>= m) (list '>= n)) `(>= ,(max m n))]
    [((? nonnegative-integer?) _) (join-arities b a)]
    [((list '>= m) n) (and (>= n m) n)]))

(module+ test
  (check-equal? (join-arities 0 0) 0)
  (check-equal? (join-arities 3 3) 3)
  (check-equal? (join-arities '(>= 0) '(>= 0)) '(>= 0))
  (check-equal? (join-arities '(>= 0) 3) 3)
  (check-equal? (join-arities 3 '(>= 0)) 3)
  (check-equal? (join-arities '(>= 3) 3) 3)
  (check-equal? (join-arities 3 '(>= 3)) 3)
  (check-equal? (join-arities '(>= 2) 3) 3)
  (check-equal? (join-arities 3 '(>= 2)) 3)
  (check-equal? (join-arities '(>= 2) '(>= 3)) '(>= 3))
  (check-equal? (join-arities '(>= 3) '(>= 2)) '(>= 3))

  (check-false (join-arities 0 3))
  (check-false (join-arities '(>= 3) 2))
  (check-false (join-arities 2 '(>= 3))))

#|
(<flop> <arity-infos> . <floargs>)
(<connops <arity-infos> . <conargs>)

<arity-infos> := (<info> <info>)
<info> := (<lvar> <arity>)
        | ((<var> ...) <arity>)
        | (((<var> ...) <arity>) ...)
|#

(define (floe-infos floe)
  (match floe
    [`(,_ (,in ,out) . ,_) (values in out)]))

(define (floe-in floe)
  (define-values (in out) (floe-infos floe))
  in)

(define (floe-out floe)
  (define-values (in out) (floe-infos floe))
  out)

(define (info-lvar info)
  (match info
    [(list (? symbol? v) _) v]
    [(? symbol? v) v]))

(define (info-simple? info)
  (match info
    [(list _ (? arity?)) #t]
    [_ #f]))

(define (info-compound? info)
  (match info
    ;; just check the first element to determine compound-ness
    [(list* (list (or (list) (list* (? symbol?) _)) (? arity?)) _) #t]
    [_ #f]))

(define (info-arity info)
  (cond
    [(info-simple? info) (info-simple-arity info)]
    [else (for/list ([i (in-list info)]) (info-simple-arity i))]))

(define (info-simple-arity info)
  (match info
    [(list _ a) a]
    [_ #f]))

(define (info-effective-arity info)
  (cond
    [(info-simple? info) (info-simple-arity info)]
    [else
     (for/fold ([s 0]) ([info (in-list info)])
       (match* (s (info-simple-arity info))
         [(`(>= ,s) (or `(>= ,i) i)) `(>= ,(+ s i))]
         [(s `(>= ,i)) `(>= ,(+ s i))]
         [(s i) (+ s i)]))]))

(define (info-simple-vars info)
  (match info
    [(list (list (? symbol? v*) ...) _) v*]
    [_ (error 'info-simple-vars "info not simple: ~a" info)]))

#;#;
(define (info-compound-vars info) ...)

(define (info-compound-arity info) ...)

(define ((make-floe-accessor ref) floe)
  (define-values (in out) (floe-infos floe))
  (values (ref in) (ref out)))

(define floe-lvars (make-floe-accessor info-lvar))
(define floe-arities (make-floe-accessor info-simple-arity))
(define floe-vars (make-floe-accessor info-simple-vars))

(define (add-lvars* floe*) (map add-lvars floe*))

(define (add-lvars floe)
  (define-values (rator arity rands)
    (match floe
      [`(,rator ,(? arity-decl? arity) . ,rands)
       (values rator arity rands)]
      [`(,rator . ,rands)
       (values rator #f rands)]))
  (define i (gensym (~a rator "-in")))
  (define o (gensym (~a rator "-out")))
  (define names
    (if arity
        (list (list i (car arity))
              (list o (cadr arity)))
        (list i o)))
  (match rator
    [(or 'thread 'tee 'relay)
     `(,rator ,names ,@(add-lvars* rands))]
    [_ `(,rator ,names ,@rands)]))

(define (constraint-simplify cst)
  (let do-simplify ([cst cst])
    (define next
      (match cst
        [`(arity-sum ,s) `(has-arity ,s 0)]
        [`(arity-sum ,s ,v) `(has-arity ,s ,v)]
        [`(arity-sum ,s 0 . ,v*) `(arity-sum ,s . ,v*)]
        [_ cst]))
    (if (equal? cst next) cst (do-simplify next))))

(define (constraints-add cst* cst)
  (set-add cst* (constraint-simplify cst)))

(define (constraints-add-all cst* . more-cst*)
  (for/fold ([cst* cst*]) ([cst (in-list more-cst*)])
    (constraints-add cst* cst)))

(define (generate-constraints/thread cst* i o floe*)
  (define-values (final-o cst*^)
    (for/fold ([last-o i] [cst* cst*]) ([floe (in-list floe*)])
      (define-values (fin fout) (floe-lvars floe))
      (values fout
              (constraints-add cst* `(has-arity ,last-o ,fin)))))
  (define cst*^^ (constraints-add cst*^ `(has-arity ,final-o ,o)))
  (generate-constraints* cst*^^ floe*))

(define (generate-constraints/tee cst* i o floe*)
  (define-values (cst*^ fo*)
    (for/fold ([cst* cst*] [fo* null]) ([floe (in-list floe*)])
      (define-values (fi fo) (floe-lvars floe))
      (values (constraints-add cst* `(has-arity ,i ,fi))
              (cons fo fo*))))
  (generate-constraints* (constraints-add cst*^ `(arity-sum ,o ,@fo*))
                         floe*))

(define (generate-constraints/relay cst* i o floe*)
  (define-values (cst*^ fo*)
    (for/fold ([cst* cst*] [fo* null]) ([floe (in-list floe*)])
      (define-values (fi fo) (floe-lvars floe))
      (values (constraints-add cst* `(has-arity ,fi 1))
              (cons fo fo*))))
  (define cst*^^ (constraints-add cst*^ `(has-arity ,i ,(length floe*))))
  (generate-constraints* (constraints-add cst*^^ `(arity-sum ,o ,@fo*))
                         floe*))

(define (generate-constraints/fine-template cst* i o expr)
  (define (count-placeholders expr)
    (for/fold ([i 0]) ([t expr])
      (if (eq? t '_) (add1 i) i)))
  (constraints-add-all cst*
                       `(has-arity ,i ,(count-placeholders expr))
                       `(has-arity ,o ,(known-return-arity (car expr)))))

(define (generate-constraints* cst* floe*)
  (for/fold ([cst* cst*]) ([floe (in-list floe*)])
    (generate-constraints cst* floe)))

(define (generate-constraints cst* floe)
  (define-values (rator i o ai ao rands)
    (match floe
      [`(,rator (,(? symbol? i) ,(? symbol? o)) . ,rands)
       (values rator i o #f #f rands)]
      [`(,rator ((,i ,ai) (,o ,ao)) . ,rands)
       (values rator i o ai ao rands)]))
  (define (add-decl-constraints cst* var arity)
    (match arity
      [#f cst*]
      [n  (constraints-add cst* `(has-arity ,var ,n))]))
  (let* ([cst* (add-decl-constraints cst* i ai)]
         [cst* (add-decl-constraints cst* o ao)])
    (match rator
      ['as
       (constraints-add-all cst*
                            `(has-arity ,i ,(length rands))
                            `(has-arity ,o 0))]
      ['ground
       (constraints-add-all cst*
                            `(has-arity ,i (>= 0))
                            `(has-arity ,o 0))]
      ['gen
       (constraints-add-all cst*
                            `(has-arity ,i (>= 0))
                            `(has-arity ,o ,(length rands)))]
      ['select
       (constraints-add-all cst*
                            `(has-arity ,i (>= ,(apply max rands)))
                            `(has-arity ,o ,(length rands)))]
      ['esc
       (constraints-add-all cst*
                            `(has-arity ,i (>= 0))
                            `(has-arity ,o (>= 0)))]
      ['thread
       (generate-constraints/thread cst* i o rands)]
      ['tee
       (generate-constraints/tee cst* i o rands)]
      ['relay
       (generate-constraints/relay cst* i o rands)]
      ['#%fine-template
       (generate-constraints/fine-template cst* i o (car rands))]
      )))

(define (update-subst subst var tgt)
  (unless (var? var)
    (error 'update-subst
           "lhs of update not a var: ~a"
           var))
  (hash-set subst var tgt))

(define (resolve subst v)
  (cond
    [(var? v)
     (let walk ([v v])
       (match (hash-ref subst v #f)
         [(? var? v^) (walk v^)]
         [a (values v a)]))]
    [else (values #f v)]))

(define (resolve/value subst var)
  (define-values (var^ val) (resolve subst var))
  val)

(define (apply-constraint/has-arity subst u v)
  (define (do-error)
    (error 'apply-constraint/has-arity
           "cannot unify ~a = ~a" u v))
  (define (update s t)
    (update-subst subst s t))
  (define (join/update v s t)
    (match (join-arities s t)
      [#f (do-error)]
      [a (update v a)]))

  (define-values (u^ uv) (resolve subst u))
  (define-values (v^ vv) (resolve subst v))
  (match* (u^ v^ uv vv)
    [(#f #f  u  v) (if (join-arities u v)
                       subst
                       (do-error))]

    [(#f v^  u #f) (update v^ u)]
    [(u^ #f #f  v) (update u^ v)]
    [(#f v^  u  v) (join/update v^ v u)]
    [(u^ #f  u  v) (join/update u^ u v)]

    [(u^ v^ #f #f) (if (eq? u^ v^) subst (update u^ v^))]
    [(u^ v^ #f  v) (update u^ v^)]
    [(u^ v^  u #f) (update v^ u^)]
    [(u^ v^  u  v) (update-subst (join/update v^ v u) u^ v^)]))

(module+ test
  (define (canon-subst subst)
    (for/hasheq ([k (in-hash-keys subst)]
                 #:do [(define-values (c v) (resolve subst k))]
                 #:when v)
      (values k v)))

  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq) 'a 'b))
                (hasheq))

  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq) 'a 10))
                (hasheq 'a 10))
  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq) 10 'a))
                (hasheq 'a 10))
  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq 'a 10) 'a 10))
                (hasheq 'a 10))
  (check-exn exn? (λ () (apply-constraint/has-arity (hasheq 'a 10) 'a 11)))

  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq 'a 10) 'a '(>= 0)))
                (hasheq 'a 10))

  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq 'a '(>= 0)) 'a '(>= 2)))
                (hasheq 'a '(>= 2)))

  (check-exn exn? (λ () (apply-constraint/has-arity (hasheq 'a '(>= 2)) 'a 1)))

  (check-equal? (canon-subst
                 (apply-constraint/has-arity (hasheq 'a 'b 'b 1) 'a '(>= 0)))
                (hasheq 'a 1 'b 1))

  (check-equal? (let* ([subst (hasheq 'a '(>= 0))]
                       [subst (apply-constraint/has-arity subst 'a 'b)]
                       [subst (apply-constraint/has-arity subst 'b 0)])
                  (canon-subst subst))
                (hasheq 'a 0 'b 0)))

(define (apply-constraint/arity-sum subst s v*)
  (define (mk cst) (constraints-add (set) cst))
  (define-values (s^ sv) (resolve subst s))
  (define-values (n v^*)
    (for/fold ([n 0]
               [v* null]
               #:result (values n (reverse v*)))
              ([v (in-list v*)])
      (define-values (v^ vv) (resolve subst v))
      (cond
        ;; XXX: use `integer?` to allow for "adjust-by" constraints
        [(integer? vv) (values (+ n vv) v*)]
        [else
         ;; not an integer then it is either "partially" solved
         ;; (arity-at-least) or unsolved.  For either keep the canonical
         ;; variable
         (values n (cons v^ v*))])))
  (match* (s^ sv n v^*)
    [(#f s n '())
     (mk `(has-arity ,s ,n))]
    [(#f s n (list v))
     (mk `(has-arity ,v ,(- s n)))]
    [(#f s n v^*)
     (mk `(arity-sum ,(- s n) . ,v^*))]
    [(s^ #f n '())
     (mk `(has-arity ,s^ ,n))]
    [(s^ #f n v^*)
     (mk `(arity-sum ,s^ ,n . ,v^*))]
    [(s^ _ n '())
     (mk `(has-arity ,s^ ,n))]
    [(s^ `(>= ,sn) n (list v^))
     (define vnt (- sn n))
     (define sv^ `(>= ,vnt))
     (set-union (mk `(arity-sum ,s^ ,n ,v^))
                (match/values (resolve subst v^)
                  [(_ #f) (mk `(has-arity ,v^ ,sv^))]
                  [(_ (and vv `(>= ,vn)))
                   (cond
                     [(= vn vnt) (set)]
                     [(> vn vnt) (error 'apply-constraint/arity-sum
                                        "cannot unify ~a = ~a" sv^ vv)]
                     [else (mk `(has-arity ,v^ ,sv))])]))]
    [(s^ `(>= ,_) n v^*)
     (mk `(arity-sum ,s^ ,n . ,v^*))]
    [(s^ sv n v^*)
     (mk `(arity-sum ,(- sv n) . ,v^*))]))

(module+ test
  (check-equal? (apply-constraint/arity-sum (hasheq 'a '(>= 0) 'b 2)
                                            'a '(b c d))
                (set '(arity-sum a 2 c d)))

  (check-equal? (apply-constraint/arity-sum
                 (hasheq 'a '(>= 0) 'b '(>= 1)) 'a '(-1 b))
                (set '(arity-sum a -1 b)))

  (check-exn exn? (λ () (apply-constraint/arity-sum
                         (hasheq 'a '(>= 0) 'b '(>= 5))
                         'a '(-1 b))))

  (check-equal? (apply-constraint/arity-sum (hasheq 'a '(>= 0)) 'a '(-1 b))
                (set '(has-arity b (>= 1)) '(arity-sum a -1 b))))

(define (apply-constraint subst defer-cst* cst)
  (match cst
    [`(has-arity ,u ,v)
     (values (apply-constraint/has-arity subst u v)
             defer-cst*)]
    [`(arity-sum ,s . ,v*)
     (define new-cst (apply-constraint/arity-sum subst s v*))
     (values subst (set-union defer-cst* new-cst))]))

(define (solve-constraints cst*)
  (let do-solve ([subst (hasheq)]
                 [cst* cst*])
    (define-values (subst^ cst^*)
      (for/fold ([subst subst] [defer-cst* (set)]) ([cst (in-set cst*)])
        (apply-constraint subst defer-cst* cst)))
    (cond
      [(set-empty? cst^*) subst^]
      [(equal? cst* cst^*)
       (warning 'solve-constraints
                "some constraints not solved: ~a"
                cst^*)
       subst^]
      [else (do-solve subst^ cst^*)])))

(module+ test
  (check-equal?
   (canon-subst
    (solve-constraints
     (set '(has-arity a 1)
          '(has-arity b (>= 0))
          '(has-arity c 1)
          '(has-arity d 4)
          '(arity-sum d a b c))))
   (hasheq 'a 1 'b 2 'c 1 'd 4))

  (check-equal?
   (canon-subst
    (solve-constraints
     (set '(has-arity #%fine-template-in852955 1)
          '(has-arity tee-in852959 thread-in852963)
          '(has-arity tee-out852960 thread-out852952)
          '(has-arity thread-in852951 relay-in852953)
          '(has-arity relay-in852953 2)
          '(arity-sum tee-out852960
                      thread-out852964
                      thread-out852962)
          '(has-arity tee-in852959 thread-in852961)
          '(has-arity #%fine-template-out852956 1)
          '(arity-sum relay-out852954
                      #%fine-template-out852958
                      #%fine-template-out852956)
          '(has-arity #%fine-template-in852957 1)
          '(has-arity thread-in852963 thread-out852964)
          '(has-arity thread-in852961 thread-out852962)
          '(has-arity #%fine-template-out852958 1)
          '(has-arity relay-out852954 tee-in852959))))
   (hasheq '#%fine-template-in852955 1
           '#%fine-template-in852957 1
           '#%fine-template-out852956 1
           '#%fine-template-out852958 1
           'relay-in852953 2
           'relay-out852954 2
           'tee-in852959 2
           'tee-out852960 4
           'thread-in852951 2
           'thread-in852961 2
           'thread-in852963 2
           'thread-out852952 4
           'thread-out852962 2
           'thread-out852964 2)))

(define (annotate-arity* subst floe*)
  (for/list ([floe (in-list floe*)])
    (annotate-arity subst floe)))

(define (annotate-arity subst floe)
  (define-values (fi fo) (floe-lvars floe))
  (define (resolve-arity subst var)
    (match (resolve/value subst var)
      [(? arity? a) a]
      [_ (warning 'annotate-arity "no arity computed for ~a" var)
         '(>= 0)]))
  (define ai (resolve-arity subst fi))
  (define ao (resolve-arity subst fo))
  (define annot `((,fi ,ai) (,fo ,ao)))
  (match-define `(,rator ,_ . ,rands) floe)
  (match rator
    [(or 'thread 'tee 'relay)
     `(,rator ,annot ,@(annotate-arity* subst rands))]
    [_ `(,rator ,annot ,@rands)]))

(define (generate-vars base-name arity)
  (match arity
    [(? nonnegative-integer?)
     (for/list ([i (in-range arity)])
       (string->symbol (~a base-name "." i)))]
    [`(>= ,n)
     (define rest
       (string->symbol (~a base-name "*")))
     (for/fold ([v* (list rest)])
               ([v (in-list (reverse (generate-vars base-name n)))])
       (cons v v*))]))

(define (add-vars floe)
  (define-values (fi fo) (floe-lvars floe))
  (define-values (ai ao) (floe-arities floe))
  (define ivars (generate-vars fi ai))
  (define ovars (generate-vars fo ao))
  (define annot
    `((,ivars ,ai) (,ovars ,ao)))
  (match-define `(,rator ,_ . ,rands) floe)
  (match rator
    [(or 'thread 'tee 'relay)
     `(,rator ,annot ,@(map add-vars rands))]
    [_ `(,rator ,annot ,@rands)]))

(define (make-connect in-info out-info)
  (unless (equal? (info-effective-arity in-info)
                  (info-effective-arity out-info))
    (error 'make-connect "non-matching arities\n  in: ~a\n  out: ~a"
           in-info out-info))
  `(connect (,in-info ,out-info)))

(define (merge-floe-info select-info floe*)
  (define info^
    (for/list ([floe (in-list floe*)]
               #:do [(define info (select-info floe))]
               #:unless (equal? 0 (info-simple-arity info)))
      info))
  (match info^
    [(list i) i]
    [_ info^]))

(define (connect-zero? ai bi)
  (and (zero? (info-simple-arity ai))
       (zero? (info-simple-arity bi))))

(define (extract-connections/select tail-conne in-info out-info n*)
  (define v*
    (let ([iv (info-simple-vars in-info)])
      (for/list ([i (in-list n*)])
        (list-ref iv (sub1 i)))))
  (define ia (info-simple-arity out-info))
  (cons (make-connect (list v* ia) out-info) tail-conne))

(define (extract-connections/tee tail-conne in-info out-info floe*)
  (define out-connect (make-connect (merge-floe-info floe-out floe*) out-info))
  (define (do-extract floe*)
    (cond
      [(null? floe*) (cons out-connect tail-conne)]
      [else
       (define tail-conne^ (do-extract (cdr floe*)))
       (define floe (car floe*))
       (define in-connect (make-connect in-info (floe-in floe)))
       (cons in-connect (extract-connections tail-conne^ floe))]))
  (do-extract floe*))

(define (extract-connections/relay tail-conne in-info out-info floe*)
  (define out-connect (make-connect (merge-floe-info floe-out floe*) out-info))
  (define (do-extract floe*)
    (cond
      [(null? floe*)
       (cons out-connect tail-conne)]
      [else
       (define tail-conne^ (do-extract (cdr floe*)))
       (extract-connections tail-conne^ (car floe*))]))
  (cons (make-connect in-info (merge-floe-info floe-in floe*))
        (do-extract floe*)))

(define (extract-connections/thread tail-conne in-info out-info floe*)
  (define (do-extract floe*)
    (cond
      [(null? floe*) (values tail-conne out-info)]
      [else
       (define-values (tail-conne^ out-info) (do-extract (cdr floe*)))
       (define floe (car floe*))
       (define in-info (floe-out floe))
       (define tail-conne^^
         (if (connect-zero? in-info out-info)
             tail-conne^
             (cons (make-connect in-info out-info) tail-conne^)))
       (values (extract-connections tail-conne^^ floe)
               (floe-in floe))]))
  (define-values (tail-conne^ out-info^) (do-extract floe*))
  (cons (make-connect in-info out-info^) tail-conne^))

(define (extract-connections tail-conne floe)
  (match floe
    [`(as (,in-info (,out-name ,_)) . ,rands)
     (define out-info^ `(,rands ,(info-simple-arity in-info)))
     (cons (make-connect in-info out-info^)
           tail-conne)]
    [`(ground ,info) tail-conne]
    [`(select (,in-info ,out-info) . ,rands)
     (extract-connections/select tail-conne in-info out-info rands)]
    [`(tee (,in-info ,out-info) . ,rands)
     (extract-connections/tee tail-conne in-info out-info rands)]
    [`(thread (,in-info ,out-info) . ,rands)
     (extract-connections/thread tail-conne in-info out-info rands)]
    [`(relay (,in-info ,out-info) . ,rands)
     (extract-connections/relay tail-conne in-info out-info rands)]
    [(list* (or '#%fine-template 'gen 'esc) _)
     (cons floe tail-conne)]))

(define (pack-info info)
  (define (do-pack info* v* a)
    (cond
      [(null? info*) (list v* a)]
      [else
       (define i (car info*))
       (define arity (info-simple-arity i))
       (cond
         [(arity-exact? arity)
          (do-pack (cdr info*) (append v* (info-simple-vars i)) (+ a arity))]
         [(zero? a)
          (match info*
            [(list i) i]
            [_ info*])]
         [else (cons (list v* a) info*)])]))
  (if (info-compound? info)
      (do-pack info null 0)
      info))

(module+ test
  (check-equal? (pack-info '((a) 1)) '((a) 1))
  (check-equal? (pack-info '((a) (>= 0))) '((a) (>= 0)))
  (check-equal? (pack-info '(((a) 1) ((b) 1) ((c) 1)))
                '((a b c) 3))
  (check-equal? (pack-info '(((a) 1) ((b) 1) ((c) (>= 0))))
                '(((a b) 2) ((c) (>= 0))))
  (check-equal? (pack-info '((() 0) (() 0) ((a b) 2)))
                '((a b) 2))
  (check-equal? (pack-info '((() 0) (() 0) ((a) 1) ((b) 1)))
                '((a b) 2))
  (check-equal? (pack-info '(((c) (>= 0))))
                '((c) (>= 0)))
  (check-equal? (pack-info '((() 0) ((c) (>= 0))))
                '((c) (>= 0)))
  (check-equal? (pack-info '(((c) (>= 0)) ((d) (>= 0))))
                '(((c) (>= 0)) ((d) (>= 0)))))

(define (split-connect in out)
  (cond
    [(and (info-simple? in) (info-simple? out)) (make-connect in out)]
    [(and (info-simple? out) (equal? '(>= 0) (info-simple-arity out)))
     (make-connect in out)]
    [(and (info-simple? out) (arity-exact? (info-simple-arity out)))
     (error 'split-connect "\n  in: ~a\n  out: ~a" in out)]
    [else
     (error 'split-connect "\n  in: ~a\n  out: ~a" in out)]))

(define (conne:optimize conne)
  (for/list ([c (in-list conne)])
    (match c
      [`(connect ,(or (list (? info-compound? in) out)
                      (list in (? info-compound? out))))
       (define in^ (pack-info in))
       (define out^ (pack-info out))
       (split-connect in^ out^)]
      [_ c])))

(define (build-args info)
  (match (info-simple-arity info)
    [(? nonnegative-integer?) (info-simple-vars info)]
    [`(>= ,_)
     (define v* (reverse (info-simple-vars info)))
     (for/fold ([nv* (car v*)]) ([v (in-list (cdr v*))])
       (cons v nv*))]))

(define (conne:codegen/fine-template in out expr tail)
  (define expr^
    (let replace ([expr expr]
                  [ivar* (info-simple-vars in)])
      (cond
        [(null? expr) null]
        [(eq? '_ (car expr))
         (cons (car ivar*)
               (replace (cdr expr) (cdr ivar*)))]
        [else
         (cons (car expr)
               (replace (cdr expr) ivar*))])))
  ;; XXX: varying return values
  `(let-values ([,(info-simple-vars out) ,expr^]) ,tail))

(define (conne:codegen/esc in out expr tail)
  (define (do-call c)
    (match (info-simple-arity in)
      [(? nonnegative-integer?) c]
      [`(>= ,_) `(apply . ,c)]))
  (define call
    (do-call `(,expr . ,(info-simple-vars in))))
  (match (info-simple-arity out)
    [(? nonnegative-integer?)
     `(let-values ([,(info-simple-vars out) ,call]) ,tail)]
    [`(>= ,_)
     `(call-with-values
       (lambda () ,call)
       (lambda ,(build-args out) ,tail))]))

(define (conne:codegen/connect in out tail)
  (match* {(info-arity in) (info-arity out)}
    [{(? arity-exact?) (? arity-exact?)}
     `(let-values ([,(info-simple-vars out)
                    (values . ,(info-simple-vars in))])
        ,tail)]
    [{'(>= 0) '(>= 0)}
     `(let ([,(car (info-simple-vars out)) ,(car (info-simple-vars in))])
        ,tail)]
    [{`(>= ,s) `(>= ,t)}
     #:when (= s t)
     `(let-values ([,(info-simple-vars out)
                    (values . ,(info-simple-vars in))])
        ,tail)]
    [{(list '(>= 0) ...) '(>= 0)}
     (define iv*
       (for/list ([i (in-list in)])
         (car (info-simple-vars i))))
     `(call-with-values
       (lambda () (apply values (append . ,iv*)))
       (lambda ,(build-args out) ,tail))]
    ))

(define (conne:codegen/tail conne* tail)
  (cond
    [(null? conne*) tail]
    [else
     (define tail^ (conne:codegen/tail (cdr conne*) tail))
     (match (car conne*)
       [`(connect (,in ,out))
        (conne:codegen/connect in out tail^)]
       [`(#%fine-template (,in ,out) ,expr)
        (conne:codegen/fine-template in out expr tail^)]
       [`(esc (,in ,out) ,expr)
        (conne:codegen/esc in out expr tail^)]
       [`(gen (,_ ,out) ,@vals)
        `(let-values ([,(info-simple-vars out) (values . ,vals)])
           ,tail^)])]))

(define (conne:codegen in out conne*)
  (define body
    (let ([args (info-simple-vars out)])
      (match (info-simple-arity out)
        [`(>= ,n) `(apply values . ,args)]
        [_ `(values . ,args)])))
  (define tail
    (conne:codegen/tail conne* body))
  `(lambda ,(build-args in) ,tail))

(define (compile floe)
  (define floe^ #R(add-lvars #R floe))
  (define cst* #R(generate-constraints (set) floe^))
  (define subst #R(solve-constraints cst*))
  (define floe-arity #R(annotate-arity subst floe^))
  (define floe-arity^ #R(add-vars floe-arity))
  (define conne #R (extract-connections null floe-arity^))
  (define conne^ #R (conne:optimize conne))
  (conne:codegen (floe-in floe-arity^)
                 (floe-out floe-arity^)
                 conne^))

#;
(compile '(select 1 3 5))

#;
(compile '(tee (thread (select 1 3 5) (#%fine-template (+ _ _ _)))
               (thread (select 2 4 6) (#%fine-template (+ _ _ _)))))

#;
(compile '(gen 1 2 3))

#;
(compile '(thread (relay (as a) (as b) (#%fine-template (+ _ a b)))
                  (#%fine-template (* a b _))))

#;
(compile '(relay (as a) (as b) (#%fine-template (+ _ a b))))

#;
(compile '(thread (gen 1 2 3) (ground) (ground) (gen 1)))

#;
(compile '(relay (esc (1 (>= 0)) list) (esc (1 (>= 0)) list)))

#;
(compile '(relay (esc (1 1) list) (esc (1 1) list)))

#;
(compile
 '(thread (relay (#%fine-template (add1 _)) (#%fine-template (sub1 _)))
          (tee (thread) (thread))))

#;
(compile '(thread))

#;
(compile '(thread (gen 1 -1) (#%fine-template (+ _ 10 _))))

#;
(compile '(tee (#%fine-template (add1 _))))

#;
(compile '(tee (#%fine-template (add1 _))
               (#%fine-template (sub1 _))))

#;
(compile '(tee (thread) (thread (1 (>= 0))) (thread)))

#;
(compile '(tee (thread) (thread) (thread)))

#;
(compile '(tee (#%fine-template (add1 _)) (thread) (thread)))

#;
(compile '(tee (#%fine-template (quotient/remainder _ _))
               (#%fine-template (* _ _))))

#;
(compile '(thread (#%fine-template (quotient/remainder _ _))
                  (#%fine-template (* _ _))))

#;
(compile '(relay (thread) (thread) (thread)))

#;
(compile '(relay (tee (thread) (thread))
                 (tee (thread) (thread))))

#;
(compile '(relay (ground) (ground)))

#;
(compile '(ground))

#;
(compile '(thread (ground) (gen 2)))

#;
(compile '(thread (#%fine-template (add1 _)) (ground) (gen 2)))

#;
(compile '(relay (esc #f) (esc #f)))