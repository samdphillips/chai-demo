#lang debug racket/base

(require racket/format
         racket/list
         racket/match
         racket/set
         (only-in racket/math nonnegative-integer?))

(module+ test
  (require rackunit))

(define (warning who msg . vals)
  (eprintf "~a: ~a~%" who (apply format msg vals)))

(define (arity? v)
  (match v
    [(or (? nonnegative-integer?)
         (list '>= (? nonnegative-integer?))) #t]
    [_ #f]))

(define (check-arity who v)
  (unless (arity? v)
    (error who "expected arity: ~a" v)))

(define (arity-decl? term)
  (match term
    [(list (? arity?) (? arity?)) #t]
    [_ #f]))

(define (var? v)
  (and (symbol? v) (not (arity? v))))

(define (known-return-arity rator)
  (match rator
    [(or '+ '- '* '/ 'add1 'sub1) 1]
    [(or 'quotient/remainder) 2]
    [_ '(>= 0)]))

(define (merge-arities a b)
  (match* (a b)
    ;; normally `merge-arities` is called after simple eqv unification has
    ;; failed so this first clause is only for the general case.
    [(_ (== a)) a]
    [((? nonnegative-integer?) (? nonnegative-integer?)) #f]
    [((list '>= m) (list '>= n)) `(>= ,(max m n))]
    [((? nonnegative-integer?) _) (merge-arities b a)]
    [((list '>= m) n) (and (>= n m) n)]))

(module+ test
  (check-equal? (merge-arities 0 0) 0)
  (check-equal? (merge-arities 3 3) 3)
  (check-equal? (merge-arities '(>= 0) '(>= 0)) '(>= 0))
  (check-equal? (merge-arities '(>= 0) 3) 3)
  (check-equal? (merge-arities 3 '(>= 0)) 3)
  (check-equal? (merge-arities '(>= 3) 3) 3)
  (check-equal? (merge-arities 3 '(>= 3)) 3)
  (check-equal? (merge-arities '(>= 2) 3) 3)
  (check-equal? (merge-arities 3 '(>= 2)) 3)
  (check-equal? (merge-arities '(>= 2) '(>= 3)) '(>= 3))
  (check-equal? (merge-arities '(>= 3) '(>= 2)) '(>= 3))

  (check-false (merge-arities 0 3))
  (check-false (merge-arities '(>= 3) 2))
  (check-false (merge-arities 2 '(>= 3))))

(define (floe-infos floe)
  (match floe
    [`(,_ (,in ,out) . ,_) (values in out)]))

(define (floe-in floe)
  (match floe
    [`(,_ (,in ,_) . ,_) in]))

(define (floe-out floe)
  (match floe
    [`(,_ (,_ ,out) . ,_) out]))

(define (info-lvar info) (car info))
(define (info-arity info) (cadr info))
(define (info-vars info) (caddr info))

(define (floe-lvars floe)
  (match floe
    [`(,_ (,(? symbol? i) ,(? symbol? o)) . ,_) (values i o)]
    [`(,_ ((,(? symbol? i) . ,_) (,(? symbol? o) . ,_)) . ,_) (values i o)]))

(define (floe-arities floe)
  (match floe
    [`(,_ ((,(? symbol?) ,(? arity? ai) . ,_)
           (,(? symbol?) ,(? arity? ao) . ,_))
          . ,_)
     (values ai ao)]))

(define (floe-vars floe)
  (match floe
    [`(,_ ((,(? symbol?) ,(? arity?) ,ivars)
           (,(? symbol?) ,(? arity?) ,ovars))
          . ,_)
     (values ivars ovars)]))

(define (floe-ivars floe)
  (call-with-values (λ () (floe-vars floe))
                    (λ (in out) in)))

(define (floe-ovars floe)
  (call-with-values (λ () (floe-vars floe))
                    (λ (in out) out)))

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

(define (simplify-constraint cst)
  (match cst
    [`(arity-sum ,s) `(has-arity ,s 0)]
    [`(arity-sum ,s ,v) `(has-arity ,s ,v)]
    [_ cst]))

(define (add-constraint cst* cst)
  (set-add cst* (simplify-constraint cst)))

(define (add-constraints cst* . more-cst*)
  (for/fold ([cst* cst*]) ([cst (in-list more-cst*)])
    (set-add cst* cst)))

(define (generate-thread-constraints cst* i o floe*)
  (define-values (final-o cst*^)
    (for/fold ([last-o i] [cst* cst*]) ([floe (in-list floe*)])
      (define-values (fin fout) (floe-lvars floe))
      (values fout
              (add-constraint cst* `(has-arity ,last-o ,fin)))))
  (define cst*^^ (add-constraint cst*^ `(has-arity ,final-o ,o)))
  (generate-constraints* cst*^^ floe*))

(define (generate-tee-constraints cst* i o floe*)
  (define-values (cst*^ fo*)
    (for/fold ([cst* cst*] [fo* null]) ([floe (in-list floe*)])
      (define-values (fi fo) (floe-lvars floe))
      (values (add-constraint cst* `(has-arity ,i ,fi))
              (cons fo fo*))))
  (generate-constraints* (add-constraint cst*^ `(arity-sum ,o ,@fo*))
                         floe*))

(define (generate-relay-constraints cst* i o floe*)
  (define-values (cst*^ fo*)
    (for/fold ([cst* cst*] [fo* null]) ([floe (in-list floe*)])
      (define-values (fi fo) (floe-lvars floe))
      (values (add-constraint cst* `(has-arity ,fi 1))
              (cons fo fo*))))
  (define cst*^^ (add-constraint cst*^ `(has-arity ,i ,(length floe*))))
  (generate-constraints* (add-constraint cst*^^ `(arity-sum ,o ,@fo*))
                         floe*))

(define (generate-fine-template-constraints cst* i o expr)
  (define (count-placeholders expr)
    (for/fold ([i 0]) ([t expr])
      (if (eq? t '_) (add1 i) i)))
  (add-constraints cst*
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
      [n  (add-constraint cst* `(has-arity ,var ,n))]))
  (let* ([cst* (add-decl-constraints cst* i ai)]
         [cst* (add-decl-constraints cst* o ao)])
    (match rator
      ['ground
       (add-constraints cst*
                        `(has-arity ,i (>= 0))
                        `(has-arity ,o 0))]
      ['gen
       (add-constraints cst*
                        `(has-arity ,i (>= 0))
                        `(has-arity ,o ,(length rands)))]
      ['select
       (add-constraints cst*
                        `(has-arity ,i (>= ,(apply max rands)))
                        `(has-arity ,o ,(length rands)))]
      ['esc
       (add-constraints cst*
                        `(has-arity ,i (>= 0))
                        `(has-arity ,o (>= 0)))]
      ['thread
       (generate-thread-constraints cst* i o rands)]
      ['tee
       (generate-tee-constraints cst* i o rands)]
      ['relay
       (generate-relay-constraints cst* i o rands)]
      ['#%fine-template
       (generate-fine-template-constraints cst* i o (car rands))]
      )))

(define (update-subst subst var tgt)
  (unless (var? var)
    (error 'update-subst
           "lhs of update not a var: ~a"
           var))
  (hash-set subst var tgt))

(define (resolve subst v)
  (cond
    [(arity? v) v]
    [else
     (match (hash-ref subst v #f)
       [#f v]
       [(? arity? a) a]
       [v^ (resolve subst v^)])]))

(define (canon-var subst v)
  (cond
    [(arity? v) #f]
    [else
     (let do-resolve ([v v])
       (match (hash-ref subst v #f)
         [#f v]
         [(? arity?) v]
         [v^ (do-resolve v^)]))]))

(define (resolve* subst v*)
  (for/list ([v (in-list v*)])
    (resolve subst v)))

(define (apply-constraint subst defer-cst* cst)
  (define (defer cst)
    (set-add defer-cst* cst))
  (match cst
    [`(has-arity ,u ,v)
     (define u^ (resolve subst u))
     (define v^ (resolve subst v))
     (values (cond
               [(eqv? u^ v^) subst]
               [(var? u^) (update-subst subst u^ v^)]
               [(var? v^) (update-subst subst v^ u^)]
               [(merge-arities u^ v^)
                => (λ (new-arity)
                     (define cu (canon-var subst u))
                     (define cv (canon-var subst v))
                     (define subst^
                       (if cv
                           (update-subst subst cv cu)
                           subst))
                     (update-subst subst^ cu new-arity))]
               [else
                (error 'apply-constraint
                       "cannot apply constraint: (has-arity ~a ~a)"
                       u^ v^)])
             defer-cst*)]
    [`(arity-sum ,s . ,v*)
     (define s^ (resolve subst s))
     (define v^* (resolve* subst v*))
     (define-values (n v^^*)
       (for/fold ([n 0]
                  [v* null]
                  #:result (values n (reverse v*)))
                 ([v (in-list v^*)])
         (cond
           [(nonnegative-integer? v) (values (+ n v) v*)]
           [else (values n (cons v v*))])))
     (cond
       [(null? v^^*)
        (values subst (defer `(has-arity ,s ,n)))]
       [(nonnegative-integer? s^)
        (values subst (defer `(arity-sum ,(- s^ n) ,@v^^*)))]
       [(zero? n)
        (values subst (defer `(arity-sum ,s ,@v^^*)))]
       [else
        (values subst (defer `(arity-sum ,s ,n ,@v^^*)))])]))

(module+ test
  (check-equal?
   (call-with-values
    (λ () (apply-constraint (hasheq 'a 1) (set) '(has-arity a (>= 0))))
    list)
   (list (hasheq 'a 1) (set)))

  (check-equal?
   (call-with-values
    (λ () (apply-constraint (hasheq 'a 'b 'b 1) (set) '(has-arity a (>= 0))))
    list)
   (list (hasheq 'a 'b 'b 1) (set)))

  )

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

(define (annotate-arity* subst floe*)
  (for/list ([floe (in-list floe*)])
    (annotate-arity subst floe)))

(define (annotate-arity subst floe)
  (define-values (fi fo) (floe-lvars floe))
  (define (resolve-arity subst var)
    (match (resolve subst var)
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
       (string->symbol (~a base-name "." i)))]))

(define (add-vars floe)
  (define-values (fi fo) (floe-lvars floe))
  (define-values (ai ao) (floe-arities floe))
  (define ivars (generate-vars fi ai))
  (define ovars (generate-vars fo ao))
  (define annot `((,fi ,ai ,ivars) (,fo ,ao ,ovars)))
  (match-define `(,rator ,_ . ,rands) floe)
  (match rator
    [(or 'thread 'tee 'relay)
     `(,rator ,annot ,@(map add-vars rands))]
    [_ `(,rator ,annot ,@rands)]))

(define (merge-floe-info select-info floe*)
  (for/fold ([arity 0]
             [v null]
             #:result `(#f ,arity ,v))
            ([floe (in-list floe*)])
    (define info (select-info floe))
    (values (+ arity (info-arity info))
            (append v (info-vars info)))))

(define (extract-routing-tee conne in-info out-info floe*)
  (define conne^
    (for/fold ([conne conne]) ([floe (in-list floe*)])
      (define conne^ (extract-routing conne floe))
      (cons `(connect ,in-info ,(floe-in floe)) conne^)))
  (cons `(connect ,(merge-floe-info floe-out floe*) ,out-info)
        conne^))

(define (extract-routing-relay conne in-info out-info floe*)
  (list* `(connect ,in-info ,(merge-floe-info floe-in floe*))
         `(connect ,(merge-floe-info floe-out floe*) ,out-info)
         (extract-routing* conne floe*)))

(define (extract-routing-thread conne in-info out-info floe*)
  (define-values (final-o conne^)
    (for/fold ([last-o in-info] [conne conne]) ([floe (in-list floe*)])
      (define-values (fin fout) (floe-infos floe))
      (define conne^ (extract-routing conne floe))
      (values fout
              (cons `(connect ,last-o ,fin) conne^))))
  (cons `(connect ,final-o ,out-info) conne^))

(define (extract-routing* conne floe*)
  (for/fold ([conne conne]) ([floe (in-list floe*)])
    (extract-routing conne floe)))

(define (extract-routing conne floe)
  (match floe
    [`(tee (,in-info ,out-info) . ,rands)
     (extract-routing-tee conne in-info out-info rands)]
    [`(thread (,in-info ,out-info) . ,rands)
     (extract-routing-thread conne in-info out-info rands)]
    [`(relay (,in-info ,out-info) . ,rands)
     (extract-routing-relay conne in-info out-info rands)]
    [(list* (or '#%fine-template) _) (cons floe conne)]))

(define (compile floe)
  (define floe^ #R(add-lvars #R floe))
  (define cst* #R(generate-constraints (set) floe^))
  (define subst #R(solve-constraints cst*))
  (define floe-arity #R(annotate-arity subst floe^))
  (define floe-arity^ #R(add-vars floe-arity))
  (values
   (floe-ivars floe-arity^)
   (floe-ovars floe-arity^)
   (extract-routing null floe-arity^)))


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
(compile '(tee (thread) (thread) (thread)))

#;
(compile '(tee (#%fine-template (add1 _)) (thread) (thread)))

#;
(compile '(tee (#%fine-template (quotient/remainder _ _))
               (#%fine-template (* _ _))))

#;
(compile '(relay (thread) (thread) (thread)))

#;
(compile '(relay (tee (thread) (thread))
                 (tee (thread) (thread))))

#;
(compile '(ground))

#;
(compile '(thread (ground) (gen 2)))

#;
(compile '(thread (#%fine-template (add1 _)) (ground) (gen 2)))

#;
(compile '(relay (esc #f) (esc #f)))