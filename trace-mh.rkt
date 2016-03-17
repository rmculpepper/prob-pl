;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         gamble
         "base.rkt"
         "lightweight-mh.rkt")
(provide (all-defined-out))

;; ============================================================
;; Traces

;; Hypothetical surface syntax

;; t ::= ts ...
;; ts ::= tvar <- primop texpr ...
;;      | tvar <- sample tvar tvar
;; texpr ::= Symbol | (quote Datum) | (cons texpr texpr)

;; Abstract Syntax

;; A Trace is (Listof TraceStmt)
;; A TraceStmt is one of
;; - (ts:primop TraceVar Primop (Listof TraceExpr))
;; - (ts:sample TraceVar TraceExpr TraceExpr)
(struct ts:primop (var primop args) #:transparent)
(struct ts:sample (var dist value) #:transparent)

;; A TraceExpr is one of
;; - (t:quote Datum)
;; - (t:cons TraceExpr TraceExpr)
;; - (t:dist Symbol (Listof TraceExpr))
;; - TraceVar
;; A TraceVar is a Symbol
(struct t:quote (datum) #:transparent)
(struct t:cons (e1 e2) #:transparent)
(struct t:dist (name args) #:transparent)

;; Intern these for easier testing --- for now
(define (gentv) (string->symbol (symbol->string (gensym 'tv))))

;; constant-te? : TraceExpr -> Boolean
(define (constant-te? te)
  (match te
    [(t:quote _) #t]
    [(t:cons e1 e2) (and (constant-te? e1) (constant-te? e2))]
    [(t:dist name args) (andmap constant-te? args)]
    [(? symbol?) #f]))

;; not-constant-te? : TraceExpr -> Boolean
(define (not-constant-te? te) (not (constant-te? te)))

;; ------------------------------------------------------------

;; A TraceMapping is Hash[ Addr => (list Boolean TraceExpr TraceExpr) ]
;; mapping addr to (list structural? dist-expr value-expr).

;; A TraceStore is Hash[ TraceVar => Value ]

(define (tstore-ref tstore tvar) (hash-ref tstore tvar))
(define (tstore-set! tstore tvar value) (hash-set! tstore tvar value))

;; ------------------------------------------------------------

;; exec-trace : Trace TraceStore -> Real
;; Returns the log of the product of the sample densities.
(define (exec-trace t tstore)
  (for/sum ([ts (in-list t)])
    (exec-trace-statement ts tstore)))

;; exec-trace-statement : TraceStatement TraceStore -> Real
(define (exec-trace-statement ts tstore)
  (match ts
    [(ts:primop var (primop name) args)
     (tstore-set! tstore var
       (apply (primop-name->procedure name) (eval-trace-exprs args tstore)))
     1]
    [(ts:sample var dist-e val-e)
     (define dist (eval-trace-expr dist-e tstore))
     (define val (eval-trace-expr val-e tstore))
     (tstore-set! tstore var val)
     (dist-pdf dist val #t)]))

;; eval-trace-expr : TraceExpr TraceStore -> Value
(define (eval-trace-expr texpr tstore)
  (match texpr
    [(? symbol? tvar)
     (tstore-ref tstore tvar)]
    [(t:quote datum)
     datum]
    [(t:cons e1 e2)
     (cons (eval-trace-expr e1 tstore) (eval-trace-expr e2 tstore))]
    [(t:dist name args)
     (apply (primop-name->procedure name) (eval-trace-exprs args tstore))]))

;; eval-trace-exprs : (Listof TraceExpr) TraceStore -> (Listof Value)
(define (eval-trace-exprs texprs tstore)
  (for/list ([texpr (in-list texprs)]) (eval-trace-expr texpr tstore)))

;; ------------------------------------------------------------

;; db-add-tstore! : DB TraceMapping TraceStore -> Void
;; Update a DB with the contents of a trace store.
(define (db-add-tstore! db tmapping tstore)
  (for ([(addr info) (in-hash tmapping)])
    (defmatch (list structural? dist-te value-te) info)
    (define dist (eval-trace-expr dist-te tstore))
    (define value (eval-trace-expr value-te tstore))
    (hash-set! db addr (entry structural? dist value))))

;; ============================================================
;; Tracing evaluator support

;; TraceEnv = (Listof (cons Symbol TraceExpr))
;; Within trace-expr, closures contain TraceEnvs rather than Envs.

;; env->trace-env : Env -> TraceEnv
(define (env->trace-env env)
  (for/list ([var+value (in-list env)])
    (cons (car var+value) (t:quote (cdr var+value)))))

;; last-db : Parameterof DB
;; Defined in lightweight-mh.rkt.

;; current-tmapping : Parameterof TraceMapping
(define current-tmapping (make-parameter '#hash()))

;; current-tstore : Parameterof TraceStore
(define current-tstore (make-parameter '#hash()))

;; current-rtrace : Parameterof Trace
;; Accumulates trace in reverse order
(define current-rtrace (make-parameter null))

;; emit-and-exec-trace-statement : TraceStatement -> Void
(define (emit-and-exec-trace-statement ts)
  (emit-trace-statement ts)
  (void (exec-trace-statement ts (current-tstore))))

;; emit-trace-statement : TraceStatement -> Void
(define (emit-trace-statement ts)
  (current-rtrace (cons ts (current-rtrace))))

;; ============================================================
;; Tracing evaluator

;; We only trace (Expr,DB) pairs known to succeed, so we eliminate
;; redundant error-checking below. We add checking that control flow
;; (functions, if branches) is completely determined by values of S
;; choices.

;; trace-top : Expr DB -> (list TraceExpr TraceMapping TraceStore Trace)
;; PRE: expr must not fail given db
(define (trace-top expr db)
  (parameterize ((last-db db)
                 (current-tmapping (make-hash))
                 (current-tstore (make-hash))
                 (current-rtrace null))
    (define result-te (trace-expr expr (env->trace-env base-env) '(top)))
    (list result-te (current-tmapping) (current-tstore) (reverse (current-rtrace)))))

;; trace-expr : Expr TraceEnv Addr -> TraceExpr
(define (trace-expr expr env addr)
  (match expr
    [(? symbol? var)
     (cdr (assoc var env))]
    [(expr:quote datum)
     (t:quote datum)]
    [(expr:let* vars rhss body)
     (define env*
       (for/fold ([env* env])
                 ([var vars]
                  [rhs rhss]
                  [i (in-naturals)])
         (cons (cons var (trace-expr rhs env* addr)) env*)))
     (trace-expr body env* addr)]
    [(expr:lambda formals body)
     (t:quote (closure formals body env))]
    [(expr:app cs f args)
     (trace-apply-function (trace-expr f env addr)
                           (trace-exprs args env addr)
                           (cons cs addr))]
    [(expr:fix expr)
     (match (trace-expr expr env addr)
       [(t:quote (? closure? clo))
        (t:quote (fixed clo))]
       [_ (error 'trace-expr "fix: function not determined by S choices")])]
    [(expr:if e1 e2 e3)
     (match (trace-expr e1 env addr)
       [(or (t:quote (? values))
            (t:cons _ _)
            (t:dist _ _))
        (trace-expr e2 env addr)]
       [(t:quote #f)
        (trace-expr e3 env addr)]
       [_ (error 'trace-expr "if: branch not determined by S choices")])]
    [(expr:S-sample cs de)
     (define d (trace-expr de env addr))
     (trace-do-S-sample d (cons cs addr))]
    [(expr:N-sample cs de)
     (define d (trace-expr de env addr))
     (trace-do-N-sample d (cons cs addr))]
    [(expr:observe-sample de ve)
     (define d (trace-expr de env addr))
     (define v (trace-expr ve env addr))
     (trace-do-observe-sample d v)]
    [(expr:fail)
     (error 'trace-expr "fail: internal error")]
    [(expr:mem cs e)
     (match (trace-expr e env addr)
       [(t:quote (? function? f))
        (t:quote (memoized f (make-hash) (cons cs addr)))]
       [_ (error 'trace-expr "mem: function not determined by S choices")])]))

;; trace-exprs : (Listof Expr) Env Addr -> (Listof TraceExpr)
(define (trace-exprs exprs env addr)
  (for/list ([expr exprs]) (trace-expr expr env addr)))

;; trace-apply-function : TraceExpr (Listof TraceExpr) Addr -> TraceExpr
(define (trace-apply-function fe args addr)
  (match fe
    [(t:quote f)
     (trace-apply-function* f args addr)]
    [(? symbol? tvar)
     (error 'trace-apply-function "function is not determined by S choices")]
    [_ (error 'trace-apply-function "bad function expr: ~e" fe)]))

;; trace-apply-function* : Value (Listof TraceExpr) Addr -> TraceExpr
(define (trace-apply-function* f args addr)
  (match f
    [(and p (primop _))
     (trace-apply-primop p args)]
    [(closure formals body env)
     (define env* (append (map cons formals args) env))
     (trace-expr body env* addr)]
    [(fixed inner-fun)
     (define fe* (trace-apply-function* inner-fun (list (t:quote f)) 'fix))
     (trace-apply-function fe* args addr)]
    [(memoized inner-fun table saved-addr)
     (unless (andmap constant-te? args)
       (error 'trace-apply-function*
              "arguments to memoized function not determined by S choices"))
     (define addr* (cons (cons 'mem (eval-trace-exprs args '#hash())) saved-addr))
     (hash-ref! table args (lambda () (trace-apply-function* inner-fun args addr*)))]
    [_ (error 'trace-apply-function* "bad function: ~e" f)]))

(define (trace-apply-primop p args)
  (match* (p args)
    [[(primop name) args]
     #:when (andmap t:quote? args)
     (t:quote (apply (primop-name->procedure name) (map t:quote-datum args)))]
    [[(primop 'cons) (list e1 e2)]
     (t:cons e1 e2)]
    [[(primop 'list) _]
     (foldr t:cons (t:quote '()) args)]
    [[(primop (? dist-primop? dist-primop)) args]
     (t:dist dist-primop args)]
    [[(primop 'car) (list (t:cons e1 e2))]
     e1]
    [[(primop 'cdr) (list (t:cons e1 e2))]
     e2]
    [[(primop 'pair?) (list (t:cons _ _))]
     (t:quote #t)]
    [[(primop 'null?) (list (t:cons _ _))]
     (t:quote #f)]
    [[(primop _) _]
     (define var (gentv))
     (emit-and-exec-trace-statement (ts:primop var p args))
     var]))

(define (trace-do-S-sample de addr)
  (defmatch (entry _ _ value) (hash-ref (last-db) addr))
  ;; value is constant wrt trace, because this is an S choice
  (unless (constant-te? de)
    ;; need to rescore if dist changes
    (emit-and-exec-trace-statement (ts:sample (gentv) de (t:quote value))))
  (hash-set! (current-tmapping) addr (list #t de (t:quote value)))
  (t:quote value))

(define (trace-do-N-sample de addr)
  (defmatch (entry _ _ value) (hash-ref (last-db) addr))
  ;; value may change wrt trace, because this is an N choice
  (define mapped-var (gentv))
  (define result-var (gentv))
  (hash-set! (current-tmapping) addr (list #f de mapped-var))
  (tstore-set! (current-tstore) mapped-var value)
  (emit-and-exec-trace-statement (ts:sample result-var de mapped-var))
  result-var)

(define (trace-do-observe-sample d v)
  (emit-and-exec-trace-statement (ts:sample (gentv) d v))
  (t:quote #f))
