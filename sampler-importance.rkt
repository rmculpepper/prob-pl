;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require racket/match
         gamble
         "base.rkt")

;; ============================================================
;; Likelihood-weighting evaluator

;; current-likelihood : Parameterof Real
;; Accumulates likelihood of observations
(define current-likelihood (make-parameter 1))

;; current-fail : Parameterof (-> Escapes)
(define current-fail (make-parameter (lambda () (error 'fail))))

;; eval-top : Expr -> (cons Value Real)
(define (eval-top expr)
  (let/ec escape
    (parameterize ((current-likelihood 1)
                   (current-fail (lambda () (escape (cons 'failed 0)))))
      (define result (eval-expr expr base-env))
      (cons result (current-likelihood)))))

;; eval-expr : Expr Env -> Value
(define (eval-expr expr env)
  (match expr
    [(? symbol? var)
     (cond [(assoc var env) => cdr]
           [else (error 'eval-expr "unbound variable: ~s" var)])]
    [(expr:quote datum)
     datum]
    [(expr:let* vars rhss body)
     (define env*
       (for/fold ([env* env])
                 ([var vars]
                  [rhs rhss]
                  [i (in-naturals)])
         (cons (cons var (eval-expr rhs env*)) env*)))
     (eval-expr body env*)]
    [(expr:lambda formals body)
     (closure formals body env)]
    [(expr:app _ f args)
     (apply-function (eval-expr f env) (eval-exprs args env))]
    [(expr:fix expr)
     (define val (eval-expr expr env))
     (unless (closure? val) (error 'eval-expr "cannot fix non-closure: ~e" val))
     (fixed val)]
    [(expr:if e1 e2 e3)
     (if (eval-expr e1 env)
         (eval-expr e2 env)
         (eval-expr e3 env))]
    [(expr:S-sample _ de)
     (define d (eval-expr de env))
     (unless (dist? d) (error 'S-sample "not a dist: ~e" d))
     (do-sample d)]
    [(expr:N-sample _ de)
     (define d (eval-expr de env))
     (unless (dist? d) (error 'N-sample "not a dist: ~e" d))
     (do-sample d)]
    [(expr:observe-sample de ve)
     (define d (eval-expr de env))
     (define v (eval-expr ve env))
     (unless (dist? d) (error 'observe-sample "not a dist: ~e" d))
     (current-likelihood (* (current-likelihood) (dist-pdf d v)))
     #f]
    [(expr:fail)
     ((current-fail))]
    [(expr:mem _ e)
     (define f (eval-expr e env))
     (unless (function? f) (error 'mem "not a function: ~e" f))
     (memoized f (make-hash) #f)]))

;; eval-exprs : (Listof Expr) Env -> (Listof Value)
(define (eval-exprs exprs env)
  (for/list ([expr exprs]) (eval-expr expr env)))

;; apply-function : Value (Listof Value) -> Value
(define (apply-function f args)
  (match f
    [(primop name)
     (apply (primop-name->procedure name) args)]
    [(closure formals body env)
     (unless (= (length formals) (length args)) (error 'apply-function "arity"))
     (define env* (append (map cons formals args) env))
     (eval-expr body env*)]
    [(fixed inner-fun)
     (apply-function (apply-function inner-fun (list f)) args)]
    [(memoized inner-fun table _)
     (hash-ref! table args (lambda () (apply-function inner-fun args)))]
    [_ (error 'apply-function "not a function: ~e" f)]))

;; do-sample : Dist -> Value
(define (do-sample d)
  (dist-sample d))

;; ============================================================

(define (raw-samples e n)
  (for/list ([i n])
    (match (eval-top e)
      [(cons v 1) v])))

;; ws-mean : (-> (cons Real Real)) Nat -> Real
(define (ws->mean proc n)
  (define-values (sum weight)
    (for/fold ([sum 0] [weight 0]) ([i (in-range n)])
      (match (proc)
        [(cons v w) (values (+ sum (* v w)) (+ weight w))])))
  (/ sum weight))

(module+ test
  (printf "p-cd: want 9.5, got: ~s\n"
          (ws->mean (lambda () (eval-top p-cd)) 100))
  (printf "p-geometric: got ~s\n"
          (raw-samples p-geometric 10))
  (printf "p-mem: got ~s\n"
          (raw-samples p-mem 3))
  (printf "p-mem2: got ~s\n"
          (raw-samples p-mem 3))
  (printf "p-match: got ~s\n"
          (for/list ([i 10]) (eval-top p-match))))
