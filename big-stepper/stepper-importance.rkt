#lang racket/base
(require racket/match
         gamble
         "../base.rkt"
         "deriv-tokens.rkt")
(provide (all-defined-out))

(define (emit sig [value #f]) ((current-emit-listener) sig value))

;; ============================================================
;; Likelihood-weighting evaluator

;; current-likelihood : Parameterof Real
;; Accumulates likelihood of observations
(define current-likelihood (make-parameter 1))

;; current-fail : Parameterof (-> Escapes)
(define current-fail (make-parameter (lambda () (error 'fail))))

;; eval-top : Expr -> (cons Value Real)
(define (eval-top expr)
  (emit 'eval-top)
  (let/ec escape
    (parameterize ((current-likelihood 1)
                   (current-fail
                    (lambda ()
                      (emit 'syntax-error 'failed)
                      (current-likelihood 0)
                      (escape (cons 'failed 0)))))
      (define result (eval-expr expr base-env))
      (cons result (current-likelihood)))))

;; eval-expr : Expr Env -> Value
(define (eval-expr expr env)
  (emit 'eval-expr (cons expr env))
  (define v (eval-expr-inner expr env))
  (emit 'return v)
  v)

;; eval-expr-inner : Expr Env -> Value
(define (eval-expr-inner expr env)
  (match expr
    [(? symbol? var)
     (emit 'expr:variable)
     (cond [(assoc var env) => cdr]
           [else
            (error 'eval-expr "unbound variable: ~s" var)])]
    [(expr:quote datum)
     (emit 'expr:quote)
     datum]
    [(expr:let* vars rhss body)
     (emit 'expr:let*)
     (define env*
       (for/fold ([env* env])
                 ([var vars]
                  [rhs rhss]
                  [i (in-naturals)])
         (emit 'next)
         (cons (cons var (eval-expr rhs env*)) env*)))
     (emit 'next-group)
     (eval-expr body env*)]
    [(expr:lambda formals body)
     (emit 'expr:lambda)
     (closure formals body env)]
    [(expr:app _ f args)
     (emit 'expr:app)
     (define fv (eval-expr f env))
     (emit 'next-group)
     (define argvs (eval-exprs args env))
     (apply-function fv argvs)]
    [(expr:fix expr)
     (emit 'expr:fix)
     (define val (eval-expr expr env))
     (unless (closure? val)
       (error 'eval-expr "cannot fix non-closure: ~e" val))
     (fixed val)]
    [(expr:if e1 e2 e3)
     (emit 'expr:if)
     (if (eval-expr e1 env)
         (eval-expr e2 env)
         (eval-expr e3 env))]
    [(expr:S-sample _ de)
     (emit 'expr:S-sample)
     (define d (eval-expr de env))
     (unless (dist? d) (error 'S-sample "not a dist: ~e" d))
     (define v (do-sample d))
     v]
    [(expr:N-sample _ de)
     (emit 'expr:N-sample)
     (define d (eval-expr de env))
     (unless (dist? d) (error 'N-sample "not a dist: ~e" d))
     (define v (do-sample d))
     v]
    [(expr:observe-sample de ve)
     (emit 'expr:observe-sample)
     (define d (eval-expr de env))
     (define v (eval-expr ve env))
     (unless (dist? d) (error 'observe-sample "not a dist: ~e" d))
     (define w (dist-pdf d v))
     (emit 'weight w)
     (current-likelihood (* (current-likelihood) w))
     v]
    [(expr:fail)
     (emit 'expr:fail)
     ((current-fail))]
    [(expr:mem _ e)
     (emit 'expr:mem)
     (define f (eval-expr e env))
     (unless (function? f) (error 'mem "not a function: ~e" f))
     (memoized f (make-hash) #f)]))

;; eval-exprs : (Listof Expr) Env -> (Listof Value)
(define (eval-exprs exprs env)
  (for/list ([expr exprs])
    (emit 'next)
    (eval-expr expr env)))

;; apply-function : Value (Listof Value) -> Value
(define (apply-function f args)
  (emit 'apply-function (cons f args))
  (define v (apply-function* f args))
  (emit 'return v)
  v)

;; apply-function* : Value (Listof Value) -> Value
(define (apply-function* f args)
  (match f
    [(primop name)
     (emit 'apply:primop)
     (define value (apply (primop-name->procedure name) args))
     value]
    [(closure formals body env)
     (emit 'apply:closure)
     (unless (= (length formals) (length args)) (error 'apply-function "arity"))
     (define env* (append (map cons formals args) env))
     (eval-expr body env*)]
    [(fixed inner-fun)
     (emit 'apply:fixed)
     (define f* (apply-function inner-fun (list f)))
     (apply-function f* args)]
    [(memoized inner-fun table _)
     (emit 'apply:memoized)
     (hash-ref! table args
                (lambda ()
                  (emit 'memo-miss)
                  (apply-function inner-fun args)))]
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
