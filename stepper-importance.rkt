#lang racket/base
(require racket/match
         gamble
         "base.rkt"
         "stepper-base.rkt")
(provide (all-defined-out))

(define (breakpoint expr step-type)
  (walk expr step-type (current-likelihood)))

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
    (parameterize ((current-state expr)
                   (current-context null))
      (parameterize ((current-likelihood 1)
                     (current-fail
                      (lambda ()
                        (current-likelihood 0)
                        (breakpoint (expr:fail) "fail")
                        (escape (cons 'failed 0)))))
        (define result (eval-expr expr base-env))
        (cons result (current-likelihood))))))

(define (step-expr expr env step-type)
  (breakpoint (expr:eval expr env) step-type)
  (eval-expr expr env))

;; eval-expr : Expr Env -> Value
(define (eval-expr expr env)
  (match expr
    [(? symbol? var)
     (cond [(assoc var env) =>
            (lambda (p)
              (define value (cdr p))
              (breakpoint (expr:value value)
                          (if (primop? value)
                              #f
                              "variable"))
              value)]
           [else (error 'eval-expr "unbound variable: ~s" var)])]
    [(expr:quote datum)
     datum]
    [(expr:lambda formals body)
     (closure formals body env)]
    [(expr:app _ f args)
     (apply-function (with-context 0 (eval-expr f env))
                     (eval-exprs args env 1))]
    [(expr:fix expr)
     (define val (with-context 1 (eval-expr expr env)))
     (unless (closure? val) (error 'eval-expr "cannot fix non-closure: ~e" val))
     (fixed val)]
    [(expr:if e1 e2 e3)
     (if (with-context 1 (eval-expr e1 env))
         (step-expr e2 env "if true")
         (step-expr e3 env "if false"))]
    [(expr:S-sample _ de)
     (define d (with-context 1 (eval-expr de env)))
     (unless (dist? d) (error 'S-sample "not a dist: ~e" d))
     (define v (do-sample d))
     (breakpoint (expr:value v) "S-sample")
     v]
    [(expr:N-sample _ de)
     (define d (with-context 1 (eval-expr de env)))
     (unless (dist? d) (error 'N-sample "not a dist: ~e" d))
     (define v (do-sample d))
     (breakpoint (expr:value v) "N-sample")
     v]
    [(expr:observe-sample de ve)
     (define d (with-context 1 (eval-expr de env)))
     (define v (with-context 2 (eval-expr ve env)))
     (unless (dist? d) (error 'observe-sample "not a dist: ~e" d))
     (left-foot (current-likelihood))
     (current-likelihood (* (current-likelihood) (dist-pdf d v)))
     (right-foot (expr:value v) "observe-sample" (current-likelihood))
     v]
    [(expr:fail)
     ((current-fail))]
    [(expr:mem _ e)
     (define f (with-context 1 (eval-expr e env)))
     (unless (function? f) (error 'mem "not a function: ~e" f))
     (memoized f (make-hash) #f)]))

;; eval-exprs : (Listof Expr) Env Nat -> (Listof Value)
(define (eval-exprs exprs env start)
  (for/list ([expr exprs] [i (in-naturals start)])
    (with-context i (eval-expr expr env))))

;; apply-function : Value (Listof Value) -> Value
(define (apply-function f args)
  (match f
    [(primop name)
     (define value (apply (primop-name->procedure name) args))
     (breakpoint (expr:value value)
                 (if (memq name constructor-primop-names)
                     #f
                     "primop"))
     value]
    [(closure formals body env)
     (unless (= (length formals) (length args)) (error 'apply-function "arity"))
     (define env* (append (map cons formals args) env))
     (step-expr body env* "apply")]
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
