#lang racket/base
(require racket/match
         racket/set
         gamble)
(provide (all-defined-out))

;; e ::= real
;;     | boolean
;;     | (quote datum)
;;     | x
;;     | (λ (x ...) e)
;;     | (fix e)
;;     | (e e ...)
;;     | (if e e e)
;;     | (sample e)
;;     | (observe-sample e e)
;;     | (fail)
;;     | (mem e)
;;     | (let* ([var e] ...) e)
;;     | (letrec ([var e]) e)

;; An Expr is one of
;; - Symbol   -- variable
;; - (expr:quote Any)
;; - (expr:lambda (Listof Symbol) Expr)
;; - (expr:fix Expr)
;; - (expr:app Expr (Listof Expr)
;; - (expr:if Expr Expr Expr)
;; - (expr:sample Expr)
;; - (expr:observe-sample Expr Expr)
;; - (expr:fail)
;; - (expr:mem Expr)
(struct expr:quote (datum) #:transparent)
(struct expr:lambda (formals body) #:transparent)
(struct expr:fix (body) #:transparent)
(struct expr:app (fun args) #:transparent)
(struct expr:if (e1 e2 e3) #:transparent)
(struct expr:sample (dist) #:transparent)
(struct expr:observe-sample (dist value) #:transparent)
(struct expr:fail () #:transparent)
(struct expr:mem (arg) #:transparent)

;; A CallSite is any value
(define (gencs) (gensym 'cs))

;; variable-symbol? : Sexpr -> Boolean
(define (variable-symbol? v)
  (and (symbol? v)
       (not (memq v '(lambda fix if sample observe-sample fail mem let* letrec)))))

;; parse-expr : Sexpr -> Expr
(define (parse-expr e)
  (match e
    [(? variable-symbol? v) v]
    [(? real? r) (expr:quote r)]
    [(? boolean? b) (expr:quote b)]
    [(list 'quote datum) (expr:quote datum)]
    [(list 'lambda (list (? symbol? vars) ...) body)
     (expr:lambda vars (parse-expr body))]
    [(list 'fix e)
     (expr:fix (parse-expr e))]
    [(list 'if e1 e2 e3)
     (expr:if (parse-expr e1) (parse-expr e2) (parse-expr e3))]
    [(list 'sample e)
     (expr:sample (parse-expr e))]
    [(list 'observe-sample e1 e2)
     (expr:observe-sample (parse-expr e1) (parse-expr e2))]
    [(list 'fail)
     (expr:fail)]
    [(list 'mem e)
     (expr:mem (parse-expr e))]
    [(list 'let* '() body)
     (parse-expr body)]
    [(list 'let* (cons [list (? symbol? var) rhs] bindings) body)
     (expr:app (expr:lambda (list var) (parse-expr `(let* ,bindings ,body)))
               (list (parse-expr rhs)))]
    [(list 'letrec (list [list (? symbol? var) rhs]) body)
     (expr:app (expr:lambda (list var) (parse-expr body))
               (list (expr:fix (expr:lambda (list var) (parse-expr rhs)))))]
    [(list f args ...)
     (expr:app (parse-expr f) (map parse-expr args))]
    [_ (error 'parse-expr "bad expr: ~e" e)]))

;; free-variables : Expr -> (Setof Symbol)
(define (free-variables e)
  (match e
    [(? symbol? var) (set var)]
    [(expr:quote datum) (set)]
    [(expr:lambda formals body) (set-subtract (free-variables body) (list->set formals))]
    [(expr:fix body) (free-variables body)]
    [(expr:app fun args) (apply set-union (free-variables fun) (map free-variables args))]
    [(expr:if e1 e2 e3) (apply set-union (map free-variables (list e1 e2 e3)))]
    [(expr:sample e) (free-variables e)]
    [(expr:observe-sample de ve) (set-union (free-variables de) (free-variables ve))]
    [(expr:fail) (set)]
    [(expr:mem arg) (free-variables arg)]))

;; parse-top : Sexpr -> Expr
(define (parse-top e)
  (define expr (parse-expr e))
  (define fvs (free-variables expr))
  (unless (set-empty? fvs)
    (error 'parse-top "free variables: ~e" (set->list fvs)))
  expr)

;; ============================================================

;; A Value is one of
;; - datum
;; - (primop (Value ... -> Value) -- applicable, but not "Function" (can't use w/ fix)
;; - Function
;; A Function is one of
;; - (closure (Listof Symbol) Expr Env)
;; - (fixed Function)
;; - (memoized Function Hash)
(struct primop (proc) #:transparent)
(struct closure (formals body env) #:transparent)
(struct fixed (fun) #:transparent)
(struct memoized (fun table) #:transparent)

(define (function? v)
  (or (closure? v) (fixed? v) (memoized? v)))

;; An Env is (Listof (cons Symbol Value))

(define base-env
  (let-syntax ([primop-env
                (syntax-rules () [(_ v ...) (list (cons 'v (primop v)) ...)])])
    (primop-env + - * / = < > <= >=
                not
                cons list car cdr null? pair?
                vector make-vector vector-ref vector? vector-length
                bernoulli-dist
                uniform-dist normal-dist)))

;; ============================================================

;; current-likelihood : Parameterof Real
;; Accumulates likelihood of observations
(define current-likelihood (make-parameter 1))

;; current-fail : Parameterof (-> Escapes)
(define current-fail (make-parameter (lambda () (error 'fail))))

(define (eval-top expr)
  (let/ec escape
    (parameterize ((current-likelihood 1)
                   (current-fail (lambda () (escape (cons 'failed 0)))))
      (define result (eval-expr expr base-env))
      (cons result (current-likelihood)))))

(define (eval-expr expr env)
  (match expr
    [(? symbol? var)
     (cond [(assoc var env) => cdr]
           [else (error 'eval-expr "unbound variable: ~s" var)])]
    [(expr:quote datum)
     datum]
    [(expr:lambda formals body)
     (closure formals body env)]
    [(expr:app f args)
     (apply-function (eval-expr f env) (eval-exprs args env))]
    [(expr:fix expr)
     (define val (eval-expr expr env))
     (unless (closure? val) (error 'eval-expr "cannot fix non-closure: ~e" val))
     (fixed val)]
    [(expr:if e1 e2 e3)
     (if (eval-expr e1 env)
         (eval-expr e2 env)
         (eval-expr e3 env))]
    [(expr:sample de)
     (define d (eval-expr de env))
     (unless (dist? d) (error 'sample "not a dist: ~e" d))
     (do-sample d)]
    [(expr:observe-sample de ve)
     (define d (eval-expr de env))
     (define v (eval-expr ve env))
     (unless (dist? d) (error 'observe-sample "not a dist: ~e" d))
     (do-observe-sample d v)]
    [(expr:fail)
     (do-fail)]
    [(expr:mem e)
     (define f (eval-expr e env))
     (unless (function? f) (error 'mem "not a function: ~e" f))
     (memoized f (make-hash))]))

(define (eval-exprs exprs env)
  (for/list ([expr exprs]) (eval-expr expr env)))

(define (apply-function f args)
  (match f
    [(primop proc)
     (apply proc args)]
    [(closure formals body env)
     (unless (= (length formals) (length args)) (error 'apply-function "arity"))
     (define env* (append (map cons formals args) env))
     (eval-expr body env*)]
    [(fixed inner-fun)
     (apply-function (apply-function inner-fun (list f)) args)]
    [(memoized inner-fun table)
     (hash-ref! table args (lambda () (apply-function inner-fun args)))]
    [_ (error 'apply-function "not a function: ~e" f)]))

(define (do-sample d)
  (dist-sample d))

(define (do-observe-sample d v)
  (current-likelihood (* (current-likelihood) (dist-pdf d v)))
  #f)

(define (do-fail)
  ((current-fail)))

;; ============================================================

(define (ws->mean proc n)
  (define-values (sum weight)
    (for/fold ([sum 0] [weight 0]) ([i (in-range n)])
      (match (proc)
        [(cons v w) (values (+ sum (* v w)) (+ weight w))])))
  (/ sum weight))
  
;; ============================================================

(define p-geometric
  '(letrec ([g (lambda () (if (= (sample (bernoulli-dist 1/2)) 0) 0 (+ 1 (g))))]) (g)))

(define p-cd
  '(let* ([r (sample (normal-dist 9 1))]
          [o (observe-sample (normal-dist r 1) 10)])
    r))

(define p-mem
  '(let* ([f (mem (lambda (i) (sample (bernoulli-dist 1/2))))])
    (list (f 1) (f 1) (f 2) (f 2))))
