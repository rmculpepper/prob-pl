#lang racket
(require gamble
         "base.rkt"
         "base-aux.rkt")
(provide (all-defined-out))

;; A HEnv is Hash[Symbol => Value]
;; We use immutable hashes instead of alists for better remove support.

;; A Context is (Listof ContextFrame)
;; A ContextFrame is one of
;; - (frame:let Symbol Expr HEnv Address)
;; - (frame:apply-to-args (Listof Value) Address)
;; - (frame:memoize Hash Key)
(struct frame:let (var expr env addr) #:transparent)
(struct frame:apply-to-args (args addr) #:transparent)
(struct frame:memoize (table key) #:transparent)

;; A DB is Hash[Address => Entry]
;; An Entry is (entry Dist Value)
(struct entry (dist value) #:transparent)

;; We use a CEK-like machine for evaluation. Note that we use
;; meta-state to represent evaluation state, so it's not a CESK
;; machine.

;; current-ll : (Parameterof Real)
(define current-ll (make-parameter 0))

;; {last,current}-db : (Parameterof DB)
(define last-db (make-parameter #hash()))
(define current-db (make-parameter #hash()))

;; current-fail : (Parameterof (-> None))
(define current-fail (make-parameter (lambda () (error 'fail))))

;; An Answer is either
;; - (answer Value Real DB)
;; - (failed)
(struct answer (value ll db) #:transparent)
(struct failed () #:transparent)

;; cek-top : Expr -> Answer
(define (cek-top e [prev-db #hash()])
  (let/ec escape
    (parameterize ((current-ll 0)
                   (current-fail (lambda () (escape (failed))))
                   (current-db #hash())
                   (last-db prev-db))
      (cek e (make-immutable-hash base-env) '() '()))))

;; cek : Expr HEnv Address Context -> Answer
(define (cek e env addr k)
  (match e
    ;; Continuation-extending expressions: let*
    [(expr:let* (list var) (list rhs) body)
     (let ([kenv (restrict-env env (free-variables body))])
       (cek rhs env addr (cons (frame:let var body kenv addr) k)))]
    [(expr:let* _ _ _)
     (error 'cek "got let* expression with multiple variables: ~e" e)]

    ;; Non-simple expressions
    [(expr:app cs fun args)
     (define funv (simple-eval fun env))
     (define argsv (for/list ([arg args]) (simple-eval arg env)))
     (apply-function funv argsv addr k)]
    [(expr:if a1 e2 e3)
     (cond [(simple-eval a1 env)
            (cek e2 env addr k)]
           [else
            (cek e3 env addr k)])]
    [(expr:S-sample cs dist-a)
     (define dist (simple-eval dist-a env))
     (return (do-sample dist addr) k)]
    [(expr:N-sample cs dist-a)
     (define dist (simple-eval dist-a env))
     (return (do-sample dist addr) k)]
    [(expr:observe-sample dist-a val-a)
     (define dist (simple-eval dist-a env))
     (define val (simple-eval val-a env))
     (current-ll (+ (current-ll) (dist-pdf dist val #t)))
     (return val k)]
    [(expr:fail)
     ((current-fail))]
    [(expr:mem cs fun-a)
     (define f (simple-eval fun-a env))
     (memoized f (cons cs addr) (make-hash))]

    ;; Simple expressions
    [simple-e
     (return (simple-eval simple-e env) k)]))

;; return : Value Context -> Answer
(define (return v k)
  (match k
    ['()
     (answer v (current-ll))]
    [(cons (frame:let var expr env addr) k)
     (cek expr (hash-set env var v) addr k)]
    [(cons (frame:apply-to-args args addr) k)
     (apply-function v args addr k)]
    [(cons (frame:memoize table key) k)
     (hash-set! table key v)
     (return v k)]))

;; apply-function : Value (Listof Value) Address Context -> Answer
(define (apply-function f args addr k)
  (match f
    [(primop name)
     (return (apply (primop-name->procedure name) args) k)]
    [(closure formals body env)
     (unless (= (length formals) (length args)) (error 'apply-function "arity"))
     (define env* (for/fold ([env env]) ([var formals] [arg args]) (hash-set env var arg)))
     (cek body env* addr k)]
    [(fixed inner-fun)
     (apply-function inner-fun (list f) addr (cons (frame:apply-to-args args addr) k))]
    [(memoized inner-fun table _)
     (cond [(hash-has-key? table args)
            (return (hash-ref table args) k)]
           [else
            (apply-function inner-fun args addr
                            (cons (frame:memoize table args) k))])]
    [_ (error 'apply-function "not a function: ~e" f)]))

;; simple-eval : Expr HEnv -> Value
(define (simple-eval e env)
  (match e
    [(? symbol? x)
     (hash-ref env x (lambda () (error 'cek "unbound variable: ~e" x)))]
    [(expr:quote datum)
     datum]
    [(expr:lambda vars body)
     (let ([env* (restrict-env env (free-variables e))])
       (closure vars body env))]
    [(expr:fix fun-a)
     (define fun (simple-eval fun-a env))
     (fixed fun)]))

;; do-sample : Dist Address -> Value
(define (do-sample dist addr)
  (cond [(hash-ref (current-db) addr #f)
         => (lambda (e) (error 'internal "collison at addr: ~e" addr))]
        [(hash-ref (last-db) addr #f)
         => (match-lambda
             [(entry last-dist last-value)
              (define new-l (dist-pdf dist last-value #t))
              (cond [(> new-l -inf.0)
                     (current-db (hash-set (current-db) addr (entry dist last-value)))
                     last-value]
                    [else ((current-fail))])])]
        [else
         (define value (dist-sample dist))
         (current-db (hash-set (current-db) addr (entry dist value)))
         value]))

;; restrict-env : HEnv (Setof Symbol) -> HEnv
(define (restrict-env env fv)
  (define diff (set-subtract (list->set (hash-keys env)) fv))
  (for/fold ([env env]) ([var diff])
    (hash-remove env var)))
