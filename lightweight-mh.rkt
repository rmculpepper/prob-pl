#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         gamble
         "base.rkt")
(provide (all-defined-out))

;; ============================================================
;; Lightweight-MH support

;; An Addr is (listof AddrFrame)
;; where AddrFrame = (U 'top 'fix CallSite (cons 'mem (Listof Value)))

;; A DB is Hash[ Addr => Entry ]

;; An Entry is (entry Boolean Dist Value)
(struct entry (structural? dist value) #:transparent)

;; ============================================================
;; Evaluator implicit state (parameters)

;; current-likelihood : Parameterof Real
;; Accumulates likelihood of observations
(define current-likelihood (make-parameter 1))

;; current-fail : Parameterof (-> (escapes))
(define current-fail (make-parameter (lambda () (error 'fail))))

;; last-db : Parameterof DB
;; The DB of the previous (successful) program execution.
(define last-db (make-parameter '#hash()))

;; current-db : Parameterof DB
;; The (partial) DB of the current program execution.
(define current-db (make-parameter '#hash()))

;; ============================================================
;; DB-based Evaluator

;; eval-top : Expr DB -> (list Value Real DB)
;; Runs the given program given a (modified) DB from the previous
;; trace. Produces a result, likelihood of observations, and a new DB.
(define (eval-top expr db)
  (let/ec escape
    (parameterize ((current-likelihood 1)
                   (current-fail (lambda () (escape (list 'failed 0 #f))))
                   (last-db db)
                   (current-db (make-hash)))
      (define result (eval-expr expr base-env '(top)))
      (list result (current-likelihood) (current-db)))))

;; eval-expr : Expr Env Addr -> Value
(define (eval-expr expr env addr)
  (match expr
    [(? symbol? var)
     (cond [(assoc var env) => cdr]
           [else (error 'eval-expr "unbound variable: ~s" var)])]
    [(expr:quote datum)
     datum]
    [(expr:lambda formals body)
     (closure formals body env)]
    [(expr:app cs f args)
     (apply-function (eval-expr f env addr) (eval-exprs args env addr) (cons cs addr))]
    [(expr:fix expr)
     (define val (eval-expr expr env addr))
     (unless (closure? val) (error 'eval-expr "cannot fix non-closure: ~e" val))
     (fixed val)]
    [(expr:if e1 e2 e3)
     (if (eval-expr e1 env addr)
         (eval-expr e2 env addr)
         (eval-expr e3 env addr))]
    [(expr:S-sample cs de)
     (define d (eval-expr de env addr))
     (unless (dist? d) (error 'S-sample "not a dist: ~e" d))
     (do-sample #t d (cons cs addr))]
    [(expr:N-sample cs de)
     (define d (eval-expr de env addr))
     (unless (dist? d) (error 'N-sample "not a dist: ~e" d))
     (do-sample #f d (cons cs addr))]
    [(expr:observe-sample de ve)
     (define d (eval-expr de env addr))
     (define v (eval-expr ve env addr))
     (unless (dist? d) (error 'observe-sample "not a dist: ~e" d))
     (current-likelihood (* (current-likelihood) (dist-pdf d v)))
     #f]
    [(expr:fail)
     ((current-fail))]
    [(expr:mem cs e)
     (define f (eval-expr e env addr))
     (unless (function? f) (error 'mem "not a function: ~e" f))
     (memoized f (make-hash) (cons cs addr))]))

;; eval-exprs : (Listof Expr) Env Addr -> (Listof Value)
(define (eval-exprs exprs env addr)
  (for/list ([expr exprs]) (eval-expr expr env addr)))

;; apply-function : Value (Listof Value) Addr -> Value
(define (apply-function f args addr)
  (match f
    [(primop _ proc)
     (apply proc args)]
    [(closure formals body env)
     (unless (= (length formals) (length args))
       (error 'apply-function "arity mismatch: expected ~s, given ~s"
              (length formals) (length args)))
     (define env* (append (map cons formals args) env))
     (eval-expr body env* addr)]
    [(fixed inner-fun)
     (apply-function (apply-function inner-fun (list f) 'fix) args addr)]
    [(memoized inner-fun table saved-addr)
     (define addr* (cons (cons 'mem args) saved-addr))
     (hash-ref! table args (lambda () (apply-function inner-fun args addr*)))]
    [_ (error 'apply-function "not a function: ~e" f)]))

;; do-sample : Boolean Dist Addr -> Value
(define (do-sample structural? d addr)
  (cond [(hash-ref (current-db) addr #f)
         => (lambda (ent) (error 'sample "INTERNAL ERROR: collision at ~s" addr))]
        [(hash-ref (last-db) addr #f)
         => (lambda (last-entry)
              (match last-entry
                [(entry _ last-dist value)
                 (cond [(positive? (dist-pdf d value))
                        (hash-set! (current-db) addr (entry structural? d value))
                        value]
                       [else
                        ;; FIXME: or could resample here, but that complicates ratio
                        ;; ie, entries in common only if same value in both dbs
                        ((current-fail))])]))]
        [else
         (define value (dist-sample d))
         (hash-set! (current-db) addr (entry structural? d value))
         value]))
