;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require racket/set
         (rename-in racket/match [match-define defmatch])
         gamble
         "base.rkt"
         "base-aux.rkt"
         "lightweight-db.rkt")
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

;; We use a CEK-like machine for evaluation. Note that we use
;; meta-state to represent evaluation state, so it's not a CESK
;; machine.

;; current-dlx : (Parameterof Real)
;; Stores Difference of Log of State (X), excluding fresh and stale
(define current-dlx (make-parameter 0))

;; current-ll : (Parameterof Real)
(define current-ll (make-parameter 0))

;; {last,current}-db : (Parameterof DB)
(define last-db (make-parameter #hash()))
(define current-db (make-parameter #hash()))

;; current-fail : (Parameterof (-> None))
(define current-fail (make-parameter (lambda () (error 'fail))))

;; An Answer is either
;; - (answer Value Real Real DB)
;; - (failed)
(struct answer (value ll dlx db) #:transparent)
(struct failed () #:transparent)

(define (cek-samples e n)
  (define old-ans
    (let loop ()
      (define ans (cek-top e))
      (if (answer? ans) ans (loop))))

  (define (next-ans old-ans)
    (defmatch (answer old-value old-ll _ old-db) old-ans)
    (defmatch (list* mod-old-db l-R/F) (perturb old-db))
    (match (cek-top e mod-old-db)
      [(and new-ans (answer value ll dlx db))
       (define threshold (accept-threshold l-R/F old-db old-ll db ll))
       (define threshold2
         (+ l-R/F
            (- (log (exact->inexact (hash-count old-db)))
               (log (exact->inexact (hash-count db))))
            (- ll old-ll)
            (- dlx l-R/F)))
       (unless (= threshold threshold2)
         (eprintf "thresholds disagree: ~s vs ~s\n" threshold threshold2))
       (define roll (log (random)))
       ;;(eprintf "~a threshold ~e rolled ~e\n"
       ;;         (if (<= roll threshold) "ACCEPTED" "REJECTED") threshold roll)
       (cond [(<= roll threshold) new-ans]
             [else old-ans])]
      [_ old-ans]))

  (define (perturb db)
    (cond [(zero? (hash-count db))
           (cons db 0)]
          [else
           (define i (random (hash-count db)))
           (define key (list-ref (hash-keys db) i))
           (defmatch (entry s? dist old-value) (hash-ref db key))
           (define new-value (dist-sample dist))
           ;;(eprintf "PERTURBED ~e\n  ~e FROM ~e TO ~e\n" key dist old-value new-value)
           (list* (hash-set db key (entry s? dist new-value))
                  (- (dist-pdf dist old-value #t)
                     (dist-pdf dist new-value #t)))]))

  (for/list ([i (in-range n)])
    (set! old-ans (next-ans old-ans))
    (answer-value old-ans)))

;; cek-top : Expr -> Answer
(define (cek-top e [prev-db #hash()])
  (let/ec escape
    (parameterize ((current-ll 0)
                   (current-dlx 0)
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
     (return (do-sample #t dist (cons cs addr)) k)]
    [(expr:N-sample cs dist-a)
     (define dist (simple-eval dist-a env))
     (return (do-sample #f dist (cons cs addr)) k)]
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
     (answer v (current-ll) (current-dlx) (current-db))]
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

;; do-sample : Boolean Dist Address -> Value
(define (do-sample s? dist addr)
  (cond [(hash-ref (current-db) addr #f)
         => (lambda (e) (error 'internal "collison at addr: ~e" addr))]
        [(hash-ref (last-db) addr #f)
         => (match-lambda
             [(entry s? last-dist last-value)
              (define new-l (dist-pdf dist last-value #t))
              (cond [(> new-l -inf.0)
                     (current-db (hash-set (current-db) addr (entry s? dist last-value)))
                     (current-dlx (+ (current-dlx)
                                     (- new-l (dist-pdf last-dist last-value #t))))
                     last-value]
                    [else ((current-fail))])])]
        [else
         (define value (dist-sample dist))
         (current-db (hash-set (current-db) addr (entry s? dist value)))
         value]))

;; restrict-env : HEnv (Setof Symbol) -> HEnv
(define (restrict-env env fv)
  (define diff (set-subtract (list->set (hash-keys env)) fv))
  (for/fold ([env env]) ([var diff])
    (hash-remove env var)))
