#lang racket/base
(require (rename-in racket/match [match-define defmatch])
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
;; - (expr:app CallSite Expr (Listof Expr)
;; - (expr:if Expr Expr Expr)
;; - (expr:sample CallSite Expr)
;; - (expr:observe-sample Expr Expr)
;; - (expr:fail)
;; - (expr:mem CallSite Expr)
(struct expr:quote (datum) #:transparent)
(struct expr:lambda (formals body) #:transparent)
(struct expr:fix (body) #:transparent)
(struct expr:app (cs fun args) #:transparent)
(struct expr:if (e1 e2 e3) #:transparent)
(struct expr:sample (cs dist) #:transparent)
(struct expr:observe-sample (dist value) #:transparent)
(struct expr:fail () #:transparent)
(struct expr:mem (cs arg) #:transparent)

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
     (expr:sample (gencs) (parse-expr e))]
    [(list 'observe-sample e1 e2)
     (expr:observe-sample (parse-expr e1) (parse-expr e2))]
    [(list 'fail)
     (expr:fail)]
    [(list 'mem e)
     (expr:mem (gencs) (parse-expr e))]
    [(list 'let* '() body)
     (parse-expr body)]
    [(list 'let* (cons [list (? symbol? var) rhs] bindings) body)
     (expr:app (gencs)
               (expr:lambda (list var) (parse-expr `(let* ,bindings ,body)))
               (list (parse-expr rhs)))]
    [(list 'letrec (list [list (? symbol? var) rhs]) body)
     (expr:app (gencs)
               (expr:lambda (list var) (parse-expr body))
               (list (expr:fix (expr:lambda (list var) (parse-expr rhs)))))]
    [(list f args ...)
     (expr:app (gencs) (parse-expr f) (map parse-expr args))]
    [_ (error 'parse-expr "bad expr: ~e" e)]))

;; free-variables : Expr -> (Setof Symbol)
(define (free-variables e)
  (match e
    [(? symbol? var) (set var)]
    [(expr:quote datum) (set)]
    [(expr:lambda formals body) (set-subtract (free-variables body) (list->set formals))]
    [(expr:fix body) (free-variables body)]
    [(expr:app cs fun args) (apply set-union (free-variables fun) (map free-variables args))]
    [(expr:if e1 e2 e3) (apply set-union (map free-variables (list e1 e2 e3)))]
    [(expr:sample cs e) (free-variables e)]
    [(expr:observe-sample de ve) (set-union (free-variables de) (free-variables ve))]
    [(expr:fail) (set)]
    [(expr:mem cs arg) (free-variables arg)]))

;; ============================================================

;; A Value is one of
;; - datum
;; - (primop (Value ... -> Value) -- applicable, but not "Function" (can't use w/ fix)
;; - Function
;; A Function is one of
;; - (closure (Listof Symbol) Expr Env)
;; - (fixed Function)
;; - (memoized Function Address Hash)
(struct primop (proc) #:transparent)
(struct closure (formals body env) #:transparent)
(struct fixed (fun) #:transparent)
(struct memoized (fun addr table) #:transparent)

(define (function? v)
  (or (closure? v) (fixed? v) (memoized? v)))

;; An Addr is (listof (U CallSite (cons 'mem (Listof Value)) 'top 'fix))

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

;; A DB is Hash[ Addr => Entry ]
;; where Entry is (entry Dist Value)
(struct entry (dist value) #:transparent)

;; {last,current}-db : Parameterof DB
(define last-db (make-parameter '#hash()))
(define current-db (make-parameter '#hash()))

;; eval-top : Expr DB -> (list Value Real DB)
(define (eval-top expr db)
  (let/ec escape
    (parameterize ((current-likelihood 1)
                   (current-fail (lambda () (escape (list 'failed 0 #f))))
                   (last-db db)
                   (current-db (make-hash)))
      (define result (eval-expr expr base-env '(top)))
      (list result (current-likelihood) (current-db)))))

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
    [(expr:sample cs de)
     (define d (eval-expr de env addr))
     (unless (dist? d) (error 'sample "not a dist: ~e" d))
     (do-sample d (cons cs addr))]
    [(expr:observe-sample de ve)
     (define d (eval-expr de env addr))
     (define v (eval-expr ve env addr))
     (unless (dist? d) (error 'observe-sample "not a dist: ~e" d))
     (do-observe-sample d v)]
    [(expr:fail)
     (do-fail)]
    [(expr:mem cs e)
     (define f (eval-expr e env addr))
     (unless (function? f) (error 'mem "not a function: ~e" f))
     (memoized f (make-hash) (cons cs addr))]))

(define (eval-exprs exprs env addr)
  (for/list ([expr exprs]) (eval-expr expr env addr)))

(define (apply-function f args addr)
  (match f
    [(primop proc)
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

(define (do-sample d addr)
  (cond [(hash-ref (current-db) addr #f)
         => (lambda (ent) (error 'sample "INTERNAL ERROR: collision at ~s" addr))]
        [(hash-ref (last-db) addr #f)
         => (lambda (last-entry)
              (match last-entry
                [(entry last-dist value)
                 (cond [(positive? (dist-pdf d value))
                        (hash-set! (current-db) addr (entry d value))
                        value]
                       [else
                        ;; FIXME: or could resample here, but that complicates ratio
                        ;; ie, entries in common only if same value in both dbs
                        (do-fail)])]))]
        [else
         (define value (dist-sample d))
         (hash-set! (current-db) addr (entry d value))
         value]))

(define (do-observe-sample d v)
  (current-likelihood (* (current-likelihood) (dist-pdf d v)))
  #f)

(define (do-fail)
  ((current-fail)))

;; ============================================================

(define (mh-eval e n)
  (define results '())

  (define-values (prev-result prev-likelihood prev-db)
    (let loop ()
      (match (eval-top e '#hash())
        [(list result likelihood db)
         (cond [(> likelihood 0)
                (values result likelihood db)]
               [else (loop)])])))

  (for ([i n])
    (define modified-last-db (hash-copy prev-db))
    (define proposal-factor (propose! modified-last-db))
    (defmatch (list new-result new-likelihood new-db)
      (eval-top e modified-last-db))
    (define accept-threshold
      ;; (Qbackward / Qforward) * (Pnew / Pprev)
      (* proposal-factor
         (/ (hash-count prev-db) (hash-count new-db))
         (/ new-likelihood prev-likelihood)
         (for/product ([(key old-entry) (in-hash prev-db)]
                       #:when (hash-has-key? new-db key))
           (define new-entry (hash-ref new-db key))
           ;; ASSERT: (entry-value new-entry) = (entry-value old-entry)
           (/ (dist-pdf (entry-dist new-entry) (entry-value new-entry))
              (dist-pdf (entry-dist old-entry) (entry-value old-entry))))))
    (cond [(< (random) accept-threshold)
           (set! results (cons new-result results))
           (set! prev-result new-result)
           (set! prev-likelihood new-likelihood)
           (set! prev-db new-db)]
          [else
           (set! results (cons prev-result results))]))
  (reverse results))

;; propose! : DB -> Real
(define (propose! db)
  (define size (hash-count db))
  (when (zero? size) (error 'propose! "program is deterministic"))
  (define i (random size))
  (define key-to-change (list-ref (hash-keys db) i))
  (defmatch (entry dist value) (hash-ref db key-to-change))
  (defmatch (cons value* logfactor) (dist-drift dist value 0.5))
  (hash-set! db key-to-change (entry dist value*))
  (exp logfactor))

;; ============================================================

(define (ws->mean proc n)
  (define-values (sum weight)
    (for/fold ([sum 0] [weight 0]) ([i (in-range n)])
      (match (proc)
        [(cons v w) (values (+ sum (* v w)) (+ weight w))])))
  (/ sum weight))

(define (samples->mean samples)
  (/ (apply + samples) (length samples)))

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

;; ============================================================

(require (only-in plot plot density plot-new-window?)
         (only-in gamble/viz hist))
(provide hist
         plot-density)

(define (plot-density vals) (plot (density vals)))

(plot-new-window? #t)
