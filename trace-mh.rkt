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
;;     | (S-sample e)
;;     | (N-sample e)
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
;; - (expr:S-sample CallSite Expr)
;; - (expr:N-sample CallSite Expr)
;; - (expr:observe-sample Expr Expr)
;; - (expr:fail)
;; - (expr:mem CallSite Expr)
(struct expr:quote (datum) #:transparent)
(struct expr:lambda (formals body) #:transparent)
(struct expr:fix (body) #:transparent)
(struct expr:app (cs fun args) #:transparent)
(struct expr:if (e1 e2 e3) #:transparent)
(struct expr:S-sample (cs dist) #:transparent)
(struct expr:N-sample (cs dist) #:transparent)
(struct expr:observe-sample (dist value) #:transparent)
(struct expr:fail () #:transparent)
(struct expr:mem (cs arg) #:transparent)

;; A CallSite is any value
(define (gencs) (gensym 'cs))

;; variable-symbol? : Sexpr -> Boolean
(define (variable-symbol? v)
  (and (symbol? v)
       (not (memq v '(lambda fix if sample S-sample N-sample observe-sample fail mem let* letrec)))))

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
    [(list 'S-sample e)
     (expr:S-sample (gencs) (parse-expr e))]
    [(list 'N-sample e)
     (expr:N-sample (gencs) (parse-expr e))]
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
    [(expr:S-sample cs e) (free-variables e)]
    [(expr:N-sample cs e) (free-variables e)]
    [(expr:observe-sample de ve) (set-union (free-variables de) (free-variables ve))]
    [(expr:fail) (set)]
    [(expr:mem cs arg) (free-variables arg)]))

;; ============================================================
;; Classic Evaluation
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

;; ------------------------------------------------------------

;; An Env is (Listof (cons Symbol Value))

(define base-env
  (let-syntax ([primop-env
                (syntax-rules ()
                  [(_ v ...) (list (cons 'v (primop v)) ...)])])
    (primop-env + - * / = < > <= >= zero?
                not
                cons list car cdr null? pair?
                vector make-vector vector-ref vector? vector-length
                bernoulli-dist poisson-dist
                uniform-dist normal-dist)))

;; ------------------------------------------------------------

;; An Addr is (listof (U CallSite (cons 'mem (Listof Value)) 'top 'fix))

;; A DB is Hash[ Addr => Entry ]
;; An Entry is (entry Boolean Dist Value)
(struct entry (structural? dist value) #:transparent)

;; {last,current}-db : Parameterof DB
(define last-db (make-parameter '#hash()))
(define current-db (make-parameter '#hash()))

;; current-likelihood : Parameterof Real
;; Accumulates likelihood of observations.
(define current-likelihood (make-parameter 1))

;; current-fail : Parameterof (-> Escapes)
(define current-fail (make-parameter (lambda () (error 'fail))))

;; ------------------------------------------------------------

;; eval-top : Expr DB -> (list Value Real DB)
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
                        (do-fail)])]))]
        [else
         (define value (dist-sample d))
         (hash-set! (current-db) addr (entry structural? d value))
         value]))

(define (do-observe-sample d v)
  (current-likelihood (* (current-likelihood) (dist-pdf d v)))
  #f)

(define (do-fail)
  ((current-fail)))


;; ============================================================
;; Tracing
;; ============================================================

;; t ::= ts ...
;; ts ::= tvar <- primop texpr ...
;;      | tvar <- sample tvar tvar
;; texpr ::= Symbol | (quote Datum)

;; A Trace is (Listof TraceStmt)
;; A TraceStmt is one of
;; - (t:primop TraceVar Procedure (Listof TraceExpr))
;; - (t:sample TraceVar TraceExpr TraceExpr)
;; A TraceExpr is one of
;; - (t:quote Datum)
;; - TraceVar
;; A TraceVar is a Symbol
(struct t:primop (var primop args) #:transparent)
(struct t:sample (var dist value) #:transparent)
(struct t:quote (datum) #:transparent)

;; Intern these for easier testing --- for now
(define (gentv) (string->symbol (symbol->string (gensym 'tv))))

;; A TraceMapping is Hash[ Addr => (list Boolean TraceExpr TraceExpr) ]
;; mapping addr to (list structural? dist-expr value-expr).

;; A TraceStore is Hash[ TraceVar => Value ]

(define (tstore-ref tstore tvar) (hash-ref tstore tvar))
(define (tstore-set! tstore tvar value) (hash-set! tstore tvar value))

;; db-add-tstore! : DB TraceMapping TraceStore -> Void
(define (db-add-tstore! db tmapping tstore)
  (for ([(addr info) (in-hash tmapping)])
    (defmatch (list structural? dist-te value-te) info)
    (define dist (eval-trace-expr dist-te tstore))
    (define value (eval-trace-expr value-te tstore))
    (hash-set! db addr (entry structural? dist value))))

;; ------------------------------------------------------------

;; exec-trace : Trace TraceStore -> Real
;; Returns the product of the sample densities.
(define (exec-trace t tstore)
  (for/product ([ts (in-list t)])
    (exec-trace-statement ts tstore)))

;; exec-trace-statement : TraceStatement TraceStore -> Real
(define (exec-trace-statement ts tstore)
  (match ts
    [(t:primop var primop args)
     (tstore-set! tstore var
       (apply primop (eval-trace-exprs args tstore)))
     1]
    [(t:sample var dist-e val-e)
     (define dist (eval-trace-expr dist-e tstore))
     (define val (eval-trace-expr val-e tstore))
     (tstore-set! tstore var val)
     (dist-pdf dist val)]))

;; eval-trace-expr : TraceExpr TraceStore -> Value
(define (eval-trace-expr texpr tstore)
  (match texpr
    [(? symbol? tvar) (tstore-ref tstore tvar)]
    [(t:quote datum) datum]))

;; eval-trace-exprs : (Listof TraceExpr) TraceStore -> (Listof Value)
(define (eval-trace-exprs texprs tstore)
  (for/list ([texpr (in-list texprs)]) (eval-trace-expr texpr tstore)))

;; ============================================================

;; last-db : Parameterof DB
;; Defined above.

;; current-tmapping : Parameterof TraceMapping
(define current-tmapping (make-parameter '#hash()))

;; current-tstore : Parameterof TraceStore
(define current-tstore (make-parameter '#hash()))

;; current-rtrace : Parameterof Trace
;; Trace stored in reverse order
(define current-rtrace (make-parameter null))

;; emit-and-exec-trace-statement : TraceStatement -> Void
(define (emit-and-exec-trace-statement ts)
  (emit-trace-statement ts)
  (void (exec-trace-statement ts (current-tstore))))

;; emit-trace-statement : TraceStatement -> Void
(define (emit-trace-statement ts)
  (current-rtrace (cons ts (current-rtrace))))

;; TraceEnv = (Listof (cons Symbol TraceExpr))
;; Within trace-expr, closures contain TraceEnvs rather than Envs.

;; env->trace-env : Env -> TraceEnv
(define (env->trace-env env)
  (for/list ([var+value (in-list env)])
    (cons (car var+value) (t:quote (cdr var+value)))))

;; ------------------------------------------------------------

;; trace-top : Expr DB -> (list TraceExpr TraceMapping TraceStore Trace)
;; PRE: expr must not fail given db
(define (trace-top expr db)
  (parameterize ((last-db db)
                 (current-fail (lambda () (error 'trace "internal error: evaluation failed")))
                 (current-tmapping (make-hash))
                 (current-tstore (make-hash))
                 (current-rtrace null))
    (define result-te (trace-expr expr (env->trace-env base-env) '(top)))
    (list result-te (current-tmapping) (current-tstore) (reverse (current-rtrace)))))

;; trace-expr : Expr TraceEnv Addr -> TraceExpr
(define (trace-expr expr env addr)
  (match expr
    [(? symbol? var)
     (cond [(assoc var env) => cdr]
           [else (error 'trace-expr "internal error: unbound variable: ~s" var)])]
    [(expr:quote datum)
     (t:quote datum)]
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
       [(t:quote val) (error 'trace-expr "fix: cannot fix non-closure: ~e" val)]
       [_ (error 'trace-expr "fix: function not determined by S choices")])]
    [(expr:if e1 e2 e3)
     (match (trace-expr e1 env addr)
       [(t:quote (? values))
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
     (trace-do-fail)]
    [(expr:mem cs e)
     (match (trace-expr e env addr)
       [(t:quote (? function? f))
        (t:quote (memoized f (make-hash (cons cs addr))))]
       [(t:quote f) (error 'trace-expr "mem: not a function: ~e" f)]
       [_ (error 'trace-expr "mem: function not determined by S choices")])]))

;; trace-exprs : (Listof Expr) Env Addr -> (Listof TraceExpr)
(define (trace-exprs exprs env addr)
  (for/list ([expr exprs]) (trace-expr expr env addr)))

;; trace-apply-function : TraceExpr (Listof TraceExpr) Addr -> TraceExpr
(define (trace-apply-function f args addr)
  (match f
    [(t:quote (primop proc))
     ;; FIXME: what about cons, car, cdr, etc? Want (car (cons tvar _)) = tvar
     (cond [(andmap t:quote? args)
            (t:quote (apply proc (map t:quote-datum args)))]
           [else
            (define var (gentv))
            (define ts (t:primop var proc args))
            (emit-and-exec-trace-statement ts)
            var])]
    [(t:quote (closure formals body env))
     (unless (= (length formals) (length args))
       (error 'trace-apply-function "arity mismatch: expected ~s, given ~s"
              (length formals) (length args)))
     (define env* (append (map cons formals args) env))
     (trace-expr body env* addr)]
    [(t:quote (fixed inner-fun))
     (define f* (trace-apply-function (t:quote inner-fun) (list f) 'fix))
     (trace-apply-function f* args addr)]
    [(t:quote (memoized inner-fun table saved-addr))
     (define addr* (cons (cons 'mem args) saved-addr))
     (unless (andmap t:quote? args)
       (error 'trace-apply-function
              "arguments to memoized function not determined by S choices"))
     (hash-ref! table args (lambda () (trace-apply-function inner-fun args addr*)))]
    [(t:quote inner-f) (error 'trace-apply-function "not a function: ~e" inner-f)]
    [(? symbol? tvar)
     (error 'trace-apply-function "function is not determined by S choices")]
    [_ (error 'trace-apply-function "bad function: ~e" f)]))

(define (trace-do-S-sample de addr)
  (defmatch (entry _ _ value) (hash-ref (last-db) addr))
  ;; value is constant wrt trace, because this is an S choice
  (match de
    [(t:quote _)        ;; d doesn't depend on any N choice; constant
     (void)]
    [(? symbol? dvar)   ;; need to rescore if d changes
     (emit-and-exec-trace-statement (t:sample (gentv) dvar (t:quote value)))])
  (hash-set! (current-tmapping) addr (list #t de (t:quote value)))
  (t:quote value))

(define (trace-do-N-sample de addr)
  (defmatch (entry _ _ value) (hash-ref (last-db) addr))
  ;; value may change wrt trace, because this is an N choice
  (define mapped-var (gentv))
  (define result-var (gentv))
  (hash-set! (current-tmapping) addr (list #f de mapped-var))
  (tstore-set! (current-tstore) mapped-var value)
  (emit-and-exec-trace-statement (t:sample result-var de mapped-var))
  result-var)

(define (trace-do-observe-sample d v)
  (emit-and-exec-trace-statement (t:sample (gentv) d v))
  (t:quote #f))

(define (trace-do-fail)
  ((current-fail)))


;; ============================================================
;; MH Sampler -- combining classic eval and tracing
;; ============================================================

(define (mh-eval expr n)
  (define results '())

  (define prev-result #f)
  (define prev-likelihood #f)
  (define prev-db #f)
  (define db-needs-update? #f)

  (define prev-trace #f)
  (define prev-result-te #f)
  (define prev-tmapping #f)
  (define prev-tstore #f)

  (let loop ()
    (match (eval-top expr '#hash())
      [(list result likelihood db)
       (cond [(> likelihood 0)
              (set! prev-result result)
              (set! prev-likelihood likelihood)
              (set! prev-db db)]
             [else (loop)])]))
  (when (zero? (hash-count prev-db))
    (error 'mh "program is deterministic"))

  ;; ERR, this has gotten complicated.
  ;; Let's try something simpler (but less efficient):
  ;; - Adapt lightweight-mh eval-expr nearly as-is, operates on DBs.
  ;; - Add trace-expr fun, completely separate (similar)
  ;; - When doing N change, trace (unless cached), then exec-trace
  ;; - When doing S change, convert tmapping+tstore -> complete DB, then eval-expr
  ;; Never have to worry about likelihood compat, etc.

  (for ([i n])
    (define key-to-change (list-ref (hash-keys prev-db) (random (hash-count prev-db))))
    (cond [(entry-structural? (hash-ref prev-db key-to-change))
           ;; Structural choice
           (when db-needs-update?
             (db-add-tstore! prev-db prev-tmapping prev-tstore)
             (set! db-needs-update? #f))
           (defmatch (entry #t dist value) (hash-ref prev-db key-to-change))
           (defmatch (cons value* proposal-factor) (propose dist value))
           (define modified-prev-db (hash-copy prev-db))
           (hash-set! modified-prev-db key-to-change (entry #t dist value*))
           (defmatch (list new-result new-likelihood new-db)
             (eval-top expr modified-prev-db))
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
                  (set! prev-db new-db)
                  (set! prev-trace #f)
                  (set! prev-result-te #f)
                  (set! prev-tmapping #f)
                  (set! prev-tstore #f)]
                 [else
                  (set! results (cons prev-result results))])]

          [else
           ;; Non-structural choice
           (unless prev-trace
             (defmatch (list result-te tmapping tstore trace) (trace-top expr prev-db))
             (set! prev-trace trace)
             (set! prev-result-te result-te)
             (set! prev-tmapping tmapping)
             (set! prev-tstore tstore))
           (defmatch (list #f dist-te value-te)
             (hash-ref prev-tmapping key-to-change))
           (define dist (eval-trace-expr dist-te prev-tstore))
           (define value (eval-trace-expr value-te prev-tstore))
           (define current-tstore (hash-copy prev-tstore))
           (define prev-l (exec-trace prev-trace current-tstore))
           (defmatch (cons value* proposal-factor) (propose dist value))
           (tstore-set! current-tstore value-te value*)
           (define current-l (exec-trace prev-trace current-tstore))
           (define result (eval-trace-expr prev-result-te current-tstore))
           (define accept-threshold
             (* 1 ;; size of db doesn't chane
                proposal-factor
                (/ current-l prev-l)))
           (cond [(< (random) accept-threshold)
                  (set! db-needs-update? #t)
                  (set! prev-tstore current-tstore)
                  (set! prev-result result)
                  (set! results (cons result results))]
                 [else
                  (set! results (cons prev-result results))])]))

  (reverse results))

;; propose : Dist Value -> (cons Value Real)
(define (propose dist value)
  (defmatch (cons value* logfactor) (dist-drift dist value 0.5))
  (cons value* (exp logfactor)))

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
  '(letrec ([g (lambda () (if (= (S-sample (bernoulli-dist 1/2)) 0) 0 (+ 1 (g))))]) (g)))

(define p-cd
  '(let* ([r (N-sample (normal-dist 9 1))]
          [o (observe-sample (normal-dist r 1) 10)])
    r))

(define p-mem
  '(let* ([f (mem (lambda (i) (N-sample (bernoulli-dist 1/2))))])
    (list (f 1) (f 1) (f 2) (f 2))))

(define p-mix
  '(let* ([A (N-sample (uniform-dist 0 1))]
          [B (N-sample (uniform-dist 0 2))]
          [X .8]
          [Y 1.3])
    (if (= 0 (S-sample (bernoulli-dist 1/2)))
        (let* ([_o1 (observe-sample (normal-dist A .1) X)]
               [_o2 (observe-sample (normal-dist B .1) Y)])
          'ax)
        (let* ([_o1 (observe-sample (normal-dist A .1) Y)]
               [_o2 (observe-sample (normal-dist B .1) X)])
          'ay))))

(define p-ising
  ;; This doesn't work because we don't separate the structure of a list
  ;; from its value --- value depends on N-choices, structure doesn't.
  ;; FIXME
  '(let* ([bigrams (fix (lambda (bigrams)
                          (lambda (lst) (if (null? (cdr lst))
                                       '()
                                       (cons (cons (car lst) (car (cdr lst)))
                                             (bigrams (cdr lst)))))))]
          [repeat (fix (lambda (repeat) (lambda (n f) (if (zero? n) '() (cons (f) (repeat (- n 1) f))))))]
          [map (fix (lambda (map)
                      (lambda (f lst)
                        (if (null? lst) '() (cons (f (car lst)) (map f (cdr lst)))))))]
          [soft-eq (lambda (a b) (observe-sample (normal-dist a 1) b))]
          ;; ----
          [n (+ 1 (S-sample (poisson-dist 3)))]
          [vals (repeat n (lambda () (N-sample (bernoulli-dist 1/2))))]
          [_o (map (lambda (b) (soft-eq (car b) (cdr b))) (bigrams vals))])
    vals))


;; ============================================================

(require (only-in plot plot density plot-new-window?)
         (only-in gamble/viz hist))
(provide hist
         plot-density)

(define (plot-density vals) (plot (density vals)))

(plot-new-window? #t)

