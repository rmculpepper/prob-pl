#lang racket/base
(require racket/match
         racket/pretty
         "base.rkt"
         mzlib/pconvert)
(provide (all-defined-out))

;; Configure pconvert
(constructor-style-printing #t)

;; IDEA: visualize env as let* context!

(struct expr:eval (expr env) #:transparent)
(struct expr:value (value) #:transparent)
(struct expr:focus (expr) #:transparent) ;; only used to mark redex/contractum

;; current-state : (Parameterof Expr+)
;; where Expr+ is like Expr+ but may contain expr:eval.
(define current-state (make-parameter #f))

;; A Context is (Listof Nat)
;; where each nat indicates the position in the expression being
;; evaluated and the frames are innermost-first.
(define current-context (make-parameter null))

;; current-left-foot : (Parameterof Any)
(define current-left-foot (make-parameter #f))

;; ------------------------------------------------------------

(define (call-with-context ctx proc)
  (parameterize ((current-context (cons ctx (current-context))))
    (define result (proc))
    (walk (expr:value result) #f)
    result))

(define-syntax-rule (with-context ctx body ...)
  (call-with-context ctx (lambda () body ...)))

;; ------------------------------------------------------------

(struct step (type ctx old-expr old-extras new-expr new-extras) #:transparent)

(define (walk expr step-type [extra #f])
  (left-foot extra)
  (right-foot expr step-type extra))

(define (left-foot [extra #f])
  (current-left-foot extra))

(define (right-foot expr step-type [extra #f])
  (define old-extra (current-left-foot))
  (define ctx (reverse (current-context)))
  (define old-state (current-state))
  (define new-state (state-update old-state ctx expr))
  (current-state new-state)
  (left-foot extra)
  (when step-type
    (emit-step (step step-type ctx
                     (mark-r/c old-state ctx) old-extra
                     (mark-r/c new-state ctx) extra))))

(define (default-emit-step s)
  (match s
    [(step step-type ctx old-state old-extra new-state new-extra)
     (printf "STEP [~a] ; weight = ~s\n" step-type new-extra)
     (print-state new-state ctx new-extra)
     (newline)]))

(define current-emit-step (make-parameter default-emit-step))

(define (emit-step s) ((current-emit-step) s))

(define (state-update state ctx expr)
  (state-update* state ctx (lambda (_) expr)))

(define (mark-r/c state ctx)
  (state-update* state ctx expr:focus))

(define (state-update* state0 ctx0 f)
  (define (bad sub subctx)
    (error 'state-update "impossible\nstate = ~s\nctx = ~s\nsub = ~s\nsubctx = ~s\nf = ~s\n"
           state0 ctx0 sub subctx (f sub)))
  (let outerloop ([state state0] [ctx ctx0])
    (match ctx
      [(cons frame ctx-rest)
       (define (C e n) (if (equal? frame n) (outerloop e ctx-rest) e))
       (let loop ([state state])
         (match state
           [(expr:eval e env)
            (expr:eval (loop e) env)]
           [(expr:app cs op args)
            (expr:app cs (C op 0) (for/list ([arg args] [i (in-naturals 1)]) (C arg i)))]
           [(expr:fix e)
            (expr:fix (C e 1))]
           [(expr:if e1 e2 e3)
            (expr:if (C e1 1) (C e2 2) (C e3 3))]
           [(expr:S-sample cs e)
            (expr:S-sample cs (C e 1))]
           [(expr:N-sample cs e)
            (expr:N-sample cs (C e 1))]
           [(expr:observe-sample e1 e2)
            (expr:observe-sample (C e1 1) (C e2 2))]
           [(expr:mem cs e)
            (expr:mem cs (C e 1))]
           [(expr:let* vars rhss body)
            (expr:let* vars (for/list ([rhs rhss] [i (in-naturals 0)]) (C rhs i)) body)]
           [_
            ;; Other forms don't have contexts.
            (bad state ctx)]))]
      ['()
       (f state)])))

;; ------------------------------------------------------------

(define (print-state state ctx likelihood)
  (pretty-write (syntax->datum (expr->stx state base-env))))

(define (expr->sexpr expr)
  (syntax->datum (expr->stx expr)))

(define (expr->stx expr [base-env base-env])
  (mkstx (expr->stx* expr base-env)))

(define (expr->stx* expr base-env)
  (define (loop expr [env base-env])
    (expr->stx expr env))
  (match expr
    [(? symbol? var) var]
    [(expr:quote value) (value->stx value base-env)]
    [(expr:lambda args body) `(lambda ,args ,(loop body))]
    [(expr:fix e) `(fix ,(loop e))]
    [(expr:app cs op args) `(,(loop op) ,@(map loop args))]
    [(expr:if e1 e2 e3) `(if ,(loop e1) ,(loop e2) ,(loop e3))]
    [(expr:S-sample cs e) `(S-sample ,(loop e))]
    [(expr:N-sample cs e) `(N-sample ,(loop e))]
    [(expr:observe-sample e1 e2) `(observe-sample ,(loop e1) ,(loop e2))]
    [(expr:fail) `(fail)]
    [(expr:mem cs e) `(mem ,(loop e))]
    [(expr:let* vars rhss body)
     (let bindingsloop ([vars vars] [rhss rhss] [env* base-env] [rbindings null])
       (match* [vars rhss]
         [['() '()]
          `(let* ,(reverse rbindings) ,(expr->stx body env*))]
         [[(cons var vars) (cons rhs rhss)]
          (bindingsloop vars rhss
                        (match rhs
                          [(expr:value v)
                           (cons (cons var v) env*)]
                          [else env*])
                        (cons (list var (expr->stx rhs env*)) rbindings))]))]
    [(expr:eval expr env)
     (wrap-env env base-env (expr->stx* expr env))]
    [(expr:value value) (value->stx value base-env)]
    [(expr:focus e)
     (let ([stx (loop e)])
       (syntax-property stx 'focus #t))]
    [(expr:forget vars e)
     `(let* (,(for/list ([var vars]) `[,var '__forget__])) ,(loop e))]
    ))

(define (value->stx v base-env)
  (mkstx
   (match v
     [(closure args body env)
      (wrap-env env base-env `(lambda ,args ,(expr->stx body env)))]
     [(fixed f)
      `(fix ,(value->stx f base-env))]
     [(primop name)
      name]
     [(? number?) v]
     [_ (print-convert v)])))

(define (wrap-env env base-env body)
  (let ([bindings (env->bindings env base-env)])
    (cond [(null? bindings)
           body]
          [else
           (match body
             [(list 'let* inner-bindings inner-body)
              `(let* ,(append bindings inner-bindings) ,inner-body)]
             [else
              `(let* ,bindings ,body)])])))

(define (env->bindings env base-env)
  (let loop ([env env] [acc null])
    (cond [(null? env) acc]
          [(extension? base-env env) acc]
          [else
           (let ([frame (list (caar env) (value->stx (cdar env) (cdr env)))])
             (loop (cdr env) (cons frame acc)))])))

(define (extension? xs ys)
  (or (eq? xs ys)
      (and (pair? xs) (extension? (cdr xs) ys))))

(define (mkstx x) (datum->syntax #f x))

(define (foci stx)
  (let loop ([stx stx] [onto null])
    (cond [(pair? stx)
           (loop (car stx) (loop (cdr stx) onto))]
          [(syntax? stx)
           (if (syntax-property stx 'focus)
               (cons stx onto)
               (loop (syntax-e stx) onto))]
          [else onto])))
