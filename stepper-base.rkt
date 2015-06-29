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
  (define old-state (current-state))
  (define old-extra (current-left-foot))
  (define ctx (current-context))
  (define new-state (state-update old-state (reverse ctx) expr))
  (current-state new-state)
  (left-foot extra)
  (when step-type
    (emit-step (step step-type ctx old-state old-extra new-state extra))))

(define (default-emit-step s)
  (match s
    [(step step-type ctx old-state old-extra new-state new-extra)
     (printf "STEP [~a] ; weight = ~s\n" step-type new-extra)
     (print-state new-state ctx new-extra)
     (newline)]))

(define current-emit-step (make-parameter default-emit-step))

(define (emit-step s) ((current-emit-step) s))

(define (state-update state0 ctx0 expr)
  (define (bad) (error 'state-update "impossible: state = ~s, ctx = ~s" state0 ctx0))
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
           [_
            ;; Other forms don't have contexts.
            (bad)]))]
      ['()
       expr])))

;; ------------------------------------------------------------

(define (print-state state ctx likelihood)
  (pretty-write (expr->sexpr state base-env)))

(define (expr->sexpr expr [base-env base-env])
  (let loop ([expr expr])
    (match expr
      [(? symbol? var) var]
      [(expr:quote value) (value->sexpr value base-env)]
      [(expr:lambda args body) `(lambda ,args ,(loop body))]
      [(expr:fix e) `(fix ,(loop e))]
      [(expr:app cs op args) `(,(loop op) ,@(map loop args))]
      [(expr:if e1 e2 e3) `(if ,(loop e1) ,(loop e2) ,(loop e3))]
      [(expr:S-sample cs e) `(S-sample ,(loop e))]
      [(expr:N-sample cs e) `(N-sample ,(loop e))]
      [(expr:observe-sample e1 e2) `(observe-sample ,(loop e1) ,(loop e2))]
      [(expr:fail) `(fail)]
      [(expr:mem cs e) `(mem ,(loop e))]
      [(expr:eval expr env)
       (wrap-env env base-env (expr->sexpr expr env))]
      [(expr:value value) (value->sexpr value base-env)]
      )))

(define (value->sexpr v base-env)
  (match v
    [(closure args body env)
     (wrap-env env base-env `(lambda ,args ,(expr->sexpr body env)))]
    [(fixed f)
     `(fix ,(value->sexpr f base-env))]
    [(primop name)
     name]
    [(? number?) v]
    [_ (print-convert v)]))

(define (wrap-env env base-env body)
  (let ([bindings (env->bindings env base-env)])
    (cond [(null? bindings)
           body]
          [else
           `(let* ,bindings ,body)])))

(define (env->bindings env base-env)
  (let loop ([env env] [acc null])
    (cond [(null? env) acc]
          [(extension? base-env env) acc]
          [else
           (let ([frame (list (caar env) (value->sexpr (cdar env) (cdr env)))])
             (loop (cdr env) (cons frame acc)))])))

(define (extension? xs ys)
  (or (eq? xs ys)
      (and (pair? xs) (extension? (cdr xs) ys))))
