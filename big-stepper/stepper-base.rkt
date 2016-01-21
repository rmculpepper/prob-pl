#lang racket/base
(require racket/match
         racket/pretty
         "../base.rkt"
         mzlib/pconvert)
(provide (all-defined-out))

;; Configure pconvert
(constructor-style-printing #t)

;; ------------------------------------------------------------

(define (expr->sexpr expr)
  (syntax->datum (expr->stx expr)))

(define (expr->stx expr)
  (mkstx (expr->stx* expr)))

(define (expr->stx* expr)
  (define (loop expr)
    (expr->stx expr))
  (match expr
    [(? symbol? var) var]
    [(expr:quote value) `(quote ,value)]
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
     `(let* ,(for/list ([var vars] [rhs rhss]) `[,var ,(loop rhs)])
       ,(loop body))]
    ))

(define (value->sexpr v [base-env base-env])
  (syntax->datum (value->stx v base-env)))

(define (value->stx v base-env)
  (mkstx
   (match v
     [(closure args body env)
      `(closure ,args ,(expr->stx body) ,(env->sexpr env base-env))]
     [(fixed f)
      `(fix ,(value->stx f base-env))]
     [(primop name)
      name]
     [(? number?) v]
     [_ (print-convert v)])))

(define (env->sexpr env [base-env base-env])
  (cond [(eq? env base-env) null]
        [(null? env) null]
        [else
         (cons (cons (caar env) (value->sexpr (cdar env)))
               (env->sexpr (cdr env) base-env))]))

(define (mkstx x) (datum->syntax #f x))
