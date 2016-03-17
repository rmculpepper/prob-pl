;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         "base.rkt")
(provide (all-defined-out))

;; A-normalization
;; u ::= x | (quote datum) | (lambda (x ...) e)
;; e ::= u | (u u ...) | (op u ...) | (S-sample u) | ...

;; We assume no variables start with "t_" because we're lazy.
(define anf-counter 0)
(define (genvar)
  (set! anf-counter (add1 anf-counter))
  (string->symbol (format "t_~s" anf-counter)))

;; type (A t) = (cons t (listof (list Symbol Expr)))
(define (Aunit x [bs null]) (cons x bs))
(define (Abind c f)
  (defmatch (cons v1 bs1) c)
  (defmatch (cons v2 bs2) (f v1))
  (cons v2 (append bs2 bs1)))
(define-syntax Ado
  (syntax-rules (=>)
    [(Ado () body)
     (let () body)]
    [(Ado () => expr)
     (Aunit expr)]
    [(Ado ([p1 rhs1] . clauses) . body)
     (Abind rhs1 (match-lambda [p1 (Ado clauses . body)]))]))

;; anf* : Expr -> (A Expr)
(define (anf* e)
  (define (recur e)
    (Ado ([a (anf* e)])
      (if (simple-expr? a)
          (Aunit a)
          (let ([var (genvar)])
            (Aunit var `([,var ,a]))))))
  (define (recur* es)
    (cond [(null? es) (Aunit null)]
          [else (Ado ([a1 (recur (car es))] [as (recur* (cdr es))]) => (cons a1 as))]))
  (match e
    [(? symbol? e) (Aunit e)]
    [(expr:quote _) (Aunit e)]
    [(expr:lambda vars body)
     (Aunit (expr:lambda vars (anf body)))]
    [(expr:fix e)
     (Ado ([a (recur e)])
          => (expr:fix a))]
    [(expr:app cs e1 es2)
     (Ado ([a1 (recur e1)]
           [as2 (recur* es2)])
          => (expr:app cs a1 as2))]
    [(expr:if e1 e2 e3)
     (Ado ([a1 (recur e1)]) => (expr:if a1 (anf e2) (anf e3)))]
    [(expr:S-sample cs e)
     (Ado ([a (recur e)]) => (expr:S-sample cs a))]
    [(expr:N-sample cs e)
     (Ado ([a (recur e)]) => (expr:N-sample cs a))]
    [(expr:observe-sample e1 e2)
     (Ado ([a1 (recur e1)]
           [a2 (recur e2)])
          => (expr:observe-sample a1 a2))]
    [(expr:fail) (Aunit e)]
    [(expr:mem cs e)
     (Ado ([a (recur e)])
          => (expr:mem cs a))]
    [(expr:let* '() '() body)
     (anf* body)]
    [(expr:let* (cons var1 vars2) (cons e1 es2) body)
     (Ado ([a1 (anf* e1)]
           [_  (Aunit 'unused `([,var1 ,a1]))])
          (anf* (expr:let* vars2 es2 body)))]))

(define (anf e)
  (match (anf* e)
    [(cons a '())
     a]
    [(cons a bs)
     (let ([bs (reverse bs)])
       (expr:let* (map car bs) (map cadr bs) a))]))

(define (simple-expr? e)
  (or (symbol? e) (expr:quote? e) (expr:lambda? e)))

;; Collapse adjacent let* bindings

(define (make-traverse f)
  (define (loop e)
    (cond [(f e) => values]
          [else
           (match e
             [(? symbol? x) x]
             [(expr:quote _) e]
             [(expr:lambda vars body)
              (expr:lambda vars (loop body))]
             [(expr:fix e)
              (expr:fix (loop e))]
             [(expr:app cs fun args)
              (expr:app cs (loop fun) (map loop args))]
             [(expr:if e1 e2 e3)
              (expr:if (loop e1) (loop e2) (loop e3))]
             [(expr:S-sample cs e)
              (expr:S-sample cs (loop e))]
             [(expr:N-sample cs e)
              (expr:N-sample cs (loop e))]
             [(expr:observe-sample e1 e2)
              (expr:observe-sample (loop e1) (loop e2))]
             [(expr:fail) e]
             [(expr:mem cs e)
              (expr:mem cs (loop e))]
             [(expr:let* vars rhss body)
              (expr:let* vars (map loop rhss) (loop body))])]))
  loop)

(define collapse-lets
  (make-traverse
   (match-lambda
    [(expr:let* vars1 rhss1 (expr:let* vars2 rhss2 body))
     (collapse-lets (expr:let* (append vars1 vars2) (append rhss1 rhss2) body))]
    [_ #f])))

(define expand-lets
  (make-traverse
   (match-lambda
    [(expr:let* '() '() body)
     (expand-lets body)]
    [(expr:let* (cons var1 vars) (cons rhs1 rhss) body)
     (expr:let* (list var1) (list rhs1) (expand-lets (expr:let* vars rhss body)))]
    [_ #f])))

;; Safe-for-space

;; Build env narrowing into evaluator, aided by memoized free-vars
;; function, rather than a src-to-src transformation.

;; free-variables : Expr -> (Setof Symbol)
;; Memoized using free-variable-table.
(define (free-variables e)
  (hash-ref! free-variable-table e (lambda () (compute-fv e))))

;; free-variable-table : Hash[Expr => (Setof Symbol)]
(define free-variable-table (make-weak-hasheq))

;; compute-fv : Expr -> (Setof Symbol)
(define (compute-fv e)
  ;; loop : Expr -> (Setof Symbol)
  (define (loop e)
    (let ([fv (loop* e)])
      (hash-set! free-variable-table e fv)
      fv))
  ;; loop* : Expr -> (Setof Symbol)
  (define (loop* e)
    (match e
      [(? symbol? x) (set x)]
      [(expr:quote _) (set)]
      [(expr:lambda vars body)
       (set-subtract (loop body) (list->set vars))]
      [(expr:fix e)
       (loop e)]
      [(expr:app cs e1 es2)
       (apply set-union (loop e1) (map loop es2))]
      [(expr:if e1 e2 e3)
       (set-union (loop e1) (loop e2) (loop e3))]
      [(expr:S-sample cs e)
       (loop e)]
      [(expr:N-sample cs e)
       (loop e)]
      [(expr:observe-sample e1 e2)
       (set-union (loop e1) (loop e2))]
      [(expr:fail) (set)]
      [(expr:mem cs e)
       (loop e)]
      [(expr:let* vars rhss body)
       (for/fold ([fv (loop body)])
                 ([var (reverse vars)] [rhs (reverse rhss)])
         (set-union (set-remove fv var) (loop rhs)))]))
  (loop e))
