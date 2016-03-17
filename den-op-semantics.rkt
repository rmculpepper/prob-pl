;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require racket/match
         (except-in gamble sequence)
         "base.rkt")
(provide (all-defined-out))

;; ============================================================
;; Denotational-Operational Semantics

;; An (Answer X) is one of
;; - (Just X)
;; - (Error String)
;; - (Fail)
;; - (Timeout)
(struct Just (value) #:transparent)
(struct Error (message) #:transparent)
(struct Fail () #:transparent)
(struct Timeout () #:transparent)

(define (unitA v)
  (Just v))

(define (bindA c f)
  (match c
    [(Just x) (f x)]
    [_ c]))

;; A (Dist X) is a (Hashof Value => Real+)
;; where the values sum to 1.

(define (unitD x)
  (hash x 1))

(define (bindD c f)
  (for*/fold ([t (hash)])
             ([(x w1) (in-hash c)]
              [(y w2) (in-hash (f x))])
    (hash-set t y (+ (hash-ref t y 0) (* w1 w2)))))

;; A (DA X) is (Dist (Answer X))
;; A Denotation is (DA Value) = (Dist (Answer Value))

;; unit : X -> DA X
(define (unit v)
  (unitD (unitA v)))

;; bind : (DA X) (X -> DA X) -> (DA X)
(define (bind c f)
  (bindD c
    (lambda (a)
      (match a
        [(Just v) (f v)]
        [_ (unitD a)]))))

;; sequence : (Listof (M a)) -> (M (Listof a))
(define (sequence cs)
  (cond [(pair? cs)
         (mdo ([v (car cs)]
               [vs (sequence (cdr cs))])
           (unit (cons v vs)))]
        [else (unit null)]))

(define-syntax mdo
  (syntax-rules ()
    [(mdo ([x e] . rest) . body)
     (bind e (lambda (x) (mdo rest . body)))]
    [(mdo () . body)
     (let () . body)]))

;; ============================================================

;; den-top : Expr Nat -> Denotation
(define (den-top expr n)
  (den-expr expr base-env n))

;; den-expr : Expr Env Nat -> Denotation
(define (den-expr expr env n)
  (cond [(zero? n)
         (unitD (Timeout))]
        [else (den-expr* expr env n)]))

(define (den-expr* expr env n+1)
  (define n (sub1 n+1))
  (match expr
    [(? symbol? var)
     (cond [(assoc var env)
            => (lambda (p) (unit (cdr p)))]
           [else (unitD (Error "unbound variable"))])]
    [(expr:quote datum)
     (unit datum)]
    [(expr:lambda formals body)
     (unit (closure formals body env))]
    [(expr:app _ f args)
     (mdo ([vf (den-expr f env n)]
           [vargs (den-exprs args env n)])
       (apply-function vf vargs n))]
    [(expr:fix expr)
     (mdo ([v (den-expr expr env n)])
       (if (closure? v)
           (unit (fixed v))
           (unitD (Error "cannot fix non-closure"))))]
    [(expr:if e1 e2 e3)
     (mdo ([v1 (den-expr e1 env n)])
       (if v1
           (den-expr e2 env n)
           (den-expr e3 env n)))]
    [(expr:S-sample _ de)
     (mdo ([d (den-expr de env n)])
       (if (dist? d)
           (do-sample d)
           (unitD (Error "not a dist"))))]
    [(expr:N-sample _ de)
     (mdo ([d (den-expr de env n)])
       (if (dist? d)
           (do-sample d)
           (unitD (Error "not a dist"))))]
    [(expr:observe-sample de ve)
     (mdo ([d (den-expr de env n)]
           [v (den-expr ve env n)])
       (if (dist? d)
           (do-observe-sample d v)
           (unitD (Error "not a dist"))))]
    [(expr:fail)
     (unitD (Fail))]
    [(expr:mem _ e)
     (unitD (Error "mem not supported"))]))

;; den-exprs : (Listof Expr) Env -> (Listof Value)
(define (den-exprs exprs env n)
  (sequence (for/list ([expr (in-list exprs)]) (den-expr expr env n))))

;; apply-function : Value (Listof Value) Nat -> Value
(define (apply-function f args n)
  (match f
    [(primop name)
     (unit (apply (primop-name->procedure name) args))]
    [(closure formals body env)
     (cond [(not (= (length formals) (length args)))
            (unitD (Error "apply-function :arity"))]
           [else
            (define env* (append (map cons formals args) env))
            (den-expr body env* n)])]
    [(fixed inner-fun)
     (mdo ([f* (apply-function inner-fun (list f) n)])
       (apply-function f* args n))]
    [(memoized inner-fun table _)
     (unitD (Error "apply-function: mem not supported"))]
    [_ (unitD (Error "apply-function: not a function"))]))

;; do-sample : Dist -> Denotation
(define (do-sample d)
  (for/hash ([(v w) (in-dist d)])
    (values (unitA v) w)))

;; do-observe-sample : Dist Value -> ???
(define (do-observe-sample d v)
  (define w (dist-pdf d v))
  (if (= w 1)
      (unit v)
      (hash (unitA v) w
            (Fail) (- 1 w))))
