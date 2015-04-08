#lang racket/base
(require racket/match
         gamble)
(provide (all-defined-out))

;; ============================================================
;; Language

;; Surface syntax

;; e ::= x
;;     | real
;;     | boolean
;;     | (quote datum)
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

;; Abstract syntax

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

;; A CallSite could be any value, but we use fresh symbols
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

;; ============================================================
;; Evaluation support

;; A Value is one of
;; - datum
;; - (primop Symbol)
;; - Function
;; A Function is one of
;; - (closure (Listof Symbol) Expr Env)
;; - (fixed Function)
;; - (memoized Function Address Hash)
;; (Note: primops are applicable, but not "Function" accepted by fix, mem.)
(struct primop (name) #:transparent)
(struct closure (formals body env) #:transparent)
(struct fixed (fun) #:transparent)
(struct memoized (fun addr table) #:transparent)

;; function? : Value -> Boolean
(define (function? v)
  (or (closure? v) (fixed? v) (memoized? v)))

;; ------------------------------------------------------------

;; An Env is (Listof (cons Symbol Value))

;; {scheme-,dist-,}primops : (Listof (cons Symbol Procedure))
(define-values (scheme-primops dist-primops)
  (let-syntax ([primop-alist
                (syntax-rules ()
                  [(_ name ...) (list (cons 'name name) ...)])])
    (values
     (primop-alist + - * / = < > <= >= zero?
                   not
                   cons list car cdr null? pair?)
     (primop-alist bernoulli-dist binomial-dist categorical-dist
                   geometric-dist poisson-dist
                   beta-dist cauchy-dist exponential-dist gamma-dist
                   logistic-dist normal-dist pareto-dist uniform-dist))))
(define primops (append scheme-primops dist-primops))

;; primop-name->procedure : Symbol -> Procedure
(define (primop-name->procedure name)
  (cond [(assq name primops) => cdr]
        [else (error 'primop-name->procedure "unknown primop name: ~s" name)]))

;; primop->procedure : Primop -> Procedure
(define (primop->procedure p)
  (primop-name->procedure (primop-name p)))

;; dist-primop? : Symbol -> Boolean
;; Indicates whether s is the name of a dist-building primop.
(define (dist-primop? s)
  (and (assq s dist-primops) #t))

;; base-env : Env
(define base-env (map (lambda (name) (cons name (primop name))) (map car primops)))

;; ============================================================
;; Example programs

(define p-geometric
  (parse-expr
   '(letrec ([g (lambda () (if (= (S-sample (bernoulli-dist 1/2)) 0) 0 (+ 1 (g))))]) (g))))

(define p-cd
  (parse-expr
   '(let* ([r (N-sample (normal-dist 9 1))]
           [o (observe-sample (normal-dist r 1) 10)])
     r)))

(define p-mem
  (parse-expr
   '(let* ([f (mem (lambda (i) (N-sample (bernoulli-dist 1/2))))])
     (list (f 1) (f 1) (f 2) (f 2)))))

(define p-mem2
  (parse-expr
   '(let* ([build-rlist
            (fix (lambda (build-rlist)
                   (lambda (n f)
                     (if (zero? n) '() (cons (f n) (build-rlist (- n 1) f))))))]
           [n (S-sample (poisson-dist 5))]
           [f (mem (lambda (i) (N-sample (bernoulli-dist 1/2))))])
     (build-rlist n f))))

(define p-match
  (parse-expr
   '(let* ([soft-eq (lambda (a b) (observe-sample (normal-dist a 1) b))]
           [A (N-sample (normal-dist 0 1))]
           [B (N-sample (normal-dist 1 1))]
           [X .3]
           [Y .8])
     (if (= 0 (S-sample (bernoulli-dist 1/2)))
         (let* ([_o (list (soft-eq A X) (soft-eq B Y))])
           'right)
         (let* ([_o (list (soft-eq A Y) (soft-eq B X))])
           'wrong)))))

(define p-ising
  (parse-expr
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
     vals)))

(define p-coin
  (parse-expr
   '(let* ([repeat (fix (lambda (repeat) (lambda (n f) (if (zero? n) '() (cons (f) (repeat (- n 1) f))))))]
           ;; ----
           [fair (S-sample (bernoulli-dist 9/10))]
           [1prob (if (= fair 1) 1/2 (N-sample (beta-dist 1 1)))]
           [obs-flip (lambda (result) (observe-sample (bernoulli-dist 1prob) result))]
           [_o (repeat 50 (lambda () (obs-flip 1)))])
     fair)))

(define p-circle
  (parse-expr
   '(let* ([soft-eq (lambda (a b) (observe-sample (normal-dist a 1) b))]
           ;; ----
           [x (N-sample (uniform-dist -2 2))]
           [y (N-sample (uniform-dist -2 2))]
           [_o (soft-eq (+ (* x x) (* y y)) 1)])
     (list x y))))
