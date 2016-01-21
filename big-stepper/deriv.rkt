#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         "../base.rkt")
(provide (all-defined-out))

(struct node:eval (expr env inner result) #:transparent)
(struct deriv:variable (?1) #:transparent)
(struct deriv:quote ()  #:transparent)
(struct deriv:let* (rhss body) #:transparent)
(struct deriv:lambda () #:transparent)
(struct deriv:app (op args apply) #:transparent)
(struct deriv:fix (arg ?1) #:transparent)
(struct deriv:if (test branch) #:transparent)
(struct deriv:S-sample (inner ?1 sample) #:transparent)
(struct deriv:N-sample (inner ?1 sample) #:transparent)
(struct deriv:observe-sample (dist value ?1 weight) #:transparent)
(struct deriv:fail (?1) #:transparent)
(struct deriv:mem (fun ?1) #:transparent)
(struct deriv:error (exn) #:transparent)

(struct node:apply (fun args inner result) #:transparent)
(struct apply:primop (?1) #:transparent)
(struct apply:closure (?1 body) #:transparent)
(struct apply:fixed (self apply) #:transparent)
(struct apply:mem-hit () #:transparent)
(struct apply:mem-miss (apply) #:transparent)
(struct apply:error (exn) #:transparent)

;; ============================================================
;; Processing on raw derivations

;; - put exn in result fields
;; - trim environments to elim base-env

;; M[A] is S -> (cons A S)
(define (Munit x) (lambda (s) (cons x s)))
(define ((Mbind c f) s0)
  (defmatch (cons a s) (c s0))
  (unless (procedure? f) (error 'Mbind "f is not procedure: ~e" f))
  (define fa (f a))
  (unless (procedure? fa)
    (error 'Mbind "fa is not procedure:\n  f = ~e\n  a = ~e\n  fa = ~e" f a fa))
  (defmatch (cons a* s*) (fa s))
  (cons a* (or s s*)))

(define (Merr x) (lambda (s) (cons (void) x)))
(define (Mget) (lambda (s) (cons s s)))
(define-syntax Mdo
  (syntax-rules (->)
    [(Mdo () -> e) (Munit e)]
    [(Mdo () e)    (let () e)]
    [(Mdo ([x e] . bs) . body)
     (Mbind e (lambda (x) (Mdo bs . body)))]))

(define (annotate d)
  (car ((ann d) #f)))

(define (ann d)
  (define-syntax copy
    (syntax-rules ($ ->)
      [(_)
       (match d)]
      [(_ [pattern -> rhs] . clauses)
       (match d [pattern rhs] [_ (copy . clauses)])]
      [(_ [$ (struct part ...)] . clauses)
       (match d
         [(struct part ...)
          (Mdo ([part (ann part)] ...) -> (struct part ...))]
         [_ (copy . clauses)])]))
  (copy
    ['() -> (Munit '())]
    [(cons e1 es) -> (Mdo ([e1 (ann e1)] [es (ann es)]) -> (cons e1 es))]
    [(node:eval expr env inner result)
     -> (Mdo ([inner (ann inner)] [ERR (Mget)])
             -> (node:eval expr env inner (or ERR result)))]
    [$ (deriv:let* rhss body)]
    [$ (deriv:app op args apply)]
    [$ (deriv:fix arg ?1)]
    [$ (deriv:if test branch)]
    [$ (deriv:S-sample inner ?1 sample)]
    [$ (deriv:N-sample inner ?1 sample)]
    [$ (deriv:observe-sample dist value ?1 weight)]
    [$ (deriv:fail ?1)]
    [$ (deriv:mem fun ?1)]
    [$ (node:apply fun args inner v)]
    [$ (apply:primop ?1)]
    [$ (apply:closure ?1 body)]
    [$ (apply:fixed self apply)]
    [$ (apply:mem-miss apply)]
    [(? exn? exn) -> (Merr exn)]
    [_ -> (Munit d)]))

;; ------------------------------------------------------------

(define (trim d)
  (match d
    [(node:eval expr env inner result)
     (node:eval expr (trim-env env) (trim inner) result)]
    [(deriv:let* rhss body)
     (deriv:let* (map trim rhss) (trim body))]
    [(deriv:app op args apply)
     (deriv:app (trim op) (map trim args) (trim apply))]
    [(deriv:fix arg ?1)
     (deriv:fix (trim arg) ?1)]
    [(deriv:if test branch)
     (deriv:if (trim test) (trim branch))]
    [(deriv:S-sample inner ?1 sample)
     (deriv:S-sample (trim inner) ?1 sample)]
    [(deriv:N-sample inner ?1 sample)
     (deriv:N-sample (trim inner) ?1 sample)]
    [(deriv:observe-sample dist value ?1 weight)
     (deriv:observe-sample (trim dist) (trim value) ?1 weight)]
    [(deriv:fail ?1)
     (deriv:fail ?1)]
    [(deriv:mem fun ?1)
     (deriv:mem (trim fun) ?1)]
    [(node:apply fun args inner result)
     (node:apply fun args (trim inner) result)]
    [(apply:closure ?1 body)
     (apply:closure ?1 (trim body))]
    [(apply:fixed self apply)
     (apply:fixed (trim self) (trim apply))]
    [(apply:mem-miss apply)
     (apply:fixed (trim apply))]
    [_ d]))

(define (trim-value v)
  (match v
    [(closure args expr env)
     (closure args expr (trim-env env))]
    [(fixed f)
     (fixed (trim-value f))]
    [(memoized f addr table)
     (memoized (trim-value f) addr table)]
    [_ v]))

(define (trim-env env)
  ;; FIXME: drop base-env
  (let loop ([env env])
    (if (eq? env base-env)
        null
        (match env
          [(cons (cons var value) rest-env)
           (cons (cons var (trim-value value))
                 (loop rest-env))]))))
